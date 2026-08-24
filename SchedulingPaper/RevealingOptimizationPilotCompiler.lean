import SchedulingPaper.RevealingOptimizationLearnedPilotAnalysis
import SchedulingPaper.RevealingOptimizationQuotaRounding
import SchedulingPaper.CompletionPairDecomposition
import Mathlib.Tactic

/-!
# A physical pilot compiler for revealing optimization

The pilot and main quota run cannot use two independent copies of the same
jobs.  This module supplies the missing finite compiler.  It executes every
pilot occurrence once, deletes those owners from an independently randomized
virtual quota run, and places the retained observations on the physical
labels.  Owner deletion only lowers the main completion cost; prepending the
pilot costs at most `2 n k (L+1)`.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace PilotCompiler

open Online
open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedEnvelope
open InstanceLearning
open QuotaStrategy
open QuotaFluid
open QuotaRounding

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Generic transcript bookkeeping -/

theorem completionCostFrom_mono_start
    {n : ℕ} (cap : Cap) (processing : Online.Label n → ℝ)
    (transcript : Online.Transcript n) {start finish : ℝ}
    (hstart : start ≤ finish) :
    Online.completionCostFrom cap processing start transcript ≤
      Online.completionCostFrom cap processing finish transcript := by
  rw [Online.completionCostFrom_eq_count_mul_add_suffixWeighted,
    Online.completionCostFrom_eq_count_mul_add_suffixWeighted]
  have hcount : (0 : ℝ) ≤ Online.completionCount processing transcript := by
    positivity
  linarith [mul_le_mul_of_nonneg_left hstart hcount]

/-- Deleting all observations owned by selected labels cannot increase the
completion cost of the retained labels. -/
theorem completionCostFrom_filter_owner_le
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Online.Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Online.Transcript n)
    (keep : Online.Label n → Prop) [DecidablePred keep]
    {start : ℝ} (hstart : 0 ≤ start) :
    Online.completionCostFrom (.finite u) processing start
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      Online.completionCostFrom (.finite u) processing start transcript := by
  induction transcript generalizing start with
  | nil => simp [Online.completionCostFrom]
  | cons observation rest ih =>
      have hduration : 0 ≤
          observation.duration (.finite u) processing := by
        cases observation with
        | testResult job value => simp [Online.Observation.duration]
        | processed job =>
            simpa [Online.Observation.duration] using hp0 job
        | rawCompleted job =>
            simpa [Online.Observation.duration, Online.rawDuration] using hu0
      have hfinish : 0 ≤
          start + observation.duration (.finite u) processing :=
        add_nonneg hstart hduration
      by_cases hkeep : keep observation.ownerLabel
      · rw [List.filter_cons, if_pos (by simp [hkeep])]
        simp only [Online.completionCostFrom]
        linarith [ih hfinish]
      · rw [List.filter_cons, if_neg (by simp [hkeep])]
        simp only [Online.completionCostFrom]
        have htail := ih hstart
        have htime := completionCostFrom_mono_start (.finite u) processing rest
          (show start ≤ start + observation.duration (.finite u) processing by
            linarith)
        have hcompletion :
            0 ≤ if (observation.completionLabel processing).isSome then
              start + observation.duration (.finite u) processing else 0 := by
          split <;> positivity
        linarith

theorem completionCost_filter_owner_le
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Online.Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Online.Transcript n)
    (keep : Online.Label n → Prop) [DecidablePred keep] :
    Online.completionCost (.finite u) processing
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      Online.completionCost (.finite u) processing transcript := by
  exact completionCostFrom_filter_owner_le hu0 processing hp0 transcript keep
    (start := 0) (by norm_num)

theorem completionCount_filter_owner_le
    {n : ℕ} (processing : Online.Label n → ℝ)
    (keep : Online.Label n → Prop) [DecidablePred keep]
    (transcript : Online.Transcript n) :
    Online.completionCount processing
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      Online.completionCount processing transcript := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      by_cases hkeep : keep observation.ownerLabel
      · rw [List.filter_cons, if_pos (by simp [hkeep])]
        simp only [Online.completionCount_cons]
        split <;> omega
      · rw [List.filter_cons, if_neg (by simp [hkeep])]
        simp only [Online.completionCount_cons]
        split <;> omega

@[simp] theorem completionCount_map_relabel
    {n : ℕ} (processing : Online.Label n → ℝ)
    (order : Equiv.Perm (Online.Label n))
    (transcript : Online.Transcript n) :
    Online.completionCount processing
        (transcript.map (Online.Observation.relabel order)) =
      Online.completionCount (fun virtual => processing (order virtual))
        transcript := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      simp only [List.map_cons, Online.completionCount_cons,
        Online.Observation.completionLabel_relabel, Option.isSome_map, ih]

theorem completionCost_append
    {n : ℕ} (cap : Cap) (processing : Online.Label n → ℝ)
    (left right : Online.Transcript n) :
    Online.completionCost cap processing (left ++ right) =
      Online.completionCost cap processing left +
        Online.completionCost cap processing right +
        Online.completionCount processing right *
          Online.transcriptElapsed cap processing left := by
  rw [Online.completionCost_eq_suffixWeightedDuration,
    Online.suffixWeightedDuration_append,
    ← Online.completionCost_eq_suffixWeightedDuration,
    ← Online.completionCost_eq_suffixWeightedDuration]
  ring

/-! ## The revealing pilot block -/

def pilotJobWord
    (processing : Online.Label n → ℝ) (job : Online.Label n) :
    Online.Transcript n :=
  [.testResult job (processing job), .processed job]

def revealingPilotTranscript
    (processing : Online.Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) : Online.Transcript n :=
  positions.toList.flatMap fun position =>
    pilotJobWord processing (order position)

def pilotOccurrenceSet
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  positions.image order

@[simp] theorem pilotJobWord_completionCount
    (processing : Online.Label n → ℝ) (job : Online.Label n) :
    Online.completionCount processing (pilotJobWord processing job) = 1 := by
  by_cases hp : processing job = 0 <;>
    simp [pilotJobWord, Online.completionCount,
      Online.Observation.completionLabel, hp]

@[simp] theorem pilotJobWord_elapsed
    (u : ℝ) (processing : Online.Label n → ℝ) (job : Online.Label n) :
    Online.transcriptElapsed (.finite u) processing
        (pilotJobWord processing job) =
      1 + processing job := by
  simp [pilotJobWord, Online.transcriptElapsed,
    Online.Observation.duration]

@[simp] theorem revealingPilotTranscript_completionCount
    (processing : Online.Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) :
    Online.completionCount processing
        (revealingPilotTranscript processing positions order) =
      positions.card := by
  unfold revealingPilotTranscript
  have hlist : ∀ list : List (Fin n),
      Online.completionCount processing
          (list.flatMap fun position =>
            pilotJobWord processing (order position)) = list.length := by
    intro list
    induction list with
    | nil => simp
    | cons position rest ih =>
        simp [Online.completionCount_append, ih, Nat.add_comm]
  simpa using hlist positions.toList

theorem revealingPilotTranscript_elapsed_le
    {u L : ℝ} (processing : Online.Label n → ℝ)
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n))
    (hpL : ∀ job, processing job ≤ L) :
    Online.transcriptElapsed (.finite u) processing
        (revealingPilotTranscript processing positions order) ≤
      positions.card * (L + 1) := by
  unfold revealingPilotTranscript
  have hlist : ∀ list : List (Fin n),
      Online.transcriptElapsed (.finite u) processing
          (list.flatMap fun position =>
            pilotJobWord processing (order position)) ≤
        list.length * (L + 1) := by
    intro list
    induction list with
    | nil => simp
    | cons position rest ih =>
        simp only [List.flatMap_cons, Online.transcriptElapsed_append,
          pilotJobWord_elapsed, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [hpL (order position)]
  simpa using hlist positions.toList

theorem revealingPilotTranscript_elapsed_nonneg
    {u : ℝ} (processing : Online.Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n)) :
    0 ≤ Online.transcriptElapsed (.finite u) processing
      (revealingPilotTranscript processing positions order) := by
  unfold revealingPilotTranscript
  have hlist : ∀ list : List (Fin n),
      0 ≤ Online.transcriptElapsed (.finite u) processing
        (list.flatMap fun position =>
          pilotJobWord processing (order position)) := by
    intro list
    induction list with
    | nil => simp
    | cons position rest ih =>
        simp only [List.flatMap_cons, Online.transcriptElapsed_append,
          pilotJobWord_elapsed]
        linarith [hp0 (order position)]
  exact hlist positions.toList

theorem completionCost_le_count_mul_elapsed
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Online.Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Online.Transcript n) :
    Online.completionCost (.finite u) processing transcript ≤
      Online.completionCount processing transcript *
        Online.transcriptElapsed (.finite u) processing transcript := by
  have helapsed_nonneg : ∀ tail : Online.Transcript n,
      0 ≤ Online.transcriptElapsed (.finite u) processing tail := by
    intro tail
    induction tail with
    | nil => simp
    | cons observation rest ih =>
        rw [Online.transcriptElapsed_cons]
        have hduration : 0 ≤
            observation.duration (.finite u) processing := by
          cases observation with
          | testResult job value => simp [Online.Observation.duration]
          | processed job =>
              simpa [Online.Observation.duration] using hp0 job
          | rawCompleted job =>
              simpa [Online.Observation.duration, Online.rawDuration] using hu0
        exact add_nonneg hduration ih
  rw [Online.completionCost_eq_suffixWeightedDuration]
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      have hduration : 0 ≤ observation.duration (.finite u) processing := by
        cases observation with
        | testResult job value => simp [Online.Observation.duration]
        | processed job =>
            simpa [Online.Observation.duration] using hp0 job
        | rawCompleted job =>
            simpa [Online.Observation.duration, Online.rawDuration] using hu0
      have helapsed : 0 ≤
          Online.transcriptElapsed (.finite u) processing rest :=
        helapsed_nonneg rest
      have hcount : Online.completionCount processing rest ≤
          Online.completionCount processing (observation :: rest) := by
        simp only [Online.completionCount_cons]
        split <;> omega
      have hcountR : (Online.completionCount processing rest : ℝ) ≤
          Online.completionCount processing (observation :: rest) := by
        exact_mod_cast hcount
      simp only [Online.suffixWeightedDuration_cons,
        Online.transcriptElapsed_cons]
      calc
        observation.duration (.finite u) processing *
              Online.completionCount processing (observation :: rest) +
            Online.suffixWeightedDuration (.finite u) processing rest ≤
          observation.duration (.finite u) processing *
              Online.completionCount processing (observation :: rest) +
            Online.completionCount processing rest *
              Online.transcriptElapsed (.finite u) processing rest := by
                linarith
        _ ≤ observation.duration (.finite u) processing *
              Online.completionCount processing (observation :: rest) +
            Online.completionCount processing (observation :: rest) *
              Online.transcriptElapsed (.finite u) processing rest := by
                have := mul_le_mul_of_nonneg_right hcountR helapsed
                linarith
        _ = Online.completionCount processing (observation :: rest) *
              (observation.duration (.finite u) processing +
                Online.transcriptElapsed (.finite u) processing rest) := by
                  ring

theorem revealingPilotTranscript_completionCost_le
    {u L : ℝ} (hu0 : 0 ≤ u)
    (processing : Online.Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n))
    (hpL : ∀ job, processing job ≤ L) :
    Online.completionCost (.finite u) processing
        (revealingPilotTranscript processing positions order) ≤
      positions.card ^ 2 * (L + 1) := by
  have hcost := completionCost_le_count_mul_elapsed hu0 processing hp0
    (revealingPilotTranscript processing positions order)
  rw [revealingPilotTranscript_completionCount] at hcost
  have helapsed := revealingPilotTranscript_elapsed_le (u := u) processing
    positions order hpL
  have hcard : (0 : ℝ) ≤ positions.card := by positivity
  calc
    Online.completionCost (.finite u) processing
        (revealingPilotTranscript processing positions order) ≤
      positions.card * Online.transcriptElapsed (.finite u) processing
        (revealingPilotTranscript processing positions order) := hcost
    _ ≤ positions.card * (positions.card * (L + 1)) :=
      mul_le_mul_of_nonneg_left helapsed hcard
    _ = positions.card ^ 2 * (L + 1) := by ring

/-! ## Delete pilot owners from the learned virtual main run -/

def learnedTemplate
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n))
    (u : ℝ) : InstanceLearning.Template ι n :=
  InstanceLearning.minimizingTemplate (n := n)
    (sampleHistogram positions (roundedGridCell G) pilotOrder) G.price u

def learnedVirtualTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) (u : ℝ) :
    Online.Transcript n :=
  let T := learnedTemplate G positions pilotOrder u
  (quotaRun T.quota.val u (fun job => processing (mainOrder job))
    (roundedTemplateLow G T)).config.transcript

def learnedRetainedTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) (u : ℝ) :
    Online.Transcript n :=
  ((learnedVirtualTranscript G positions pilotOrder mainOrder u).filter
      fun observation =>
        mainOrder observation.ownerLabel ∉
          pilotOccurrenceSet positions pilotOrder).map
    (Online.Observation.relabel mainOrder)

def learnedPilotTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) (u : ℝ) :
    Online.Transcript n :=
  revealingPilotTranscript processing positions pilotOrder ++
    learnedRetainedTranscript G positions pilotOrder mainOrder u

def learnedPilotCost
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) (u : ℝ) : ℝ :=
  Online.completionCost (.finite u) processing
    (learnedPilotTranscript G positions pilotOrder mainOrder u)

theorem learnedRetainedCost_le
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    Online.completionCost (.finite u) processing
        (learnedRetainedTranscript G positions pilotOrder mainOrder u) ≤
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n
            (learnedTemplate G positions pilotOrder u).quota.val
            (roundedTemplateLow G
              (learnedTemplate G positions pilotOrder u)) mainOrder)
          (2 * n + 1)) := by
  let virtual := learnedVirtualTranscript G positions pilotOrder mainOrder u
  let keep : Fin n → Prop := fun job =>
    mainOrder job ∉ pilotOccurrenceSet positions pilotOrder
  have hfilter := completionCost_filter_owner_le hu0
    (fun job => processing (mainOrder job))
    (fun job => G.processing_nonneg (mainOrder job)) virtual keep
  rw [show learnedRetainedTranscript G positions pilotOrder mainOrder u =
      (virtual.filter fun observation => keep observation.ownerLabel).map
        (Online.Observation.relabel mainOrder) by rfl,
    Online.completionCost_map_relabel]
  simpa [virtual, learnedVirtualTranscript, learnedTemplate, quotaRun,
    QuotaStrategy.randomizedQuotaStrategy,
    Online.runCompletionCost_relabel] using hfilter

theorem learnedVirtual_completionCount
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    Online.completionCount (fun job => processing (mainOrder job))
        (learnedVirtualTranscript G positions pilotOrder mainOrder u) = n := by
  let T := learnedTemplate G positions pilotOrder u
  have hperm := quotaStrategy_completionLabels_perm T.quota_le u
    (fun job => processing (mainOrder job)) (roundedTemplateLow G T)
  rw [Online.completionCount_eq_completionLabels_length]
  have hlength := hperm.length_eq
  simpa [learnedVirtualTranscript, T, quotaRun] using hlength

theorem learnedRetained_completionCount_le
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    Online.completionCount processing
      (learnedRetainedTranscript G positions pilotOrder mainOrder u) ≤ n := by
  let virtual := learnedVirtualTranscript G positions pilotOrder mainOrder u
  let keep : Fin n → Prop := fun job =>
    mainOrder job ∉ pilotOccurrenceSet positions pilotOrder
  have hfilter := completionCount_filter_owner_le
    (fun job => processing (mainOrder job)) keep virtual
  rw [show learnedRetainedTranscript G positions pilotOrder mainOrder u =
      (virtual.filter fun observation => keep observation.ownerLabel).map
        (Online.Observation.relabel mainOrder) by rfl,
    completionCount_map_relabel]
  rw [learnedVirtual_completionCount G positions pilotOrder mainOrder] at hfilter
  exact hfilter

/-- Pointwise compiler overhead. -/
theorem learnedPilotCost_le
    {n : ℕ} {u L : ℝ} (hu0 : 0 ≤ u)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n))
    (hL : 0 ≤ L + 1)
    (hpL : ∀ job, processing job ≤ L) :
    learnedPilotCost G positions pilotOrder mainOrder u ≤
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n
            (learnedTemplate G positions pilotOrder u).quota.val
            (roundedTemplateLow G
              (learnedTemplate G positions pilotOrder u)) mainOrder)
          (2 * n + 1)) +
        2 * n * positions.card * (L + 1) := by
  let pilot := revealingPilotTranscript processing positions pilotOrder
  let main := learnedRetainedTranscript G positions pilotOrder mainOrder u
  have hpilotCost := revealingPilotTranscript_completionCost_le hu0 processing
    G.processing_nonneg positions pilotOrder hpL
  have hpilotElapsed := revealingPilotTranscript_elapsed_le (u := u) processing
    positions pilotOrder hpL
  have hmainCost := learnedRetainedCost_le hu0 G positions pilotOrder mainOrder
  have hmainCount := learnedRetained_completionCount_le (u := u) G positions
    pilotOrder mainOrder
  have hcard : positions.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ positions)
  have hcountR : (Online.completionCount processing main : ℝ) ≤ n := by
    exact_mod_cast hmainCount
  have hcardR : (positions.card : ℝ) ≤ n := by exact_mod_cast hcard
  have hpilotElapsed0 : 0 ≤
      Online.transcriptElapsed (.finite u) processing pilot :=
    revealingPilotTranscript_elapsed_nonneg processing G.processing_nonneg
      positions pilotOrder
  rw [learnedPilotCost, learnedPilotTranscript, completionCost_append]
  change Online.completionCost (.finite u) processing pilot +
      Online.completionCost (.finite u) processing main +
      Online.completionCount processing main *
        Online.transcriptElapsed (.finite u) processing pilot ≤ _
  have hoverhead :
      Online.completionCost (.finite u) processing pilot +
          Online.completionCount processing main *
            Online.transcriptElapsed (.finite u) processing pilot ≤
        2 * n * positions.card * (L + 1) := by
    calc
      Online.completionCost (.finite u) processing pilot +
            Online.completionCount processing main *
              Online.transcriptElapsed (.finite u) processing pilot ≤
          positions.card ^ 2 * (L + 1) +
            n * (positions.card * (L + 1)) := by
              gcongr
      _ ≤ 2 * n * positions.card * (L + 1) := by
        have hkA : (positions.card : ℝ) * (L + 1) ≤ n * (L + 1) :=
          mul_le_mul_of_nonneg_right hcardR hL
        have hk0 : (0 : ℝ) ≤ positions.card := by positivity
        have hkk : (positions.card : ℝ) *
              (positions.card * (L + 1)) ≤
            n * (positions.card * (L + 1)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg hk0 hL)
        nlinarith
  linarith

/-! ## Complete expected rounded-grid bound -/

theorem learnedRoundedPilotCost_le
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (u : ℝ) (hu0 : 0 ≤ u)
    (hpriceU : ∀ i, G.price i ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u)
    (target : InstanceLearning.Template ι n) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        learnedPilotCost G positions pilotOrder mainOrder u /
          (n : ℝ) ^ 2)) ≤
      InstanceLearning.gridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
        (5 * u + 8) / (2 * n) +
        2 * positions.card * (u + 1) / n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hpU : ∀ job, processing job ≤ u := fun job =>
    (G.processing_le_roundedProcessing job).trans (hroundedU job)
  let overhead : ℝ := 2 * n * positions.card * (u + 1)
  have hinner : ∀ pilotOrder : Equiv.Perm (Fin n),
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        learnedPilotCost G positions pilotOrder mainOrder u /
          (n : ℝ) ^ 2) ≤
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (QuotaStrategy.randomizedQuotaStrategy n
              (learnedTemplate G positions pilotOrder u).quota.val
              (roundedTemplateLow G
                (learnedTemplate G positions pilotOrder u)) mainOrder)
            (2 * n + 1)) /
          (n : ℝ) ^ 2) + overhead / (n : ℝ) ^ 2 := by
    intro pilotOrder
    have hpoint : ∀ mainOrder : Equiv.Perm (Fin n),
        learnedPilotCost G positions pilotOrder mainOrder u /
            (n : ℝ) ^ 2 ≤
          Online.runCompletionCost (.finite u) processing
              (Online.run (.finite u) (Online.fixedOracle processing)
                (QuotaStrategy.randomizedQuotaStrategy n
                  (learnedTemplate G positions pilotOrder u).quota.val
                  (roundedTemplateLow G
                    (learnedTemplate G positions pilotOrder u)) mainOrder)
                (2 * n + 1)) /
            (n : ℝ) ^ 2 + overhead / (n : ℝ) ^ 2 := by
      intro mainOrder
      have hcost := learnedPilotCost_le hu0 G positions pilotOrder mainOrder
        (by linarith) hpU
      dsimp [overhead]
      have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      exact (div_le_div_of_nonneg_right hcost hn2).trans_eq (add_div _ _ _)
    have havg := uniformAverage_mono hpoint
    simpa [uniformAverage_add, uniformAverage_const] using havg
  have houter := uniformAverage_mono hinner
  have hmain := learnedRoundedRandomizedQuotaRun_le hn G hprice0 hprice
    positions hpositions u hu0 hpriceU hroundedU target
  have hmain' :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
          Online.runCompletionCost (.finite u) processing
            (Online.run (.finite u) (Online.fixedOracle processing)
              (QuotaStrategy.randomizedQuotaStrategy n
                (learnedTemplate G positions pilotOrder u).quota.val
                (roundedTemplateLow G
                  (learnedTemplate G positions pilotOrder u)) mainOrder)
              (2 * n + 1)) /
            (n : ℝ) ^ 2)) ≤
        InstanceLearning.gridTemplateValue
            (populationHistogram (roundedGridCell G)) G.price u target +
          2 * (u + 2) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
          (5 * u + 8) / (2 * n) := by
    calc
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
          Online.runCompletionCost (.finite u) processing
            (Online.run (.finite u) (Online.fixedOracle processing)
              (QuotaStrategy.randomizedQuotaStrategy n
                (learnedTemplate G positions pilotOrder u).quota.val
                (roundedTemplateLow G
                  (learnedTemplate G positions pilotOrder u)) mainOrder)
              (2 * n + 1)) /
            (n : ℝ) ^ 2)) =
          uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
            let learned := InstanceLearning.minimizingTemplate (n := n)
              (sampleHistogram positions (roundedGridCell G) pilotOrder)
                G.price u
            uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
              Online.runCompletionCost (.finite u) processing
                (Online.run (.finite u) (Online.fixedOracle processing)
                  (QuotaStrategy.randomizedQuotaStrategy n learned.quota.val
                    (roundedTemplateLow G learned) mainOrder)
                  (2 * n + 1))) / (n : ℝ) ^ 2) := by
            apply congrArg uniformAverage
            funext pilotOrder
            dsimp [learnedTemplate]
            let cost := fun mainOrder : Equiv.Perm (Fin n) =>
              Online.runCompletionCost (.finite u) processing
                (Online.run (.finite u) (Online.fixedOracle processing)
                  (QuotaStrategy.randomizedQuotaStrategy n
                    (InstanceLearning.minimizingTemplate (n := n)
                      (sampleHistogram positions (roundedGridCell G)
                        pilotOrder) G.price u).quota.val
                    (roundedTemplateLow G
                      (InstanceLearning.minimizingTemplate (n := n)
                        (sampleHistogram positions (roundedGridCell G)
                          pilotOrder) G.price u)) mainOrder)
                  (2 * n + 1))
            change uniformAverage (fun mainOrder =>
              cost mainOrder / (n : ℝ) ^ 2) =
                uniformAverage cost / (n : ℝ) ^ 2
            calc
              uniformAverage (fun mainOrder =>
                  cost mainOrder / (n : ℝ) ^ 2) =
                uniformAverage (fun mainOrder =>
                  ((n : ℝ) ^ 2)⁻¹ * cost mainOrder) := by
                    congr 1
                    funext mainOrder
                    rw [div_eq_mul_inv, mul_comm]
              _ = ((n : ℝ) ^ 2)⁻¹ * uniformAverage cost := by
                rw [uniformAverage_smul]
              _ = uniformAverage cost / (n : ℝ) ^ 2 := by
                rw [div_eq_mul_inv, mul_comm]
      _ ≤ _ := hmain
  have hcompiled :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
          learnedPilotCost G positions pilotOrder mainOrder u /
            (n : ℝ) ^ 2)) ≤
        (InstanceLearning.gridTemplateValue
            (populationHistogram (roundedGridCell G)) G.price u target +
          2 * (u + 2) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
          (5 * u + 8) / (2 * n)) + overhead / (n : ℝ) ^ 2 := by
    have houter' :
        uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
          uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
            learnedPilotCost G positions pilotOrder mainOrder u /
              (n : ℝ) ^ 2)) ≤
          uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
            uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
              Online.runCompletionCost (.finite u) processing
                (Online.run (.finite u) (Online.fixedOracle processing)
                  (QuotaStrategy.randomizedQuotaStrategy n
                    (learnedTemplate G positions pilotOrder u).quota.val
                    (roundedTemplateLow G
                      (learnedTemplate G positions pilotOrder u)) mainOrder)
                  (2 * n + 1)) /
                (n : ℝ) ^ 2)) + overhead / (n : ℝ) ^ 2 := by
      simpa [uniformAverage_add, uniformAverage_const] using houter
    linarith [houter', hmain']
  have hnR : (0 : ℝ) < n := by positivity
  have hoverhead : overhead / (n : ℝ) ^ 2 =
      2 * positions.card * (u + 1) / n := by
    dsimp [overhead]
    field_simp [hnR.ne']
  rw [hoverhead] at hcompiled
  linarith

end

end PilotCompiler
end RevealingOptimization
end SchedulingPaper
