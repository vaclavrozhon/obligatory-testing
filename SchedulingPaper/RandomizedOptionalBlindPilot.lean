import SchedulingPaper.RandomizedOptionalPilotLearningUpper
import SchedulingPaper.RandomizedOptionalObservedPairAccounting
import Mathlib.Tactic

/-!
# Blind-pilot compiler for optional testing

This file turns the learned full-population canonical comparison into a
physical schedule.  The pilot jobs are first completed blindly.  An
independent canonical word is then restricted by deleting every operation
owned by a pilot job.  Deleting operations cannot increase completion cost;
prepending the blind pilot costs only `O(L n k)`.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

open Randomized
open AnnouncedRoundedLower
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

theorem completionCostFrom_mono_start
    {n : ℕ} (processing : Label n → ℝ) (transcript : Transcript n)
    {start finish : ℝ} (hstart : start ≤ finish) :
    completionCostFrom processing start transcript ≤
      completionCostFrom processing finish transcript := by
  rw [completionCostFrom_eq_count_mul_add_suffixWeighted,
    completionCostFrom_eq_count_mul_add_suffixWeighted]
  have hcount : (0 : ℝ) ≤ completionCount processing transcript := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hstart hcount
  linarith

theorem completionCostFrom_filter_owner_le
    {n : ℕ} (processing : Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Transcript n)
    (hmatch : AllRevealsMatch processing transcript)
    (keep : Label n → Prop)
    [DecidablePred keep] {start : ℝ}
    (hstart : 0 ≤ start) :
    completionCostFrom processing start
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      completionCostFrom processing start transcript := by
  induction transcript generalizing start with
  | nil => simp [completionCostFrom]
  | cons observation rest ih =>
      have hrestMatch : AllRevealsMatch processing rest := by
        intro job value hmem
        exact hmatch job value (by
          cases observation <;>
            simp [Transcript.revealedResults, hmem])
      have hduration : 0 ≤ observation.actualDuration processing := by
        cases observation with
        | testResult job value => simp [Observation.actualDuration]
        | processed job => simpa [Observation.actualDuration] using hp0 job
        | blindCompleted job value =>
            have hvalue : value = processing job :=
              hmatch job value (by simp [Transcript.revealedResults])
            simpa [Observation.actualDuration, hvalue] using hp0 job
      have hfinish : 0 ≤ start + observation.actualDuration processing :=
        add_nonneg hstart hduration
      by_cases hkeep : keep observation.ownerLabel
      · rw [List.filter_cons, if_pos (by simp [hkeep])]
        simp only [completionCostFrom]
        linarith [ih hrestMatch hfinish]
      · rw [List.filter_cons, if_neg (by simp [hkeep])]
        simp only [completionCostFrom]
        have htail := ih hrestMatch hstart
        have htime := completionCostFrom_mono_start processing rest
          (show start ≤ start + observation.actualDuration processing by
            linarith)
        have hcompletion :
            0 ≤ if (observation.completionLabel processing).isSome then
              start + observation.actualDuration processing else 0 := by
          split <;> positivity
        linarith

theorem completionCost_filter_owner_le
    {n : ℕ} (processing : Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Transcript n)
    (hmatch : AllRevealsMatch processing transcript)
    (keep : Label n → Prop)
    [DecidablePred keep] :
    completionCost processing
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      completionCost processing transcript := by
  exact completionCostFrom_filter_owner_le processing hp0 transcript hmatch keep
    (start := 0) (by norm_num)

theorem completionCount_filter_owner_le
    {n : ℕ} (processing : Label n → ℝ) (keep : Label n → Prop)
    [DecidablePred keep] (transcript : Transcript n) :
    completionCount processing
        (transcript.filter fun observation => keep observation.ownerLabel) ≤
      completionCount processing transcript := by
  induction transcript with
  | nil => simp [completionCount]
  | cons observation rest ih =>
      by_cases hkeep : keep observation.ownerLabel
      · rw [List.filter_cons, if_pos (by simp [hkeep])]
        simp only [completionCount]
        split <;> omega
      · rw [List.filter_cons, if_neg (by simp [hkeep])]
        simp only [completionCount]
        split <;> omega

@[simp] theorem completionCount_map_relabel
    {n : ℕ} (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (transcript : Transcript n) :
    completionCount physicalProcessing
        (transcript.map (Observation.relabel order)) =
      completionCount (fun virtual => physicalProcessing (order virtual))
        transcript := by
  induction transcript with
  | nil => simp [completionCount]
  | cons observation rest ih =>
      simp only [List.map_cons, completionCount,
        Observation.completionLabel_relabel, Option.isSome_map, ih]

@[simp] theorem elapsed_append
    {n : ℕ} (processing : Label n → ℝ)
    (left right : Transcript n) :
    elapsed processing (left ++ right) =
      elapsed processing left + elapsed processing right := by
  induction left with
  | nil => simp [elapsed]
  | cons observation rest ih => simp [elapsed, ih, add_assoc]

theorem completionCostFrom_append
    {n : ℕ} (processing : Label n → ℝ) (start : ℝ)
    (left right : Transcript n) :
    completionCostFrom processing start (left ++ right) =
      completionCostFrom processing start left +
        completionCostFrom processing (start + elapsed processing left) right := by
  induction left generalizing start with
  | nil => simp [completionCostFrom, elapsed]
  | cons observation rest ih =>
      simp only [List.cons_append, completionCostFrom, elapsed]
      conv_lhs => rw [ih]
      by_cases hcompletion :
          (observation.completionLabel processing).isSome
      · simp only [if_pos hcompletion]
        ring
      · simp only [if_neg hcompletion, zero_add]
        ring

theorem completionCost_append
    {n : ℕ} (processing : Label n → ℝ)
    (left right : Transcript n) :
    completionCost processing (left ++ right) =
      completionCost processing left + completionCost processing right +
        completionCount processing right * elapsed processing left := by
  unfold completionCost
  rw [completionCostFrom_append]
  simp only [zero_add]
  simp only [completionCostFrom_eq_count_mul_add_suffixWeighted]
  ring

def blindPilotTranscript
    {n : ℕ} (processing : Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) : Transcript n :=
  positions.toList.map fun position =>
    .blindCompleted (order position) (processing (order position))

def pilotOccurrenceSet
    {n : ℕ} (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  positions.image order

@[simp] theorem blindPilotTranscript_length
    {n : ℕ} (processing : Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) :
    (blindPilotTranscript processing positions order).length = positions.card := by
  simp [blindPilotTranscript]

theorem blindPilotTranscript_elapsed_le
    {n : ℕ} (processing : Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) {L : ℝ}
    (hpL : ∀ job, processing job ≤ L) :
    elapsed processing (blindPilotTranscript processing positions order) ≤
      positions.card * L := by
  unfold blindPilotTranscript
  have hlist : ∀ list : List (Fin n),
      elapsed processing (list.map fun position =>
        .blindCompleted (order position) (processing (order position))) ≤
        list.length * L := by
    intro list
    induction list with
    | nil => simp [elapsed]
    | cons position rest ih =>
        simp only [List.map_cons, elapsed, Observation.actualDuration,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [hpL (order position)]
  simpa using hlist positions.toList

@[simp] theorem blindPilotTranscript_completionCount
    {n : ℕ} (processing : Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) :
    completionCount processing (blindPilotTranscript processing positions order) =
      positions.card := by
  unfold blindPilotTranscript
  have hlist : ∀ list : List (Fin n),
      completionCount processing (list.map fun position =>
        .blindCompleted (order position) (processing (order position))) =
        list.length := by
    intro list
    induction list with
    | nil => simp [completionCount]
    | cons position rest ih =>
        simp [completionCount, Observation.completionLabel, ih]
        omega
  simpa using hlist positions.toList

theorem blindPilotTranscript_revealsMatch
    {n : ℕ} (processing : Label n → ℝ) (positions : Finset (Fin n))
    (order : Equiv.Perm (Fin n)) :
    AllRevealsMatch processing
      (blindPilotTranscript processing positions order) := by
  unfold blindPilotTranscript
  have hlist : ∀ list : List (Fin n),
      AllRevealsMatch processing
        (list.map fun position =>
          .blindCompleted (order position) (processing (order position))) := by
    intro list
    induction list with
    | nil => simp [AllRevealsMatch, Transcript.revealedResults]
    | cons position rest ih =>
        intro job value hmem
        simp only [List.map_cons, Transcript.revealedResults,
          List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · have hjob : job = order position := congrArg Prod.fst hmem
          subst job
          simpa using congrArg Prod.snd hmem
        · exact ih job value hmem
  exact hlist positions.toList

theorem completionCost_le_count_mul_elapsed
    {n : ℕ} (processing : Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (transcript : Transcript n)
    (hmatch : AllRevealsMatch processing transcript) :
    completionCost processing transcript ≤
      completionCount processing transcript * elapsed processing transcript := by
  rw [completionCost_eq_suffixWeightedDuration]
  induction transcript with
  | nil => simp [suffixWeightedDuration, completionCount, elapsed]
  | cons observation rest ih =>
      have hrestMatch : AllRevealsMatch processing rest := by
        intro job value hmem
        exact hmatch job value (by
          cases observation <;>
            simp [Transcript.revealedResults, hmem])
      have hduration : 0 ≤ observation.actualDuration processing := by
        cases observation with
        | testResult job value => simp [Observation.actualDuration]
        | processed job => simpa [Observation.actualDuration] using hp0 job
        | blindCompleted job value =>
            have hvalue : value = processing job :=
              hmatch job value (by simp [Transcript.revealedResults])
            simpa [Observation.actualDuration, hvalue] using hp0 job
      simp only [suffixWeightedDuration, elapsed]
      have hcount : completionCount processing rest ≤
          completionCount processing (observation :: rest) := by
        simp only [completionCount]
        split <;> omega
      have helapsed : 0 ≤ elapsed processing rest :=
        ObservedEnvelope.elapsed_nonneg_of_revealsMatch rest hp0 hrestMatch
      have hcountR : (completionCount processing rest : ℝ) ≤
          completionCount processing (observation :: rest) := by
        exact_mod_cast hcount
      calc
        observation.actualDuration processing *
              completionCount processing (observation :: rest) +
            suffixWeightedDuration processing rest ≤
          observation.actualDuration processing *
              completionCount processing (observation :: rest) +
            completionCount processing rest * elapsed processing rest :=
          by linarith [ih hrestMatch]
        _ ≤ observation.actualDuration processing *
              completionCount processing (observation :: rest) +
            completionCount processing (observation :: rest) *
              elapsed processing rest :=
          by
            have := mul_le_mul_of_nonneg_right hcountR helapsed
            linarith
        _ = completionCount processing (observation :: rest) *
              (observation.actualDuration processing +
                elapsed processing rest) := by ring

theorem blindPilotTranscript_completionCost_le
    {n : ℕ} (processing : Label n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n)) {L : ℝ}
    (hpL : ∀ job, processing job ≤ L) :
    completionCost processing (blindPilotTranscript processing positions order) ≤
      positions.card ^ 2 * L := by
  have hcost := completionCost_le_count_mul_elapsed processing hp0
    (blindPilotTranscript processing positions order)
    (blindPilotTranscript_revealsMatch processing positions order)
  rw [blindPilotTranscript_completionCount] at hcost
  have helapsed := blindPilotTranscript_elapsed_le processing positions order hpL
  have hcard : (0 : ℝ) ≤ positions.card := by positivity
  calc
    completionCost processing (blindPilotTranscript processing positions order) ≤
        positions.card * elapsed processing
          (blindPilotTranscript processing positions order) := hcost
    _ ≤ positions.card * (positions.card * L) :=
      mul_le_mul_of_nonneg_left helapsed hcard
    _ = positions.card ^ 2 * L := by ring

/-! ## The physical learned schedule -/

open SchedulingPaper.RandomizedOptional

def learnedCanonicalVirtualTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : Transcript n :=
  let T := learnedPositiveGridTemplate G pilotPositions pilotOrder
  (canonicalRun T.1.quota.val (fun job => processing (mainOrder job))
    (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
    (pullbackRoundedSelector G (gridTemplateRoundedMedium G.price T))).config.transcript

def learnedCanonicalRetainedTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : Transcript n :=
  ((learnedCanonicalVirtualTranscript G pilotPositions pilotOrder mainOrder).filter
      fun observation =>
        mainOrder observation.ownerLabel ∉
          pilotOccurrenceSet pilotPositions pilotOrder).map
    (Observation.relabel mainOrder)

def blindPilotLearnedTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : Transcript n :=
  blindPilotTranscript processing pilotPositions pilotOrder ++
    learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder

def blindPilotLearnedCost
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : ℝ :=
  completionCost processing
    (blindPilotLearnedTranscript G pilotPositions pilotOrder mainOrder)

theorem learnedCanonicalVirtualTranscript_revealsMatch
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    AllRevealsMatch (fun job => processing (mainOrder job))
      (learnedCanonicalVirtualTranscript G pilotPositions pilotOrder mainOrder) := by
  let T := learnedPositiveGridTemplate G pilotPositions pilotOrder
  simpa [learnedCanonicalVirtualTranscript, T, canonicalRun] using
    (run_historyInvariant (fun job => processing (mainOrder job))
      (canonicalStrategy n T.1.quota.val
        (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
        (pullbackRoundedSelector G (gridTemplateRoundedMedium G.price T)))
      (2 * n + 1)).revealsMatch

theorem learnedCanonicalRetainedCost_le
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (hp0 : ∀ job, 0 ≤ processing job)
    (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    completionCost processing
        (learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder) ≤
      learnedCanonicalPlacedCost G pilotPositions pilotOrder mainOrder := by
  let virtual :=
    learnedCanonicalVirtualTranscript G pilotPositions pilotOrder mainOrder
  let keep : Fin n → Prop := fun job =>
    mainOrder job ∉ pilotOccurrenceSet pilotPositions pilotOrder
  have hfilter := completionCost_filter_owner_le
    (fun job => processing (mainOrder job)) (fun job => hp0 (mainOrder job))
    virtual (learnedCanonicalVirtualTranscript_revealsMatch
      G pilotPositions pilotOrder mainOrder) keep
  rw [show learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder =
      (virtual.filter fun observation => keep observation.ownerLabel).map
        (Observation.relabel mainOrder) by
      rfl,
    completionCost_map_relabel]
  simpa [virtual, learnedCanonicalVirtualTranscript,
    learnedCanonicalPlacedCost] using hfilter

theorem learnedCanonicalRetained_completionCount_le
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    completionCount processing
      (learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder) ≤ n := by
  let T := learnedPositiveGridTemplate G pilotPositions pilotOrder
  let virtual :=
    learnedCanonicalVirtualTranscript G pilotPositions pilotOrder mainOrder
  let keep : Fin n → Prop := fun job =>
    mainOrder job ∉ pilotOccurrenceSet pilotPositions pilotOrder
  have hfilter := completionCount_filter_owner_le
    (fun job => processing (mainOrder job)) keep virtual
  have hdone := (canonicalRun_completed T.quota_le
    (fun job => processing (mainOrder job))
    (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
    (pullbackRoundedSelector G
      (gridTemplateRoundedMedium G.price T))).2.2
  have hcount : completionCount (fun job => processing (mainOrder job))
      virtual = n := by
    dsimp [virtual, learnedCanonicalVirtualTranscript, T]
    exact completionCount_eq_n_of_done
      (run_completionInvariant (fun job => processing (mainOrder job))
        (canonicalStrategy n T.1.quota.val
          (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
          (pullbackRoundedSelector G
            (gridTemplateRoundedMedium G.price T))) (2 * n + 1)) hdone
  rw [show learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder =
      (virtual.filter fun observation => keep observation.ownerLabel).map
        (Observation.relabel mainOrder) by rfl,
    completionCount_map_relabel]
  omega

/-- Pointwise cost of the physical blind-pilot compiler.  The bound is
independent of the two random permutations. -/
theorem blindPilotLearnedCost_le
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (hp0 : ∀ job, 0 ≤ processing job)
    (G : RoundedPositiveGrid ι processing)
    (pilotPositions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) {L : ℝ}
    (hpL : ∀ job, processing job ≤ L) :
    blindPilotLearnedCost G pilotPositions pilotOrder mainOrder ≤
      learnedCanonicalPlacedCost G pilotPositions pilotOrder mainOrder +
        2 * n * pilotPositions.card * L := by
  let pilot := blindPilotTranscript processing pilotPositions pilotOrder
  let main :=
    learnedCanonicalRetainedTranscript G pilotPositions pilotOrder mainOrder
  have hpilotCost := blindPilotTranscript_completionCost_le processing hp0
    pilotPositions pilotOrder hpL
  have hpilotElapsed := blindPilotTranscript_elapsed_le processing
    pilotPositions pilotOrder hpL
  have hmainCost := learnedCanonicalRetainedCost_le hp0 G pilotPositions
    pilotOrder mainOrder
  have hmainCount := learnedCanonicalRetained_completionCount_le G
    pilotPositions pilotOrder mainOrder
  have hcard : pilotPositions.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ pilotPositions)
  have hcountR : (completionCount processing main : ℝ) ≤ n := by
    exact_mod_cast hmainCount
  have hcardR : (pilotPositions.card : ℝ) ≤ n := by exact_mod_cast hcard
  have helapsed0 : 0 ≤ elapsed processing pilot :=
    ObservedEnvelope.elapsed_nonneg_of_revealsMatch pilot hp0
      (blindPilotTranscript_revealsMatch processing pilotPositions pilotOrder)
  rw [blindPilotLearnedCost, blindPilotLearnedTranscript,
    completionCost_append]
  change completionCost processing pilot + completionCost processing main +
      completionCount processing main * elapsed processing pilot ≤ _
  have hoverhead :
      completionCost processing pilot +
          completionCount processing main * elapsed processing pilot ≤
        2 * n * pilotPositions.card * L := by
    calc
      completionCost processing pilot +
            completionCount processing main * elapsed processing pilot ≤
          pilotPositions.card ^ 2 * L +
            n * (pilotPositions.card * L) := by
        gcongr
      _ ≤ 2 * n * pilotPositions.card * L := by
        nlinarith
  linarith

/-- The physical blind-pilot compiler compared with any fixed finite grid
template.  This target form also covers the all-zero population, where the
positive-mean benchmark structure is intentionally unavailable. -/
theorem blindPilotLearnedCost_le_target
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (target : GridTemplate ι n)
    {scale L : ℝ} (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, processing job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale)
    (hpriceScale : ∀ i, G.price i ≤ scale)
    (hpL : ∀ job, processing job ≤ L) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price target +
        24 * (scale + 1) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / pilotPositions.card) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh +
        2 * pilotPositions.card * L / n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hmain := learnedCanonicalPlacedCost_le_target hn G hprice0 hprice
    pilotPositions hpilot target hscaleOne hpScale hroundedScale hpriceScale
  let overhead : ℝ := 2 * n * pilotPositions.card * L
  have hinner : ∀ pilotOrder : Equiv.Perm (Fin n),
      uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder) ≤
        uniformAverage
          (learnedCanonicalPlacedCost G pilotPositions pilotOrder) + overhead := by
    intro pilotOrder
    have hpoint : ∀ mainOrder : Equiv.Perm (Fin n),
        blindPilotLearnedCost G pilotPositions pilotOrder mainOrder ≤
          learnedCanonicalPlacedCost G pilotPositions pilotOrder mainOrder +
            overhead := by
      intro mainOrder
      exact blindPilotLearnedCost_le G.processing_nonneg G pilotPositions
        pilotOrder mainOrder hpL
    simpa [uniformAverage_add, uniformAverage_const] using
      uniformAverage_mono hpoint
  have hdouble := uniformAverage_mono hinner
  have hdouble' :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder)) ≤
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage
          (learnedCanonicalPlacedCost G pilotPositions pilotOrder)) + overhead := by
    simpa [uniformAverage_add, uniformAverage_const] using hdouble
  have hnR : (0 : ℝ) < n := by positivity
  have hdiv := div_le_div_of_nonneg_right hdouble' (sq_nonneg (n : ℝ))
  have hoverhead : overhead / (n : ℝ) ^ 2 =
      2 * pilotPositions.card * L / n := by
    dsimp [overhead]
    field_simp [hnR.ne']
  rw [add_div, hoverhead] at hdiv
  linarith

/-- The complete unknown-multiset upper bound: a blind uniform pilot chooses
the template, an independent canonical permutation executes it on every
non-pilot job, and all costs are measured on the original processing times. -/
theorem blindPilotLearnedCost_le_benchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (B : BenchmarkData processing G)
    {scale L : ℝ} (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, processing job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale)
    (hpriceScale : ∀ i, G.price i ≤ scale)
    (hpL : ∀ job, processing job ≤ L) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      B.value +
        24 * (scale + 1) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / pilotPositions.card) +
        (17 + 63 * scale) / n +
        12 * (scale + 1) * G.mesh +
        2 * pilotPositions.card * L / n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hmain := learnedCanonicalPlacedCost_le_benchmark hn G hprice0 hprice
    pilotPositions hpilot B hscaleOne hpScale hroundedScale hpriceScale
  let overhead : ℝ := 2 * n * pilotPositions.card * L
  have hinner : ∀ pilotOrder : Equiv.Perm (Fin n),
      uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder) ≤
        uniformAverage
          (learnedCanonicalPlacedCost G pilotPositions pilotOrder) + overhead := by
    intro pilotOrder
    have hpoint : ∀ mainOrder : Equiv.Perm (Fin n),
        blindPilotLearnedCost G pilotPositions pilotOrder mainOrder ≤
          learnedCanonicalPlacedCost G pilotPositions pilotOrder mainOrder +
            overhead := by
      intro mainOrder
      exact blindPilotLearnedCost_le G.processing_nonneg G pilotPositions
        pilotOrder mainOrder hpL
    simpa [uniformAverage_add, uniformAverage_const] using
      uniformAverage_mono hpoint
  have hdouble := uniformAverage_mono hinner
  have hdouble' :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (blindPilotLearnedCost G pilotPositions pilotOrder)) ≤
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage
          (learnedCanonicalPlacedCost G pilotPositions pilotOrder)) + overhead := by
    simpa [uniformAverage_add, uniformAverage_const] using hdouble
  have hnR : (0 : ℝ) < n := by positivity
  have hdiv := div_le_div_of_nonneg_right hdouble' (sq_nonneg (n : ℝ))
  have hoverhead : overhead / (n : ℝ) ^ 2 =
      2 * pilotPositions.card * L / n := by
    dsimp [overhead]
    field_simp [hnR.ne']
  rw [add_div, hoverhead] at hdiv
  linarith

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
