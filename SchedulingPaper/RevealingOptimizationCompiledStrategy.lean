import SchedulingPaper.RevealingOptimizationPilotCompiler
import Mathlib.Tactic

/-!
# Transcript-only strategy for the revealing pilot compiler

This file records the actual online decision rule corresponding to the
physical compiler.  Its parameters are public grid data and private random
seeds only.  In particular it receives neither the processing vector nor a
population histogram.  The sample template is recomputed from the pilot
`testResult` records in the public transcript.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace CompiledStrategy

open Online
open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedEnvelope
open InstanceLearning
open QuotaStrategy
open QuotaFluid
open LearnedPilot
open PilotCompiler

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Classify an arbitrary publicly observed value using only the public grid
predicates.  Values outside the promised grid support are harmlessly sent to
the zero cell. -/
def publicGridCell
    {ι : Type*} [Fintype ι]
    (category : ι → ℝ → Bool) (value : ℝ) : Option ι :=
  if value = 0 then none
  else if h : ∃ cell, category cell value = true then some h.choose
  else none

@[simp] theorem publicGridCell_zero
    {ι : Type*} [Fintype ι] (category : ι → ℝ → Bool) :
    publicGridCell category 0 = none := by
  simp [publicGridCell]

/-- On every realized job, public classification agrees with the analytic
`roundedGridCell` used by the sampling theorem. -/
theorem publicGridCell_processing
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) :
    publicGridCell G.category (processing job) = roundedGridCell G job := by
  by_cases hz : processing job = 0
  · simp [publicGridCell, roundedGridCell, hz]
  · have hp : 0 < processing job :=
      lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm hz)
    let unique := G.category_unique job hp
    have hexists : ∃ cell, G.category cell (processing job) = true :=
      ⟨unique.choose, unique.choose_spec.1⟩
    rw [publicGridCell, if_neg hz, dif_pos hexists]
    unfold roundedGridCell
    rw [dif_neg hz]
    exact congrArg some (unique.choose_spec.2 _ hexists.choose_spec)

/-- The low selector computed from a public cell classifier. -/
def publicTemplateLow
    {ι : Type*} [Fintype ι] {n : ℕ}
    (category : ι → ℝ → Bool) (T : InstanceLearning.Template ι n)
    (value : ℝ) : Bool :=
  T.lowWithZero (publicGridCell category value)

@[simp] theorem publicTemplateLow_zero
    {ι : Type*} [Fintype ι] {n : ℕ}
    (category : ι → ℝ → Bool) (T : InstanceLearning.Template ι n) :
    publicTemplateLow category T 0 = true := by
  simp [publicTemplateLow, InstanceLearning.Template.lowWithZero]

theorem publicTemplateLow_at_job
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (T : InstanceLearning.Template ι n) (job : Fin n) :
    publicTemplateLow G.category T (processing job) =
      T.lowWithZero (roundedGridCell G job) := by
  rw [publicTemplateLow, publicGridCell_processing]

/-- Fixed pilot actions.  Every pilot occurrence is tested and then
processed; the latter is a zero-duration administrative action for a zero
job. -/
def pilotActions
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    List (Online.Action n) :=
  positions.toList.flatMap fun position =>
    [.test (pilotOrder position), .process (pilotOrder position)]

@[simp] theorem pilotActions_length
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    (pilotActions positions pilotOrder).length = 2 * positions.card := by
  simp [pilotActions, Nat.mul_comm]

/-- First untouched nonpilot virtual position satisfying `eligible`, placed
on its physical label. -/
def nextRestrictedLabel?
    (n : ℕ) (pilot : Finset (Fin n))
    (mainOrder : Equiv.Perm (Fin n))
    (eligible : Fin n → Bool) (transcript : Online.Transcript n) :
    Option (Fin n) :=
  ((List.finRange n).find? fun virtual =>
    eligible virtual &&
      decide (mainOrder virtual ∉ pilot) &&
      decide (mainOrder virtual ∉ transcript.startedLabels)).map mainOrder

def restrictedTestLabel?
    (n quota : ℕ) (pilot : Finset (Fin n))
    (mainOrder : Equiv.Perm (Fin n))
    (transcript : Online.Transcript n) : Option (Fin n) :=
  nextRestrictedLabel? n pilot mainOrder
    (fun virtual => decide (virtual.val < quota)) transcript

def restrictedRawLabel?
    (n quota : ℕ) (pilot : Finset (Fin n))
    (mainOrder : Equiv.Perm (Fin n))
    (transcript : Online.Transcript n) : Option (Fin n) :=
  nextRestrictedLabel? n pilot mainOrder
    (fun virtual => decide (quota ≤ virtual.val)) transcript

/-- Restricted main phase for a template already fixed by the completed
pilot. -/
def restrictedFixedMainStrategy
    {ι : Type*} [Fintype ι]
    (n : ℕ) (category : ι → ℝ → Bool)
    (T : InstanceLearning.Template ι n)
    (pilot : Finset (Fin n)) (mainOrder : Equiv.Perm (Fin n)) :
    Online.Strategy n := fun transcript =>
  match safeLastLowPending? (publicTemplateLow category T) transcript with
  | some job => some (.process job)
  | none =>
      match restrictedTestLabel? n T.quota.val pilot mainOrder transcript with
      | some job => some (.test job)
      | none =>
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none =>
              (restrictedRawLabel? n T.quota.val pilot mainOrder transcript).map
                Online.Action.raw

/-- Main phase after the revealing pilot.  It learns from the first `k`
public test results, tests the retained virtual quota, drains the tested
stock by SPT, and runs every retained position outside the quota raw. -/
def restrictedLearnedMainStrategy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n k : ℕ) (category : ι → ℝ → Bool) (price : ι → ℝ) (u : ℝ)
    (pilot : Finset (Fin n)) (mainOrder : Equiv.Perm (Fin n)) :
    Online.Strategy n := fun transcript =>
  let histogram := resultHistogram k (publicGridCell category)
    (transcript.testResults.take k)
  let T := InstanceLearning.minimizingTemplate (n := n) histogram price u
  restrictedFixedMainStrategy n category T pilot mainOrder transcript

/-- Complete unknown-input policy.  The policy's closure contains only the
public grid and two private permutations/position sets. -/
def compiledLearnedStrategy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (category : ι → ℝ → Bool) (price : ι → ℝ) (u : ℝ)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : Online.Strategy n :=
  fun transcript =>
    let actions := pilotActions positions pilotOrder
    if transcript.length < actions.length then
      actions[transcript.length]?.map id
    else
      restrictedLearnedMainStrategy n positions.card category price u
        (pilotOccurrenceSet positions pilotOrder) mainOrder transcript

/-- The strategy's learned template at the end of the literal pilot equals
the analytic empirical minimizer used by the compiler. -/
theorem resultHistogram_revealingPilotTranscript
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    resultHistogram positions.card (publicGridCell G.category)
        (revealingPilotTranscript processing positions pilotOrder).testResults =
      sampleHistogram positions (roundedGridCell G) pilotOrder := by
  funext cell
  unfold resultHistogram sampleHistogram sampleCategoryFraction
    permutationSampleSum categoryClass categoryIndicator
  have hresults :
      (revealingPilotTranscript processing positions
        pilotOrder).testResults =
      positions.toList.map fun position =>
        (pilotOrder position, processing (pilotOrder position)) := by
    unfold revealingPilotTranscript
    have hlist : ∀ list : List (Fin n),
        Online.Transcript.testResults (list.flatMap fun position =>
          PilotCompiler.pilotJobWord processing
            (pilotOrder position)) =
        list.map fun position =>
          (pilotOrder position, processing (pilotOrder position)) := by
      intro list
      induction list with
      | nil => rfl
      | cons position rest ih =>
          rw [List.flatMap_cons, Online.Transcript.testResults_append, ih]
          simp [PilotCompiler.pilotJobWord]
    exact hlist positions.toList
  rw [hresults]
  rw [show (positions.toList.map fun position =>
      (pilotOrder position, processing (pilotOrder position))).filter
        (fun result => publicGridCell G.category result.2 = cell) =
      (positions.toList.filter fun position =>
        roundedGridCell G (pilotOrder position) = cell).map
          (fun position =>
            (pilotOrder position, processing (pilotOrder position))) by
      induction positions.toList with
      | nil => rfl
      | cons position rest ih =>
          simp only [List.filter_cons, List.map_cons]
          rw [publicGridCell_processing]
          split <;> simp_all]
  simp only [List.length_map]
  apply congrArg (fun numerator : ℝ =>
    numerator / positions.card)
  norm_cast
  rw [← Finset.card_filter]
  rw [← List.toFinset_card_of_nodup
    ((Finset.nodup_toList positions).filter _)]
  rw [List.toFinset_filter]
  rw [show positions.toList.toFinset = positions by simp]
  simp only [decide_eq_true_eq]
  rw [show (Finset.univ : Finset ↥positions) = positions.attach by
    ext position
    simp]
  rw [show (positions.attach.filter fun position =>
      pilotOrder position.val ∈
        (Finset.univ.filter fun job => roundedGridCell G job = cell)) =
      (positions.attach.filter fun position =>
        roundedGridCell G (pilotOrder position.val) = cell) by
    ext position
    simp]
  change (positions.filter fun position =>
      roundedGridCell G (pilotOrder position) = cell).card =
    (positions.attach.filter fun position =>
      (fun job => roundedGridCell G (pilotOrder job) = cell)
        position.val).card
  have hattach := congrArg Finset.card
    (Finset.filter_attach
      (fun job => roundedGridCell G (pilotOrder job) = cell) positions)
  simpa using hattach.symm

@[simp] theorem revealingPilotTranscript_length
    {n : ℕ} (processing : Fin n → ℝ)
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    (revealingPilotTranscript processing positions pilotOrder).length =
      2 * positions.card := by
  unfold revealingPilotTranscript PilotCompiler.pilotJobWord
  simp [Nat.mul_comm]

@[simp] theorem revealingPilotTranscript_testResults_length
    {n : ℕ} (processing : Fin n → ℝ)
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    (revealingPilotTranscript processing positions
      pilotOrder).testResults.length = positions.card := by
  unfold revealingPilotTranscript
  have hlist : ∀ list : List (Fin n),
      (Online.Transcript.testResults (list.flatMap fun position =>
        PilotCompiler.pilotJobWord processing
          (pilotOrder position))).length = list.length := by
    intro list
    induction list with
    | nil => rfl
    | cons position rest ih =>
        rw [List.flatMap_cons, Online.Transcript.testResults_append]
        rw [List.length_append, ih]
        simp [PilotCompiler.pilotJobWord, Nat.add_comm]
  simpa using hlist positions.toList

theorem pilot_testResults_take_of_suffix
    {n : ℕ} (processing : Fin n → ℝ)
    (positions : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n))
    (suffix : Online.Transcript n) :
    (Online.Transcript.testResults
      (revealingPilotTranscript processing positions pilotOrder ++ suffix)
        ).take positions.card =
      (revealingPilotTranscript processing positions pilotOrder).testResults := by
  rw [Online.Transcript.testResults_append]
  rw [show positions.card =
      (revealingPilotTranscript processing positions
        pilotOrder).testResults.length by simp]
  exact List.take_left

/-- Before the pilot has produced all of its two-observation job words, the
compiled strategy is exactly the fixed public pilot action list. -/
theorem compiledLearnedStrategy_before_pilot
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : ι → ℝ → Bool) (price : ι → ℝ) (u : ℝ)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n))
    (transcript : Online.Transcript n)
    (hpilot : transcript.length < 2 * positions.card) :
    compiledLearnedStrategy n category price u positions pilotOrder mainOrder
        transcript =
      (pilotActions positions pilotOrder)[transcript.length]?.map id := by
  simp [compiledLearnedStrategy, pilotActions_length, hpilot]

/-- After the literal pilot prefix, the transcript-only learner stabilizes
to the same fixed template used by the analytic compiler, independently of
the later suffix. -/
theorem compiledLearnedStrategy_after_pilot
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (u : ℝ) (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n))
    (suffix : Online.Transcript n) :
    compiledLearnedStrategy n G.category G.price u positions
        pilotOrder mainOrder
        (revealingPilotTranscript processing positions pilotOrder ++ suffix) =
      restrictedFixedMainStrategy n G.category
        (learnedTemplate G positions pilotOrder u)
        (pilotOccurrenceSet positions pilotOrder) mainOrder
        (revealingPilotTranscript processing positions pilotOrder ++ suffix) := by
  unfold compiledLearnedStrategy
  rw [if_neg]
  · unfold restrictedLearnedMainStrategy learnedTemplate
    rw [pilot_testResults_take_of_suffix]
    rw [resultHistogram_revealingPilotTranscript]
  · simp

end

end CompiledStrategy
end RevealingOptimization
end SchedulingPaper
