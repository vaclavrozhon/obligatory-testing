import SchedulingPaper.RandomizedOptionalObservedCompletionIntegral
import Mathlib.Tactic

/-!
# Revealing optimization inside the observed first-touch runtime

The observed optional runtime already supplies the adaptive first-touch
bijection used by the announced lower bound.  Revealing optimization differs
only in the duration and information content of an untouched completion: a
raw operation lasts the public duration `u`.  This file defines that timing
without changing the existing runtime and proves the generic
completion-curve integral for it.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace RawObserved

open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedEnvelope

noncomputable section

/-- Duration of an observed operation when a blind first touch is charged as
the revealing model's public raw operation. -/
def rawObservationDuration {n : ℕ} (u : ℝ)
    (processing : Fin n → ℝ) : Observation n → ℝ
  | .testResult _ _ => 1
  | .processed job => processing job
  | .blindCompleted _ _ => u

/-- Elapsed revealing-model time of an observed transcript. -/
def rawElapsed {n : ℕ} (u : ℝ) (processing : Fin n → ℝ) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      rawObservationDuration u processing observation +
        rawElapsed u processing rest

def rawTranscriptCompletionSteps {n : ℕ} (u : ℝ)
    (processing : Fin n → ℝ) (transcript : Transcript n) :
    List CompletionStep :=
  transcript.map fun observation =>
    ⟨rawObservationDuration u processing observation,
      observationCompletionCount processing observation⟩

/-- Exact suffix-weighted sum of completion times with blind first touches
charged duration `u`. -/
def rawCompletionCost {n : ℕ} (u : ℝ)
    (processing : Fin n → ℝ) (transcript : Transcript n) : ℝ :=
  completionStepsCost (rawTranscriptCompletionSteps u processing transcript)

@[simp] theorem rawTranscriptCompletionSteps_append {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ)
    (left right : Transcript n) :
    rawTranscriptCompletionSteps u processing (left ++ right) =
      rawTranscriptCompletionSteps u processing left ++
        rawTranscriptCompletionSteps u processing right := by
  simp [rawTranscriptCompletionSteps]

@[simp] theorem completionStepsTime_rawTranscriptCompletionSteps {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsTime
        (rawTranscriptCompletionSteps u processing transcript) =
      rawElapsed u processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      change rawObservationDuration u processing observation +
          completionStepsTime
            (rawTranscriptCompletionSteps u processing rest) =
        rawObservationDuration u processing observation +
          rawElapsed u processing rest
      rw [ih]

@[simp] theorem completionStepsCount_rawTranscriptCompletionSteps {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsCount
        (rawTranscriptCompletionSteps u processing transcript) =
      completionCount processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      change observationCompletionCount processing observation +
          completionStepsCount
            (rawTranscriptCompletionSteps u processing rest) =
        (if (observation.completionLabel processing).isSome then 1 else 0) +
          completionCount processing rest
      rw [ih]
      rfl

@[simp] theorem completionStepsCost_rawTranscriptCompletionSteps {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsCost
        (rawTranscriptCompletionSteps u processing transcript) =
      rawCompletionCost u processing transcript := by
  rfl

theorem rawObservationDuration_nonneg {n : ℕ} {u : ℝ}
    {processing : Fin n → ℝ} (hu : 0 ≤ u)
    (hp : ∀ job, 0 ≤ processing job) (observation : Observation n) :
    0 ≤ rawObservationDuration u processing observation := by
  cases observation <;> simp [rawObservationDuration, hu, hp]

theorem rawTranscriptCompletionSteps_duration_nonneg {n : ℕ} {u : ℝ}
    {processing : Fin n → ℝ} (hu : 0 ≤ u)
    (hp : ∀ job, 0 ≤ processing job) (transcript : Transcript n) :
    ∀ step ∈ rawTranscriptCompletionSteps u processing transcript,
      0 ≤ step.duration := by
  intro step hstep
  obtain ⟨observation, _hmem, rfl⟩ := List.mem_map.mp hstep
  exact rawObservationDuration_nonneg hu hp observation

theorem rawElapsed_nonneg {n : ℕ} {u : ℝ}
    {processing : Fin n → ℝ} (hu : 0 ≤ u)
    (hp : ∀ job, 0 ≤ processing job) (transcript : Transcript n) :
    0 ≤ rawElapsed u processing transcript := by
  rw [← completionStepsTime_rawTranscriptCompletionSteps]
  exact completionStepsTime_nonneg
    (rawTranscriptCompletionSteps_duration_nonneg hu hp transcript)

theorem rawCompletionCost_nonneg {n : ℕ} {u : ℝ}
    {processing : Fin n → ℝ} (hu : 0 ≤ u)
    (hp : ∀ job, 0 ≤ processing job) (transcript : Transcript n) :
    0 ≤ rawCompletionCost u processing transcript := by
  rw [← completionStepsCost_rawTranscriptCompletionSteps]
  exact completionStepsCost_nonneg
    (rawTranscriptCompletionSteps_duration_nonneg hu hp transcript)

/-- Raw timing decomposes into tests, known processing, and a public `u`
charge for every blind first touch. -/
theorem rawElapsed_eq_test_add_processed_add_raw {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) (transcript : Transcript n) :
    rawElapsed u processing transcript =
      transcript.testResults.length + processedWork processing transcript +
        u * blindCount transcript := by
  induction transcript with
  | nil => simp [rawElapsed, processedWork, blindCount,
      Transcript.testResults]
  | cons observation rest ih =>
      cases observation <;>
        simp [rawElapsed, rawObservationDuration, processedWork, blindCount,
          Transcript.testResults, ih] <;> ring

/-- Generic prefix-to-area theorem under revealing raw timing. -/
theorem rawTranscriptCost_ge_remaining_integral
    {n : ℕ} (hn : 0 < n) {u : ℝ} {processing : Fin n → ℝ}
    (transcript : Transcript n) (curve : ℝ → ℝ)
    (hcurveContinuous : Continuous curve) (hcurveMono : Monotone curve)
    (ζ ε : ℝ) (hu : 0 ≤ u) (hp : ∀ job, 0 ≤ processing job)
    (hcomplete : completionCount processing transcript = n)
    (hprefix : ∀ pre, pre <+: transcript →
      (completionCount processing pre : ℝ) / n ≤
        curve (rawElapsed u processing pre / n + ζ) + ε) :
    (∫ x in 0..rawElapsed u processing transcript / n,
        (1 - curve (x + ζ) - ε)) ≤
      rawCompletionCost u processing transcript / (n : ℝ) ^ 2 := by
  let steps := rawTranscriptCompletionSteps u processing transcript
  have hstepsDuration : ∀ step ∈ steps, 0 ≤ step.duration := by
    simpa [steps] using
      rawTranscriptCompletionSteps_duration_nonneg hu hp transcript
  have hstepsComplete : completionStepsCount steps = n := by
    simpa [steps] using hcomplete
  have hstepsPrefix : ∀ pre, pre <+: steps →
      (completionStepsCount pre : ℝ) / n ≤
        curve (completionStepsTime pre / n + ζ) + ε := by
    intro pre hpre
    rcases List.prefix_map_iff.mp (by
      simpa [steps, rawTranscriptCompletionSteps] using hpre) with
      ⟨source, hsource, rfl⟩
    change
      (completionStepsCount
          (rawTranscriptCompletionSteps u processing source) : ℝ) / n ≤
        curve
            (completionStepsTime
                (rawTranscriptCompletionSteps u processing source) / n + ζ) +
          ε
    rw [completionStepsCount_rawTranscriptCompletionSteps,
      completionStepsTime_rawTranscriptCompletionSteps]
    exact hprefix source hsource
  rw [← completionStepsCost_rawTranscriptCompletionSteps]
  simpa [steps] using completionStepsCost_ge_remaining_integral hn curve
    hcurveContinuous hcurveMono ζ ε steps hstepsDuration hstepsComplete
      hstepsPrefix

end

end RawObserved
end RevealingOptimization
end SchedulingPaper
