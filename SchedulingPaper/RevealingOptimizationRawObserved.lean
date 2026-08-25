import SchedulingPaper.RandomizedOptionalObservedCompletionIntegral
import SchedulingPaper.RandomizedOptionalWorkInvariant
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
open RandomizedOptional.ObservedTrace

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

/-- Known-processing work is bounded by the public cap times the number of
known processing operations. -/
theorem processedWork_le_cap_mul_processedLabels_length
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    (hcap : ∀ job, processing job ≤ u) (transcript : Transcript n) :
    processedWork processing transcript ≤
      u * transcript.processedLabels.length := by
  induction transcript with
  | nil => simp [processedWork, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult job value =>
          simpa [processedWork, Transcript.processedLabels] using ih
      | processed job =>
          simp only [processedWork, Transcript.processedLabels, List.length_cons,
            Nat.cast_add, Nat.cast_one]
          nlinarith [hcap job]
      | blindCompleted job value =>
          simpa [processedWork, Transcript.processedLabels] using ih

/-- Every settled revealing run has normalized raw horizon at most `1+u`.
This uses only the public cap, not any distributional estimate. -/
theorem settled_rawElapsed_div_le_one_add_cap
    {n : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    (policy : CompletePolicy p) (σ : ObservedTrace.Placement n)
    {u : ℝ} (hu : 0 ≤ u) (hcap : ∀ job, p job ≤ u) :
    rawElapsed u (placedProcessing p σ)
        (settledRun p policy.strategy σ).config.transcript / n ≤ 1 + u := by
  let transcript := (settledRun p policy.strategy σ).config.transcript
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgood := run_historyInvariant (placedProcessing p σ)
    policy.strategy (2 * n + 1)
  have hprocessedCount :
      transcript.processedLabels.length ≤ transcript.testResults.length := by
    have hcount := ObservedOnline.processedClassCount_le_testClassCount
      hgood (fun _ => true)
    dsimp [transcript, settledRun]
    simpa [ObservedOnline.processedClassCount,
      ObservedOnline.testClassCount] using hcount
  have htouched :
      transcript.testResults.length + blindCount transcript = n := by
    rw [← touchChoices_length_eq_test_add_blind]
    have hchoices := touchTrace_choices_ofFn p policy σ
    dsimp [transcript]
    rw [← hchoices]
    simp
  have hprocessedBlind :
      transcript.processedLabels.length + blindCount transcript ≤ n := by
    omega
  have htestLe : transcript.testResults.length ≤ n := by omega
  have hwork := processedWork_le_cap_mul_processedLabels_length
    (processing := placedProcessing p σ) (u := u)
    (fun job => hcap (σ job)) transcript
  have hprocessedBlindR :
      (transcript.processedLabels.length : ℝ) + blindCount transcript ≤ n := by
    exact_mod_cast hprocessedBlind
  have htestR : (transcript.testResults.length : ℝ) ≤ n := by
    exact_mod_cast htestLe
  have htail :
      processedWork (placedProcessing p σ) transcript +
          u * blindCount transcript ≤ u * n := by
    have hmul := mul_le_mul_of_nonneg_left hprocessedBlindR hu
    push_cast at hmul
    nlinarith
  rw [rawElapsed_eq_test_add_processed_add_raw]
  rw [div_le_iff₀ hnR]
  dsimp [transcript] at htestR htail ⊢
  nlinarith

/-- At completion, known processing work is exactly the processing mass of
the occurrence tokens selected for testing by the adaptive first-touch
bijection. -/
theorem settled_processedWork_eq_compiledTestWork
    {n : ℕ} (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n) :
    processedWork (placedProcessing p σ)
        (settledRun p policy.strategy σ).config.transcript =
      ∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ) *
          p (TraceBijection.revealOrder (touchTrace p policy) σ k) := by
  let transcript := (settledRun p policy.strategy σ).config.transcript
  let reveal := TraceBijection.revealOrder (touchTrace p policy) σ
  let selected : ℝ := ∑ k, compiledTestSelector p policy k reveal * p (reveal k)
  have hwork := run_processingWork_eq_sum_of_done
    (placedProcessing p σ) policy.strategy (2 * n + 1) (policy.completes σ)
  have hblind := compiled_blind_work_sum_eq_operational p policy σ
  have hsumPlaced : (∑ job, placedProcessing p σ job) = ∑ job, p job := by
    simpa [placedProcessing] using Equiv.sum_comp σ p
  have hsplit : selected +
      (∑ k, (1 - compiledTestSelector p policy k reveal) * p (reveal k)) =
        ∑ job, p job := by
    dsimp [selected]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x, (compiledTestSelector p policy x reveal * p (reveal x) +
          (1 - compiledTestSelector p policy x reveal) * p (reveal x))) =
          ∑ x, p (reveal x) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = ∑ job, p job := by simpa using Equiv.sum_comp reveal p
  change processedWork (placedProcessing p σ) transcript +
      blindWork transcript = ∑ job, placedProcessing p σ job at hwork
  change (∑ k, (1 - compiledTestSelector p policy k reveal) * p (reveal k)) =
      blindWork transcript at hblind
  dsimp [transcript, reveal, selected] at hwork hblind hsplit hsumPlaced ⊢
  linarith

/-- The completed first-touch trace partitions all jobs into tested and raw
jobs. -/
theorem settled_testCount_add_blindCount_eq_n
    {n : ℕ} (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n) :
    (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ)) +
      blindCount (settledRun p policy.strategy σ).config.transcript = n := by
  let transcript := (settledRun p policy.strategy σ).config.transcript
  have htest := compiled_test_class_sum_eq_operational
    p policy σ (fun _ => true)
  have htouch : (touchChoices transcript).length = n := by
    have hchoices := touchTrace_choices_ofFn p policy σ
    dsimp [transcript]
    rw [← hchoices]
    simp
  have hpartition := touchChoices_length_eq_test_add_blind transcript
  have htest' :
      (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ)) =
          transcript.testResults.length := by
    simpa [transcript] using htest
  dsimp [transcript] at hpartition htouch htest' ⊢
  rw [htest']
  exact_mod_cast hpartition.symm.trans htouch

/-- Exact terminal raw timing in compiled-selector coordinates. -/
theorem settled_rawElapsed_eq_compiledTestWork
    {n : ℕ} (u : ℝ) (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n) :
    rawElapsed u (placedProcessing p σ)
        (settledRun p policy.strategy σ).config.transcript =
      (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ)) +
      (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ) *
          p (TraceBijection.revealOrder (touchTrace p policy) σ k)) +
      u * blindCount (settledRun p policy.strategy σ).config.transcript := by
  rw [rawElapsed_eq_test_add_processed_add_raw,
    settled_processedWork_eq_compiledTestWork]
  have htest := compiled_test_class_sum_eq_operational
    p policy σ (fun _ => true)
  simpa using congrArg (fun x : ℝ =>
    x + (∑ k, compiledTestSelector p policy k
      (TraceBijection.revealOrder (touchTrace p policy) σ) *
        p (TraceBijection.revealOrder (touchTrace p policy) σ k)) +
      u * blindCount (settledRun p policy.strategy σ).config.transcript) htest.symm

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

theorem rawTranscriptCost_ge_fluidBlocksArea_of_terminal_le_shift
    {n : ℕ} (hn : 0 < n) {u : ℝ} {processing : Fin n → ℝ}
    (transcript : Transcript n) (blocks : List FluidBlock)
    (ζ ε : ℝ)
    (hζ : 0 ≤ ζ) (hu : 0 ≤ u)
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hcomplete : completionCount processing transcript = n)
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass)
    (hmassOne : fluidBlocksMass blocks = 1)
    (hterminal : fluidBlocksWork blocks ≤
      rawElapsed u processing transcript / n + ζ)
    (hprefix : ∀ pre, pre <+: transcript →
      (completionCount processing pre : ℝ) / n ≤
        fluidBlocksCompleted blocks (rawElapsed u processing pre / n + ζ) + ε) :
    fluidBlocksArea blocks - ζ -
        ε * (rawElapsed u processing transcript / n) ≤
      rawCompletionCost u processing transcript / (n : ℝ) ^ 2 := by
  let curve : ℝ → ℝ := fluidBlocksCompleted blocks
  let remaining : ℝ → ℝ := fun x => 1 - curve x
  let T := fluidBlocksWork blocks
  let A := rawElapsed u processing transcript / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcurveContinuous : Continuous curve := by
    simpa [curve] using fluidBlocksCompleted_continuous blocks
  have hcurveMono : Monotone curve := by
    simpa [curve] using fluidBlocksCompleted_monotone hcost
  have hT : 0 ≤ T := by
    dsimp [T]
    exact fluidBlocksWork_nonneg hcost hmass
  have helapsed0 : 0 ≤ rawElapsed u processing transcript :=
    rawElapsed_nonneg hu hprocessing transcript
  have hA : 0 ≤ A := div_nonneg helapsed0 hnR.le
  have hremainingContinuous : Continuous remaining :=
    continuous_const.sub hcurveContinuous
  have hremaining0 : ∀ x, 0 ≤ remaining x := by
    intro x
    dsimp [remaining, curve]
    exact sub_nonneg.mpr (by
      simpa [hmassOne] using fluidBlocksCompleted_le_mass hmass x)
  have hremaining1 : ∀ x, remaining x ≤ 1 := by
    intro x
    dsimp [remaining, curve]
    linarith [fluidBlocksCompleted_nonneg hmass x]
  have harea : (∫ x in 0..T, remaining x) = fluidBlocksArea blocks := by
    dsimp [remaining, curve, T]
    simpa [hmassOne] using
      fluidBlocks_remaining_integral_eq_area blocks hcost hmass
  have hshiftedInt : IntervalIntegrable (fun x => remaining (x + ζ))
      MeasureTheory.volume 0 A :=
    (hremainingContinuous.comp
      (continuous_id.add continuous_const)).intervalIntegrable 0 A
  have hconstantInt : IntervalIntegrable (fun _x : ℝ => ε)
      MeasureTheory.volume 0 A := continuous_const.intervalIntegrable 0 A
  have hhorizontal :
      (∫ x in 0..T, remaining x) - ζ ≤
        ∫ x in 0..A, remaining (x + ζ) := by
    by_cases hζT : ζ ≤ T
    · have hTend : T ≤ A + ζ := by simpa [T, A] using hterminal
      have hInt0ζ : IntervalIntegrable remaining MeasureTheory.volume 0 ζ :=
        hremainingContinuous.intervalIntegrable 0 ζ
      have hIntζT : IntervalIntegrable remaining MeasureTheory.volume ζ T :=
        hremainingContinuous.intervalIntegrable ζ T
      have hIntTend :
          IntervalIntegrable remaining MeasureTheory.volume T (A + ζ) :=
        hremainingContinuous.intervalIntegrable T (A + ζ)
      have hsplit0 :
          (∫ x in 0..ζ, remaining x) + (∫ x in ζ..T, remaining x) =
            ∫ x in 0..T, remaining x :=
        intervalIntegral.integral_add_adjacent_intervals hInt0ζ hIntζT
      have hsplitT :
          (∫ x in ζ..T, remaining x) +
              (∫ x in T..A + ζ, remaining x) =
            ∫ x in ζ..A + ζ, remaining x :=
        intervalIntegral.integral_add_adjacent_intervals hIntζT hIntTend
      have hfirst : (∫ x in 0..ζ, remaining x) ≤ ζ := by
        calc
          (∫ x in 0..ζ, remaining x) ≤ ∫ _x in 0..ζ, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hζ hInt0ζ (by simp) (by
              intro x hx
              exact hremaining1 x)
          _ = ζ := by simp
      have hlast : 0 ≤ ∫ x in T..A + ζ, remaining x :=
        intervalIntegral.integral_nonneg_of_forall hTend hremaining0
      have hshift :
          (∫ x in 0..A, remaining (x + ζ)) =
            ∫ x in ζ..A + ζ, remaining x := by simp
      rw [hshift]
      linarith
    · have hTζ : T ≤ ζ := le_of_not_ge hζT
      have hareaLe : (∫ x in 0..T, remaining x) ≤ T := by
        have hInt0T :
            IntervalIntegrable remaining MeasureTheory.volume 0 T :=
          hremainingContinuous.intervalIntegrable 0 T
        calc
          (∫ x in 0..T, remaining x) ≤ ∫ _x in 0..T, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hT hInt0T (by simp) (by
              intro x hx
              exact hremaining1 x)
          _ = T := by simp
      have hshiftNonneg : 0 ≤ ∫ x in 0..A, remaining (x + ζ) :=
        intervalIntegral.integral_nonneg_of_forall hA fun x =>
          hremaining0 (x + ζ)
      linarith
  have hintegral := rawTranscriptCost_ge_remaining_integral hn transcript curve
    hcurveContinuous hcurveMono ζ ε hu hprocessing hcomplete hprefix
  have hvertical :
      (∫ x in 0..A, (remaining (x + ζ) - ε)) =
        (∫ x in 0..A, remaining (x + ζ)) - ε * A := by
    rw [intervalIntegral.integral_sub hshiftedInt hconstantInt]
    simp
    ring
  change (∫ x in 0..A, (remaining (x + ζ) - ε)) ≤ _ at hintegral
  rw [hvertical] at hintegral
  rw [harea] at hhorizontal
  linarith

end

end RawObserved
end RevealingOptimization
end SchedulingPaper
