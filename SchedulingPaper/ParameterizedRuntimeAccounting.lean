import SchedulingPaper.AdaptiveRuntimeAccounting
import SchedulingPaper.PlateauRuntimeInvariant

/-!
# Exact accounting for parameterized AdaptiveThreshold

The earlier adaptive runtime account specializes the symbolic state to
`rhoStar`.  This module keeps the executable coefficient arbitrary and
classifies each fixed-input label directly from the public counter prefix.
-/

namespace SchedulingPaper.Online

noncomputable section

open SchedulingPaper

/-- Live threshold reconstructed from all fixed test results preceding a
label. -/
def parameterizedRuntimeThreshold
    (c : ℝ) (processingTime : Label n → ℝ) (job : Label n) : ℝ :=
  (parameterizedCountersFromResults n c
      ((fixedTestResults processingTime).take job.val)).threshold n c

/-- Runtime decision class indexed by the original label. -/
def parameterizedRuntimeOutcomeByLabel
    (c : ℝ) (processingTime : Label n → ℝ) (job : Label n) :
    BoundaryOutcome :=
  if processingTime job = 0 then .zero
  else if processingTime job ≤
      parameterizedRuntimeThreshold c processingTime job
    then .immediate else .deferred

theorem parameterizedRuntimeThreshold_ge_one
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ) (job : Label n) :
    1 ≤ parameterizedRuntimeThreshold c processingTime job := by
  have hlength :
      ((fixedTestResults processingTime).take job.val).length < n := by
    rw [List.length_take, fixedTestResults_length]
    omega
  have hy :=
    parameterizedCountersFromResults_y_nonpos n hc
      ((fixedTestResults processingTime).take job.val) hlength
  unfold parameterizedRuntimeThreshold
  exact parameterizedAdaptiveThreshold_ge_one_of_nonpos hc hy

theorem parameterizedRuntimeThreshold_nonneg
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ) (job : Label n) :
    0 ≤ parameterizedRuntimeThreshold c processingTime job :=
  zero_le_one.trans
    (parameterizedRuntimeThreshold_ge_one hc processingTime job)

theorem parameterizedRuntimeOutcome_deferred_iff
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ) (job : Label n) :
    parameterizedRuntimeOutcomeByLabel c processingTime job =
        .deferred ↔
      parameterizedRuntimeThreshold c processingTime job <
        processingTime job := by
  unfold parameterizedRuntimeOutcomeByLabel
  by_cases hzero : processingTime job = 0
  · rw [hzero]
    simp [parameterizedRuntimeThreshold_nonneg hc]
  · simp [hzero, not_le]

theorem parameterizedRuntimeOutcome_nonzero_of_deferred
    {c : ℝ} (processingTime : Label n → ℝ) (job : Label n)
    (hjob :
      parameterizedRuntimeOutcomeByLabel c processingTime job =
        .deferred) :
    processingTime job ≠ 0 := by
  intro hzero
  simp [parameterizedRuntimeOutcomeByLabel, hzero] at hjob

/-- The executable pending selector after a displayed test agrees exactly
with the prefix-counter runtime class. -/
theorem parameterizedPendingImmediate_after_test_eq_runtimeOutcome
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ)
    {config : Config n} {before after : Transcript n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (htrace : TestProcessTrace config.transcript)
    (hdone : ∀ job, config.jobs job = .done)
    (job : Label n) (p : ℝ)
    (hdecomp :
      config.transcript =
        before ++ Observation.testResult job p :: after) :
    Transcript.parameterizedPendingImmediate?
        n c (before ++ [Observation.testResult job p]) =
      if parameterizedRuntimeOutcomeByLabel c processingTime job =
          .deferred
        then none else some job := by
  have hp : p = processingTime job := by
    apply hmatch job p
    apply
      (testResult_mem_iff_observation_mem
        config.transcript job p).2
    rw [hdecomp]
    simp
  have hprefix :=
    testsBefore_eq_fixedTestResults_take
      hstruct hmatch htrace hdone job p hdecomp
  have hcounters :
      Transcript.parameterizedCountersBeforeLastTest
          n c (before ++ [Observation.testResult job p]) =
        parameterizedCountersFromResults n c
          before.testResults := by
    unfold Transcript.parameterizedCountersBeforeLastTest
    simp
  have hpending :
      Transcript.parameterizedPendingImmediate?
          n c (before ++ [Observation.testResult job p]) =
        if p ≤ parameterizedRuntimeThreshold c processingTime job
          then some job else none := by
    unfold Transcript.parameterizedPendingImmediate?
    rw [List.getLast?_concat]
    simp only
    rw [hcounters, hprefix]
    rfl
  rw [hpending, hp]
  unfold parameterizedRuntimeOutcomeByLabel
  by_cases hzero : processingTime job = 0
  · have hle :
        processingTime job ≤
          parameterizedRuntimeThreshold c processingTime job := by
      rw [hzero]
      exact parameterizedRuntimeThreshold_nonneg hc _ _
    rw [if_pos hle]
    simp [hzero]
  · by_cases hle :
      processingTime job ≤
        parameterizedRuntimeThreshold c processingTime job
    · rw [if_pos hle]
      simp [hzero, hle]
    · rw [if_neg hle]
      simp [hzero, hle]

theorem parameterizedRuntime_immediateFor
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ)
    {config : Config n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (htrace : TestProcessTrace config.transcript)
    (hdone : ∀ job, config.jobs job = .done)
    (job : Label n)
    (hjob :
      parameterizedRuntimeOutcomeByLabel c processingTime job ≠
        .deferred) :
    config.transcript.ImmediateFor
      (fun transcript =>
        transcript.parameterizedPendingImmediate? n c) job := by
  intro before after p hdecomp
  change
    Transcript.parameterizedPendingImmediate?
      n c (before ++ [Observation.testResult job p]) = some job
  rw [parameterizedPendingImmediate_after_test_eq_runtimeOutcome
    hc processingTime hstruct hmatch htrace hdone job p hdecomp]
  simp [hjob]

theorem parameterizedRuntime_deferredFor
    {c : ℝ} (hc : 0 < c)
    (processingTime : Label n → ℝ)
    {config : Config n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (htrace : TestProcessTrace config.transcript)
    (hdone : ∀ job, config.jobs job = .done)
    (job : Label n)
    (hjob :
      parameterizedRuntimeOutcomeByLabel c processingTime job =
        .deferred) :
    config.transcript.DeferredFor
      (fun transcript =>
        transcript.parameterizedPendingImmediate? n c) job := by
  intro before after p hdecomp
  change
    Transcript.parameterizedPendingImmediate?
      n c (before ++ [Observation.testResult job p]) = none
  rw [parameterizedPendingImmediate_after_test_eq_runtimeOutcome
    hc processingTime hstruct hmatch htrace hdone job p hdecomp]
  simp [hjob]

theorem run_parameterizedAdaptiveThresholdStrategy_completionLabels_perm_generic
    (n : ℕ) (c : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    (result.config.transcript.completionLabels processingTime).Perm
      (List.ofFn id) := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (parameterizedAdaptiveThresholdStrategy n c)
      (2 * n + 1)
  have hrun :=
    run_parameterizedAdaptiveThresholdStrategy_canonicalTrace
      n c cap processingTime
  have hnodup :
      (result.config.transcript.completionLabels
        processingTime).Nodup :=
    hrun.2.2.2.1.nodup
  have hmem :
      ∀ job,
        job ∈ result.config.transcript.completionLabels
          processingTime := by
    intro job
    rw [hrun.2.2.2.1.mem_iff]
    simp [hrun.2.2.2.2.2 job,
      JobState.completionRecorded]
  apply
    (List.perm_ext_iff_of_nodup hnodup
      (List.nodup_ofFn.mpr Function.injective_id)).mpr
  intro job
  simp [hmem job]

theorem run_parameterizedAdaptiveThresholdStrategy_pairCharge_eq_generic
    (n : ℕ) {c : ℝ} (hc : 0 < c) (cap : Cap)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right) :
    let result :=
      run cap (fixedOracle processingTime)
        (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    tracePairCharge cap processingTime
        result.config.transcript left right =
      obligatoryALGPairCharge
        ⟨parameterizedRuntimeOutcomeByLabel c processingTime left,
          processingTime left⟩
        ⟨parameterizedRuntimeOutcomeByLabel c processingTime right,
          processingTime right⟩ := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (parameterizedAdaptiveThresholdStrategy n c)
      (2 * n + 1)
  have hrun :=
    run_parameterizedAdaptiveThresholdStrategy_canonicalTrace
      n c cap processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hfollow :
      result.config.transcript.FollowsStrategy
        (testProcessStrategy
          (fun transcript =>
            transcript.parameterizedPendingImmediate? n c)) := by
    simpa [result,
      parameterizedAdaptiveThresholdStrategy_eq_testProcessStrategy] using
      run_followsStrategy cap (fixedOracle processingTime)
        (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
  exact
    hrun.2.2.2.2.1.tracePairCharge_eq_obligatoryALGPairCharge
      hrun.2.2.1 hallTests hallProcessed hfollow
      (parameterizedPendingImmediate_selectsLastTest n c)
      (parameterizedRuntimeOutcomeByLabel c processingTime)
      (parameterizedRuntime_immediateFor hc processingTime
        hrun.2.1 hrun.2.2.1 hrun.2.2.2.2.1
        hrun.2.2.2.2.2)
      (parameterizedRuntime_deferredFor hc processingTime
        hrun.2.1 hrun.2.2.1 hrun.2.2.2.2.1
        hrun.2.2.2.2.2)
      (parameterizedRuntimeOutcome_nonzero_of_deferred
        processingTime)
      cap horder

/-- Exact diagonal-plus-status-pairs formula for arbitrary positive
coefficient `c`. -/
theorem run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_statusPairs_generic
    (n : ℕ) {c : ℝ} (hc : 0 < c) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    runCompletionCost cap processingTime result =
      Finset.univ.sum
          (fun job : Label n => (1 : ℝ) + processingTime job) +
        Finset.univ.sum (fun left : Label n =>
          (Finset.univ.filter
            (fun right : Label n => left < right)).sum
              (fun right =>
                obligatoryALGPairCharge
                  ⟨parameterizedRuntimeOutcomeByLabel
                      c processingTime left,
                    processingTime left⟩
                  ⟨parameterizedRuntimeOutcomeByLabel
                      c processingTime right,
                    processingTime right⟩)) := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (parameterizedAdaptiveThresholdStrategy n c)
      (2 * n + 1)
  have hrun :=
    run_parameterizedAdaptiveThresholdStrategy_canonicalTrace
      n c cap processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hperm :
      (result.config.transcript.completionLabels
        processingTime).Perm (List.ofFn id) := by
    simpa [result] using
      run_parameterizedAdaptiveThresholdStrategy_completionLabels_perm_generic
        n c cap processingTime
  have hdecomposition :=
    completionCost_eq_traceSelf_add_pairs cap processingTime
      result.config.transcript hperm
  have hself :
      ∀ job : Label n,
        traceSelfCharge cap processingTime
            result.config.transcript job =
          1 + processingTime job := by
    intro job
    apply traceSelfCharge_eq_one_add_of_projection
    · exact
        hrun.2.2.2.2.1.terminal_selfProjection
          hrun.2.2.1 hallTests hallProcessed job
    · rfl
  unfold runCompletionCost
  rw [hdecomposition]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro job _hjob
    exact hself job
  · apply Finset.sum_congr rfl
    intro left _hleft
    apply Finset.sum_congr rfl
    intro right hright
    exact
      run_parameterizedAdaptiveThresholdStrategy_pairCharge_eq_generic
        n hc cap processingTime
        (Finset.mem_filter.mp hright).2

/-- Exact recursive pair objective for arbitrary positive coefficient `c`. -/
theorem run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_ALG_generic
    (n : ℕ) {c : ℝ} (hc : 0 < c) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    runCompletionCost cap processingTime result =
      obligatoryALGPairObjective
        (obligatoryJobsOfFunctions
          (parameterizedRuntimeOutcomeByLabel c processingTime)
          processingTime) := by
  dsimp only
  rw [run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_statusPairs_generic
    n hc cap processingTime]
  exact
    (obligatoryALGPairObjective_jobsOfFunctions_eq_finSums
      (parameterizedRuntimeOutcomeByLabel c processingTime)
      processingTime).symm

end

end SchedulingPaper.Online
