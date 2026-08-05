import SchedulingPaper.AdaptiveRuntimeAccounting
import SchedulingPaper.UTEFiniteEndpointAccounting
import SchedulingPaper.UTEFixedWordRuntimeBridge
import Mathlib.Tactic

/-!
# Status-sensitive runtime accounting for the UTE endpoint branch

The generic test/process accounting theorem already proves the exact
three-case pair table of the paper.  This file specializes its abstract
immediate/deferred status to `ForcedPrefixUTE` on the range `u = s + 1`,
`s ≥ 1`.

Keeping the status separate from the processing coordinate is important:
the endpoint reduction represents a deferred value tending to one by the
formal endpoint `boundaryDeferred`, although an actual value equal to one
would be processed immediately.
-/

namespace SchedulingPaper

noncomputable section

open LowerBound

/-- Frozen immediate/deferred status of a UTE run with forced prefix `k`. -/
def uteRuntimeOutcome {n : ℕ} (k : ℕ)
    (processing : Fin n → ℝ) (job : Fin n) : BoundaryOutcome :=
  if job.val < k ∨ processing job ≤ 1 then
    .immediate
  else
    .deferred

@[simp] theorem uteRuntimeOutcome_eq_deferred_iff
    {n k : ℕ} {processing : Fin n → ℝ} {job : Fin n} :
    uteRuntimeOutcome k processing job = .deferred ↔
      ¬ (job.val < k ∨ processing job ≤ 1) := by
  unfold uteRuntimeOutcome
  split <;> simp_all

@[simp] theorem uteRuntimeOutcome_ne_deferred_iff
    {n k : ℕ} {processing : Fin n → ℝ} {job : Fin n} :
    uteRuntimeOutcome k processing job ≠ .deferred ↔
      job.val < k ∨ processing job ≤ 1 := by
  unfold uteRuntimeOutcome
  split <;> simp_all

namespace Online

/-- Every job classified as immediate is selected immediately after its
unique test in the completed endpoint-range trace. -/
theorem uteRuntime_immediateFor
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (k : ℕ) :
    ∀ job,
      uteRuntimeOutcome k processingTime job ≠ .deferred →
        transcript.ImmediateFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n k (uteThreshold (s + 1)))
          job := by
  intro job himmediate before after p hdecomp
  have hp :
      p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  change
    Transcript.forcedPrefixPendingImmediate?
        n k (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      some job
  rw [uteThreshold_add_one_eq_one hs,
    forcedPrefixPendingImmediate_append_testResult,
    hbefore, hp]
  have hcondition :
      job.val < k ∨ processingTime job ≤ 1 :=
    uteRuntimeOutcome_ne_deferred_iff.mp himmediate
  simp [hcondition]

/-- Every job classified as deferred leaves the pending selector empty
immediately after its unique test. -/
theorem uteRuntime_deferredFor
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (k : ℕ) :
    ∀ job,
      uteRuntimeOutcome k processingTime job = .deferred →
        transcript.DeferredFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n k (uteThreshold (s + 1)))
          job := by
  intro job hdeferred before after p hdecomp
  have hp :
      p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  change
    Transcript.forcedPrefixPendingImmediate?
        n k (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      none
  rw [uteThreshold_add_one_eq_one hs,
    forcedPrefixPendingImmediate_append_testResult,
    hbefore, hp]
  have hcondition :
      ¬ (job.val < k ∨ processingTime job ≤ 1) :=
    uteRuntimeOutcome_eq_deferred_iff.mp hdeferred
  simp [hcondition]

theorem uteRuntime_deferred_nonzero
    {n k : ℕ} {processingTime : Label n → ℝ} :
    ∀ job,
      uteRuntimeOutcome k processingTime job = .deferred →
        processingTime job ≠ 0 := by
  intro job hdeferred hzero
  have hcondition :=
    uteRuntimeOutcome_eq_deferred_iff.mp hdeferred
  apply hcondition
  right
  rw [hzero]
  norm_num

/-- Exact pair-table charge of the concrete endpoint-range UTE run. -/
theorem run_forcedPrefixUTE_endpoint_pairCharge_eq
    (n : ℕ) {s b : ℝ} (hs : 1 ≤ s)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
    tracePairCharge (.finite (s + 1)) processingTime
        result.config.transcript left right =
      obligatoryALGPairCharge
        ⟨uteRuntimeOutcome (forcedPrefixCount n b)
            processingTime left,
          processingTime left⟩
        ⟨uteRuntimeOutcome (forcedPrefixCount n b)
            processingTime right,
          processingTime right⟩ := by
  dsimp only
  let result :=
    run (.finite (s + 1)) (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n (s + 1) b (.finite (s + 1)) processingTime
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
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n (forcedPrefixCount n b)
                (uteThreshold (s + 1)))) := by
    have h :=
      run_followsStrategy (.finite (s + 1))
        (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b)
        (2 * n + 1)
    rw [forcedPrefixUTEStrategy_eq_testProcessStrategy] at h
    exact h
  exact
    hrun.2.2.2.2.1.tracePairCharge_eq_obligatoryALGPairCharge
      hrun.2.2.1 hallTests hallProcessed hfollow
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n b) (uteThreshold (s + 1)))
      (uteRuntimeOutcome (forcedPrefixCount n b) processingTime)
      (uteRuntime_immediateFor hs hrun.2.2.2.2.1
        hrun.2.2.1 hallTests (forcedPrefixCount n b))
      (uteRuntime_deferredFor hs hrun.2.2.2.2.1
        hrun.2.2.1 hallTests (forcedPrefixCount n b))
      (uteRuntime_deferred_nonzero
        (k := forcedPrefixCount n b)
        (processingTime := processingTime))
      (.finite (s + 1)) horder

/-- The whole concrete completion cost is the recursive status-sensitive
pair objective. -/
theorem run_forcedPrefixUTE_endpoint_completionCost_eq_statusALG
    (n : ℕ) {s b : ℝ} (hs : 1 ≤ s)
    (processingTime : Label n → ℝ) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
    runCompletionCost (.finite (s + 1)) processingTime result =
      obligatoryALGPairObjective
        (obligatoryJobsOfFunctions
          (uteRuntimeOutcome (forcedPrefixCount n b) processingTime)
          processingTime) := by
  dsimp only
  rw [run_forcedPrefixUTEStrategy_completionCost_eq_self_add_pairs]
  rw [obligatoryALGPairObjective_jobsOfFunctions_eq_finSums]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro left _hleft
    apply Finset.sum_congr rfl
    intro right hright
    exact run_forcedPrefixUTE_endpoint_pairCharge_eq
      n hs processingTime (Finset.mem_filter.mp hright).2

end Online

/-- Status-sensitive exact competitive excess before endpoint reduction. -/
def uteRuntimeExcess {n : ℕ}
    (s : ℝ) (k : ℕ) (processing : Fin n → ℝ) : ℝ :=
  obligatoryALGPairObjective
      (obligatoryJobsOfFunctions
        (uteRuntimeOutcome k processing) processing) -
    uteRho s * vectorOfflineCost (.finite (s + 1)) processing

/-- One frozen-status pair contribution to competitive excess. -/
def uteStatusPairExcess
    (s : ℝ) (leftOutcome rightOutcome : BoundaryOutcome)
    (p q : ℝ) : ℝ :=
  obligatoryALGPairCharge
      ⟨leftOutcome, p⟩ ⟨rightOutcome, q⟩ -
    uteRho s * uteFixedOPTPairCharge s p q

/-- Finite-index form of the exact UTE status objective. -/
def uteStatusWordExcess {n : ℕ}
    (s : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, uteFixedSelfExcessAt s (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      uteStatusPairExcess s
        (outcome i) (outcome j) (processing i) (processing j)

theorem uteRuntimeExcess_eq_statusWordExcess
    {n k : ℕ} (s : ℝ) (processing : Fin n → ℝ) :
    uteRuntimeExcess s k processing =
      uteStatusWordExcess s
        (uteRuntimeOutcome k processing) processing := by
  rw [uteRuntimeExcess,
    Online.obligatoryALGPairObjective_jobsOfFunctions_eq_finSums,
    vectorOfflineCost_finite_add_one_eq_uteFixedWordOPT]
  unfold uteStatusWordExcess uteStatusPairExcess
    uteFixedSelfExcessAt uteFixedWordOPT
  simp only [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  ring

/-- Endpoint status used by the frozen endpoint word. -/
def UTEEndpoint.outcome : UTEEndpoint → BoundaryOutcome
  | .forcedCap | .forcedZero | .immediateOne | .suffixZero =>
      .immediate
  | .cappedDeferred | .boundaryDeferred => .deferred

@[simp] theorem obligatoryALGPairCharge_uteEndpoint
    (s : ℝ) (left right : UTEEndpoint) :
    obligatoryALGPairCharge
        ⟨left.outcome, uteEndpointProcessing s left⟩
        ⟨right.outcome, uteEndpointProcessing s right⟩ =
      uteALGPairCharge s left right := by
  cases left <;> cases right <;>
    simp [UTEEndpoint.outcome, obligatoryALGPairCharge,
      uteALGPairCharge, UTEEndpoint.IsImmediate,
      uteEndpointProcessing]

@[simp] theorem uteFixedOPTPairCharge_uteEndpoint
    (s : ℝ) (left right : UTEEndpoint) :
    uteFixedOPTPairCharge s
        (uteEndpointProcessing s left)
        (uteEndpointProcessing s right) =
      uteOPTPairCharge s left right := by
  rfl

/-- Competitive excess of a formal endpoint word, including its diagonal. -/
def uteEndpointWordExcess {n : ℕ}
    (s : ℝ) (endpoint : Fin n → UTEEndpoint) : ℝ :=
  uteStatusWordExcess s
    (fun i => (endpoint i).outcome)
    (fun i => uteEndpointProcessing s (endpoint i))

theorem uteEndpointWordExcess_eq_self_add_pairLists
    {n : ℕ} (s : ℝ) (endpoint : Fin n → UTEEndpoint) :
    uteEndpointWordExcess s endpoint =
      (∑ i,
        uteFixedSelfExcessAt s
          (uteEndpointProcessing s (endpoint i))) +
        listPairObjective (fun _ => 0)
            (uteALGPairCharge s) (List.ofFn endpoint) -
        uteRho s *
          listPairObjective (fun _ => 0)
            (uteOPTPairCharge s) (List.ofFn endpoint) := by
  unfold uteEndpointWordExcess uteStatusWordExcess
    uteStatusPairExcess
  have halg :=
    finSelfPairSum_eq_listPairObjective
      (fun _ : UTEEndpoint => 0)
      (uteALGPairCharge s) endpoint
  have hopt :=
    finSelfPairSum_eq_listPairObjective
      (fun _ : UTEEndpoint => 0)
      (uteOPTPairCharge s) endpoint
  simp only [Finset.sum_const_zero, zero_add] at halg hopt
  simp_rw [obligatoryALGPairCharge_uteEndpoint,
    uteFixedOPTPairCharge_uteEndpoint]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [halg, hopt]
  ring

/-- Exact operational excess of `ForcedPrefixUTE` on the endpoint range. -/
theorem run_forcedPrefixUTE_endpoint_excess_eq
    (n : ℕ) {s b : ℝ} (hs : 1 ≤ s)
    (processingTime : Online.Label n → ℝ) :
    let result :=
      Online.run (.finite (s + 1))
        (Online.fixedOracle processingTime)
        (Online.forcedPrefixUTEStrategy n (s + 1) b)
        (2 * n + 1)
    Online.runCompletionCost (.finite (s + 1))
          processingTime result -
        uteRho s *
          vectorOfflineCost (.finite (s + 1)) processingTime =
      uteRuntimeExcess s
        (Online.forcedPrefixCount n b) processingTime := by
  dsimp only
  rw [Online.run_forcedPrefixUTE_endpoint_completionCost_eq_statusALG
    n hs processingTime]
  rfl

end

end SchedulingPaper
