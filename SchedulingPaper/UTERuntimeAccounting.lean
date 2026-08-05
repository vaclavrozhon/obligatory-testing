import SchedulingPaper.StrategyTermination
import SchedulingPaper.UTEPairAccounting
import Mathlib.Tactic

/-!
# Runtime facts for ForcedPrefixUTE

This file records the operational facts needed before the literal UTE pair
calculation can be applied to a genuine run.

The generic termination theorem only retained completion.  Here we retain its
test/process invariant as well and add the fact that every published test
answer is the value of the fixed input.  Consequently, at the terminal
configuration:

* exactly `n` tests occurred, in label order;
* every label occurs with its genuine processing value;
* the local immediate/deferred decision after a test is exactly the predicate
  used in the paper.

These statements are independent of the still-missing global
transcript-to-unordered-pairs identity.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Every test result in a public transcript agrees with a fixed processing
vector. -/
def Transcript.TestsMatch
    (processingTime : Label n → ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults →
    p = processingTime job

@[simp] theorem Transcript.testsMatch_nil
    (processingTime : Label n → ℝ) :
    Transcript.TestsMatch processingTime [] := by
  intro job p h
  simp at h

/-- A successful operation against a fixed oracle preserves agreement of all
published test results with the fixed vector. -/
theorem Config.step_preserves_testsMatch
    (cap : Cap) (processingTime : Label n → ℝ)
    {config next : Config n} {action : Action n}
    (hmatch : config.transcript.TestsMatch processingTime)
    (hstep :
      config.step cap (fixedOracle processingTime) action = some next) :
    next.transcript.TestsMatch processingTime := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp only [Config.step, hjob, fixedOracle,
            Option.some.injEq] at hstep
          subst next
          intro other q hmem
          rw [Transcript.testResults_append] at hmem
          rcases List.mem_append.mp hmem with hold | hnew
          · exact hmatch other q hold
          · simp only [Transcript.testResults_testResult_cons,
              Transcript.testResults_nil, List.mem_singleton] at hnew
            rcases hnew with ⟨rfl, rfl⟩
            rfl
      | tested old =>
          simp [Config.step, hjob] at hstep
      | done =>
          simp [Config.step, hjob] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
      | tested p =>
          simp only [Config.step, hjob, Option.some.injEq] at hstep
          subst next
          simpa [Transcript.TestsMatch] using hmatch
      | done =>
          simp [Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp only [Config.step, hjob, Option.some.injEq] at hstep
              subst next
              simpa [Transcript.TestsMatch] using hmatch
          | tested p =>
              simp [Config.step, hjob] at hstep
          | done =>
              simp [Config.step, hjob] at hstep

/-- The work-rank proof while retaining both the structural transcript
invariant and agreement with the fixed input. -/
theorem runFuel_testProcessStrategy_completed_with_fixed_invariant
    (cap : Cap) (processingTime : Label n → ℝ)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending) (extra : ℕ) :
    let result :=
      runFuel cap (fixedOracle processingTime)
        (testProcessStrategy pending)
        (2 * n + 1 + extra) (Config.initial n)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      result.config.transcript.TestsMatch processingTime ∧
      ∀ job, result.config.jobs job = .done := by
  let Good : Config n → Prop :=
    fun config =>
      config.TestProcessInvariant ∧
        config.transcript.TestsMatch processingTime
  have hstop :
      ∀ config, Good config → config.remainingWork = 0 →
        testProcessStrategy pending config.transcript = none := by
    intro config hgood hzero
    exact testProcessStrategy_stop_of_zero hpending hgood.1 hzero
  have hprogress :
      ∀ config, Good config → 0 < config.remainingWork →
        WorkStep cap (fixedOracle processingTime)
          (testProcessStrategy pending) Good config := by
    intro config hgood hpos
    obtain ⟨action, next, haction, hstep, hnext, hwork⟩ :=
      testProcessStrategy_progress cap (fixedOracle processingTime)
        hpending hgood.1 hpos
    refine ⟨action, next, haction, hstep, ⟨hnext, ?_⟩, hwork⟩
    exact Config.step_preserves_testsMatch cap processingTime
      hgood.2 hstep
  have hrun :=
    runFuel_completedNormally_of_workRank cap
      (fixedOracle processingTime) (testProcessStrategy pending)
      Good hstop hprogress (Config.initial n)
      ⟨Config.initial_testProcessInvariant n,
        Transcript.testsMatch_nil processingTime⟩ extra
  rw [Config.initial_remainingWork] at hrun
  exact ⟨hrun.1, hrun.2.1.1, hrun.2.1.2, hrun.2.2⟩

/-- The strengthened terminal invariant for the actual ForcedPrefixUTE
strategy at the common analysis fuel. -/
theorem run_forcedPrefixUTEStrategy_fixed_invariant
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      result.config.transcript.TestsMatch processingTime ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run
  rw [forcedPrefixUTEStrategy_eq_testProcessStrategy]
  simpa using
    runFuel_testProcessStrategy_completed_with_fixed_invariant
      cap processingTime
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n b) (uteThreshold u)) 0

/-- A completed configuration satisfying the test/process invariant has
performed exactly one test per job. -/
theorem Config.TestProcessInvariant.testResults_length_eq
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hdone : ∀ job, config.jobs job = .done) :
    config.transcript.testResults.length = n := by
  by_contra hne
  have hbound := hgood.testBound
  have hlt : config.transcript.testResults.length < n := by
    omega
  let job : Label n :=
    ⟨config.transcript.testResults.length, hlt⟩
  have huntouched :
      config.jobs job = .untouched :=
    hgood.labelAtTestCount_untouched rfl
  rw [hdone job] at huntouched
  contradiction

/-- Every job occurs in the terminal test list, with its fixed value. -/
theorem terminal_testResult_mem
    {processingTime : Label n → ℝ} {config : Config n}
    (hgood : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (hdone : ∀ job, config.jobs job = .done)
    (job : Label n) :
    (job, processingTime job) ∈ config.transcript.testResults := by
  have hlength :
      config.transcript.testResults.length = n :=
    hgood.testResults_length_eq hdone
  have hval :
      job.val ∈
        config.transcript.testResults.map (fun result => result.1.val) := by
    rw [hgood.testOrder, hlength]
    simp
  rcases List.mem_map.mp hval with
    ⟨result, hresult, hresultValue⟩
  rcases result with ⟨resultJob, q⟩
  have hjob : resultJob = job := Fin.ext hresultValue
  subst resultJob
  have hp : q = processingTime job :=
    hmatch job q hresult
  subst q
  exact hresult

/-- The UTE threshold on the endpoint range `u=s+1`, `s≥1`, is exactly
one. -/
theorem uteThreshold_add_one_eq_one
    {s : ℝ} (hs : 1 ≤ s) :
    uteThreshold (s + 1) = 1 := by
  unfold uteThreshold
  rw [min_eq_left]
  linarith

/-- Exact local decision made immediately after appending one test result. -/
theorem forcedPrefixPendingImmediate_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (k : ℕ) (threshold : ℝ) :
    (transcript ++ [Observation.testResult job p]).forcedPrefixPendingImmediate?
        n k threshold =
      if transcript.testResults.length < k ∨ p ≤ threshold
        then some job else none := by
  unfold Transcript.forcedPrefixPendingImmediate?
  simp [Transcript.testResults_append]

/-- In the UTE endpoint range, the just-tested job is selected immediately
iff it lies in the forced prefix or its value is at most one. -/
theorem forcedPrefixPendingImmediate_ute_endpoint
    {s : ℝ} (hs : 1 ≤ s)
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).forcedPrefixPendingImmediate?
        n (forcedPrefixCount n (SchedulingPaper.uteB s))
          (uteThreshold (s + 1)) =
      if transcript.testResults.length <
            forcedPrefixCount n (SchedulingPaper.uteB s) ∨ p ≤ 1
        then some job else none := by
  rw [uteThreshold_add_one_eq_one hs]
  exact forcedPrefixPendingImmediate_append_testResult
    transcript job p _ _

end

end SchedulingPaper.Online
