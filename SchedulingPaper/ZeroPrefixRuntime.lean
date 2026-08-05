import SchedulingPaper.StrategyTermination
import Mathlib.Tactic

/-!
# Runtime shape of the Zero-prefix strategy

This file discharges the purely operational part of the Zero-prefix bridge.
At the common analysis fuel, the concrete `ForcedPrefixUTE(n,s+1,0)` run

* stops normally with every job completed,
* still satisfies the test/process state invariant,
* has tested exactly all `n` labels in label order, and
* every published test answer agrees with the fixed processing vector.

For `s ≥ 1`, its zero forced prefix and threshold also simplify exactly:
after a test, the just-tested job is selected for immediate processing iff
its processing time is at most one.  Thus the only mathematical step left
between this operational transcript and the four-class Zero-prefix game is
the ordered exchange/endpoint reduction for the deferred suffix.
-/

namespace SchedulingPaper.Online

noncomputable section

/-! ## Fixed answers are preserved by arbitrary executions -/

/-- Every test answer in a public transcript is the value of the same label
in the underlying fixed processing vector. -/
def Transcript.MatchesFixed
    (processingTime : Label n → ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults →
    p = processingTime job

@[simp] theorem Transcript.matchesFixed_nil
    (processingTime : Label n → ℝ) :
    Transcript.MatchesFixed processingTime [] := by
  simp [Transcript.MatchesFixed]

theorem Transcript.MatchesFixed.append_testResult
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (hmatch : transcript.MatchesFixed processingTime)
    (job : Label n) :
    (transcript ++
      [Observation.testResult job (processingTime job)]).MatchesFixed
        processingTime := by
  intro other p hmem
  rw [Transcript.testResults_append] at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact hmatch other p hold
  · simp only [Transcript.testResults_testResult_cons,
      Transcript.testResults_nil, List.mem_singleton] at hnew
    cases hnew
    rfl

theorem Transcript.MatchesFixed.append_processed
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (hmatch : transcript.MatchesFixed processingTime)
    (job : Label n) :
    (transcript ++ [Observation.processed job]).MatchesFixed
      processingTime := by
  intro other p hmem
  rw [Transcript.testResults_append] at hmem
  exact hmatch other p (by simpa using hmem)

theorem Transcript.MatchesFixed.append_rawCompleted
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (hmatch : transcript.MatchesFixed processingTime)
    (job : Label n) :
    (transcript ++ [Observation.rawCompleted job]).MatchesFixed
      processingTime := by
  intro other p hmem
  rw [Transcript.testResults_append] at hmem
  exact hmatch other p (by simpa using hmem)

/-- A single successful step against a fixed oracle preserves agreement of
all published test answers with the fixed vector. -/
theorem Config.step_fixedOracle_matchesFixed
    (cap : Cap) (processingTime : Label n → ℝ)
    {config next : Config n} {action : Action n}
    (hmatch : config.transcript.MatchesFixed processingTime)
    (hstep :
      config.step cap (fixedOracle processingTime) action = some next) :
    next.transcript.MatchesFixed processingTime := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob, fixedOracle] at hstep
          subst next
          exact hmatch.append_testResult job
      | tested old =>
          simp [Config.step, hjob] at hstep
      | done =>
          simp [Config.step, hjob] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
      | tested p =>
          simp [Config.step, hjob] at hstep
          subst next
          exact hmatch.append_processed job
      | done =>
          simp [Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [Config.step, hjob] at hstep
              subst next
              exact hmatch.append_rawCompleted job
          | tested p =>
              simp [Config.step, hjob] at hstep
          | done =>
              simp [Config.step, hjob] at hstep

/-- Agreement with a fixed vector holds after any fuelled run, independently
of the strategy. -/
theorem runFuel_fixedOracle_matchesFixed
    (cap : Cap) (processingTime : Label n → ℝ)
    (strategy : Strategy n) (fuel : ℕ) (config : Config n)
    (hmatch : config.transcript.MatchesFixed processingTime) :
    (runFuel cap (fixedOracle processingTime) strategy fuel config).config
      |>.transcript.MatchesFixed processingTime := by
  induction fuel generalizing config with
  | zero =>
      simpa [runFuel] using hmatch
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simpa [haction] using hmatch
      | some action =>
          simp only
          cases hstep :
              config.step cap (fixedOracle processingTime) action with
          | none =>
              simpa [hstep] using hmatch
          | some next =>
              simp only
              exact ih next
                (Config.step_fixedOracle_matchesFixed
                  cap processingTime hmatch hstep)

theorem run_fixedOracle_matchesFixed
    (cap : Cap) (processingTime : Label n → ℝ)
    (strategy : Strategy n) (fuel : ℕ) :
    (run cap (fixedOracle processingTime) strategy fuel).config.transcript
      |>.MatchesFixed processingTime := by
  unfold run
  exact runFuel_fixedOracle_matchesFixed
    cap processingTime strategy fuel (Config.initial n)
      (Transcript.matchesFixed_nil processingTime)

/-! ## The completed ForcedPrefixUTE run retains its invariant -/

/-- Strengthening of `run_forcedPrefixUTEStrategy_completed`: the final
configuration also retains the full test/process invariant. -/
theorem run_forcedPrefixUTEStrategy_completed_invariant
    (n : ℕ) (u b : ℝ) (cap : Cap) (oracle : Oracle n) :
    let result :=
      run cap oracle (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run
  rw [forcedPrefixUTEStrategy_eq_testProcessStrategy]
  have hrun :=
    runFuel_completedNormally_of_workRank cap oracle
      (testProcessStrategy
        (fun transcript =>
          transcript.forcedPrefixPendingImmediate? n
            (forcedPrefixCount n b) (uteThreshold u)))
      Config.TestProcessInvariant
      (fun _ hgood hzero =>
        testProcessStrategy_stop_of_zero
          (forcedPrefixPendingImmediate_selectsLastTest n
            (forcedPrefixCount n b) (uteThreshold u))
          hgood hzero)
      (fun _ hgood hpos =>
        testProcessStrategy_progress cap oracle
          (forcedPrefixPendingImmediate_selectsLastTest n
            (forcedPrefixCount n b) (uteThreshold u))
          hgood hpos)
      (Config.initial n) (Config.initial_testProcessInvariant n) 0
  rw [Config.initial_remainingWork] at hrun
  simpa using hrun

/-- A completed configuration satisfying the test/process invariant has
tested exactly all labels. -/
theorem Config.TestProcessInvariant.zeroPrefix_testResults_length_eq
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hdone : ∀ job, config.jobs job = .done) :
    config.transcript.testResults.length = n := by
  apply Nat.le_antisymm hgood.testBound
  by_contra hnot
  have hlt : config.transcript.testResults.length < n := by omega
  let job : Label n :=
    ⟨config.transcript.testResults.length, hlt⟩
  have huntouched : config.jobs job = .untouched :=
    hgood.labelAtTestCount_untouched rfl
  rw [hdone job] at huntouched
  contradiction

/-- Consequently the concrete ForcedPrefixUTE run contains exactly `n`
test observations. -/
theorem run_forcedPrefixUTEStrategy_testResults_length
    (n : ℕ) (u b : ℝ) (cap : Cap) (oracle : Oracle n) :
    let result :=
      run cap oracle (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    result.config.transcript.testResults.length = n := by
  dsimp only
  have hrun :=
    run_forcedPrefixUTEStrategy_completed_invariant
      n u b cap oracle
  exact hrun.2.1.zeroPrefix_testResults_length_eq hrun.2.2

/-- Every label occurs among those `n` tests. -/
theorem Config.TestProcessInvariant.exists_testResult
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hall : config.transcript.testResults.length = n)
    (job : Label n) :
    ∃ p, (job, p) ∈ config.transcript.testResults := by
  have hval :
      job.val ∈
        config.transcript.testResults.map
          (fun result => result.1.val) := by
    rw [hgood.testOrder, hall]
    simp
  rcases List.mem_map.mp hval with
    ⟨⟨label, p⟩, hresult, hvalue⟩
  have hjob : label = job := Fin.ext hvalue
  subst label
  exact ⟨p, hresult⟩

/-- On a fixed input, the exact pair `(job, processingTime job)` occurs in
the final test-result list for every label. -/
theorem run_forcedPrefixUTEStrategy_has_fixed_testResult
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) (job : Label n) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    (job, processingTime job) ∈ result.config.transcript.testResults := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n u b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_completed_invariant
      n u b cap (fixedOracle processingTime)
  have hall :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.zeroPrefix_testResults_length_eq hrun.2.2
  obtain ⟨p, hp⟩ :=
    hrun.2.1.exists_testResult hall job
  have hmatch :
      result.config.transcript.MatchesFixed processingTime := by
    exact run_fixedOracle_matchesFixed cap processingTime
      (forcedPrefixUTEStrategy n u b) (2 * n + 1)
  have hpEq : p = processingTime job :=
    hmatch job p hp
  simpa [hpEq] using hp

/-! ## Exact zero-prefix threshold rule -/

@[simp] theorem forcedPrefixCount_zero (n : ℕ) :
    forcedPrefixCount n 0 = 0 := by
  simp [forcedPrefixCount]

theorem zeroPrefix_uteThreshold_add_one_eq_one
    {s : ℝ} (hs : 1 ≤ s) :
    uteThreshold (s + 1) = 1 := by
  simp [uteThreshold, min_eq_left hs]

/-- With prefix parameter zero and `s ≥ 1`, the pending selector is exactly
the test-result threshold `p ≤ 1`. -/
theorem forcedPrefixPendingImmediate_zero
    (n : ℕ) {s : ℝ} (hs : 1 ≤ s)
    (transcript : Transcript n) :
    transcript.forcedPrefixPendingImmediate? n
        (forcedPrefixCount n 0) (uteThreshold (s + 1)) =
      match transcript.getLast? with
      | some (Observation.testResult job p) =>
          if p ≤ 1 then some job else none
      | some (Observation.processed _)
      | some (Observation.rawCompleted _)
      | none => none := by
  rw [forcedPrefixCount_zero, zeroPrefix_uteThreshold_add_one_eq_one hs]
  unfold Transcript.forcedPrefixPendingImmediate?
  cases hlast : transcript.getLast? with
  | none =>
      simp
  | some observation =>
      cases observation <;> simp

/-- Immediately after a low test, the concrete Zero-prefix strategy requests
processing of precisely the just-tested job. -/
theorem forcedPrefixUTEStrategy_zero_after_low_test
    (n : ℕ) {s p : ℝ} (hs : 1 ≤ s) (hp : p ≤ 1)
    (transcript : Transcript n) (job : Label n) :
    forcedPrefixUTEStrategy n (s + 1) 0
        (transcript ++ [Observation.testResult job p]) =
      some (Action.process job) := by
  unfold forcedPrefixUTEStrategy
  dsimp only
  rw [forcedPrefixCount_zero, zeroPrefix_uteThreshold_add_one_eq_one hs]
  simp [Transcript.forcedPrefixPendingImmediate?, hp]

/-- Immediately after a high test, the pending-immediate selector is empty;
the strategy therefore continues the test phase (or enters its
shortest-remaining suffix if all labels were tested). -/
theorem forcedPrefixPendingImmediate_zero_after_high_test
    (n : ℕ) {s p : ℝ} (hs : 1 ≤ s) (hp : 1 < p)
    (transcript : Transcript n) (job : Label n) :
    Transcript.forcedPrefixPendingImmediate? n
      (forcedPrefixCount n 0) (uteThreshold (s + 1))
      (transcript ++ [Observation.testResult job p]) = none := by
  rw [forcedPrefixCount_zero, zeroPrefix_uteThreshold_add_one_eq_one hs]
  simp [Transcript.forcedPrefixPendingImmediate?,
    not_le.mpr hp]

/-- Once all tests are present and no immediate processing is pending, the
concrete Zero-prefix strategy is definitionally the shortest-remaining
selector. -/
theorem forcedPrefixUTEStrategy_zero_after_all_tests
    (n : ℕ) (s : ℝ) (transcript : Transcript n)
    (hall : transcript.testResults.length = n)
    (hpending :
      transcript.forcedPrefixPendingImmediate? n
        (forcedPrefixCount n 0) (uteThreshold (s + 1)) = none) :
    forcedPrefixUTEStrategy n (s + 1) 0 transcript =
      match transcript.shortestRemaining? with
      | some job => some (Action.process job)
      | none => none := by
  simp only [forcedPrefixUTEStrategy, hpending]
  split
  · omega
  · rfl

end

end SchedulingPaper.Online
