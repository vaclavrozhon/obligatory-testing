import SchedulingPaper.ForcedPrefixUTE
import Mathlib.Tactic

/-!
# Finite termination of the test/process strategies

The three threshold strategies share one operational skeleton: every job is
tested once in label order and is then processed at most once.  The work rank
assigns weight two to an untouched job, one to a tested job, and zero to a
completed job.  Every successful action lowers this rank by one, so the
initial rank `2n` plus one final stopping query proves the exact `2n+1` fuel
bound.

The abstract work-rank theorem is independent of the particular strategies.
The transcript invariant below supplies its hypotheses for AdaptiveThreshold,
its parameterized variant, and ForcedPrefixUTE.
-/

namespace SchedulingPaper.Online

noncomputable section

def jobWork : JobState → ℕ
  | .untouched => 2
  | .tested _ => 1
  | .done => 0

def Config.remainingWork (config : Config n) : ℕ :=
  ∑ job : Label n, jobWork (config.jobs job)

theorem remainingWork_update_test
    (jobs : Label n → JobState) (job : Label n) (p : ℝ)
    (hjob : jobs job = .untouched) :
    (∑ i : Label n, jobWork ((Function.update jobs job (.tested p)) i)) + 1 =
      ∑ i : Label n, jobWork (jobs i) := by
  classical
  have hsum :
      (∑ i ∈ Finset.univ.erase job,
          jobWork ((Function.update jobs job (.tested p)) i)) =
        ∑ i ∈ Finset.univ.erase job, jobWork (jobs i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [Function.update, hi.1]
  calc
    (∑ i : Label n,
          jobWork ((Function.update jobs job (.tested p)) i)) + 1 =
        ((∑ i ∈ Finset.univ.erase job,
          jobWork ((Function.update jobs job (.tested p)) i)) +
          jobWork ((Function.update jobs job (.tested p)) job)) + 1 := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ job)]
    _ = ((∑ i ∈ Finset.univ.erase job, jobWork (jobs i)) +
          jobWork (jobs job)) := by
          rw [hsum]
          simp [Function.update, jobWork, hjob]
    _ = ∑ i : Label n, jobWork (jobs i) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ job)

theorem remainingWork_update_process
    (jobs : Label n → JobState) (job : Label n) (p : ℝ)
    (hjob : jobs job = .tested p) :
    (∑ i : Label n, jobWork ((Function.update jobs job .done) i)) + 1 =
      ∑ i : Label n, jobWork (jobs i) := by
  classical
  have hsum :
      (∑ i ∈ Finset.univ.erase job,
          jobWork ((Function.update jobs job .done) i)) =
        ∑ i ∈ Finset.univ.erase job, jobWork (jobs i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [Function.update, hi.1]
  calc
    (∑ i : Label n,
          jobWork ((Function.update jobs job .done) i)) + 1 =
        ((∑ i ∈ Finset.univ.erase job,
            jobWork ((Function.update jobs job .done) i)) +
          jobWork ((Function.update jobs job .done) job)) + 1 := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ job)]
    _ = ((∑ i ∈ Finset.univ.erase job, jobWork (jobs i)) +
          jobWork (jobs job)) := by
          rw [hsum]
          simp [Function.update, jobWork, hjob]
    _ = ∑ i : Label n, jobWork (jobs i) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ job)

theorem Config.remainingWork_eq_zero_iff (config : Config n) :
    config.remainingWork = 0 ↔ ∀ job, config.jobs job = .done := by
  constructor
  · intro hzero job
    have hle :
        jobWork (config.jobs job) ≤ config.remainingWork := by
      unfold Config.remainingWork
      exact Finset.single_le_sum
        (f := fun j : Label n => jobWork (config.jobs j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ job)
    have hw : jobWork (config.jobs job) = 0 := by omega
    cases hjob : config.jobs job <;>
      simp [jobWork, hjob] at hw ⊢
  · intro hdone
    unfold Config.remainingWork
    apply Finset.sum_eq_zero
    intro job _
    simp [hdone job, jobWork]

/-- The transcript and machine state produced by a test/process policy
agree, and tests have occurred in label order. -/
structure Config.TestProcessInvariant (config : Config n) : Prop where
  testOrder :
    config.transcript.testResults.map (fun result => result.1.val) =
      List.range config.transcript.testResults.length
  testBound : config.transcript.testResults.length ≤ n
  untouched_iff :
    ∀ job, config.jobs job = .untouched ↔
      job ∉ config.transcript.testResults.map Prod.fst
  done_iff :
    ∀ job, config.jobs job = .done ↔
      job ∈ config.transcript.processedLabels
  tested_iff :
    ∀ job p, config.jobs job = .tested p ↔
      (job, p) ∈ config.transcript.testResults ∧
        job ∉ config.transcript.processedLabels
  lastTest :
    ∀ job p, config.transcript.getLast? = some (.testResult job p) →
      config.jobs job = .tested p

theorem Config.initial_testProcessInvariant (n : ℕ) :
    (Config.initial n).TestProcessInvariant := by
  constructor <;> simp [Config.initial, Transcript.processedLabels]

@[simp] theorem Transcript.testResults_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).testResults =
      transcript.testResults ++ [(job, p)] := by
  simp

@[simp] theorem Transcript.processedLabels_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).processedLabels =
      transcript.processedLabels := by
  simp [Transcript.processedLabels]

@[simp] theorem Transcript.processedLabels_append_processed
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.processed job]).processedLabels =
      transcript.processedLabels ++ [job] := by
  simp [Transcript.processedLabels]

theorem Config.TestProcessInvariant.labelAtTestCount_untouched
    {config : Config n} (hgood : config.TestProcessInvariant)
    {job : Label n}
    (hval : job.val = config.transcript.testResults.length) :
    config.jobs job = .untouched := by
  rw [hgood.untouched_iff]
  intro hmem
  have hval :
      config.transcript.testResults.length ∈
        config.transcript.testResults.map (fun result => result.1.val) := by
    rcases List.mem_map.mp hmem with ⟨result, hresult, heq⟩
    exact List.mem_map.mpr
      ⟨result, hresult, by simpa [heq] using hval⟩
  rw [hgood.testOrder] at hval
  simp at hval

theorem Config.TestProcessInvariant.afterTest
    {config : Config n} (hgood : config.TestProcessInvariant)
    (job : Label n)
    (hval : job.val = config.transcript.testResults.length) (p : ℝ) :
    ({
      jobs := Function.update config.jobs job (.tested p)
      transcript := config.transcript ++ [.testResult job p]
    } : Config n).TestProcessInvariant := by
  have hjob : config.jobs job = .untouched := by
    exact hgood.labelAtTestCount_untouched hval
  have hnotTested :
      job ∉ config.transcript.testResults.map Prod.fst := by
    exact (hgood.untouched_iff job).mp hjob
  have hnoTestPair :
      ∀ q, (job, q) ∉ config.transcript.testResults := by
    intro q hmem
    exact hnotTested (List.mem_map.mpr ⟨(job, q), hmem, rfl⟩)
  have hnotProcessed :
      job ∉ config.transcript.processedLabels := by
    intro hmem
    have hdone := (hgood.done_iff job).mpr hmem
    rw [hjob] at hdone
    contradiction
  constructor
  · simp only [Transcript.testResults_append_testResult, List.map_append,
      List.map_singleton, List.length_append, List.length_singleton]
    rw [hval, hgood.testOrder]
    simpa [Nat.add_comm] using
      (List.range_succ
        (n := config.transcript.testResults.length)).symm
  · simp only [Transcript.testResults_append_testResult,
      List.length_append, List.length_singleton]
    omega
  · intro other
    rw [Transcript.testResults_append_testResult, List.map_append,
      List.map_singleton]
    by_cases heq : other = job
    · subst other
      simp [Function.update, hnotTested]
    · simp [Function.update, heq, hgood.untouched_iff other]
  · intro other
    rw [Transcript.processedLabels_append_testResult]
    by_cases heq : other = job
    · subst other
      simp [Function.update, hnotProcessed]
    · simp [Function.update, heq, Transcript.processedLabels,
        hgood.done_iff other]
  · intro other q
    rw [Transcript.testResults_append_testResult,
      Transcript.processedLabels_append_testResult]
    by_cases heq : other = job
    · subst other
      simp [Function.update, hnoTestPair q, hnotProcessed]
      constructor <;> intro h <;> exact h.symm
    · simp [Function.update, heq,
        hgood.tested_iff other q]
  · intro other q hlast
    have heq : job = other ∧ p = q := by
      simpa using hlast
    rcases heq with ⟨rfl, rfl⟩
    simp [Function.update]

theorem Config.TestProcessInvariant.afterProcess
    {config : Config n} (hgood : config.TestProcessInvariant)
    (job : Label n) (p : ℝ) (hjob : config.jobs job = .tested p) :
    ({
      jobs := Function.update config.jobs job .done
      transcript := config.transcript ++ [.processed job]
    } : Config n).TestProcessInvariant := by
  have htested :
      (job, p) ∈ config.transcript.testResults := by
    exact (hgood.tested_iff job p).mp hjob |>.1
  have hnotProcessed :
      job ∉ config.transcript.processedLabels := by
    exact (hgood.tested_iff job p).mp hjob |>.2
  have hlabelTested :
      job ∈ config.transcript.testResults.map Prod.fst :=
    List.mem_map.mpr ⟨(job, p), htested, rfl⟩
  constructor
  · simpa using hgood.testOrder
  · simpa using hgood.testBound
  · intro other
    by_cases heq : other = job
    · subst other
      simp [Function.update, hlabelTested]
    · simp [Function.update, heq, hgood.untouched_iff other]
  · intro other
    rw [Transcript.processedLabels_append_processed]
    by_cases heq : other = job
    · subst other
      simp [Function.update]
    · simp [Function.update, heq, hgood.done_iff other]
  · intro other q
    rw [Transcript.processedLabels_append_processed]
    by_cases heq : other = job
    · subst other
      simp [Function.update]
    · simp [Function.update, heq, hgood.tested_iff other q]
  · intro other q hlast
    simp at hlast

private theorem shortestFold_mem
    (best : Label n × ℝ) (rest : List (Label n × ℝ)) :
    rest.foldl
        (fun best candidate =>
          if candidate.2 < best.2 then candidate else best)
        best ∈ best :: rest := by
  induction rest generalizing best with
  | nil => simp
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hlt : candidate.2 < best.2
      · have hmem := ih candidate
        simp only [if_pos hlt] at hmem ⊢
        exact List.mem_cons_of_mem best hmem
      · have hmem := ih best
        simp only [if_neg hlt] at hmem ⊢
        rw [List.mem_cons] at hmem ⊢
        exact hmem.imp id (fun hrest =>
          List.mem_cons_of_mem candidate hrest)

theorem shortestResult?_eq_none_iff
    (results : List (Label n × ℝ)) :
    shortestResult? results = none ↔ results = [] := by
  cases results <;> simp [shortestResult?]

theorem shortestResult?_mem
    {results : List (Label n × ℝ)} {result : Label n × ℝ}
    (hresult : shortestResult? results = some result) :
    result ∈ results := by
  cases results with
  | nil => simp [shortestResult?] at hresult
  | cons best rest =>
      simp only [shortestResult?, Option.some.injEq] at hresult
      subst result
      exact shortestFold_mem best rest

theorem Config.TestProcessInvariant.shortestRemaining_tested
    {config : Config n} (hgood : config.TestProcessInvariant)
    {job : Label n}
    (hshort : config.transcript.shortestRemaining? = some job) :
    ∃ p, config.jobs job = .tested p := by
  unfold Transcript.shortestRemaining? at hshort
  cases hresult :
      shortestResult? config.transcript.remainingTestResults with
  | none =>
      simp [hresult] at hshort
  | some result =>
      have hfst : result.1 = job := by
        simpa [hresult] using hshort
      have hmem :
          result ∈ config.transcript.remainingTestResults :=
        shortestResult?_mem hresult
      unfold Transcript.remainingTestResults at hmem
      have hparts := List.mem_filter.mp hmem
      subst job
      refine ⟨result.2, (hgood.tested_iff result.1 result.2).mpr ?_⟩
      simpa using hparts

theorem Config.TestProcessInvariant.done_of_allTests_of_noRemaining
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hall : config.transcript.testResults.length = n)
    (hnone : config.transcript.shortestRemaining? = none) :
    ∀ job, config.jobs job = .done := by
  have hshortest :
      shortestResult? config.transcript.remainingTestResults = none := by
    unfold Transcript.shortestRemaining? at hnone
    exact Option.map_eq_none_iff.mp hnone
  have hremaining :
      config.transcript.remainingTestResults = [] :=
    (shortestResult?_eq_none_iff _).mp hshortest
  intro job
  apply (hgood.done_iff job).mpr
  have hval :
      job.val ∈
        config.transcript.testResults.map (fun result => result.1.val) := by
    rw [hgood.testOrder, hall]
    simp
  rcases List.mem_map.mp hval with ⟨result, hresult, hresultVal⟩
  have hresultJob : result.1 = job :=
    Fin.ext hresultVal
  subst job
  by_contra hnotProcessed
  have hmemRemaining :
      result ∈ config.transcript.remainingTestResults := by
    unfold Transcript.remainingTestResults
    exact List.mem_filter.mpr (by simpa using And.intro hresult hnotProcessed)
  rw [hremaining] at hmemRemaining
  simp at hmemRemaining

/-- A selector may request immediate processing only for the final,
just-revealed test result. -/
def SelectsLastTest
    (pending : Transcript n → Option (Label n)) : Prop :=
  ∀ transcript job, pending transcript = some job →
    ∃ p, transcript.getLast? = some (.testResult job p)

/-- Common control skeleton of AdaptiveThreshold and ForcedPrefixUTE. -/
def testProcessStrategy
    (pending : Transcript n → Option (Label n)) : Strategy n :=
  fun transcript =>
    match pending transcript with
    | some job => some (.process job)
    | none =>
        let tested := transcript.testResults.length
        if h : tested < n then
          some (.test ⟨tested, h⟩)
        else
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none => none

def WorkStep
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (Good : Config n → Prop) (config : Config n) : Prop :=
  ∃ action next,
    strategy config.transcript = some action ∧
    config.step cap oracle action = some next ∧
    Good next ∧ next.remainingWork + 1 = config.remainingWork

/-- Abstract rank argument.  It applies to any strategy and any invariant:
zero work must stop, while positive work must perform one enabled action
which decreases the `2/1/0` work rank by exactly one. -/
theorem runFuel_completedNormally_of_workRank
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (Good : Config n → Prop)
    (hstop :
      ∀ config, Good config → config.remainingWork = 0 →
        strategy config.transcript = none)
    (hprogress :
      ∀ config, Good config → 0 < config.remainingWork →
        WorkStep cap oracle strategy Good config)
    (config : Config n) (hgood : Good config) (extra : ℕ) :
    let result :=
      runFuel cap oracle strategy
        (config.remainingWork + 1 + extra) config
    result.reason = .strategyStopped ∧
      Good result.config ∧
      ∀ job, result.config.jobs job = .done := by
  induction hwork : config.remainingWork generalizing config extra with
  | zero =>
      have hnone := hstop config hgood hwork
      rw [show 0 + 1 + extra = extra + 1 by omega]
      simp only [runFuel]
      rw [hnone]
      exact ⟨rfl, hgood,
        (Config.remainingWork_eq_zero_iff config).mp hwork⟩
  | succ work ih =>
      obtain ⟨action, next, haction, hstep, hnextGood, hdrop⟩ :=
        hprogress config hgood (by omega)
      have hnextWork : next.remainingWork = work := by omega
      rw [show (work + 1) + 1 + extra =
          (work + 1 + extra) + 1 by omega]
      simp only [runFuel]
      rw [haction]
      simp only
      rw [hstep]
      exact ih next hnextGood extra hnextWork

theorem Config.initial_remainingWork (n : ℕ) :
    (Config.initial n).remainingWork = 2 * n := by
  simp [Config.remainingWork, Config.initial, jobWork]
  omega

theorem testProcessStrategy_stop_of_zero
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending)
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hzero : config.remainingWork = 0) :
    testProcessStrategy pending config.transcript = none := by
  have hdone :
      ∀ job, config.jobs job = .done :=
    (Config.remainingWork_eq_zero_iff config).mp hzero
  unfold testProcessStrategy
  cases hp : pending config.transcript with
  | some job =>
      obtain ⟨p, hlast⟩ := hpending config.transcript job hp
      have htested := hgood.lastTest job p hlast
      rw [hdone job] at htested
      contradiction
  | none =>
      simp only
      split
      next hlt =>
        let job : Label n :=
          ⟨config.transcript.testResults.length, hlt⟩
        have huntouched :
            config.jobs job = .untouched :=
          hgood.labelAtTestCount_untouched rfl
        rw [hdone job] at huntouched
        contradiction
      next hnotlt =>
        split
        next job hshort =>
          obtain ⟨p, htested⟩ :=
            hgood.shortestRemaining_tested hshort
          rw [hdone job] at htested
          contradiction
        next => rfl

theorem testProcessStrategy_progress
    (cap : Cap) (oracle : Oracle n)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending)
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hpos : 0 < config.remainingWork) :
    WorkStep cap oracle (testProcessStrategy pending)
      Config.TestProcessInvariant config := by
  unfold WorkStep
  unfold testProcessStrategy
  cases hp : pending config.transcript with
  | some job =>
      obtain ⟨p, hlast⟩ := hpending config.transcript job hp
      have hjob : config.jobs job = .tested p :=
        hgood.lastTest job p hlast
      let next : Config n := {
        jobs := Function.update config.jobs job .done
        transcript := config.transcript ++ [.processed job]
      }
      refine ⟨.process job, next, by simp, ?_, ?_, ?_⟩
      · simp [Config.step, hjob, next]
      · exact hgood.afterProcess job p hjob
      · exact remainingWork_update_process config.jobs job p hjob
  | none =>
      simp only
      split
      next hlt =>
        let job : Label n :=
          ⟨config.transcript.testResults.length, hlt⟩
        let p := oracle config.transcript job
        have hjob : config.jobs job = .untouched :=
          hgood.labelAtTestCount_untouched rfl
        let next : Config n := {
          jobs := Function.update config.jobs job (.tested p)
          transcript := config.transcript ++ [.testResult job p]
        }
        refine ⟨.test job, next, rfl, ?_, ?_, ?_⟩
        · simp [Config.step, hjob, next, p]
        · exact hgood.afterTest job rfl p
        · exact remainingWork_update_test config.jobs job p hjob
      next hnotlt =>
        have hall :
            config.transcript.testResults.length = n := by
          have hbound := hgood.testBound
          omega
        split
        next job hshort =>
          obtain ⟨p, hjob⟩ :=
            hgood.shortestRemaining_tested hshort
          let next : Config n := {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.processed job]
          }
          refine ⟨.process job, next, rfl, ?_, ?_, ?_⟩
          · simp [Config.step, hjob, next]
          · exact hgood.afterProcess job p hjob
          · exact remainingWork_update_process config.jobs job p hjob
        next hnone =>
          have hdone :=
            hgood.done_of_allTests_of_noRemaining hall hnone
          have := (Config.remainingWork_eq_zero_iff config).mpr hdone
          omega

theorem runFuel_testProcessStrategy_completed
    (cap : Cap) (oracle : Oracle n)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending) (extra : ℕ) :
    let result :=
      runFuel cap oracle (testProcessStrategy pending)
        (2 * n + 1 + extra) (Config.initial n)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  have hrun :=
    runFuel_completedNormally_of_workRank cap oracle
      (testProcessStrategy pending) Config.TestProcessInvariant
      (fun _ hgood hzero =>
        testProcessStrategy_stop_of_zero hpending hgood hzero)
      (fun _ hgood hpos =>
        testProcessStrategy_progress cap oracle hpending hgood hpos)
      (Config.initial n) (Config.initial_testProcessInvariant n) extra
  rw [Config.initial_remainingWork] at hrun
  exact ⟨hrun.1, hrun.2.2⟩

theorem parameterizedPendingImmediate_selectsLastTest
    (n : ℕ) (c : ℝ) :
    SelectsLastTest
      (fun transcript =>
        transcript.parameterizedPendingImmediate? n c) := by
  intro transcript job hpending
  unfold Transcript.parameterizedPendingImmediate? at hpending
  simp only at hpending
  cases hlast : transcript.getLast? with
  | none => simp [hlast] at hpending
  | some observation =>
      cases observation with
      | processed processedJob => simp [hlast] at hpending
      | rawCompleted rawJob => simp [hlast] at hpending
      | testResult testedJob p =>
          rw [hlast] at hpending
          simp only at hpending
          split at hpending
          next =>
            simp only [Option.some.injEq] at hpending
            subst job
            exact ⟨p, rfl⟩
          next => simp_all

theorem pendingImmediate_selectsLastTest
    (n : ℕ) :
    SelectsLastTest
      (fun transcript => transcript.pendingImmediate? n) := by
  intro transcript job hpending
  unfold Transcript.pendingImmediate? at hpending
  simp only at hpending
  cases hlast : transcript.getLast? with
  | none => simp [hlast] at hpending
  | some observation =>
      cases observation with
      | processed processedJob => simp [hlast] at hpending
      | rawCompleted rawJob => simp [hlast] at hpending
      | testResult testedJob p =>
          rw [hlast] at hpending
          simp only at hpending
          split at hpending
          next =>
            simp only [Option.some.injEq] at hpending
            subst job
            exact ⟨p, rfl⟩
          next => simp_all

theorem forcedPrefixPendingImmediate_selectsLastTest
    (n k : ℕ) (threshold : ℝ) :
    SelectsLastTest
      (fun transcript =>
        transcript.forcedPrefixPendingImmediate? n k threshold) := by
  intro transcript job hpending
  unfold Transcript.forcedPrefixPendingImmediate? at hpending
  simp only at hpending
  cases hlast : transcript.getLast? with
  | none => simp [hlast] at hpending
  | some observation =>
      cases observation with
      | processed processedJob => simp [hlast] at hpending
      | rawCompleted rawJob => simp [hlast] at hpending
      | testResult testedJob p =>
          rw [hlast] at hpending
          simp only at hpending
          split at hpending
          next =>
            simp only [Option.some.injEq] at hpending
            subst job
            exact ⟨p, rfl⟩
          next => simp_all

theorem parameterizedAdaptiveThresholdStrategy_eq_testProcessStrategy
    (n : ℕ) (c : ℝ) :
    parameterizedAdaptiveThresholdStrategy n c =
      testProcessStrategy
        (fun transcript =>
          transcript.parameterizedPendingImmediate? n c) := rfl

theorem adaptiveThresholdStrategy_eq_testProcessStrategy
    (n : ℕ) :
    adaptiveThresholdStrategy n =
      testProcessStrategy
        (fun transcript => transcript.pendingImmediate? n) := rfl

theorem forcedPrefixUTEStrategy_eq_testProcessStrategy
    (n : ℕ) (u b : ℝ) :
    forcedPrefixUTEStrategy n u b =
      testProcessStrategy
        (fun transcript =>
          transcript.forcedPrefixPendingImmediate? n
            (forcedPrefixCount n b) (uteThreshold u)) := rfl

/-- The parameterized adaptive strategy has completed every job and stopped
normally after the common `2n+1` analysis fuel. -/
theorem run_parameterizedAdaptiveThresholdStrategy_completed
    (n : ℕ) (c : ℝ) (cap : Cap) (oracle : Oracle n) :
    let result :=
      run cap oracle (parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run
  rw [parameterizedAdaptiveThresholdStrategy_eq_testProcessStrategy]
  simpa using
    runFuel_testProcessStrategy_completed cap oracle
      (parameterizedPendingImmediate_selectsLastTest n c) 0

/-- The obligatory-endpoint AdaptiveThreshold strategy obeys the same
`2n+1` completion bound. -/
theorem run_adaptiveThresholdStrategy_completed
    (n : ℕ) (cap : Cap) (oracle : Oracle n) :
    let result :=
      run cap oracle (adaptiveThresholdStrategy n) (2 * n + 1)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run
  rw [adaptiveThresholdStrategy_eq_testProcessStrategy]
  simpa using
    runFuel_testProcessStrategy_completed cap oracle
      (pendingImmediate_selectsLastTest n) 0

/-- `ForcedPrefixUTE` has completed every job and stopped normally after
the common `2n+1` analysis fuel.  No restrictions on `u` or `b` are needed
for this operational fact. -/
theorem run_forcedPrefixUTEStrategy_completed
    (n : ℕ) (u b : ℝ) (cap : Cap) (oracle : Oracle n) :
    let result :=
      run cap oracle (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run
  rw [forcedPrefixUTEStrategy_eq_testProcessStrategy]
  simpa using
    runFuel_testProcessStrategy_completed cap oracle
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n b) (uteThreshold u)) 0

end

end SchedulingPaper.Online
