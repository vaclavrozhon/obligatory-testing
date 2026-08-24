import SchedulingPaper.RevealingOptimizationInstanceLearning
import SchedulingPaper.RandomizedOptionalStrategy
import SchedulingPaper.HiddenStoppingGlobalExchange
import SchedulingPaper.FixedTestProcessCompletion
import SchedulingPaper.LowBaseline
import Mathlib.Tactic

/-!
# Operational quota templates for revealing optimization

This is the literal finite policy used by the instance-optimal upper bound.
It tests a canonical quota, immediately processes selected low outcomes,
drains every other tested job by SPT, and finally runs untouched jobs raw.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace QuotaStrategy

open Online

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A safe version of the immediate selector: membership in the remaining
tested stock is checked from the public transcript itself. -/
def safeLastLowPending? (low : ℝ → Bool)
    (transcript : Online.Transcript n) : Option (Online.Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) =>
      if low p && decide (job ∈ transcript.remainingTestResults.map Prod.fst)
        then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- Canonical revealing-optimization template with an integral test quota. -/
def quotaStrategy (n q : ℕ) (low : ℝ → Bool) : Online.Strategy n :=
  fun transcript =>
    match safeLastLowPending? low transcript with
    | some job => some (.process job)
    | none =>
        if transcript.testResults.length < q then
          (RandomizedOptional.nextCanonicalTouch? n transcript).map
            Online.Action.test
        else
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none =>
              (RandomizedOptional.nextCanonicalTouch? n transcript).map
                Online.Action.raw

/-- Private random placement of the virtual canonical labels. -/
def randomizedQuotaStrategy (n q : ℕ) (low : ℝ → Bool) :
    Equiv.Perm (Fin n) → Online.Strategy n :=
  fun order => (quotaStrategy n q low).relabel order

/-! ## Reachability invariant -/

structure Config.Invariant
    (processing : Online.Label n → ℝ) (q : ℕ)
    (config : Online.Config n) : Prop where
  started : config.StartedHistoryInvariant
  process : config.ProcessHistoryInvariant
  testsMatch : config.transcript.TestsMatch processing
  touchOrder : config.transcript.startedLabels.map Fin.val =
    List.range config.transcript.startedLabels.length
  testBound : config.transcript.testResults.length ≤ q
  beforeQuota : config.transcript.testResults.length < q →
    config.transcript.startedLabels.length =
      config.transcript.testResults.length
  completion : config.FixedCompletionInvariant processing

theorem Config.initial_invariant
    (processing : Online.Label n → ℝ) (q : ℕ) :
    Invariant processing q (Online.Config.initial n) := by
  constructor <;>
    simp [Online.Config.initial, Online.Transcript.startedLabels,
      Online.Transcript.TestsMatch]
  · exact Online.Config.initial_startedHistoryInvariant n
  · exact Online.Config.initial_processHistoryInvariant n
  · exact Online.Config.initial_fixedCompletionInvariant processing

theorem Config.Invariant.touchBound
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config) :
    config.transcript.startedLabels.length ≤ n := by
  calc
    config.transcript.startedLabels.length =
        config.transcript.startedLabels.toFinset.card :=
      (List.toFinset_card_of_nodup hgood.started.nodup).symm
    _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

theorem Config.Invariant.tested_value_eq_fixed
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n} {p : ℝ}
    (hstate : config.jobs job = .tested p) :
    p = processing job := by
  exact hgood.testsMatch job p
    (hgood.process.testedRecorded job p hstate)

theorem Config.Invariant.notStarted_untouched
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    (job : Online.Label n)
    (hnot : job ∉ config.transcript.startedLabels) :
    config.jobs job = .untouched := by
  by_contra hstate
  exact hnot (hgood.process.nonuntouchedStarted job hstate)

theorem nextCanonicalTouch_some_iff
    {n : ℕ} {transcript : Online.Transcript n}
    {job : Online.Label n} :
    RandomizedOptional.nextCanonicalTouch? n transcript = some job ↔
      transcript.startedLabels.length < n ∧
        job.val = transcript.startedLabels.length := by
  unfold RandomizedOptional.nextCanonicalTouch?
  split
  next hlt =>
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst job
      exact ⟨hlt, rfl⟩
    · rintro ⟨_, hval⟩
      apply congrArg some
      apply Fin.ext
      simpa using hval.symm
  next hnot =>
    constructor
    · simp
    · rintro ⟨hlt, _⟩
      exact (hnot hlt).elim

theorem Config.Invariant.nextTouch_untouched
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n}
    (hnext : RandomizedOptional.nextCanonicalTouch? n
      config.transcript = some job) :
    config.jobs job = .untouched := by
  have hvalue := (nextCanonicalTouch_some_iff.mp hnext).2
  apply hgood.notStarted_untouched job
  intro hmem
  have hvalMem : job.val ∈
      config.transcript.startedLabels.map Fin.val :=
    List.mem_map.mpr ⟨job, hmem, rfl⟩
  rw [hgood.touchOrder, hvalue] at hvalMem
  simp at hvalMem

theorem Config.Invariant.safeLastLowPending_tested
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    {low : ℝ → Bool} {job : Online.Label n}
    (hselected : safeLastLowPending? low config.transcript = some job) :
    ∃ p, config.jobs job = .tested p := by
  cases hlast : config.transcript.getLast? with
  | none => simp [safeLastLowPending?, hlast] at hselected
  | some observation =>
      cases observation with
      | processed processedJob =>
          simp [safeLastLowPending?, hlast] at hselected
      | rawCompleted rawJob =>
          simp [safeLastLowPending?, hlast] at hselected
      | testResult testedJob p =>
          have hfacts :
              (low p = true ∧ ∃ value,
                (testedJob, value) ∈
                  config.transcript.remainingTestResults) ∧
                testedJob = job := by
            simpa [safeLastLowPending?, hlast] using hselected
          obtain ⟨⟨_, value, hmem⟩, rfl⟩ := hfacts
          have hparts := List.mem_filter.mp hmem
          exact ⟨value, hgood.process.recordedUnprocessedTested
            testedJob value hparts.1 (by simpa using hparts.2)⟩

theorem Config.Invariant.shortestRemaining_tested
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n}
    (hshort : config.transcript.shortestRemaining? = some job) :
    ∃ p, config.jobs job = .tested p := by
  unfold Online.Transcript.shortestRemaining? at hshort
  cases hresult : Online.shortestResult?
      config.transcript.remainingTestResults with
  | none => simp [hresult] at hshort
  | some result =>
      have hjob : result.1 = job := by simpa [hresult] using hshort
      have hmem := Online.shortestResult?_mem hresult
      have hparts := List.mem_filter.mp hmem
      subst job
      exact ⟨result.2, hgood.process.recordedUnprocessedTested
        result.1 result.2 hparts.1 (by simpa using hparts.2)⟩

/-! ## Preservation by the three legal operation kinds -/

theorem Config.Invariant.afterTest
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config next : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n}
    (hquota : config.transcript.testResults.length < q)
    (hnext : RandomizedOptional.nextCanonicalTouch? n
      config.transcript = some job)
    (hstep : config.step (.finite u) (Online.fixedOracle processing)
      (.test job) = some next) :
    Invariant processing q next := by
  have hstate := hgood.nextTouch_untouched hnext
  have hvalue := (nextCanonicalTouch_some_iff.mp hnext).2
  have hlegal := hstep
  simp [Online.Config.step, hstate, Online.fixedOracle] at hstep
  subst next
  constructor
  · exact Online.Config.startedHistoryInvariant_step hgood.started
      hlegal
  · exact Online.Config.processHistoryInvariant_step hgood.process
      hgood.started hlegal
  · exact Online.Config.step_preserves_testsMatch (.finite u) processing
      hgood.testsMatch hlegal
  · simp only [Online.Transcript.startedLabels_append_testResult,
      List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [hvalue, hgood.touchOrder]
    simpa [Nat.add_comm] using
      (List.range_succ
        (n := config.transcript.startedLabels.length)).symm
  · simp only [Online.Transcript.testResults_append_testResult,
      List.length_append, List.length_singleton]
    omega
  · intro hstill
    simp only [Online.Transcript.testResults_append_testResult,
      Online.Transcript.startedLabels_append_testResult,
      List.length_append, List.length_singleton] at hstill ⊢
    rw [hgood.beforeQuota (by omega)]
  · exact Online.Config.fixedCompletionInvariant_step_of_tested_value
      (.finite u) processing (fun hstate =>
        hgood.tested_value_eq_fixed hstate) hgood.completion hlegal

theorem Config.Invariant.afterProcess
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config next : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n} {p : ℝ}
    (hstate : config.jobs job = .tested p)
    (hstep : config.step (.finite u) (Online.fixedOracle processing)
      (.process job) = some next) :
    Invariant processing q next := by
  have hlegal := hstep
  simp [Online.Config.step, hstate] at hstep
  subst next
  constructor
  · exact Online.Config.startedHistoryInvariant_step hgood.started
      hlegal
  · exact Online.Config.processHistoryInvariant_step hgood.process
      hgood.started hlegal
  · exact Online.Config.step_preserves_testsMatch (.finite u) processing
      hgood.testsMatch hlegal
  · simpa using hgood.touchOrder
  · simpa using hgood.testBound
  · intro hlt
    have hlt' : config.transcript.testResults.length < q := by
      simpa using hlt
    simpa using hgood.beforeQuota hlt'
  · exact Online.Config.fixedCompletionInvariant_step_of_tested_value
      (.finite u) processing (fun hstate =>
        hgood.tested_value_eq_fixed hstate) hgood.completion hlegal

theorem Config.Invariant.afterRaw
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config next : Online.Config n} (hgood : Invariant processing q config)
    {job : Online.Label n}
    (hreached : q ≤ config.transcript.testResults.length)
    (hnext : RandomizedOptional.nextCanonicalTouch? n
      config.transcript = some job)
    (hstep : config.step (.finite u) (Online.fixedOracle processing)
      (.raw job) = some next) :
    Invariant processing q next := by
  have hstate := hgood.nextTouch_untouched hnext
  have hvalue := (nextCanonicalTouch_some_iff.mp hnext).2
  have hlegal := hstep
  simp [Online.Config.step, hstate] at hstep
  subst next
  constructor
  · exact Online.Config.startedHistoryInvariant_step hgood.started
      hlegal
  · exact Online.Config.processHistoryInvariant_step hgood.process
      hgood.started hlegal
  · exact Online.Config.step_preserves_testsMatch (.finite u) processing
      hgood.testsMatch hlegal
  · simp only [Online.Transcript.startedLabels_append_rawCompleted,
      List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [hvalue, hgood.touchOrder]
    simpa [Nat.add_comm] using
      (List.range_succ
        (n := config.transcript.startedLabels.length)).symm
  · simpa using hgood.testBound
  · intro hlt
    simp at hlt
    omega
  · exact Online.Config.fixedCompletionInvariant_step_of_tested_value
      (.finite u) processing (fun hstate =>
        hgood.tested_value_eq_fixed hstate) hgood.completion hlegal

/-! ## Work-rank termination -/

def StrictWorkStep
    (u : ℝ) (processing : Online.Label n → ℝ) (q : ℕ)
    (strategy : Online.Strategy n) (config : Online.Config n) : Prop :=
  ∃ (action : Online.Action n) (next : Online.Config n),
    strategy config.transcript = some action ∧
      config.step (.finite u) (Online.fixedOracle processing) action =
        some next ∧
      Config.Invariant processing q next ∧
      next.remainingWork < config.remainingWork

theorem Config.Invariant.done_of_no_next_no_remaining
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n} (hgood : Invariant processing q config)
    (hnext : RandomizedOptional.nextCanonicalTouch? n
      config.transcript = none)
    (hremaining : config.transcript.shortestRemaining? = none) :
    ∀ job, config.jobs job = .done := by
  have hlength : config.transcript.startedLabels.length = n := by
    apply Nat.le_antisymm hgood.touchBound
    by_contra hlt
    have hsome : RandomizedOptional.nextCanonicalTouch? n
        config.transcript = some
          ⟨config.transcript.startedLabels.length, by omega⟩ := by
      exact nextCanonicalTouch_some_iff.mpr ⟨by omega, rfl⟩
    rw [hnext] at hsome
    contradiction
  have hallStarted : ∀ job : Online.Label n,
      job ∈ config.transcript.startedLabels := by
    intro job
    have hcard : config.transcript.startedLabels.toFinset.card = n := by
      rw [List.toFinset_card_of_nodup hgood.started.nodup, hlength]
    have huniv : config.transcript.startedLabels.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hcard
    rw [← List.mem_toFinset, huniv]
    simp
  have hremainingEmpty : config.transcript.remainingTestResults = [] := by
    apply (Online.shortestResult?_eq_none_iff _).mp
    unfold Online.Transcript.shortestRemaining? at hremaining
    exact Option.map_eq_none_iff.mp hremaining
  intro job
  cases hstate : config.jobs job with
  | done => rfl
  | untouched =>
      exact False.elim (hgood.started.untouched_not_mem job hstate
        (hallStarted job))
  | tested p =>
      have htest := hgood.process.testedRecorded job p hstate
      have hnotProcessed : job ∉ config.transcript.processedLabels := by
        intro hmem
        have hdone := hgood.process.processedDone job hmem
        rw [hstate] at hdone
        contradiction
      have hmem : (job, p) ∈ config.transcript.remainingTestResults :=
        List.mem_filter.mpr ⟨htest, by simpa using hnotProcessed⟩
      rw [hremainingEmpty] at hmem
      simp at hmem

theorem quotaStrategy_progress
    {processing : Online.Label n → ℝ} {q : ℕ} (hq : q ≤ n)
    {config : Online.Config n} (hgood : Config.Invariant processing q config)
    (hpos : 0 < config.remainingWork) (u : ℝ) (low : ℝ → Bool) :
    StrictWorkStep u processing q (quotaStrategy n q low) config := by
  unfold quotaStrategy
  cases hlow : safeLastLowPending? low config.transcript with
  | some job =>
      obtain ⟨p, hstate⟩ := hgood.safeLastLowPending_tested hlow
      let next : Online.Config n := {
        jobs := Function.update config.jobs job .done
        transcript := config.transcript ++ [.processed job] }
      have hstep : config.step (.finite u) (Online.fixedOracle processing)
          (.process job) = some next := by
        simp [Online.Config.step, hstate, next]
      exact ⟨.process job, next, by simp [hlow], hstep,
        hgood.afterProcess hstate hstep,
        Online.Config.remainingWork_step_lt hstep⟩
  | none =>
      by_cases htest : config.transcript.testResults.length < q
      · have hstarted := hgood.beforeQuota htest
        have hstartedLt : config.transcript.startedLabels.length < n := by
          omega
        let job : Online.Label n :=
          ⟨config.transcript.startedLabels.length, hstartedLt⟩
        have hnext : RandomizedOptional.nextCanonicalTouch? n
            config.transcript = some job :=
          nextCanonicalTouch_some_iff.mpr ⟨hstartedLt, rfl⟩
        have hstate := hgood.nextTouch_untouched hnext
        let next : Online.Config n := {
          jobs := Function.update config.jobs job (.tested (processing job))
          transcript := config.transcript ++
            [.testResult job (processing job)] }
        have hstep : config.step (.finite u) (Online.fixedOracle processing)
            (.test job) = some next := by
          simp [Online.Config.step, hstate, Online.fixedOracle, next]
        exact ⟨.test job, next, by simp [hlow, htest, hnext], hstep,
          hgood.afterTest htest hnext hstep,
          Online.Config.remainingWork_step_lt hstep⟩
      · have hreached : q ≤ config.transcript.testResults.length :=
          Nat.le_of_not_gt htest
        cases hshort : config.transcript.shortestRemaining? with
        | some job =>
            obtain ⟨p, hstate⟩ := hgood.shortestRemaining_tested hshort
            let next : Online.Config n := {
              jobs := Function.update config.jobs job .done
              transcript := config.transcript ++ [.processed job] }
            have hstep : config.step (.finite u) (Online.fixedOracle processing)
                (.process job) = some next := by
              simp [Online.Config.step, hstate, next]
            exact ⟨.process job, next,
              by simp [hlow, htest, hshort], hstep,
              hgood.afterProcess hstate hstep,
              Online.Config.remainingWork_step_lt hstep⟩
        | none =>
            cases hnext : RandomizedOptional.nextCanonicalTouch? n
                config.transcript with
            | some job =>
                have hstate := hgood.nextTouch_untouched hnext
                let next : Online.Config n := {
                  jobs := Function.update config.jobs job .done
                  transcript := config.transcript ++ [.rawCompleted job] }
                have hstep : config.step (.finite u)
                    (Online.fixedOracle processing) (.raw job) = some next := by
                  simp [Online.Config.step, hstate, next]
                exact ⟨.raw job, next,
                  by simp [hlow, htest, hshort, hnext], hstep,
                  hgood.afterRaw hreached hnext hstep,
                  Online.Config.remainingWork_step_lt hstep⟩
            | none =>
                have hdone := hgood.done_of_no_next_no_remaining hnext hshort
                have hzero :=
                  (Online.Config.remainingWork_eq_zero_iff config).mpr hdone
                omega

theorem runFuel_quotaStrategy_completed
    {processing : Online.Label n → ℝ} {q : ℕ} (hq : q ≤ n)
    (u : ℝ) (low : ℝ → Bool) (fuel : ℕ) (config : Online.Config n)
    (hgood : Config.Invariant processing q config)
    (hfuel : config.remainingWork < fuel) :
    let result := Online.runFuel (.finite u) (Online.fixedOracle processing)
      (quotaStrategy n q low) fuel config
    result.reason = .strategyStopped ∧
      Config.Invariant processing q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  induction fuel generalizing config with
  | zero => omega
  | succ fuel ih =>
      by_cases hzero : config.remainingWork = 0
      · have hdone := (Online.Config.remainingWork_eq_zero_iff config).mp hzero
        have hnext : RandomizedOptional.nextCanonicalTouch? n
            config.transcript = none := by
          unfold RandomizedOptional.nextCanonicalTouch?
          have hlength : config.transcript.startedLabels.length = n := by
            have hall : ∀ job : Online.Label n,
                job ∈ config.transcript.startedLabels := by
              intro job
              exact hgood.process.nonuntouchedStarted job (by simp [hdone job])
            have hcard : config.transcript.startedLabels.toFinset.card = n := by
              apply Nat.le_antisymm
              · rw [List.toFinset_card_of_nodup hgood.started.nodup]
                exact hgood.touchBound
              · have hsubset : (Finset.univ : Finset (Online.Label n)) ⊆
                    config.transcript.startedLabels.toFinset := by
                  intro job _
                  simpa using hall job
                have hc := Finset.card_le_card hsubset
                simpa using hc
            rw [List.toFinset_card_of_nodup hgood.started.nodup] at hcard
            exact hcard
          rw [hlength]
          simp
        have hremaining : config.transcript.shortestRemaining? = none := by
          unfold Online.Transcript.shortestRemaining?
          rw [Option.map_eq_none_iff]
          apply (Online.shortestResult?_eq_none_iff _).2
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro result hmem
          have hparts := List.mem_filter.mp hmem
          have htested := hgood.process.recordedUnprocessedTested
            result.1 result.2 hparts.1 (by simpa using hparts.2)
          rw [hdone result.1] at htested
          contradiction
        have htestEq : config.transcript.testResults.length = q := by
          apply Nat.le_antisymm hgood.testBound
          by_contra hlt
          have hbefore := hgood.beforeQuota (Nat.lt_of_not_ge hlt)
          have hlength : config.transcript.startedLabels.length = n := by
            apply Nat.le_antisymm hgood.touchBound
            by_contra hstarted
            have hsome : RandomizedOptional.nextCanonicalTouch? n
                config.transcript = some
                  ⟨config.transcript.startedLabels.length, by omega⟩ :=
              nextCanonicalTouch_some_iff.mpr ⟨by omega, rfl⟩
            rw [hnext] at hsome
            contradiction
          omega
        have hsafe : safeLastLowPending? low config.transcript = none := by
          cases hs : safeLastLowPending? low config.transcript with
          | none => rfl
          | some job =>
              obtain ⟨p, htested⟩ := hgood.safeLastLowPending_tested hs
              rw [hdone job] at htested
              contradiction
        have hstop : quotaStrategy n q low config.transcript = none := by
          simp [quotaStrategy, hsafe, htestEq, hremaining, hnext]
        simp only [Online.runFuel, hstop]
        exact ⟨trivial, hgood, hdone⟩
      · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
        obtain ⟨action, next, hchosen, hlegal, hnextGood, hdec⟩ :=
          quotaStrategy_progress hq hgood hpos u low
        simp only [Online.runFuel, hchosen, hlegal]
        apply ih next hnextGood
        omega

/-- Every fixed quota template legally completes all jobs in the common
`2n+1` analysis fuel. -/
theorem quotaStrategy_completes
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (quotaStrategy n q low) (2 * n + 1)
    result.reason = .strategyStopped ∧
      Config.Invariant processing q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  unfold Online.run
  apply runFuel_quotaStrategy_completed hq u low
    (2 * n + 1) (Online.Config.initial n)
    (Config.initial_invariant processing q)
  rw [Online.Config.initial_remainingWork]
  omega

/-- A completed quota run records every completion exactly once, including
zero jobs completed by their test and untouched jobs completed raw. -/
theorem quotaStrategy_completionLabels_perm
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (quotaStrategy n q low) (2 * n + 1)
    (result.config.transcript.completionLabels processing).Perm
      (List.ofFn id) := by
  let result := Online.run (.finite u) (Online.fixedOracle processing)
    (quotaStrategy n q low) (2 * n + 1)
  have hrun := quotaStrategy_completes hq u processing low
  have hnodup :
      (result.config.transcript.completionLabels processing).Nodup :=
    hrun.2.1.completion.nodup
  have hmem : ∀ job,
      job ∈ result.config.transcript.completionLabels processing := by
    intro job
    rw [hrun.2.1.completion.mem_iff]
    simp [hrun.2.2 job, Online.JobState.completionRecorded]
  apply (List.perm_ext_iff_of_nodup hnodup
    (List.nodup_ofFn.mpr Function.injective_id)).mpr
  intro job
  simp [hmem job]

theorem randomizedQuotaStrategy_completes
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    (order : Equiv.Perm (Fin n)) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (randomizedQuotaStrategy n q low order) (2 * n + 1)).config.jobs job =
        .done := by
  rw [randomizedQuotaStrategy, Online.run_relabel_config]
  intro job
  change
    (Online.run (.finite u)
      (Online.fixedOracle fun virtual => processing (order virtual))
      (quotaStrategy n q low) (2 * n + 1)).config.jobs
        (order.symm job) = .done
  exact (quotaStrategy_completes hq u
    (fun virtual => processing (order virtual)) low).2.2 (order.symm job)

end

end QuotaStrategy
end RevealingOptimization
end SchedulingPaper
