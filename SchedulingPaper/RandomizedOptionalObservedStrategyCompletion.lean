import SchedulingPaper.RandomizedOptionalObservedStrategy
import SchedulingPaper.RandomizedOptionalObservedTrace
import Mathlib.Tactic

/-!
# Termination of the observed canonical optional-testing strategy

The lower bound quantifies over `CompletePolicy`.  This file proves that the
literal four-block upper strategy is itself such a policy.  The only
strategy-specific state is that first touches occur in virtual-label order;
the generic operational history invariant supplies freshness and truthful
observations.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section
attribute [local instance] Classical.propDecidable

structure Config.CanonicalInvariant (config : Config n) : Prop where
  touchOrder :
    config.transcript.startedLabels.map Fin.val =
      List.range config.transcript.startedLabels.length
  touchBound : config.transcript.startedLabels.length ≤ n
  tested_iff : ∀ job p,
    config.jobs job = .tested p ↔
      (job, p) ∈ config.transcript.testResults ∧
        job ∉ config.transcript.processedLabels
  lastTest : ∀ job p,
    config.transcript.getLast? = some (.testResult job p) →
      config.jobs job = .tested p

theorem Config.initial_canonicalInvariant (n : ℕ) :
    (Config.initial n).CanonicalInvariant := by
  constructor <;>
    simp [Config.initial, Transcript.startedLabels,
      Transcript.revealedResults, Transcript.testResults,
      Transcript.processedLabels]

theorem Config.CanonicalInvariant.nextTouch_untouched
    {processing : Label n → ℝ} {config : Config n}
    (hcanonical : config.CanonicalInvariant)
    (hhistory : HistoryInvariant processing config)
    {job : Label n}
    (hnext : nextCanonicalTouch? n config.transcript = some job) :
    config.jobs job = .untouched := by
  unfold nextCanonicalTouch? at hnext
  split at hnext
  next hlt =>
    simp only [Option.some.injEq] at hnext
    subst job
    apply hhistory.notStartedUntouched
    intro hmem
    have hvalmem : config.transcript.startedLabels.length ∈
        config.transcript.startedLabels.map Fin.val := by
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    rw [hcanonical.touchOrder] at hvalmem
    simpa using hvalmem
  next => simp at hnext

private theorem testResult_mem_startedLabels
    {transcript : Transcript n} {job : Label n} {p : ℝ}
    (hmem : (job, p) ∈ transcript.testResults) :
    job ∈ transcript.startedLabels := by
  unfold Transcript.startedLabels
  exact List.mem_map.mpr
    ⟨(job, p), Transcript.mem_revealedResults_of_mem_testResults hmem, rfl⟩

theorem Config.CanonicalInvariant.afterTest
    {processing : Label n → ℝ} {config : Config n}
    (hcanonical : config.CanonicalInvariant)
    (hhistory : HistoryInvariant processing config)
    (job : Label n)
    (hval : job.val = config.transcript.startedLabels.length) :
    ({
      jobs := Function.update config.jobs job (.tested (processing job))
      transcript := config.transcript ++
        [.testResult job (processing job)]
    } : Config n).CanonicalInvariant := by
  have hjob : config.jobs job = .untouched := by
    apply hhistory.notStartedUntouched
    intro hmem
    have hvalmem : config.transcript.startedLabels.length ∈
        config.transcript.startedLabels.map Fin.val :=
      List.mem_map.mpr ⟨job, hmem, hval⟩
    rw [hcanonical.touchOrder] at hvalmem
    simpa using hvalmem
  have hnotStarted := hhistory.untouchedNotStarted job hjob
  have hnotProcessed : job ∉ config.transcript.processedLabels := by
    intro hmem
    have hdone := hhistory.processedDone job hmem
    rw [hjob] at hdone
    contradiction
  have hnoTestPair : ∀ q, (job, q) ∉ config.transcript.testResults := by
    intro q hmem
    exact hnotStarted (testResult_mem_startedLabels hmem)
  constructor
  · simp only [Transcript.startedLabels_append_test, List.map_append,
      List.map_singleton, List.length_append, List.length_singleton]
    rw [hval, hcanonical.touchOrder]
    simpa [Nat.add_comm] using
      (List.range_succ
        (n := config.transcript.startedLabels.length)).symm
  · simp only [Transcript.startedLabels_append_test,
      List.length_append, List.length_singleton]
    omega
  · intro other q
    rw [Transcript.testResults_append_test,
      Transcript.processedLabels_append_test]
    by_cases heq : other = job
    · subst other
      simp [Function.update, hnoTestPair q, hnotProcessed]
      constructor <;> intro h <;> exact h.symm
    · simp [Function.update, heq, hcanonical.tested_iff other q]
  · intro other q hlast
    have heq : job = other ∧ processing job = q := by
      simpa using hlast
    rcases heq with ⟨rfl, rfl⟩
    simp [Function.update]

theorem Config.CanonicalInvariant.afterProcess
    {processing : Label n → ℝ} {config : Config n}
    (hcanonical : config.CanonicalInvariant)
    (job : Label n) (p : ℝ) (hjob : config.jobs job = .tested p) :
    ({
      jobs := Function.update config.jobs job .done
      transcript := config.transcript ++ [.processed job]
    } : Config n).CanonicalInvariant := by
  have htested := (hcanonical.tested_iff job p).mp hjob
  constructor
  · simpa using hcanonical.touchOrder
  · simpa using hcanonical.touchBound
  · intro other q
    rw [Transcript.testResults_append_process,
      Transcript.processedLabels_append_process]
    by_cases heq : other = job
    · subst other
      simp [Function.update]
    · simp [Function.update, heq, hcanonical.tested_iff other q]
  · intro other q hlast
    simp at hlast

theorem Config.CanonicalInvariant.afterBlind
    {processing : Label n → ℝ} {config : Config n}
    (hcanonical : config.CanonicalInvariant)
    (hhistory : HistoryInvariant processing config)
    (job : Label n)
    (hval : job.val = config.transcript.startedLabels.length) :
    ({
      jobs := Function.update config.jobs job .done
      transcript := config.transcript ++
        [.blindCompleted job (processing job)]
    } : Config n).CanonicalInvariant := by
  have hjob : config.jobs job = .untouched := by
    apply hhistory.notStartedUntouched
    intro hmem
    have hvalmem : config.transcript.startedLabels.length ∈
        config.transcript.startedLabels.map Fin.val :=
      List.mem_map.mpr ⟨job, hmem, hval⟩
    rw [hcanonical.touchOrder] at hvalmem
    simpa using hvalmem
  have hnotStarted := hhistory.untouchedNotStarted job hjob
  have hnoTestPair : ∀ q, (job, q) ∉ config.transcript.testResults := by
    intro q hmem
    exact hnotStarted (testResult_mem_startedLabels hmem)
  constructor
  · simp only [Transcript.startedLabels_append_blind, List.map_append,
      List.map_singleton, List.length_append, List.length_singleton]
    rw [hval, hcanonical.touchOrder]
    simpa [Nat.add_comm] using
      (List.range_succ
        (n := config.transcript.startedLabels.length)).symm
  · simp only [Transcript.startedLabels_append_blind,
      List.length_append, List.length_singleton]
    omega
  · intro other q
    rw [Transcript.testResults_append_blind,
      Transcript.processedLabels_append_blind]
    by_cases heq : other = job
    · subst other
      simp [Function.update, hnoTestPair q]
    · simp [Function.update, heq, hcanonical.tested_iff other q]
  · intro other q hlast
    simp at hlast

private theorem shortestFold_mem
    (best : Label n × ℝ) (rest : List (Label n × ℝ)) :
    rest.foldl
        (fun best candidate =>
          if resultBefore candidate best then candidate else best)
        best ∈ best :: rest := by
  induction rest generalizing best with
  | nil => simp
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hlt : resultBefore candidate best
      · have hmem := ih candidate
        simp only [if_pos hlt] at hmem ⊢
        exact List.mem_cons_of_mem best hmem
      · have hmem := ih best
        simp only [if_neg hlt] at hmem ⊢
        rw [List.mem_cons] at hmem ⊢
        exact hmem.imp id (fun hrest => List.mem_cons_of_mem candidate hrest)

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

theorem shortestResult?_eq_none_iff
    (results : List (Label n × ℝ)) :
    shortestResult? results = none ↔ results = [] := by
  cases results <;> simp [shortestResult?]

theorem Config.CanonicalInvariant.shortestClassPending_tested
    {config : Config n} (hcanonical : config.CanonicalInvariant)
    (category : ℝ → Bool) {job : Label n}
    (hshort : shortestClassPending? category config.transcript = some job) :
    ∃ p, config.jobs job = .tested p := by
  unfold shortestClassPending? at hshort
  cases hresult : shortestResult?
      (classRemainingResults category config.transcript) with
  | none => simp [hresult] at hshort
  | some result =>
      have hfst : result.1 = job := by simpa [hresult] using hshort
      have hmem := shortestResult?_mem hresult
      unfold classRemainingResults Transcript.remainingTestResults at hmem
      have hclass := List.mem_filter.mp hmem
      have hremaining := List.mem_filter.mp hclass.1
      have hnotProcessed : result.1 ∉ config.transcript.processedLabels := by
        simpa using hremaining.2
      subst job
      exact ⟨result.2,
        (hcanonical.tested_iff result.1 result.2).mpr
          ⟨hremaining.1, hnotProcessed⟩⟩

theorem Config.CanonicalInvariant.lastLowPending_tested
    {config : Config n} (hcanonical : config.CanonicalInvariant)
    (low : ℝ → Bool) {job : Label n}
    (hlow : lastLowPending? low config.transcript = some job) :
    ∃ p, config.jobs job = .tested p := by
  unfold lastLowPending? at hlow
  cases hlast : config.transcript.getLast? with
  | none => simp [hlast] at hlow
  | some observation =>
      rw [hlast] at hlow
      cases observation with
      | testResult testedJob p =>
          by_cases hp : low p = true
          · simp [hp] at hlow
            subst job
            exact ⟨p, hcanonical.lastTest testedJob p hlast⟩
          · simp [hp] at hlow
      | processed processedJob => simp at hlow
      | blindCompleted blindJob p => simp at hlow

theorem Config.CanonicalInvariant.shortestRemaining_tested
    {config : Config n} (hcanonical : config.CanonicalInvariant)
    {result : Label n × ℝ}
    (hshort : shortestResult? config.transcript.remainingTestResults =
      some result) :
    ∃ p, config.jobs result.1 = .tested p := by
  have hmem := shortestResult?_mem hshort
  unfold Transcript.remainingTestResults at hmem
  have hremaining := List.mem_filter.mp hmem
  have hnotProcessed : result.1 ∉ config.transcript.processedLabels := by
    simpa using hremaining.2
  exact ⟨result.2, (hcanonical.tested_iff result.1 result.2).mpr
    ⟨hremaining.1, hnotProcessed⟩⟩

structure Config.QuotaInvariant (config : Config n) (q : ℕ) : Prop where
  testBound : config.transcript.testResults.length ≤ q
  beforeQuota : config.transcript.testResults.length < q →
    config.transcript.startedLabels.length =
      config.transcript.testResults.length

theorem Config.initial_quotaInvariant (n q : ℕ) :
    (Config.initial n).QuotaInvariant q := by
  constructor <;>
    simp [Config.initial, Transcript.testResults,
      Transcript.startedLabels, Transcript.revealedResults]

theorem Config.QuotaInvariant.afterTest
    {config : Config n} {q : ℕ} (hquota : config.QuotaInvariant q)
    (hlt : config.transcript.testResults.length < q)
    (job : Label n) (p : ℝ) :
    ({
      jobs := Function.update config.jobs job (.tested p)
      transcript := config.transcript ++ [.testResult job p]
    } : Config n).QuotaInvariant q := by
  constructor
  · simp only [Transcript.testResults_append_test,
      List.length_append, List.length_singleton]
    omega
  · intro hstill
    simp only [Transcript.testResults_append_test,
      Transcript.startedLabels_append_test,
      List.length_append, List.length_singleton] at hstill ⊢
    rw [hquota.beforeQuota (by omega)]

theorem Config.QuotaInvariant.afterProcess
    {config : Config n} {q : ℕ} (hquota : config.QuotaInvariant q)
    (job : Label n) :
    ({
      jobs := Function.update config.jobs job .done
      transcript := config.transcript ++ [.processed job]
    } : Config n).QuotaInvariant q := by
  constructor
  · simpa using hquota.testBound
  · intro hlt
    simp only [Transcript.testResults_append_process] at hlt
    simpa using hquota.beforeQuota hlt

theorem Config.QuotaInvariant.afterBlind
    {config : Config n} {q : ℕ} (hquota : config.QuotaInvariant q)
    (hreached : q ≤ config.transcript.testResults.length)
    (job : Label n) (p : ℝ) :
    ({
      jobs := Function.update config.jobs job .done
      transcript := config.transcript ++ [.blindCompleted job p]
    } : Config n).QuotaInvariant q := by
  constructor
  · simpa using hquota.testBound
  · intro hlt
    simp only [Transcript.testResults_append_blind] at hlt
    omega

def Config.CanonicalGood
    (processing : Label n → ℝ) (q : ℕ) (config : Config n) : Prop :=
  HistoryInvariant processing config ∧
    config.CanonicalInvariant ∧ config.QuotaInvariant q

theorem Config.initial_canonicalGood
    (processing : Label n → ℝ) (q : ℕ) :
    (Config.initial n).CanonicalGood processing q :=
  ⟨Config.initial_historyInvariant processing,
    Config.initial_canonicalInvariant n,
    Config.initial_quotaInvariant n q⟩

theorem Config.remainingWork_eq_zero_iff (config : Config n) :
    config.remainingWork = 0 ↔ ∀ job, config.jobs job = .done := by
  constructor
  · intro hzero job
    have hle : (config.jobs job).work ≤ config.remainingWork := by
      unfold Config.remainingWork
      exact Finset.single_le_sum
        (f := fun j : Label n => (config.jobs j).work)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ job)
    have hw : (config.jobs job).work = 0 := by omega
    cases hjob : config.jobs job <;>
      simp [JobState.work, hjob] at hw ⊢
  · intro hdone
    unfold Config.remainingWork
    apply Finset.sum_eq_zero
    intro job _
    simp [hdone job, JobState.work]

theorem Config.CanonicalGood.started_length_eq_n_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) :
    config.transcript.startedLabels.length = n := by
  apply hgood.1.startedLabels_length_eq_n_of_done
  exact config.remainingWork_eq_zero_iff.mp hzero

theorem Config.CanonicalGood.lastLowPending_eq_none_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) (low : ℝ → Bool) :
    lastLowPending? low config.transcript = none := by
  cases hlast : lastLowPending? low config.transcript with
  | none => rfl
  | some job =>
      obtain ⟨p, hp⟩ := hgood.2.1.lastLowPending_tested low hlast
      have hdone := config.remainingWork_eq_zero_iff.mp hzero job
      rw [hdone] at hp
      contradiction

theorem Config.CanonicalGood.shortestClassPending_eq_none_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) (category : ℝ → Bool) :
    shortestClassPending? category config.transcript = none := by
  cases hshort : shortestClassPending? category config.transcript with
  | none => rfl
  | some job =>
      obtain ⟨p, hp⟩ :=
        hgood.2.1.shortestClassPending_tested category hshort
      have hdone := config.remainingWork_eq_zero_iff.mp hzero job
      rw [hdone] at hp
      contradiction

theorem Config.CanonicalGood.shortestRemaining_eq_none_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) :
    shortestResult? config.transcript.remainingTestResults = none := by
  cases hshort : shortestResult? config.transcript.remainingTestResults with
  | none => rfl
  | some result =>
      obtain ⟨p, hp⟩ := hgood.2.1.shortestRemaining_tested hshort
      have hdone := config.remainingWork_eq_zero_iff.mp hzero result.1
      rw [hdone] at hp
      contradiction

theorem Config.CanonicalGood.test_length_eq_quota_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hq : q ≤ n) (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) :
    config.transcript.testResults.length = q := by
  apply Nat.le_antisymm hgood.2.2.testBound
  by_contra hnot
  have hlt : config.transcript.testResults.length < q :=
    Nat.lt_of_not_ge hnot
  have hphase := hgood.2.2.beforeQuota hlt
  have hstarted := hgood.started_length_eq_n_of_zero hzero
  omega

theorem Config.CanonicalGood.nextCanonicalTouch_eq_none_of_zero
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0) :
    nextCanonicalTouch? n config.transcript = none := by
  unfold nextCanonicalTouch?
  rw [hgood.started_length_eq_n_of_zero hzero]
  simp

theorem canonicalStrategy_stop_of_zero
    {processing : Label n → ℝ} {q : ℕ} (hq : q ≤ n)
    {config : Config n} (hgood : config.CanonicalGood processing q)
    (hzero : config.remainingWork = 0)
    (low medium : ℝ → Bool) :
    canonicalStrategy n q low medium config.transcript = none := by
  unfold canonicalStrategy
  rw [hgood.lastLowPending_eq_none_of_zero hzero low]
  rw [if_neg (by
    rw [hgood.test_length_eq_quota_of_zero hq hzero]
    exact Nat.lt_irrefl q)]
  rw [hgood.shortestClassPending_eq_none_of_zero hzero medium]
  rw [hgood.nextCanonicalTouch_eq_none_of_zero hzero]
  rw [hgood.shortestRemaining_eq_none_of_zero hzero]
  rfl

theorem nextCanonicalTouch_some_iff
    {n : ℕ} {transcript : Transcript n} {job : Label n} :
    nextCanonicalTouch? n transcript = some job ↔
      transcript.startedLabels.length < n ∧
        job.val = transcript.startedLabels.length := by
  unfold nextCanonicalTouch?
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

theorem Config.CanonicalGood.done_of_no_next_no_remaining
    {processing : Label n → ℝ} {q : ℕ} {config : Config n}
    (hgood : config.CanonicalGood processing q)
    (hnext : nextCanonicalTouch? n config.transcript = none)
    (hremaining : shortestResult? config.transcript.remainingTestResults = none) :
    ∀ job, config.jobs job = .done := by
  have hnotLt : ¬ config.transcript.startedLabels.length < n := by
    intro hlt
    let job : Label n := ⟨config.transcript.startedLabels.length, hlt⟩
    have : nextCanonicalTouch? n config.transcript = some job := by
      exact nextCanonicalTouch_some_iff.mpr ⟨hlt, rfl⟩
    rw [hnext] at this
    contradiction
  have hlength : config.transcript.startedLabels.length = n := by
    exact Nat.le_antisymm hgood.2.1.touchBound (Nat.le_of_not_gt hnotLt)
  have hallStarted : ∀ job : Label n,
      job ∈ config.transcript.startedLabels := by
    intro job
    by_contra hnot
    have huntouched := hgood.1.notStartedUntouched job hnot
    have hnodup := hgood.1.startedNodup
    have hcard : config.transcript.startedLabels.toFinset.card = n := by
      calc
        config.transcript.startedLabels.toFinset.card =
            config.transcript.startedLabels.length :=
          List.toFinset_card_of_nodup hnodup
        _ = n := hlength
    have hproper : config.transcript.startedLabels.toFinset ⊂
        (Finset.univ : Finset (Label n)) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have : job ∈ config.transcript.startedLabels.toFinset := by
        rw [heq]
        simp
      exact hnot (List.mem_toFinset.mp this)
    have hcardLt := Finset.card_lt_card hproper
    simp [hcard] at hcardLt
  have hremainingEmpty : config.transcript.remainingTestResults = [] :=
    (shortestResult?_eq_none_iff _).mp hremaining
  intro job
  cases hstate : config.jobs job with
  | done => rfl
  | untouched =>
      exact False.elim
        ((hgood.1.untouchedNotStarted job hstate) (hallStarted job))
  | tested p =>
      have hpair := (hgood.2.1.tested_iff job p).mp hstate
      have hmem : (job, p) ∈ config.transcript.remainingTestResults := by
        unfold Transcript.remainingTestResults
        apply List.mem_filter.mpr
        exact ⟨hpair.1, by simpa using hpair.2⟩
      rw [hremainingEmpty] at hmem
      simp at hmem

structure CanonicalStep
    {n : ℕ} (processing : Label n → ℝ) (q : ℕ)
    (low medium : ℝ → Bool) (config : Config n) where
  action : Action n
  next : Config n
  chosen : canonicalStrategy n q low medium config.transcript = some action
  legal : config.step processing action = some next
  good : next.CanonicalGood processing q
  decreases : next.remainingWork < config.remainingWork

theorem canonicalStrategy_progress
    {n q : ℕ} (hq : q ≤ n) {processing : Label n → ℝ}
    {config : Config n} (hgood : config.CanonicalGood processing q)
    (hpos : 0 < config.remainingWork) (low medium : ℝ → Bool) :
    Nonempty (CanonicalStep processing q low medium config) := by
  classical
  cases hlow : lastLowPending? low config.transcript with
  | some job =>
      obtain ⟨p, hjob⟩ := hgood.2.1.lastLowPending_tested low hlow
      let next : Config n := {
        jobs := Function.update config.jobs job .done
        transcript := config.transcript ++ [.processed job] }
      have hchosen : canonicalStrategy n q low medium config.transcript =
          some (.process job) := by simp [canonicalStrategy, hlow]
      have hstep : config.step processing (.process job) = some next := by
        simp [Config.step, hjob, next]
      refine ⟨⟨.process job, next, hchosen, hstep, ?_,
        Config.remainingWork_step_lt hstep⟩⟩
      exact ⟨hgood.1.step hstep,
        hgood.2.1.afterProcess (processing := processing) job p hjob,
        hgood.2.2.afterProcess job⟩
  | none =>
      by_cases htest : config.transcript.testResults.length < q
      · have hstartedLt : config.transcript.startedLabels.length < n := by
          rw [hgood.2.2.beforeQuota htest]
          omega
        let job : Label n :=
          ⟨config.transcript.startedLabels.length, hstartedLt⟩
        have hnextTouch : nextCanonicalTouch? n config.transcript = some job :=
          nextCanonicalTouch_some_iff.mpr ⟨hstartedLt, rfl⟩
        have hjob : config.jobs job = .untouched :=
          hgood.2.1.nextTouch_untouched hgood.1 hnextTouch
        let next : Config n := {
          jobs := Function.update config.jobs job (.tested (processing job))
          transcript := config.transcript ++
            [.testResult job (processing job)] }
        have hchosen : canonicalStrategy n q low medium config.transcript =
            some (.test job) := by
          simp [canonicalStrategy, hlow, htest, hnextTouch]
        have hstep : config.step processing (.test job) = some next := by
          simp [Config.step, hjob, next]
        refine ⟨⟨.test job, next, hchosen, hstep, ?_,
          Config.remainingWork_step_lt hstep⟩⟩
        exact ⟨hgood.1.step hstep,
          hgood.2.1.afterTest hgood.1 job rfl,
          hgood.2.2.afterTest htest job (processing job)⟩
      · have hreached : q ≤ config.transcript.testResults.length :=
          Nat.le_of_not_gt htest
        cases hmedium : shortestClassPending? medium config.transcript with
        | some job =>
            obtain ⟨p, hjob⟩ :=
              hgood.2.1.shortestClassPending_tested medium hmedium
            let next : Config n := {
              jobs := Function.update config.jobs job .done
              transcript := config.transcript ++ [.processed job] }
            have hchosen : canonicalStrategy n q low medium config.transcript =
                some (.process job) := by
              simp [canonicalStrategy, hlow, htest, hmedium]
            have hstep : config.step processing (.process job) = some next := by
              simp [Config.step, hjob, next]
            refine ⟨⟨.process job, next, hchosen, hstep, ?_,
              Config.remainingWork_step_lt hstep⟩⟩
            exact ⟨hgood.1.step hstep,
              hgood.2.1.afterProcess (processing := processing) job p hjob,
              hgood.2.2.afterProcess job⟩
        | none =>
            cases hnextTouch : nextCanonicalTouch? n config.transcript with
            | some job =>
                have hjob : config.jobs job = .untouched :=
                  hgood.2.1.nextTouch_untouched hgood.1 hnextTouch
                have hval := (nextCanonicalTouch_some_iff.mp hnextTouch).2
                let next : Config n := {
                  jobs := Function.update config.jobs job .done
                  transcript := config.transcript ++
                    [.blindCompleted job (processing job)] }
                have hchosen :
                    canonicalStrategy n q low medium config.transcript =
                      some (.blind job) := by
                  simp [canonicalStrategy, hlow, htest, hmedium, hnextTouch]
                have hstep : config.step processing (.blind job) = some next := by
                  simp [Config.step, hjob, next]
                refine ⟨⟨.blind job, next, hchosen, hstep, ?_,
                  Config.remainingWork_step_lt hstep⟩⟩
                exact ⟨hgood.1.step hstep,
                  hgood.2.1.afterBlind hgood.1 job hval,
                  hgood.2.2.afterBlind hreached job (processing job)⟩
            | none =>
                cases htail : shortestResult?
                    config.transcript.remainingTestResults with
                | some result =>
                    obtain ⟨p, hjob⟩ :=
                      hgood.2.1.shortestRemaining_tested htail
                    let next : Config n := {
                      jobs := Function.update config.jobs result.1 .done
                      transcript := config.transcript ++ [.processed result.1] }
                    have hchosen :
                        canonicalStrategy n q low medium config.transcript =
                          some (.process result.1) := by
                      simp [canonicalStrategy, hlow, htest, hmedium,
                        hnextTouch, htail]
                    have hstep : config.step processing (.process result.1) =
                        some next := by
                      simp [Config.step, hjob, next]
                    refine ⟨⟨.process result.1, next, hchosen, hstep, ?_,
                      Config.remainingWork_step_lt hstep⟩⟩
                    exact ⟨hgood.1.step hstep,
                      hgood.2.1.afterProcess (processing := processing)
                        result.1 p hjob,
                      hgood.2.2.afterProcess result.1⟩
                | none =>
                    have hdone :=
                      hgood.done_of_no_next_no_remaining hnextTouch htail
                    have hzero := config.remainingWork_eq_zero_iff.mpr hdone
                    omega

theorem runFuel_canonicalStrategy_completed
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (fuel : ℕ) (config : Config n)
    (hgood : config.CanonicalGood processing q)
    (hfuel : config.remainingWork < fuel) :
    let result := runFuel processing (canonicalStrategy n q low medium)
      fuel config
    result.reason = .strategyStopped ∧
      result.config.CanonicalGood processing q ∧
      result.config.remainingWork = 0 := by
  induction fuel generalizing config with
  | zero => omega
  | succ fuel ih =>
      by_cases hzero : config.remainingWork = 0
      · have hstop := canonicalStrategy_stop_of_zero hq hgood hzero low medium
        simp [runFuel, hstop, hgood, hzero]
      · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
        obtain ⟨step⟩ := canonicalStrategy_progress hq hgood hpos low medium
        simp only [runFuel, step.chosen, step.legal]
        apply ih step.next step.good
        have hdec := step.decreases
        have hcurrent : config.remainingWork ≤ fuel := by omega
        omega

/-- The literal four-block strategy legally finishes every job within the
generic `2n+1` lifecycle budget. -/
theorem run_canonicalStrategy_completed
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    let result := run processing (canonicalStrategy n q low medium) (2 * n + 1)
    result.reason = .strategyStopped ∧
      result.config.CanonicalGood processing q ∧
      ∀ job, result.config.jobs job = .done := by
  have hrun := runFuel_canonicalStrategy_completed hq processing low medium
    (2 * n + 1) (Config.initial n)
    (Config.initial_canonicalGood processing q) (by simp)
  simpa [run] using ⟨hrun.1, hrun.2.1,
    (Config.remainingWork_eq_zero_iff _).mp hrun.2.2⟩

/-- A canonical policy packaged for direct use by the announced lower/upper
wrappers. -/
def canonicalCompletePolicy
    {n q : ℕ} (hq : q ≤ n) (p : Fin n → ℝ)
    (low medium : ℝ → Bool) : ObservedTrace.CompletePolicy p where
  strategy := canonicalStrategy n q low medium
  completes := by
    intro σ job
    exact (run_canonicalStrategy_completed hq
      (ObservedTrace.placedProcessing p σ) low medium).2.2 job

/-- Relabelling the canonical virtual order by any private permutation also
finishes all physical jobs. -/
theorem randomizedCanonicalStrategy_completed
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (order : Equiv.Perm (Label n)) :
    ∀ job,
      (run processing (randomizedCanonicalStrategy n q low medium order)
        (2 * n + 1)).config.jobs job = .done := by
  intro job
  rw [randomizedCanonicalStrategy, run_relabel_config]
  change
    (run (fun virtual => processing (order virtual))
      (canonicalStrategy n q low medium) (2 * n + 1)).config.jobs
        (order.symm job) = .done
  exact (run_canonicalStrategy_completed hq
    (fun virtual => processing (order virtual)) low medium).2.2 (order.symm job)

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
