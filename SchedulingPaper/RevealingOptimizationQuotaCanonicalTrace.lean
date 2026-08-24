import SchedulingPaper.RevealingOptimizationQuotaStrategy
import SchedulingPaper.RevealingOptimizationQuotaPairAccounting
import Mathlib.Tactic

/-!
# Canonical trace of the revealing-optimization quota policy

The literal quota execution is globally ordered by discovery, deferred SPT,
and raw phases.  This turns the lifecycle multiset identity into the exact
two-label words used by the finite quota kernel.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace QuotaStrategy

open Online
open RandomizedOptional
open QuotaPairAccounting

noncomputable section
attribute [local instance] Classical.propDecidable

def quotaRun
    {n : ℕ} (q : ℕ) (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) : Online.RunResult n :=
  Online.run (.finite u) (Online.fixedOracle processing)
    (quotaStrategy n q low) (2 * n + 1)

theorem quotaRun_completed
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (quotaRun q u processing low).reason = .strategyStopped ∧
      Config.Invariant processing q (quotaRun q u processing low).config ∧
      ∀ job, (quotaRun q u processing low).config.jobs job = .done := by
  simpa [quotaRun] using quotaStrategy_completes hq u processing low

theorem quotaRun_followsStrategy
    {n q : ℕ} (u : ℝ) (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (quotaRun q u processing low).config.transcript.FollowsStrategy
      (quotaStrategy n q low) := by
  simpa [quotaRun] using Online.run_followsStrategy (.finite u)
    (Online.fixedOracle processing) (quotaStrategy n q low) (2 * n + 1)

def observationTouchLabel? {n : ℕ} :
    Online.Observation n → Option (Online.Label n)
  | .testResult job _ => some job
  | .processed _ => none
  | .rawCompleted job => some job

theorem Transcript.startedLabels_eq_filterMap_touchLabel
    (transcript : Online.Transcript n) :
    transcript.startedLabels = transcript.filterMap observationTouchLabel? := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [Online.Transcript.startedLabels,
          observationTouchLabel?, ih]

theorem quotaRun_startedLabels_eq_ofFn
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (quotaRun q u processing low).config.transcript.startedLabels =
      List.ofFn id := by
  let result := quotaRun q u processing low
  have hcompleted := quotaRun_completed hq u processing low
  have horder := hcompleted.2.1.touchOrder
  have hlength := hcompleted.2.1.startedLabels_length_eq_of_done
    hcompleted.2.2
  have hright : (List.ofFn id : List (Fin n)).map Fin.val =
      List.range n := by
    rw [List.map_ofFn]
    simp [List.ofFn_eq_pmap]
  apply (List.map_injective_iff.mpr Fin.val_injective)
  simpa [result, hlength, hright] using horder

theorem quotaRun_pairwise_touch_order
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (quotaRun q u processing low).config.transcript.Pairwise
      (fun first second =>
        ∀ firstJob, observationTouchLabel? first = some firstJob →
        ∀ secondJob, observationTouchLabel? second = some secondJob →
          firstJob.val < secondJob.val) := by
  have hlabels :
      (quotaRun q u processing low).config.transcript.startedLabels.Pairwise
        (fun first second => first.val < second.val) := by
    rw [quotaRun_startedLabels_eq_ofFn hq u processing low,
      List.pairwise_ofFn]
    intro i j hij
    simpa using hij
  rw [Transcript.startedLabels_eq_filterMap_touchLabel,
    List.pairwise_filterMap] at hlabels
  exact hlabels

theorem quotaRun_touch_label_lt_of_before
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {before between after : Online.Transcript n}
    {first second : Online.Observation n}
    {firstJob secondJob : Online.Label n}
    (hdecomp :
      (quotaRun q u processing low).config.transcript =
        before ++ first :: between ++ second :: after)
    (hfirst : observationTouchLabel? first = some firstJob)
    (hsecond : observationTouchLabel? second = some secondJob) :
    firstJob.val < secondJob.val := by
  have hpw := quotaRun_pairwise_touch_order hq u processing low
  rw [hdecomp, List.pairwise_append] at hpw
  have hrel := hpw.2.2 first (by simp) second (by simp)
  exact hrel firstJob hfirst secondJob hsecond

theorem quotaStrategy_process_cases
    {n q : ℕ} {low : ℝ → Bool} {transcript : Online.Transcript n}
    {job : Online.Label n}
    (haction : quotaStrategy n q low transcript = some (.process job)) :
    safeLastLowPending? low transcript = some job ∨
      (safeLastLowPending? low transcript = none ∧
        q ≤ transcript.testResults.length ∧
        transcript.shortestRemaining? = some job) := by
  unfold quotaStrategy at haction
  cases hsafe : safeLastLowPending? low transcript with
  | some selected =>
      simp only [hsafe, Option.some.injEq] at haction
      apply Or.inl
      simpa using haction
  | none =>
      right
      refine ⟨rfl, ?_⟩
      by_cases htest : transcript.testResults.length < q
      · simp [hsafe, htest] at haction
      · refine ⟨Nat.le_of_not_gt htest, ?_⟩
        cases hshort : transcript.shortestRemaining? with
        | some selected =>
            simp [hsafe, htest, hshort] at haction
            simpa using haction
        | none =>
            simp [hsafe, htest, hshort] at haction

theorem quotaStrategy_test_implies_below_quota
    {n q : ℕ} {low : ℝ → Bool} {transcript : Online.Transcript n}
    {job : Online.Label n}
    (haction : quotaStrategy n q low transcript = some (.test job)) :
    transcript.testResults.length < q := by
  unfold quotaStrategy at haction
  cases hsafe : safeLastLowPending? low transcript <;>
    simp [hsafe] at haction
  split at haction
  next hlt => exact hlt
  next hnot =>
    split at haction <;> simp_all

theorem quotaStrategy_raw_implies_no_remaining
    {n q : ℕ} {low : ℝ → Bool} {transcript : Online.Transcript n}
    {job : Online.Label n}
    (haction : quotaStrategy n q low transcript = some (.raw job)) :
    q ≤ transcript.testResults.length ∧
      transcript.shortestRemaining? = none := by
  unfold quotaStrategy at haction
  cases hsafe : safeLastLowPending? low transcript <;>
    simp [hsafe] at haction
  split at haction
  next hlt => simp at haction
  next hnot =>
    constructor
    · omega
    · split at haction
      next selected hshort => simp at haction
      next hnone => exact hnone

theorem shortestRemaining_mem
    {transcript : Online.Transcript n} {job : Online.Label n}
    (hshort : transcript.shortestRemaining? = some job) :
    ∃ value, (job, value) ∈ transcript.remainingTestResults := by
  unfold Online.Transcript.shortestRemaining? at hshort
  cases hresult : Online.shortestResult? transcript.remainingTestResults with
  | none => simp [hresult] at hshort
  | some result =>
      have hjob : result.1 = job := by simpa [hresult] using hshort
      rcases result with ⟨label, value⟩
      change label = job at hjob
      subst label
      exact ⟨value, Online.shortestResult?_mem hresult⟩

def stableResultAtMost
    (chosen candidate : Online.Label n × ℝ) : Prop :=
  chosen.2 < candidate.2 ∨
    (chosen.2 = candidate.2 ∧ chosen.1.val ≤ candidate.1.val)

theorem stableResultAtMost_refl (result : Online.Label n × ℝ) :
    stableResultAtMost result result := by
  exact Or.inr ⟨rfl, le_rfl⟩

theorem stableResultAtMost_trans
    {first second third : Online.Label n × ℝ}
    (hfirst : stableResultAtMost first second)
    (hsecond : stableResultAtMost second third) :
    stableResultAtMost first third := by
  rcases hfirst with hlt | ⟨heq, hlabel⟩ <;>
    rcases hsecond with hlt' | ⟨heq', hlabel'⟩
  · exact Or.inl (lt_trans hlt hlt')
  · exact Or.inl (by simpa [heq'] using hlt)
  · exact Or.inl (by simpa [heq] using hlt')
  · exact Or.inr ⟨heq.trans heq', hlabel.trans hlabel'⟩

private theorem shortestFold_stable_minimal
    (best : Online.Label n × ℝ) (rest : List (Online.Label n × ℝ))
    (hbest : ∀ candidate ∈ rest, best.1.val < candidate.1.val)
    (hpair : rest.Pairwise
      (fun first second => first.1.val < second.1.val)) :
    let chosen := rest.foldl
      (fun current candidate =>
        if candidate.2 < current.2 then candidate else current) best
    stableResultAtMost chosen best ∧
      ∀ candidate ∈ rest, stableResultAtMost chosen candidate := by
  induction rest generalizing best with
  | nil => simp [stableResultAtMost_refl]
  | cons candidate rest ih =>
      rw [List.pairwise_cons] at hpair
      simp only [List.foldl_cons]
      by_cases hvalue : candidate.2 < best.2
      · rw [if_pos hvalue]
        have htail := ih candidate hpair.1 hpair.2
        constructor
        · exact stableResultAtMost_trans htail.1 (Or.inl hvalue)
        · intro other hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · exact htail.1
          · exact htail.2 other hrest
      · rw [if_neg hvalue]
        have hbestTail : ∀ other ∈ rest,
            best.1.val < other.1.val := by
          intro other hmem
          exact (hbest candidate (by simp)).trans (hpair.1 other hmem)
        have htail := ih best hbestTail hpair.2
        constructor
        · exact htail.1
        · intro other hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · apply stableResultAtMost_trans htail.1
            rcases lt_or_eq_of_le (le_of_not_gt hvalue) with hlt | heq
            · exact Or.inl hlt
            · exact Or.inr ⟨heq, (hbest other (by simp)).le⟩
          · exact htail.2 other hrest

theorem shortestResult_stableAtMost
    {results : List (Online.Label n × ℝ)}
    (hpair : results.Pairwise
      (fun first second => first.1.val < second.1.val))
    {chosen candidate : Online.Label n × ℝ}
    (hchosen : Online.shortestResult? results = some chosen)
    (hcandidate : candidate ∈ results) :
    stableResultAtMost chosen candidate := by
  cases results with
  | nil => simp [Online.shortestResult?] at hchosen
  | cons best rest =>
      rw [List.pairwise_cons] at hpair
      simp only [Online.shortestResult?, Option.some.injEq] at hchosen
      subst chosen
      have hminimal := shortestFold_stable_minimal best rest hpair.1 hpair.2
      rcases List.mem_cons.mp hcandidate with rfl | hrest
      · exact hminimal.1
      · exact hminimal.2 candidate hrest

theorem range_pairwise_lt (k : ℕ) :
    (List.range k).Pairwise (· < ·) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simpa [List.get_eq_getElem] using hij

theorem quotaRun_prefix_testsMatch
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {initial suffix : Online.Transcript n}
    (hfull : (quotaRun q u processing low).config.transcript =
      initial ++ suffix) :
    initial.TestsMatch processing := by
  intro job value hmem
  apply (quotaRun_completed hq u processing low).2.1.testsMatch job value
  apply (Online.testResult_mem_iff_observation_mem _ job value).mpr
  rw [hfull]
  exact List.mem_append_left _
    ((Online.testResult_mem_iff_observation_mem initial job value).mp hmem)

theorem quotaRun_prefix_remaining_pairwise
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {initial suffix : Online.Transcript n}
    (hfull : (quotaRun q u processing low).config.transcript =
      initial ++ suffix) :
    initial.remainingTestResults.Pairwise
      (fun first second => first.1.val < second.1.val) := by
  have hfinalPair :
      (quotaRun q u processing low).config.transcript.testResults.Pairwise
        (fun first second => first.1.val < second.1.val) := by
    rw [← List.pairwise_map]
    rw [(quotaRun_completed hq u processing low).2.1.testOrder]
    exact range_pairwise_lt _
  have hprefix : initial.testResults.Sublist
      (quotaRun q u processing low).config.transcript.testResults := by
    rw [hfull, Online.Transcript.testResults_append]
    exact List.sublist_append_left _ _
  exact (hfinalPair.sublist hprefix).filter _

theorem quotaRun_low_test_immediately_processed
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {before after : Online.Transcript n} {job : Online.Label n} {value : ℝ}
    {observation : Online.Observation n}
    (hdecomp :
      (quotaRun q u processing low).config.transcript =
        before ++ .testResult job value :: observation :: after)
    (hlow : low value = true) :
    observation = .processed job := by
  let current := before ++ [.testResult job value]
  have hfullTest : (job, value) ∈
      (quotaRun q u processing low).config.transcript.testResults :=
    (Online.testResult_mem_iff_observation_mem _ job value).mpr (by
      rw [hdecomp]
      simp)
  have hlt :=
    (Config.Invariant.testResult_mem_iff_val_lt_of_done hq
      (quotaRun_completed hq u processing low).2.1
        (quotaRun_completed hq u processing low).2.2 job).mp
      ⟨value, hfullTest⟩
  have hself :=
    Config.Invariant.selfProjection_eq_terminalWord hq
      (quotaRun_completed hq u processing low).2.1
        (quotaRun_completed hq u processing low).2.2 job
  rw [if_pos hlt] at hself
  have hvalue : value = processing job :=
    (quotaRun_completed hq u processing low).2.1.testsMatch job value hfullTest
  have hnotProcessed : job ∉ before.processedLabels := by
    intro hprocessed
    have hobservation : Online.Observation.processed job ∈ before :=
      (Online.processed_mem_iff_observation_mem before job).mp hprocessed
    obtain ⟨left, right, hbefore⟩ := List.mem_iff_append.mp hobservation
    have hsub : List.Sublist
        ([.processed job, .testResult job value] : Online.Transcript n)
          ((quotaRun q u processing low).config.transcript.pairProjection job job) := by
      rw [hdecomp, Online.Transcript.pairProjection_append,
        hbefore, Online.Transcript.pairProjection_append]
      have hprocessedProjection :
          Online.Transcript.pairProjection job job
              (.processed job :: right) =
            .processed job ::
              Online.Transcript.pairProjection job job right := by
        simp [Online.Transcript.pairProjection,
          Online.Observation.ownerLabel]
      have htestProjection :
          Online.Transcript.pairProjection job job
              (.testResult job value :: observation :: after) =
            .testResult job value ::
              Online.Transcript.pairProjection job job
                (observation :: after) := by
        simp [Online.Transcript.pairProjection,
          Online.Observation.ownerLabel]
      rw [hprocessedProjection, htestProjection]
      have htest : (List.Sublist
          ([.testResult job value] : Online.Transcript n)
          (Online.Transcript.pairProjection job job right ++
            .testResult job value ::
              Online.Transcript.pairProjection job job
                (observation :: after))) :=
        (List.Sublist.cons_cons _ (List.nil_sublist _)).trans
          (List.sublist_append_right
            (Online.Transcript.pairProjection job job right) _)
      have htail : (List.Sublist
          ([.processed job, .testResult job value] : Online.Transcript n)
            (.processed job ::
              (Online.Transcript.pairProjection job job right ++
                .testResult job value ::
                  Online.Transcript.pairProjection job job
                    (observation :: after)))) :=
        List.Sublist.cons_cons _ htest
      simpa [List.append_assoc] using htail.trans
        (List.sublist_append_right
          (Online.Transcript.pairProjection job job left) _)
    rw [hself] at hsub
    have heq := hsub.eq_of_length (by simp)
    simp [hvalue] at heq
  have hpending : (job, value) ∈ current.remainingTestResults := by
    apply List.mem_filter.mpr
    constructor
    · simp [current]
    · change decide (job ∉
          (before ++ [Online.Observation.testResult job value]).processedLabels) = true
      rw [decide_eq_true_eq,
        Online.Transcript.processedLabels_append_testResult]
      exact hnotProcessed
  have hlabelPending : job ∈ current.remainingTestResults.map Prod.fst :=
    List.mem_map.mpr ⟨(job, value), hpending, rfl⟩
  have hsafe : safeLastLowPending? low current = some job := by
    simp [safeLastLowPending?, current, hlow, hlabelPending]
  have hdecomp' :
      (quotaRun q u processing low).config.transcript =
        current ++ observation :: after := by
    simpa [current, List.append_assoc] using hdecomp
  have haction := (quotaRun_followsStrategy u processing low).action_at hdecomp'
  simp [quotaStrategy, hsafe, Online.Observation.requestedAction] at haction
  cases observation <;> simp_all [Online.Observation.requestedAction]

theorem quotaPrefix_pending_low_is_last
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {initial suffix : Online.Transcript n} {job : Online.Label n} {value : ℝ}
    (hfull :
      (quotaRun q u processing low).config.transcript = initial ++ suffix)
    (hpending : (job, value) ∈ initial.remainingTestResults)
    (hlow : low value = true) :
    initial.getLast? = some (.testResult job value) := by
  have hparts := List.mem_filter.mp hpending
  have htest : Online.Observation.testResult job value ∈ initial :=
    (Online.testResult_mem_iff_observation_mem initial job value).mp hparts.1
  obtain ⟨left, right, hinitial⟩ := List.mem_iff_append.mp htest
  cases right with
  | nil => simp [hinitial]
  | cons next rest =>
      have hdecomp :
          (quotaRun q u processing low).config.transcript =
            left ++ .testResult job value :: next :: (rest ++ suffix) := by
        rw [hfull, hinitial]
        simp [List.append_assoc]
      have hnext := quotaRun_low_test_immediately_processed hq u processing low
        hdecomp hlow
      subst next
      have hprocessed : job ∈ initial.processedLabels := by
        apply (Online.processed_mem_iff_observation_mem initial job).mpr
        rw [hinitial]
        simp
      have hnotProcessed : job ∉ initial.processedLabels := by
        simpa using hparts.2
      exact (hnotProcessed hprocessed).elim

theorem quotaRun_process_classification
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {before after : Online.Transcript n} {job : Online.Label n}
    (hdecomp :
      (quotaRun q u processing low).config.transcript =
        before ++ .processed job :: after) :
    (low (processing job) = true ∧
        before.getLast? = some (.testResult job (processing job))) ∨
      (low (processing job) = false ∧
        q ≤ before.testResults.length ∧
        before.shortestRemaining? = some job) := by
  have haction := (quotaRun_followsStrategy u processing low).action_at hdecomp
  simp only [Online.Observation.requestedAction] at haction
  rcases quotaStrategy_process_cases haction with hsafe | htail
  · left
    unfold safeLastLowPending? at hsafe
    cases hlast : before.getLast? with
    | none => simp [hlast] at hsafe
    | some observation =>
        rw [hlast] at hsafe
        cases observation with
        | testResult testedJob value =>
            have hfacts :
                (low value = true ∧ ∃ p,
                  (testedJob, p) ∈ before.remainingTestResults) ∧
                  testedJob = job := by
              simpa [hlast] using hsafe
            obtain ⟨⟨hl, _, _⟩, heq⟩ := hfacts
            subst testedJob
            have hvalue : value = processing job := by
              exact (quotaRun_completed hq u processing low).2.1.testsMatch job value
                  (by
                    apply (Online.testResult_mem_iff_observation_mem
                      _ job value).mpr
                    rw [hdecomp]
                    exact List.mem_append_left _
                      (List.mem_of_getLast? hlast))
            exact ⟨by simpa [hvalue] using hl, by simpa [hvalue] using hlast⟩
        | processed other => simp [hlast] at hsafe
        | rawCompleted other => simp [hlast] at hsafe
  · right
    rcases htail with ⟨hsafe, hquota, hshort⟩
    obtain ⟨value, hpending⟩ :=
      shortestRemaining_mem hshort
    have hvalue : value = processing job := by
      have htest := (List.mem_filter.mp hpending).1
      have hfullMatch := (quotaRun_completed hq u processing low).2.1.testsMatch
      apply hfullMatch job value
      apply (Online.testResult_mem_iff_observation_mem _ job value).mpr
      rw [hdecomp]
      exact List.mem_append_left _
        ((Online.testResult_mem_iff_observation_mem before job value).mp htest)
    have hnotLow : low value = false := by
      cases hl : low value with
      | false => rfl
      | true =>
          have hlast := quotaPrefix_pending_low_is_last hq u processing low
            (suffix := .processed job :: after) (by simpa using hdecomp)
            hpending hl
          unfold safeLastLowPending? at hsafe
          rw [hlast] at hsafe
          simp [hl, hpending] at hsafe
          exact (hsafe value hpending).elim
    exact ⟨by simpa [hvalue] using hnotLow, hquota, hshort⟩

theorem shortestRemaining_stableAtMost
    {processing : Online.Label n → ℝ}
    {transcript : Online.Transcript n}
    (hmatch : transcript.TestsMatch processing)
    (hpair : transcript.remainingTestResults.Pairwise
      (fun first second => first.1.val < second.1.val))
    {chosen candidate : Online.Label n} {value : ℝ}
    (hshort : transcript.shortestRemaining? = some chosen)
    (hcandidate : (candidate, value) ∈ transcript.remainingTestResults) :
    stableResultAtMost (chosen, processing chosen) (candidate, value) := by
  unfold Online.Transcript.shortestRemaining? at hshort
  cases hresult : Online.shortestResult? transcript.remainingTestResults with
  | none => simp [hresult] at hshort
  | some result =>
      have hlabel : result.1 = chosen := by simpa [hresult] using hshort
      have hmem := Online.shortestResult?_mem hresult
      have hvalue : result.2 = processing result.1 :=
        hmatch result.1 result.2 (List.mem_filter.mp hmem).1
      have hstable := shortestResult_stableAtMost hpair hresult hcandidate
      rcases result with ⟨label, resultValue⟩
      change label = chosen at hlabel
      change resultValue = processing label at hvalue
      subst label
      subst resultValue
      exact hstable

set_option maxHeartbeats 2000000 in
theorem quotaRun_adjacent_observations_le
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {before after : Online.Transcript n}
    {first second : Online.Observation n}
    (hdecomp :
      (quotaRun q u processing low).config.transcript =
        before ++ first :: second :: after) :
    quotaObservationLE processing low first second := by
  let current := before ++ [first]
  have hfirstAction :=
    (quotaRun_followsStrategy u processing low).action_at hdecomp
  have hsecondDecomp :
      (quotaRun q u processing low).config.transcript =
        current ++ second :: after := by
    simpa [current, List.append_assoc] using hdecomp
  have hsecondAction :=
    (quotaRun_followsStrategy u processing low).action_at hsecondDecomp
  cases first with
  | testResult firstJob firstValue =>
      cases second with
      | testResult secondJob secondValue =>
          have hlabel := quotaRun_touch_label_lt_of_before hq u processing low
            (before := before) (between := [])
            (first := Online.Observation.testResult firstJob firstValue)
            (second := Online.Observation.testResult secondJob secondValue)
            (firstJob := firstJob) (secondJob := secondJob)
            (by simpa using hdecomp) rfl rfl
          simp [quotaObservationLE, quotaObservationKey,
            Prod.lex_iff, hlabel]
      | rawCompleted secondJob =>
          simp [quotaObservationLE, quotaObservationKey, Prod.lex_iff]
      | processed secondJob =>
          rcases quotaRun_process_classification hq u processing low
              hsecondDecomp with hlow | htail
          · rcases hlow with ⟨hlow, hlast⟩
            have hsame : firstJob = secondJob ∧
                firstValue = processing secondJob := by
              simpa [current] using hlast
            rcases hsame with ⟨rfl, hvalue⟩
            simp [quotaObservationLE, quotaObservationKey,
              Prod.lex_iff, hlow]
          · rcases htail with ⟨hnotLow, _, _⟩
            simp [quotaObservationLE, quotaObservationKey,
              Prod.lex_iff, hnotLow]
  | processed firstJob =>
      have hfirstClass := quotaRun_process_classification hq u processing low
        (before := before) (after := second :: after) hdecomp
      cases second with
      | testResult secondJob secondValue =>
          rcases hfirstClass with hlow | htail
          · rcases hlow with ⟨hlow, hlast⟩
            have hbeforeEq :
                before.dropLast ++
                    [Online.Observation.testResult firstJob
                      (processing firstJob)] = before :=
              List.dropLast_append_getLast?
                (Online.Observation.testResult firstJob (processing firstJob))
                (by rw [hlast]; simp)
            have htouchDecomp :
                (quotaRun q u processing low).config.transcript =
                  before.dropLast ++
                    Online.Observation.testResult firstJob
                      (processing firstJob) ::
                    [.processed firstJob] ++
                    .testResult secondJob secondValue :: after := by
              calc
                _ = before ++ .processed firstJob ::
                      .testResult secondJob secondValue :: after := hdecomp
                _ = before.dropLast ++
                      .testResult firstJob (processing firstJob) ::
                      [.processed firstJob] ++
                      .testResult secondJob secondValue :: after := by
                    rw [← hbeforeEq]
                    simp [List.append_assoc]
            have hlabel := quotaRun_touch_label_lt_of_before hq u processing low
              (before := before.dropLast)
              (between := [.processed firstJob])
              (first := Online.Observation.testResult firstJob
                (processing firstJob))
              (second := Online.Observation.testResult secondJob secondValue)
              (firstJob := firstJob) (secondJob := secondJob)
              htouchDecomp rfl rfl
            simp [quotaObservationLE, quotaObservationKey,
              Prod.lex_iff, hlow, hlabel]
          · rcases htail with ⟨_, hquota, _⟩
            have hbelow := quotaStrategy_test_implies_below_quota
              (by simpa [Online.Observation.requestedAction] using hsecondAction)
            simp [current] at hbelow
            omega
      | rawCompleted secondJob =>
          rcases hfirstClass with hlow | htail
          · simp [quotaObservationLE, quotaObservationKey,
              Prod.lex_iff, hlow.1]
          · simp [quotaObservationLE, quotaObservationKey,
              Prod.lex_iff, htail.1]
      | processed secondJob =>
          have hsecondClass := quotaRun_process_classification hq u processing low
            hsecondDecomp
          rcases hfirstClass with hfirstLow | hfirstTail
          · rcases hfirstLow with ⟨hfirstLow, _⟩
            rcases hsecondClass with hsecondLow | hsecondTail
            · rcases hsecondLow with ⟨_, hlast⟩
              simp [current] at hlast
            · rcases hsecondTail with ⟨hsecondLow, _, _⟩
              simp [quotaObservationLE, quotaObservationKey,
                Prod.lex_iff, hfirstLow, hsecondLow]
          · rcases hfirstTail with
              ⟨hfirstLow, _, hfirstShort⟩
            rcases hsecondClass with hsecondLow | hsecondTail
            · rcases hsecondLow with ⟨_, hlast⟩
              simp [current] at hlast
            · rcases hsecondTail with
                ⟨hsecondLow, _, hsecondShort⟩
              obtain ⟨value, hpendingCurrent⟩ :=
                shortestRemaining_mem hsecondShort
              have hparts := List.mem_filter.mp hpendingCurrent
              have hnotCurrent : secondJob ∉ current.processedLabels := by
                simpa using hparts.2
              have hpendingBefore :
                  (secondJob, value) ∈ before.remainingTestResults := by
                apply List.mem_filter.mpr
                constructor
                · simpa [current] using hparts.1
                · rw [decide_eq_true_eq]
                  intro hprocessed
                  apply hnotCurrent
                  change secondJob ∈
                    (before ++ [Online.Observation.processed firstJob]).processedLabels
                  rw [Online.Transcript.processedLabels_append_processed]
                  exact List.mem_append_left _ hprocessed
              have hfullBefore :
                  (quotaRun q u processing low).config.transcript =
                    before ++ (.processed firstJob ::
                      .processed secondJob :: after) := by
                simpa using hdecomp
              have hstable := shortestRemaining_stableAtMost
                (quotaRun_prefix_testsMatch hq u processing low hfullBefore)
                (quotaRun_prefix_remaining_pairwise hq u processing low hfullBefore)
                hfirstShort hpendingBefore
              have hvalue : value = processing secondJob :=
                (quotaRun_prefix_testsMatch hq u processing low hfullBefore)
                  secondJob value (List.mem_filter.mp hpendingBefore).1
              rcases hstable with hlt | ⟨heq, hlabel⟩
              · simp [quotaObservationLE, quotaObservationKey,
                  Prod.lex_iff, hfirstLow, hsecondLow]
                exact Or.inl (by simpa [hvalue] using hlt)
              · change processing firstJob = value at heq
                rw [hvalue] at heq
                rcases lt_or_eq_of_le hlabel with hlabelLt | hlabelEq
                · simp [quotaObservationLE, quotaObservationKey,
                    Prod.lex_iff, hfirstLow, hsecondLow, heq]
                  exact Or.inl hlabelLt
                · simp [quotaObservationLE, quotaObservationKey,
                    Prod.lex_iff, hfirstLow, hsecondLow, heq]
                  exact Or.inr hlabelEq
  | rawCompleted firstJob =>
      have hfirstFacts := quotaStrategy_raw_implies_no_remaining
        (by simpa [Online.Observation.requestedAction] using hfirstAction)
      cases second with
      | testResult secondJob secondValue =>
          have hbelow := quotaStrategy_test_implies_below_quota
            (by simpa [Online.Observation.requestedAction] using hsecondAction)
          simp [current] at hbelow
          omega
      | rawCompleted secondJob =>
          have hlabel := quotaRun_touch_label_lt_of_before hq u processing low
            (before := before) (between := [])
            (first := Online.Observation.rawCompleted firstJob)
            (second := Online.Observation.rawCompleted secondJob)
            (firstJob := firstJob) (secondJob := secondJob)
            (by simpa using hdecomp) rfl rfl
          simp [quotaObservationLE, quotaObservationKey,
            Prod.lex_iff, hlabel]
      | processed secondJob =>
          rcases quotaRun_process_classification hq u processing low
              hsecondDecomp with hlow | htail
          · simp [current] at hlow
          · have hnone : current.shortestRemaining? = none := by
              have hremaining : current.remainingTestResults =
                  before.remainingTestResults := by
                unfold Online.Transcript.remainingTestResults
                change
                  (before ++ [Online.Observation.rawCompleted firstJob]).testResults.filter
                      (fun result => result.1 ∉
                        (before ++ [Online.Observation.rawCompleted firstJob]).processedLabels) =
                    before.testResults.filter
                      (fun result => result.1 ∉ before.processedLabels)
                rw [Online.Transcript.processedLabels_append_rawCompleted]
                rw [Online.Transcript.testResults_append]
                have hrawTests : Online.Transcript.testResults
                    ([Online.Observation.rawCompleted firstJob] :
                      Online.Transcript n) = [] := by rfl
                rw [hrawTests, List.append_nil]
              unfold Online.Transcript.shortestRemaining?
              rw [hremaining]
              exact hfirstFacts.2
            rw [hnone] at htail
            simp at htail

theorem quotaRun_pairwise_observation_order
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (quotaRun q u processing low).config.transcript.Pairwise
      (quotaObservationLE processing low) := by
  let relation := quotaObservationLE processing low
  letI : Trans relation relation relation :=
    ⟨fun hleft hright =>
      quotaObservationLE_trans processing low hleft hright⟩
  have hchain :
      (quotaRun q u processing low).config.transcript.IsChain relation := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro first second before after hdecomp
    exact quotaRun_adjacent_observations_le hq u processing low hdecomp
  exact hchain.pairwise

def quotaPairWord
    {n : ℕ} (q : ℕ) (processing : Fin n → ℝ) (low : ℝ → Bool)
    (left right : Fin n) : Online.Transcript n :=
  if right.val < q then testedPairWord processing low left right
  else if left.val < q then testedRawWord processing left right
  else rawPairWord left right

theorem quotaPairWord_pairwise
    {n q : ℕ} (processing : Fin n → ℝ) (low : ℝ → Bool)
    {left right : Fin n} (horder : left < right) :
    (quotaPairWord q processing low left right).Pairwise
      (quotaObservationLE processing low) := by
  by_cases hright : right.val < q
  · rw [quotaPairWord, if_pos hright]
    exact testedPairWord_pairwise processing low horder
  · rw [quotaPairWord, if_neg hright]
    by_cases hleft : left.val < q
    · rw [if_pos hleft]
      exact testedRawWord_pairwise processing low left right
    · rw [if_neg hleft]
      exact rawPairWord_pairwise processing low horder

set_option maxHeartbeats 1000000 in
theorem quotaPairWord_perm_self_append
    {n q : ℕ} (processing : Fin n → ℝ) (low : ℝ → Bool)
    {left right : Fin n} (horder : left < right) :
    (quotaPairWord q processing low left right).Perm
      ((if left.val < q then
          [.testResult left (processing left), .processed left]
        else [.rawCompleted left]) ++
       (if right.val < q then
          [.testResult right (processing right), .processed right]
        else [.rawCompleted right])) := by
  have hval : left.val < right.val := horder
  by_cases hright : right.val < q
  · have hleft : left.val < q := lt_trans hval hright
    cases hl : low (processing left) <;>
    cases hr : low (processing right) <;>
    simp [quotaPairWord, testedPairWord, hleft, hright, hl, hr] <;>
      (try split) <;> simp_all
    all_goals
      first
      | exact List.Perm.swap _ _ _
      | exact ((List.Perm.swap _ _ []).cons _).trans
          (List.Perm.swap _ _ _)
  · by_cases hleft : left.val < q
    · simp [quotaPairWord, testedRawWord, hleft, hright]
    · simp [quotaPairWord, rawPairWord, hleft, hright]

theorem quotaRun_pairProjection_perm_pairWord
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {left right : Fin n} (horder : left < right) :
    ((quotaRun q u processing low).config.transcript.pairProjection
      left right).Perm (quotaPairWord q processing low left right) := by
  have hne : left ≠ right := ne_of_lt horder
  have hactual := Online.Transcript.pairProjection_perm_self_append hne
    (quotaRun q u processing low).config.transcript
  rw [Config.Invariant.selfProjection_eq_terminalWord hq
      (quotaRun_completed hq u processing low).2.1
      (quotaRun_completed hq u processing low).2.2 left,
    Config.Invariant.selfProjection_eq_terminalWord hq
      (quotaRun_completed hq u processing low).2.1
      (quotaRun_completed hq u processing low).2.2 right] at hactual
  exact hactual.trans
    (quotaPairWord_perm_self_append processing low horder).symm

theorem quotaRun_pairProjection_eq_pairWord
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    {left right : Fin n} (horder : left < right) :
    (quotaRun q u processing low).config.transcript.pairProjection
      left right = quotaPairWord q processing low left right := by
  have hperm := quotaRun_pairProjection_perm_pairWord hq u processing low horder
  have hactual :=
    (quotaRun_pairwise_observation_order hq u processing low).filter
      (fun observation =>
        observation.ownerLabel = left ∨ observation.ownerLabel = right)
  have htarget := quotaPairWord_pairwise (q := q) processing low horder
  exact hperm.eq_of_pairwise
    (fun first second _ _ hfirst hsecond =>
      quotaObservationLE_antisymm processing low hfirst hsecond)
    hactual htarget

theorem quotaRun_projectionSpec
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    QuotaProjectionSpec q processing low
      (quotaRun q u processing low).config.transcript := by
  constructor
  · intro job
    exact Config.Invariant.selfProjection_eq_terminalWord hq
      (quotaRun_completed hq u processing low).2.1
      (quotaRun_completed hq u processing low).2.2 job
  · intro left right horder
    simpa [quotaPairWord] using
      quotaRun_pairProjection_eq_pairWord hq u processing low horder

/-- Exact operational identity between the executable quota policy and its
finite position kernel. -/
theorem quotaRun_completionCost_eq_quotaKernelCost
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) (hzero : low 0 = true) :
    Online.completionCost (.finite u) processing
        (quotaRun q u processing low).config.transcript =
      QuotaKernel.quotaKernelCost q u processing low (Equiv.refl (Fin n)) := by
  apply completionCost_eq_quotaKernelCost u processing low hzero
  · simpa [quotaRun] using quotaStrategy_completionLabels_perm
      hq u processing low
  · exact quotaRun_projectionSpec hq u processing low

end

end QuotaStrategy
end RevealingOptimization
end SchedulingPaper
