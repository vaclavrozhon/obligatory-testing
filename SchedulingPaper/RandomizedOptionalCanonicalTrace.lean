import SchedulingPaper.RandomizedOptionalObservedPolicyAccounting
import SchedulingPaper.RandomizedOptionalObservedTrace
import SchedulingPaper.RandomizedOptionalCanonicalWord
import Mathlib.Tactic

/-!
# Operational trace of the canonical optional-testing policy

This file begins the final bridge from the executable strategy to the finite
kernel.  It identifies the test/blind cutoff in every completed canonical
run and, as a first exact projection result, proves the one-label word.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

open ObservedTrace

noncomputable section

def canonicalRun
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) : RunResult n :=
  run processing (canonicalStrategy n q low medium) (2 * n + 1)

theorem canonicalRun_completed
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    (canonicalRun q processing low medium).reason = .strategyStopped ∧
      (canonicalRun q processing low medium).config.CanonicalGood processing q ∧
      ∀ job, (canonicalRun q processing low medium).config.jobs job = .done := by
  simpa [canonicalRun] using
    run_canonicalStrategy_completed hq processing low medium

theorem canonicalRun_followsStrategy
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    (canonicalRun q processing low medium).config.transcript.FollowsStrategy
      (canonicalStrategy n q low medium) := by
  simpa [canonicalRun] using run_followsStrategy processing
    (canonicalStrategy n q low medium) (2 * n + 1)

theorem Transcript.testResults_length_le_startedLabels_length
    (transcript : Transcript n) :
    transcript.testResults.length ≤ transcript.startedLabels.length := by
  rw [Transcript.startedLabels, List.length_map]
  induction transcript with
  | nil => simp [Transcript.testResults, Transcript.revealedResults]
  | cons observation rest ih =>
      cases observation <;>
        simp [Transcript.testResults, Transcript.revealedResults, ih] <;>
        omega

/-- A displayed prefix of the settled canonical run is exactly the run with
fuel equal to that prefix's operation length, and therefore carries the
canonical invariant. -/
theorem canonicalPrefix_eq_run_and_good
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {observation : Observation n}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ observation :: after) :
    (run processing (canonicalStrategy n q low medium) before.length).config.transcript =
        before ∧
      Config.CanonicalGood processing q
        (run processing (canonicalStrategy n q low medium) before.length).config := by
  let full := (canonicalRun q processing low medium).config.transcript
  have hbeforeLength : before.length ≤ full.length := by
    dsimp [full]
    rw [hdecomp]
    simp
  have hfullLength : full.length ≤ 2 * n + 1 := by
    dsimp [full, canonicalRun]
    rw [ObservedTrace.run_transcript_eq_runWord]
    exact ObservedTrace.runWord_length_le_fuel _ _ _ _
  have hfuel : before.length ≤ 2 * n + 1 :=
    hbeforeLength.trans hfullLength
  have htake := ObservedTrace.run_transcript_eq_take_of_le_length
    processing (canonicalStrategy n q low medium) hfuel hbeforeLength
  have htakeBefore : full.take before.length = before := by
    dsimp [full]
    rw [hdecomp]
    simp
  constructor
  · exact htake.trans htakeBefore
  · exact run_canonicalGood hq processing low medium before.length

theorem canonical_test_job_lt_quota
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n} {value : ℝ}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ .testResult job value :: after) :
    job.val < q := by
  have hprefix := canonicalPrefix_eq_run_and_good hq processing low medium hdecomp
  have haction := (canonicalRun_followsStrategy processing low medium).action_at hdecomp
  simp only [Observation.requestedAction] at haction
  have hbelow := canonicalStrategy_test_implies_below_quota haction
  have hnext := canonicalStrategy_test_implies_nextTouch haction
  have hjobVal := (nextCanonicalTouch_some_iff.mp hnext).2
  have hbelowRun :
      List.length (Transcript.testResults
        (run processing (canonicalStrategy n q low medium) before.length).config.transcript) < q := by
    rw [hprefix.1]
    exact hbelow
  have hcount := hprefix.2.2.2.beforeQuota hbelowRun
  rw [hprefix.1] at hcount
  omega

theorem canonical_blind_job_ge_quota
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n} {value : ℝ}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ .blindCompleted job value :: after) :
    q ≤ job.val := by
  have hprefix := canonicalPrefix_eq_run_and_good hq processing low medium hdecomp
  have haction := (canonicalRun_followsStrategy processing low medium).action_at hdecomp
  simp only [Observation.requestedAction] at haction
  have hreached := canonicalStrategy_blind_implies_quota_reached haction
  have hnext := canonicalStrategy_blind_implies_nextTouch haction
  have hjobVal := (nextCanonicalTouch_some_iff.mp hnext).2
  have htestLe := before.testResults_length_le_startedLabels_length
  omega

/-- A revealed low job is literally the next operation of the canonical
run, not merely an eventually early job. -/
theorem canonical_low_test_immediately_processed
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n} {value : ℝ}
    {observation : Observation n}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ Observation.testResult job value :: observation :: after)
    (hlow : low value = true) :
    observation = Observation.processed job := by
  let touchPrefix : Transcript n :=
    before ++ [Observation.testResult job value]
  have hprefixLow : lastLowPending? low touchPrefix = some job := by
    simp [touchPrefix, lastLowPending?, hlow]
  have hchosen : canonicalStrategy n q low medium touchPrefix =
      some (.process job) :=
    canonicalStrategy_processes_last_low hprefixLow
  have hdecomp' :
      (canonicalRun q processing low medium).config.transcript =
        touchPrefix ++ observation :: after := by
    simpa [touchPrefix, List.append_assoc] using hdecomp
  have haction :=
    (canonicalRun_followsStrategy processing low medium).action_at hdecomp'
  rw [hchosen] at haction
  cases observation with
  | testResult other p => simp [Observation.requestedAction] at haction
  | processed other =>
      simp only [Observation.requestedAction, Option.some.injEq,
        Action.process.injEq] at haction
      subst other
      rfl
  | blindCompleted other p => simp [Observation.requestedAction] at haction

/-- The owner-only projection of a completed canonical run is precisely the
single-position word used by `canonicalSingleKernel`. -/
theorem canonicalRun_ownerProjection_eq_selfWord
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (job : Label n) :
    (canonicalRun q processing low medium).config.transcript.ownerProjection job job =
      canonicalSelfWord q processing job := by
  let result := canonicalRun q processing low medium
  have hdone := (canonicalRun_completed hq processing low medium).2.2 job
  have hinv := run_ownerProjectionInvariant processing
    (canonicalStrategy n q low medium) (2 * n + 1)
  have hshape := hinv.done job (by simpa [result, canonicalRun] using hdone)
  change result.config.transcript.ownerProjection job job = _
  by_cases ht : job.val < q
  · rw [canonicalSelfWord, if_pos ht]
    rcases hshape with hblind | htested
    · have hmemProjection :
          Observation.blindCompleted job (processing job) ∈
            result.config.transcript.ownerProjection job job := by
          have hblind' :
              result.config.transcript.ownerProjection job job =
                [.blindCompleted job (processing job)] := by
            simpa [result, canonicalRun] using hblind
          rw [hblind']
          simp
      have hmem := (List.mem_filter.mp hmemProjection).1
      obtain ⟨before, after, hdecomp⟩ := List.mem_iff_append.mp hmem
      have hge := canonical_blind_job_ge_quota hq processing low medium
        (by simpa [result] using hdecomp)
      omega
    · exact htested
  · rw [canonicalSelfWord, if_neg ht]
    rcases hshape with hblind | htested
    · exact hblind
    · have hmemProjection :
          Observation.testResult job (processing job) ∈
            result.config.transcript.ownerProjection job job := by
          have htested' :
              result.config.transcript.ownerProjection job job =
                [.testResult job (processing job), .processed job] := by
            simpa [result, canonicalRun] using htested
          rw [htested']
          simp
      have hmem := (List.mem_filter.mp hmemProjection).1
      obtain ⟨before, after, hdecomp⟩ := List.mem_iff_append.mp hmem
      have hlt := canonical_test_job_lt_quota hq processing low medium
        (by simpa [result] using hdecomp)
      exact (ht hlt).elim

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
