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

/-- The completed canonical run first touches the virtual labels in literal
`Fin` order. -/
theorem canonicalRun_startedLabels_eq_ofFn
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    (canonicalRun q processing low medium).config.transcript.startedLabels =
      List.ofFn id := by
  let result := canonicalRun q processing low medium
  have hcompleted := canonicalRun_completed hq processing low medium
  have horder := hcompleted.2.1.2.1.touchOrder
  have hlength : result.config.transcript.startedLabels.length = n :=
    hcompleted.2.1.1.startedLabels_length_eq_n_of_done hcompleted.2.2
  have hright : (List.ofFn id : List (Fin n)).map Fin.val = List.range n := by
    rw [List.map_ofFn]
    simp [List.ofFn_eq_pmap]
  apply (List.map_injective_iff.mpr Fin.val_injective)
  simpa [result, hlength, hright] using horder

theorem touchChoices_mem_test_iff
    {transcript : Transcript n} {job : Label n} :
    (job, TraceBijection.TouchKind.test) ∈ ObservedTrace.touchChoices transcript ↔
      ∃ value, Observation.testResult job value ∈ transcript := by
  induction transcript with
  | nil => simp [ObservedTrace.touchChoices]
  | cons observation rest ih =>
      cases observation <;> simp [ObservedTrace.touchChoices,
        ObservedTrace.observationTouchChoice?, ih] <;> aesop

theorem touchChoices_mem_blind_iff
    {transcript : Transcript n} {job : Label n} :
    (job, TraceBijection.TouchKind.blind) ∈ ObservedTrace.touchChoices transcript ↔
      ∃ value, Observation.blindCompleted job value ∈ transcript := by
  induction transcript with
  | nil => simp [ObservedTrace.touchChoices]
  | cons observation rest ih =>
      cases observation <;> simp [ObservedTrace.touchChoices,
        ObservedTrace.observationTouchChoice?, ih] <;> aesop

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

/-- Both the label and the test/blind kind of every first touch are fixed by
the virtual position and the integral quota. -/
theorem canonicalRun_touchChoices_eq
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    ObservedTrace.touchChoices
        (canonicalRun q processing low medium).config.transcript =
      List.ofFn fun job : Fin n =>
        (job, if job.val < q then TraceBijection.TouchKind.test
          else TraceBijection.TouchKind.blind) := by
  let choices := ObservedTrace.touchChoices
    (canonicalRun q processing low medium).config.transcript
  have hkind : ∀ choice ∈ choices,
      choice.2 = if choice.1.val < q then TraceBijection.TouchKind.test
        else TraceBijection.TouchKind.blind := by
    intro choice hmem
    rcases choice with ⟨job, kind⟩
    cases kind with
    | test =>
        have hobs := touchChoices_mem_test_iff.mp hmem
        obtain ⟨value, hvalue⟩ := hobs
        obtain ⟨before, after, hdecomp⟩ := List.mem_iff_append.mp hvalue
        have hlt := canonical_test_job_lt_quota hq processing low medium
          (by simpa [choices] using hdecomp)
        simp [hlt]
    | blind =>
        have hobs := touchChoices_mem_blind_iff.mp hmem
        obtain ⟨value, hvalue⟩ := hobs
        obtain ⟨before, after, hdecomp⟩ := List.mem_iff_append.mp hvalue
        have hge := canonical_blind_job_ge_quota hq processing low medium
          (by simpa [choices] using hdecomp)
        simp [Nat.not_lt_of_ge hge]
  calc
    choices = choices.map (fun choice =>
        (choice.1, if choice.1.val < q then TraceBijection.TouchKind.test
          else TraceBijection.TouchKind.blind)) := by
      symm
      calc
        choices.map (fun choice =>
            (choice.1, if choice.1.val < q then TraceBijection.TouchKind.test
              else TraceBijection.TouchKind.blind)) =
            choices.map id := by
          apply List.map_congr_left
          intro choice hmem
          apply Prod.ext
          · rfl
          · exact (hkind choice hmem).symm
        _ = choices := List.map_id _
    _ = (choices.map Prod.fst).map (fun job =>
        (job, if job.val < q then TraceBijection.TouchKind.test
          else TraceBijection.TouchKind.blind)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro choice _
      rfl
    _ = List.ofFn fun job : Fin n =>
        (job, if job.val < q then TraceBijection.TouchKind.test
          else TraceBijection.TouchKind.blind) := by
      rw [ObservedTrace.touchChoices_map_fst,
        canonicalRun_startedLabels_eq_ofFn hq processing low medium,
        List.map_ofFn]
      rfl

/-- In the physical transcript, any two first-touch observations that occur
in chronological order have strictly increasing virtual labels.  Processing
observations between them are ignored. -/
theorem canonicalRun_pairwise_touch_order
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    (canonicalRun q processing low medium).config.transcript.Pairwise
      (fun first second =>
        ∀ firstChoice,
          ObservedTrace.observationTouchChoice? first = some firstChoice →
        ∀ secondChoice,
          ObservedTrace.observationTouchChoice? second = some secondChoice →
          firstChoice.1.val < secondChoice.1.val) := by
  have hchoices :
      (ObservedTrace.touchChoices
        (canonicalRun q processing low medium).config.transcript).Pairwise
          (fun first second => first.1.val < second.1.val) := by
    rw [canonicalRun_touchChoices_eq hq processing low medium,
      List.pairwise_ofFn]
    intro i j hij
    simpa using hij
  rw [ObservedTrace.touchChoices_eq_filterMap,
    List.pairwise_filterMap] at hchoices
  exact hchoices

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

/-- The operational two-label projection already has exactly the multiset
of observations prescribed by the canonical four-block word.  The remaining
bridge is purely an ordering statement. -/
theorem canonicalRun_ownerProjection_perm_pairWordOrdered
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n} (hij : i.val < j.val) :
    ((canonicalRun q processing low medium).config.transcript.ownerProjection i j).Perm
      (canonicalPairWordOrdered q processing low medium i j) := by
  have hne : i ≠ j := Fin.ne_of_lt hij
  have hactual := Transcript.ownerProjection_perm_self_append hne
    (canonicalRun q processing low medium).config.transcript
  rw [canonicalRun_ownerProjection_eq_selfWord hq processing low medium i,
    canonicalRun_ownerProjection_eq_selfWord hq processing low medium j] at hactual
  exact hactual.trans
    (canonicalPairWordOrdered_perm_self_append processing low medium hij).symm

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
