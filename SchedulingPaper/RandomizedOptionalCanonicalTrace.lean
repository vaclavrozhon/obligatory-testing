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

open Randomized ObservedTrace

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## A total phase order for canonical observations -/

/-- The lexicographic key of an operation in the canonical four-block word.
Discovery is ordered by virtual label with a test immediately before its low
completion; the two known-job blocks use SPT with virtual-label tie breaking;
and the blind block again uses virtual-label order. -/
def canonicalObservationKey
    {n : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) : Observation n → ℕ × (ℝ × (ℕ × ℝ))
  | .testResult job value => (0, (job.val, (0, value)))
  | .processed job =>
      if low (processing job) then (0, (job.val, (1, 0)))
      else if medium (processing job) then
        (1, (processing job, (job.val, 0)))
      else (3, (processing job, (job.val, 0)))
  | .blindCompleted job value => (2, (job.val, (0, value)))

/-- Lexicographic nondecreasing order on canonical observation keys. -/
def canonicalObservationLE
    {n : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (first second : Observation n) : Prop :=
  Prod.Lex (fun x y : ℕ => x < y)
    (Prod.Lex (fun x y : ℝ => x < y)
      (Prod.Lex (fun x y : ℕ => x < y) (fun x y : ℝ => x ≤ y)))
    (canonicalObservationKey processing low medium first)
    (canonicalObservationKey processing low medium second)

theorem canonicalObservationLE_trans
    {n : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    Transitive (canonicalObservationLE processing low medium) := by
  intro first second third hfirst hsecond
  unfold canonicalObservationLE at hfirst hsecond ⊢
  exact Prod.Lex.trans hfirst hsecond

theorem canonicalObservationKey_injective
    {n : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    Function.Injective (canonicalObservationKey processing low medium) := by
  intro first second heq
  cases first <;> cases second <;>
    simp only [canonicalObservationKey] at heq ⊢
  all_goals
    repeat' split at heq
    all_goals simp_all [Fin.ext_iff]

theorem canonicalObservationLE_antisymm
    {n : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {first second : Observation n}
    (hfirst : canonicalObservationLE processing low medium first second)
    (hsecond : canonicalObservationLE processing low medium second first) :
    first = second := by
  apply canonicalObservationKey_injective processing low medium
  unfold canonicalObservationLE at hfirst hsecond
  simp only [Prod.lex_iff] at hfirst hsecond
  rcases hfirst with hphase | ⟨hphase, hfirst⟩
  · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> omega
  · rcases hsecond with hreverse | ⟨hreverse, hsecond⟩
    · omega
    · apply Prod.ext hphase
      rcases hfirst with hvalue | ⟨hvalue, hfirst⟩
      · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> linarith
      · rcases hsecond with hreverse | ⟨hreverse, hsecond⟩
        · linarith
        · apply Prod.ext hvalue
          rcases hfirst with hlabel | ⟨hlabel, hpayload⟩
          · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> omega
          · rcases hsecond with hreverse | ⟨hreverse, hpayload'⟩
            · omega
            · apply Prod.ext hlabel
              exact le_antisymm hpayload hpayload'

set_option maxHeartbeats 2000000 in
/-- The explicit two-job word is sorted by the same total phase order used
by the executable policy. -/
theorem canonicalPairWordOrdered_pairwise
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n} (hij : i.val < j.val) :
    (canonicalPairWordOrdered q processing low medium i j).Pairwise
      (canonicalObservationLE processing low medium) := by
  by_cases hti : i.val < q
  · by_cases htj : j.val < q
    · have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
      have hqj : ¬q ≤ j.val := Nat.not_le_of_lt htj
      cases hli : low (processing i) <;>
      cases hmi : medium (processing i) <;>
      cases hlj : low (processing j) <;>
      cases hmj : medium (processing j) <;>
      simp [canonicalPairWordOrdered, canonicalTestLowWord,
        canonicalProcessPair, canonicalMediumEligible, canonicalHighEligible,
        canonicalBlindWord, canonicalObservationLE, canonicalObservationKey,
        hti, htj, hqi, hqj, hli, hmi, hlj, hmj, hij, Prod.lex_iff] <;>
        (try split) <;> simp_all [canonicalObservationLE,
          canonicalObservationKey, Prod.lex_iff]
      all_goals
        rcases lt_or_eq_of_le ‹processing i ≤ processing j› with hlt | heq
        · exact Or.inl hlt
        · simp [heq, hij]
    · have hqj : q ≤ j.val := Nat.le_of_not_gt htj
      have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
      cases hli : low (processing i) <;>
      cases hmi : medium (processing i) <;>
      cases hlj : low (processing j) <;>
      cases hmj : medium (processing j) <;>
      simp [canonicalPairWordOrdered, canonicalTestLowWord,
        canonicalProcessPair, canonicalMediumEligible, canonicalHighEligible,
        canonicalBlindWord, canonicalObservationLE, canonicalObservationKey,
        hti, htj, hqi, hqj, hli, hmi, hlj, hmj, hij, Prod.lex_iff] <;>
        (try split) <;> simp_all [Prod.lex_iff]
  · have hqi : q ≤ i.val := Nat.le_of_not_gt hti
    have hqj : q ≤ j.val := hqi.trans hij.le
    have htj : ¬j.val < q := Nat.not_lt_of_ge hqj
    simp [canonicalPairWordOrdered, canonicalTestLowWord,
      canonicalProcessPair, canonicalMediumEligible, canonicalHighEligible,
      canonicalBlindWord, canonicalObservationLE, canonicalObservationKey,
      hti, htj, hqi, hqj, hij, Prod.lex_iff]

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

theorem Transcript.mem_testResults_of_testResult_mem
    {transcript : Transcript n} {job : Label n} {value : ℝ}
    (hmem : Observation.testResult job value ∈ transcript) :
    (job, value) ∈ transcript.testResults := by
  induction transcript with
  | nil => simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult other otherValue =>
          simp only [List.mem_cons, Observation.testResult.injEq] at hmem
          simp only [Transcript.testResults, List.mem_cons]
          exact hmem.imp (by rintro ⟨rfl, rfl⟩; rfl) ih
      | processed other => exact ih (by simpa using hmem)
      | blindCompleted other otherValue => exact ih (by simpa using hmem)

theorem Transcript.mem_revealedResults_of_blindCompleted_mem
    {transcript : Transcript n} {job : Label n} {value : ℝ}
    (hmem : Observation.blindCompleted job value ∈ transcript) :
    (job, value) ∈ transcript.revealedResults := by
  induction transcript with
  | nil => simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult other otherValue =>
          exact List.mem_cons_of_mem _ (ih (by simpa using hmem))
      | processed other => exact ih (by simpa using hmem)
      | blindCompleted other otherValue =>
          simp only [List.mem_cons, Observation.blindCompleted.injEq] at hmem
          simp only [Transcript.revealedResults, List.mem_cons]
          exact hmem.imp (by rintro ⟨rfl, rfl⟩; rfl) ih

theorem canonicalRun_test_value_eq_processing
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n} {value : ℝ}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ .testResult job value :: after) :
    value = processing job := by
  have hmatch := (run_historyInvariant processing
    (canonicalStrategy n q low medium) (2 * n + 1)).revealsMatch
  apply hmatch job value
  have hd :
      (run processing (canonicalStrategy n q low medium)
        (2 * n + 1)).config.transcript =
        before ++ .testResult job value :: after := by
    simpa [canonicalRun] using hdecomp
  apply Transcript.mem_revealedResults_of_mem_testResults
  apply Transcript.mem_testResults_of_testResult_mem
  rw [hd]
  simp

theorem canonicalRun_blind_value_eq_processing
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n} {value : ℝ}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ .blindCompleted job value :: after) :
    value = processing job := by
  have hmatch := (run_historyInvariant processing
    (canonicalStrategy n q low medium) (2 * n + 1)).revealsMatch
  apply hmatch job value
  have hd :
      (run processing (canonicalStrategy n q low medium)
        (2 * n + 1)).config.transcript =
        before ++ .blindCompleted job value :: after := by
    simpa [canonicalRun] using hdecomp
  apply Transcript.mem_revealedResults_of_blindCompleted_mem
  rw [hd]
  simp

theorem Transcript.testResult_mem_of_mem_testResults
    {transcript : Transcript n} {job : Label n} {value : ℝ}
    (hmem : (job, value) ∈ transcript.testResults) :
    Observation.testResult job value ∈ transcript := by
  induction transcript with
  | nil => simp [Transcript.testResults] at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult other otherValue =>
          simp only [Transcript.testResults, List.mem_cons] at hmem ⊢
          rcases hmem with hsame | hrest
          · exact Or.inl (by cases hsame; rfl)
          · exact Or.inr (ih hrest)
      | processed other => exact List.mem_cons_of_mem _ (ih hmem)
      | blindCompleted other otherValue =>
          exact List.mem_cons_of_mem _ (ih hmem)

theorem Transcript.processed_mem_of_mem_processedLabels
    {transcript : Transcript n} {job : Label n}
    (hmem : job ∈ transcript.processedLabels) :
    Observation.processed job ∈ transcript := by
  induction transcript with
  | nil => simp [Transcript.processedLabels] at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult other value => exact List.mem_cons_of_mem _ (ih hmem)
      | processed other =>
          simp only [Transcript.processedLabels, List.mem_cons] at hmem ⊢
          exact hmem.imp (by rintro rfl; rfl) ih
      | blindCompleted other value => exact List.mem_cons_of_mem _ (ih hmem)

theorem Transcript.mem_processedLabels_of_processed_mem
    {transcript : Transcript n} {job : Label n}
    (hmem : Observation.processed job ∈ transcript) :
    job ∈ transcript.processedLabels := by
  induction transcript with
  | nil => simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult other value =>
          exact ih (by simpa using hmem)
      | processed other =>
          simp only [List.mem_cons, Observation.processed.injEq] at hmem
          simp only [Transcript.processedLabels, List.mem_cons]
          exact hmem.imp id ih
      | blindCompleted other value =>
          exact ih (by simpa using hmem)

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

theorem canonical_touch_label_lt_of_before
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before between after : Transcript n}
    {first second : Observation n}
    {firstChoice secondChoice : Label n × TraceBijection.TouchKind}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ first :: between ++ second :: after)
    (hfirst : ObservedTrace.observationTouchChoice? first = some firstChoice)
    (hsecond : ObservedTrace.observationTouchChoice? second = some secondChoice) :
    firstChoice.1.val < secondChoice.1.val := by
  have hpw := canonicalRun_pairwise_touch_order hq processing low medium
  rw [hdecomp, List.pairwise_append] at hpw
  have hrel := hpw.2.2 first (by simp) second (by simp)
  exact hrel firstChoice hfirst secondChoice hsecond

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

/-- In every canonical prefix, a revealed low result can be pending only as
the last observation.  This is the trace form of "low outcomes are processed
immediately" and rules out a stale low job in a later phase. -/
theorem canonicalPrefix_pending_low_is_last
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {initial suffix : Transcript n} {job : Label n} {value : ℝ}
    (hfull :
      (canonicalRun q processing low medium).config.transcript =
        initial ++ suffix)
    (hpending : (job, value) ∈ initial.remainingTestResults)
    (hlow : low value = true) :
    initial.getLast? = some (.testResult job value) := by
  have hfiltered := List.mem_filter.mp hpending
  have htestMem : Observation.testResult job value ∈ initial :=
    Transcript.testResult_mem_of_mem_testResults hfiltered.1
  obtain ⟨left, right, hinitial⟩ := List.mem_iff_append.mp htestMem
  cases right with
  | nil => simp [hinitial]
  | cons next rest =>
      have hdecomp :
          (canonicalRun q processing low medium).config.transcript =
            left ++ .testResult job value :: next :: (rest ++ suffix) := by
        rw [hfull, hinitial]
        simp [List.append_assoc]
      have hnext := canonical_low_test_immediately_processed processing
        low medium hdecomp hlow
      subst next
      have hprocessed : job ∈ initial.processedLabels := by
        apply Transcript.mem_processedLabels_of_processed_mem
        rw [hinitial]
        simp
      have hnot : job ∉ initial.processedLabels := by
        simpa using hfiltered.2
      exact (hnot hprocessed).elim

theorem canonicalPrefix_pending_value_eq_processing
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {initial suffix : Transcript n} {job : Label n} {value : ℝ}
    (hfull :
      (canonicalRun q processing low medium).config.transcript =
        initial ++ suffix)
    (hpending : (job, value) ∈ initial.remainingTestResults) :
    value = processing job := by
  have htest := (List.mem_filter.mp hpending).1
  have hobs : Observation.testResult job value ∈
      (canonicalRun q processing low medium).config.transcript := by
    rw [hfull]
    exact List.mem_append_left suffix
      (Transcript.testResult_mem_of_mem_testResults htest)
  obtain ⟨before, after, hdecomp⟩ := List.mem_iff_append.mp hobs
  exact canonicalRun_test_value_eq_processing processing low medium hdecomp

/-- Every physical processing operation of the canonical run is certified
as exactly one of its low, medium, or high branches.  For medium and high we
also retain the precise SPT-selector equation used at that prefix. -/
theorem canonical_process_classification
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {job : Label n}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ .processed job :: after) :
    (low (processing job) = true ∧
        before.getLast? =
          some (.testResult job (processing job))) ∨
      (low (processing job) = false ∧
        medium (processing job) = true ∧
        q ≤ before.testResults.length ∧
        shortestResult? (classRemainingResults medium before) =
          some (job, processing job)) ∨
      (low (processing job) = false ∧
        medium (processing job) = false ∧
        q ≤ before.testResults.length ∧
        shortestClassPending? medium before = none ∧
        nextCanonicalTouch? n before = none ∧
        shortestResult? before.remainingTestResults =
          some (job, processing job)) := by
  have haction :=
    (canonicalRun_followsStrategy processing low medium).action_at hdecomp
  simp only [Observation.requestedAction] at haction
  rcases canonicalStrategy_process_cases haction with
      hlow | hmedium | htail
  · unfold lastLowPending? at hlow
    cases hlast : before.getLast? with
    | none => simp [hlast] at hlow
    | some observation =>
        rw [hlast] at hlow
        cases observation with
        | testResult testedJob value =>
            cases hl : low value <;> simp [hl] at hlow
            subst testedJob
            have hvalue : value = processing job := by
              have hobs : Observation.testResult job value ∈
                  (canonicalRun q processing low medium).config.transcript := by
                rw [hdecomp]
                exact List.mem_append_left _
                  (List.mem_of_mem_getLast? (by simp [hlast]))
              obtain ⟨left, right, htest⟩ := List.mem_iff_append.mp hobs
              exact canonicalRun_test_value_eq_processing processing
                low medium htest
            exact Or.inl ⟨by simpa [hvalue] using hl, by
              simpa [hvalue] using hlast⟩
        | processed other => simp [hlast] at hlow
        | blindCompleted other value => simp [hlast] at hlow
  · rcases hmedium with ⟨hlastNone, hquota, hshort⟩
    obtain ⟨value, hselected, hpending, hclass⟩ :=
      shortestClassPending?_spec hshort
    have hvalue := canonicalPrefix_pending_value_eq_processing processing
      low medium (suffix := .processed job :: after)
      (by simpa using hdecomp) hpending
    have hnotLow : low value = false := by
      cases hl : low value with
      | false => rfl
      | true =>
          have hlast := canonicalPrefix_pending_low_is_last processing
            low medium (suffix := .processed job :: after)
            (by simpa using hdecomp) hpending hl
          unfold lastLowPending? at hlastNone
          rw [hlast] at hlastNone
          simp [hl] at hlastNone
    exact Or.inr (Or.inl ⟨by simpa [hvalue] using hnotLow,
      by simpa [hvalue] using hclass, hquota,
      by simpa [hvalue] using hselected⟩)
  · rcases htail with
      ⟨hlastNone, hquota, hmediumNone, hnextNone, value, hselected⟩
    have hpending := shortestResult?_mem hselected
    have hvalue := canonicalPrefix_pending_value_eq_processing processing
      low medium (suffix := .processed job :: after)
      (by simpa using hdecomp) hpending
    have hnotLow : low value = false := by
      cases hl : low value with
      | false => rfl
      | true =>
          have hlast := canonicalPrefix_pending_low_is_last processing
            low medium (suffix := .processed job :: after)
            (by simpa using hdecomp) hpending hl
          unfold lastLowPending? at hlastNone
          rw [hlast] at hlastNone
          simp [hl] at hlastNone
    have hnotMedium : medium value = false := by
      cases hm : medium value with
      | false => rfl
      | true =>
          have hclassMem : (job, value) ∈
              classRemainingResults medium before :=
            List.mem_filter.mpr ⟨hpending, by simpa using hm⟩
          exact (shortestClassPending?_ne_none_of_mem hclassMem
            hmediumNone).elim
    exact Or.inr (Or.inr ⟨by simpa [hvalue] using hnotLow,
      by simpa [hvalue] using hnotMedium, hquota, hmediumNone,
      hnextNone, by simpa [hvalue] using hselected⟩)

set_option maxHeartbeats 2000000 in
/-- Consecutive physical operations of the canonical run respect the total
four-phase order.  The nontrivial cases are consecutive medium or high
processing operations; there the statement is exactly the lexicographic SPT
minimality of `shortestResult?`. -/
theorem canonical_adjacent_observations_le
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    {before after : Transcript n} {first second : Observation n}
    (hdecomp :
      (canonicalRun q processing low medium).config.transcript =
        before ++ first :: second :: after) :
    canonicalObservationLE processing low medium first second := by
  let current := before ++ [first]
  have hfirstAction :=
    (canonicalRun_followsStrategy processing low medium).action_at
      (before := before) (after := second :: after) hdecomp
  have hsecondDecomp :
      (canonicalRun q processing low medium).config.transcript =
        current ++ second :: after := by
    simpa [current, List.append_assoc] using hdecomp
  have hsecondAction :=
    (canonicalRun_followsStrategy processing low medium).action_at
      hsecondDecomp
  cases first with
  | testResult firstJob firstValue =>
      cases second with
      | testResult secondJob secondValue =>
          have hlabel := canonical_touch_label_lt_of_before hq processing
            low medium (before := before) (between := [])
            (first := Observation.testResult firstJob firstValue)
            (second := Observation.testResult secondJob secondValue)
            (firstChoice := (firstJob, .test))
            (secondChoice := (secondJob, .test)) (by simpa using hdecomp)
            rfl rfl
          simp [canonicalObservationLE, canonicalObservationKey,
            Prod.lex_iff, hlabel]
      | blindCompleted secondJob secondValue =>
          simp [canonicalObservationLE, canonicalObservationKey, Prod.lex_iff]
      | processed secondJob =>
          rcases canonical_process_classification processing low medium
              hsecondDecomp with hlow | hmedium | hhigh
          · rcases hlow with ⟨hlow, hlast⟩
            have hsame : firstJob = secondJob ∧
                firstValue = processing secondJob := by
              simpa [current] using hlast
            rcases hsame with ⟨rfl, hvalue⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow]
          · rcases hmedium with ⟨hlow, hmedium, _, _⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow, hmedium]
          · rcases hhigh with ⟨hlow, hmedium, _, _, _, _⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow, hmedium]
  | processed firstJob =>
      have hfirstClass := canonical_process_classification processing
        low medium (before := before) (after := second :: after) hdecomp
      cases second with
      | testResult secondJob secondValue =>
          rcases hfirstClass with hlow | hmedium | hhigh
          · rcases hlow with ⟨hlow, hlast⟩
            have hbeforeEq :
                before.dropLast ++
                    [Observation.testResult firstJob (processing firstJob)] =
                  before :=
              List.dropLast_append_getLast?
                (Observation.testResult firstJob (processing firstJob))
                (by rw [hlast]; simp)
            have htouchDecomp :
                (canonicalRun q processing low medium).config.transcript =
                  before.dropLast ++
                    .testResult firstJob (processing firstJob) ::
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
            have hlabel := canonical_touch_label_lt_of_before hq processing
              low medium (before := before.dropLast)
              (between := [.processed firstJob])
              (first := Observation.testResult firstJob
                (processing firstJob))
              (second := Observation.testResult secondJob secondValue)
              (firstChoice := (firstJob, .test))
              (secondChoice := (secondJob, .test)) htouchDecomp rfl rfl
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow, hlabel]
          · rcases hmedium with ⟨_, _, hquota, _⟩
            have hbelow := canonicalStrategy_test_implies_below_quota
              (by simpa [Observation.requestedAction] using hsecondAction)
            simp [current] at hbelow
            omega
          · rcases hhigh with ⟨_, _, hquota, _, _, _⟩
            have hbelow := canonicalStrategy_test_implies_below_quota
              (by simpa [Observation.requestedAction] using hsecondAction)
            simp [current] at hbelow
            omega
      | blindCompleted secondJob secondValue =>
          rcases hfirstClass with hlow | hmedium | hhigh
          · rcases hlow with ⟨hlow, _⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow]
          · rcases hmedium with ⟨hlow, hmedium, _, _⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hlow, hmedium]
          · rcases hhigh with ⟨_, _, _, _, hnextNone, _⟩
            have hnext := canonicalStrategy_blind_implies_nextTouch
              (by simpa [Observation.requestedAction] using hsecondAction)
            have : nextCanonicalTouch? n current = none := by
              unfold nextCanonicalTouch? at hnextNone ⊢
              simpa [current] using hnextNone
            rw [this] at hnext
            contradiction
      | processed secondJob =>
          have hsecondClass := canonical_process_classification processing
            low medium hsecondDecomp
          rcases hfirstClass with hfirstLow | hfirstMedium | hfirstHigh
          · rcases hfirstLow with ⟨hfirstLow, _⟩
            rcases hsecondClass with hsecondLow | hsecondMedium | hsecondHigh
            · rcases hsecondLow with ⟨_, hlast⟩
              simp [current] at hlast
            · rcases hsecondMedium with ⟨hsecondLow, hsecondMedium, _, _⟩
              simp [canonicalObservationLE, canonicalObservationKey,
                Prod.lex_iff, hfirstLow, hsecondLow, hsecondMedium]
            · rcases hsecondHigh with ⟨hsecondLow, hsecondMedium, _, _, _, _⟩
              simp [canonicalObservationLE, canonicalObservationKey,
                Prod.lex_iff, hfirstLow, hsecondLow, hsecondMedium]
          · rcases hfirstMedium with
              ⟨hfirstLow, hfirstMedium, _, hfirstSelected⟩
            rcases hsecondClass with hsecondLow | hsecondMedium | hsecondHigh
            · rcases hsecondLow with ⟨_, hlast⟩
              simp [current] at hlast
            · rcases hsecondMedium with
                ⟨hsecondLow, hsecondMedium, _, hsecondSelected⟩
              have hcandidateNow := shortestResult?_mem hsecondSelected
              have hcandidateBefore :=
                classRemainingResults_append_process_subset medium before
                  firstJob (secondJob, processing secondJob) hcandidateNow
              have horder := shortestResult?_resultAtMost hfirstSelected
                hcandidateBefore
              rcases horder with hlt | ⟨heq, hlabel⟩
              · simp [canonicalObservationLE, canonicalObservationKey,
                  Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                  hsecondMedium, hlt]
              · change processing firstJob = processing secondJob at heq
                change firstJob.val ≤ secondJob.val at hlabel
                rcases lt_or_eq_of_le hlabel with hlabelLt | hlabelEq
                · simp [canonicalObservationLE, canonicalObservationKey,
                    Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                    hsecondMedium, heq, hlabelLt]
                · simp [canonicalObservationLE, canonicalObservationKey,
                    Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                    hsecondMedium, heq, hlabelEq]
            · rcases hsecondHigh with
                ⟨hsecondLow, hsecondMedium, _, _, _, _⟩
              simp [canonicalObservationLE, canonicalObservationKey,
                Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                hsecondMedium]
          · rcases hfirstHigh with
              ⟨hfirstLow, hfirstMedium, _, hnoMedium, _, hfirstSelected⟩
            rcases hsecondClass with hsecondLow | hsecondMedium | hsecondHigh
            · rcases hsecondLow with ⟨_, hlast⟩
              simp [current] at hlast
            · rcases hsecondMedium with
                ⟨_, _, _, hsecondSelected⟩
              have hcandidateNow := shortestResult?_mem hsecondSelected
              have hcandidateBefore :=
                classRemainingResults_append_process_subset medium before
                  firstJob (secondJob, processing secondJob) hcandidateNow
              exact (shortestClassPending?_ne_none_of_mem hcandidateBefore
                hnoMedium).elim
            · rcases hsecondHigh with
                ⟨hsecondLow, hsecondMedium, _, _, _, hsecondSelected⟩
              have hcandidateNow := shortestResult?_mem hsecondSelected
              have hcandidateBefore :=
                remainingTestResults_append_process_subset before firstJob
                  (secondJob, processing secondJob) hcandidateNow
              have horder := shortestResult?_resultAtMost hfirstSelected
                hcandidateBefore
              rcases horder with hlt | ⟨heq, hlabel⟩
              · simp [canonicalObservationLE, canonicalObservationKey,
                  Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                  hsecondMedium, hlt]
              · change processing firstJob = processing secondJob at heq
                change firstJob.val ≤ secondJob.val at hlabel
                rcases lt_or_eq_of_le hlabel with hlabelLt | hlabelEq
                · simp [canonicalObservationLE, canonicalObservationKey,
                    Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                    hsecondMedium, heq, hlabelLt]
                · simp [canonicalObservationLE, canonicalObservationKey,
                    Prod.lex_iff, hfirstLow, hfirstMedium, hsecondLow,
                    hsecondMedium, heq, hlabelEq]
  | blindCompleted firstJob firstValue =>
      have hquota := canonicalStrategy_blind_implies_quota_reached
        (by simpa [Observation.requestedAction] using hfirstAction)
      have hnoMedium := canonicalStrategy_blind_implies_no_medium
        (by simpa [Observation.requestedAction] using hfirstAction)
      cases second with
      | testResult secondJob secondValue =>
          have hbelow := canonicalStrategy_test_implies_below_quota
            (by simpa [Observation.requestedAction] using hsecondAction)
          simp [current] at hbelow
          omega
      | blindCompleted secondJob secondValue =>
          have hlabel := canonical_touch_label_lt_of_before hq processing
            low medium (before := before) (between := [])
            (first := Observation.blindCompleted firstJob firstValue)
            (second := Observation.blindCompleted secondJob secondValue)
            (firstChoice := (firstJob, .blind))
            (secondChoice := (secondJob, .blind)) (by simpa using hdecomp)
            rfl rfl
          simp [canonicalObservationLE, canonicalObservationKey,
            Prod.lex_iff, hlabel]
      | processed secondJob =>
          rcases canonical_process_classification processing low medium
              hsecondDecomp with hsecondLow | hsecondMedium | hsecondHigh
          · rcases hsecondLow with ⟨_, hlast⟩
            simp [current] at hlast
          · rcases hsecondMedium with ⟨_, _, _, hselected⟩
            have hcandidate : (secondJob, processing secondJob) ∈
                classRemainingResults medium before := by
              have hmem := shortestResult?_mem hselected
              simpa [current, classRemainingResults,
                Transcript.remainingTestResults] using hmem
            exact (shortestClassPending?_ne_none_of_mem hcandidate
              hnoMedium).elim
          · rcases hsecondHigh with ⟨hsecondLow, hsecondMedium, _, _, _, _⟩
            simp [canonicalObservationLE, canonicalObservationKey,
              Prod.lex_iff, hsecondLow, hsecondMedium]

/-- The complete physical transcript is globally sorted by the canonical
phase/SPT key. -/
theorem canonicalRun_pairwise_observation_order
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) :
    (canonicalRun q processing low medium).config.transcript.Pairwise
      (canonicalObservationLE processing low medium) := by
  let relation := canonicalObservationLE processing low medium
  letI : Trans relation relation relation :=
    ⟨fun hleft hright =>
      canonicalObservationLE_trans processing low medium hleft hright⟩
  have hchain :
      (canonicalRun q processing low medium).config.transcript.IsChain
        relation := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro first second before after hdecomp
    exact canonical_adjacent_observations_le hq processing low medium hdecomp
  exact hchain.pairwise

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

/-- The operational two-label projection is exactly, not only up to
permutation, the explicit word used in the finite pair kernel. -/
theorem canonicalRun_ownerProjection_eq_pairWordOrdered
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n} (hij : i.val < j.val) :
    (canonicalRun q processing low medium).config.transcript.ownerProjection i j =
      canonicalPairWordOrdered q processing low medium i j := by
  have hperm := canonicalRun_ownerProjection_perm_pairWordOrdered hq
    processing low medium hij
  have hactual :=
    (canonicalRun_pairwise_observation_order hq processing low medium).filter
      (fun observation =>
        observation.ownerLabel = i ∨ observation.ownerLabel = j)
  have htarget :
      (canonicalPairWordOrdered q processing low medium i j).Pairwise
        (canonicalObservationLE processing low medium) :=
    canonicalPairWordOrdered_pairwise processing low medium hij
  exact hperm.eq_of_pairwise
    (fun first second _ _ hfirst hsecond =>
      canonicalObservationLE_antisymm processing low medium hfirst hsecond)
    hactual htarget

/-! ## Exact operational cost identity -/

private theorem sum_eq_of_swap_add_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (f g : OrderedDistinct α → ℝ)
    (hpair : ∀ z,
      f z + f (swapOrderedDistinct z) =
        g z + g (swapOrderedDistinct z)) :
    (∑ z, f z) = ∑ z, g z := by
  have hf :
      (∑ z, f (swapOrderedDistinct z)) = ∑ z, f z := by
    simpa using Equiv.sum_comp (swapOrderedDistinct (α := α)) f
  have hg :
      (∑ z, g (swapOrderedDistinct z)) = ∑ z, g z := by
    simpa using Equiv.sum_comp (swapOrderedDistinct (α := α)) g
  have hsum :
      (∑ z, f z) + ∑ z, f (swapOrderedDistinct z) =
        (∑ z, g z) + ∑ z, g (swapOrderedDistinct z) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => hpair z
  linarith

private theorem Transcript.ownerProjection_comm
    (transcript : Transcript n) (left right : Label n) :
    transcript.ownerProjection left right =
      transcript.ownerProjection right left := by
  unfold Transcript.ownerProjection
  apply List.filter_congr
  intro observation _
  simp [or_comm]

private theorem canonicalRun_oriented_sum_eq_pairKernel_sum
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true) :
    (∑ z : OrderedDistinct (Label n),
      observedTraceOrientedCharge processing
        (canonicalRun q processing low medium).config.transcript
        z.val.1 z.val.2) =
      ∑ z : OrderedDistinct (Fin n),
        canonicalPairKernel q processing low medium (canonicalHigh low medium)
          z z.val.1 z.val.2 := by
  let transcript := (canonicalRun q processing low medium).config.transcript
  let actual : OrderedDistinct (Fin n) → ℝ := fun z =>
    observedTraceOrientedCharge processing transcript z.val.1 z.val.2
  let kernel : OrderedDistinct (Fin n) → ℝ := fun z =>
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
      z z.val.1 z.val.2
  change (∑ z, actual z) = ∑ z, kernel z
  apply sum_eq_of_swap_add_eq actual kernel
  rintro ⟨⟨i, j⟩, hne⟩
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij | hji
  · have hleft :
        actual ⟨(i, j), hne⟩ =
          observedTraceOrientedCharge processing
            (canonicalPairWordOrdered q processing low medium i j) i j := by
      unfold actual observedTraceOrientedCharge transcript
      rw [← ownedDurationUntilCompletion_ownerProjection processing i j,
        canonicalRun_ownerProjection_eq_pairWordOrdered hq processing low medium hij]
    have hright :
        actual (swapOrderedDistinct ⟨(i, j), hne⟩) =
          observedTraceOrientedCharge processing
            (canonicalPairWordOrdered q processing low medium i j) j i := by
      unfold actual observedTraceOrientedCharge transcript swapOrderedDistinct
      change ownedDurationUntilCompletion processing i j
          (canonicalRun q processing low medium).config.transcript = _
      rw [← ownedDurationUntilCompletion_ownerProjection processing j i,
        Transcript.ownerProjection_comm _ j i,
        canonicalRun_ownerProjection_eq_pairWordOrdered hq processing low medium hij]
    have hkernel := canonicalPairKernel_symm_eq_pairWordCharges_ordered
      (q := q) processing low medium hdisjoint hzeroLow hij
    rw [hleft, hright]
    simpa [kernel, swapOrderedDistinct] using hkernel.symm
  · have hleft :
        actual ⟨(i, j), hne⟩ =
          observedTraceOrientedCharge processing
            (canonicalPairWordOrdered q processing low medium j i) i j := by
      unfold actual observedTraceOrientedCharge transcript
      rw [← ownedDurationUntilCompletion_ownerProjection processing i j,
        Transcript.ownerProjection_comm _ i j,
        canonicalRun_ownerProjection_eq_pairWordOrdered hq processing low medium hji]
    have hright :
        actual (swapOrderedDistinct ⟨(i, j), hne⟩) =
          observedTraceOrientedCharge processing
            (canonicalPairWordOrdered q processing low medium j i) j i := by
      unfold actual observedTraceOrientedCharge transcript swapOrderedDistinct
      change ownedDurationUntilCompletion processing i j
          (canonicalRun q processing low medium).config.transcript = _
      rw [← ownedDurationUntilCompletion_ownerProjection processing j i,
        canonicalRun_ownerProjection_eq_pairWordOrdered hq processing low medium hji]
    have hkernel := canonicalPairKernel_symm_eq_pairWordCharges_ordered
      (q := q) processing low medium hdisjoint hzeroLow hji
    rw [hleft, hright]
    simpa [kernel, swapOrderedDistinct, add_comm] using hkernel.symm

/-- The executable canonical policy has exactly the finite kernel cost,
before taking expectations or making an asymptotic approximation. -/
theorem canonicalRun_completionCost_eq_kernel
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true) :
    completionCost processing
        (canonicalRun q processing low medium).config.transcript =
      canonicalKernelCost q processing low medium (canonicalHigh low medium)
        (Equiv.refl (Fin n)) := by
  let transcript := (canonicalRun q processing low medium).config.transcript
  have hperm :
      (Transcript.completionLabels processing transcript).Perm
        (List.ofFn id) := by
    apply run_completionLabels_perm_of_done processing
      (canonicalStrategy n q low medium) (2 * n + 1)
    intro job
    exact (canonicalRun_completed hq processing low medium).2.2 job
  rw [completionCost_eq_self_add_orderedDistinct processing transcript hperm]
  unfold canonicalKernelCost positionKernelCost
  simp only [Equiv.refl_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro job _
    unfold observedTraceSelfCharge transcript
    rw [← ownedDurationUntilCompletion_ownerProjection processing job job,
      canonicalRun_ownerProjection_eq_selfWord hq processing low medium job,
      ← canonicalSingleKernel_eq_selfWord processing low medium hdisjoint job]
  · exact canonicalRun_oriented_sum_eq_pairKernel_sum hq processing
      low medium hdisjoint hzeroLow

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
