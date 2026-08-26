import SchedulingPaper.ObligatoryGrowingCutoffStrategy
import SchedulingPaper.RandomizedLooseTestProcessTrace

/-!
# Runtime trace of the growing-cutoff obligatory policy

This module specializes the reusable loose test/process trace to the
variable-cutoff learner.  It proves the exact pair words needed for
operational cost accounting without fixing the cutoff to a constant.
-/

namespace SchedulingPaper
namespace Online

noncomputable section

theorem Transcript.growingSampleRemainingResults_append_nonsample_test
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (hk : k ≤ transcript.testResults.length)
    (hjob : ¬job.val < k) :
    (transcript ++ [Observation.testResult job p]).growingSampleRemainingResults
        n k d B η hη =
      transcript.growingSampleRemainingResults n k d B η hη := by
  unfold Transcript.growingSampleRemainingResults
  have htake :
      (transcript.testResults ++ [(job, p)]).take k =
        transcript.testResults.take k :=
    List.take_append_of_le_length hk
  simp only [Transcript.testResults_append_testResult,
    Transcript.remainingTestResults,
    Transcript.processedLabels_append_testResult,
    List.filter_append, List.filter_singleton, htake]
  by_cases hprocessed : job ∈ transcript.processedLabels
  · simp [hprocessed]
  · simp [hprocessed, hjob]

theorem Transcript.growingSamplePending_append_nonsample_test
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (hk : k ≤ transcript.testResults.length)
    (hjob : ¬job.val < k) :
    (transcript ++ [Observation.testResult job p]).growingSamplePending?
        n k d B η hη =
      transcript.growingSamplePending? n k d B η hη := by
  unfold Transcript.growingSamplePending?
  rw [Transcript.growingSampleRemainingResults_append_nonsample_test
    transcript job p k d B η hη hk hjob]

/-- Every label returned by the sampled pending selector is classified early
by the fixed sample currently stored in the transcript. -/
theorem growingObligatoryPending_some_classifiedEarly
    (transcript : Transcript n) (job : Label n)
    (k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (hpending : transcript.growingObligatoryPending? n k d B η hη = some job) :
    ∃ p, (job, p) ∈ transcript.testResults ∧
      growingLearnedClassifiesEarly B d η hη
        (transcript.testResults.take k) p = true := by
  by_cases hsampleIncomplete : transcript.testResults.length < k
  · simp [Transcript.growingObligatoryPending?, hsampleIncomplete] at hpending
  · cases hsample : transcript.growingSamplePending? n k d B η hη with
    | some selected =>
        have hselected : selected = job := by
          simpa [Transcript.growingObligatoryPending?, hsampleIncomplete,
            hsample] using hpending
        unfold Transcript.growingSamplePending? at hsample
        cases hshort : shortestResult?
            (transcript.growingSampleRemainingResults n k d B η hη) with
        | none => simp [hshort] at hsample
        | some result =>
            have hlabel : result.1 = selected := by
              simpa [hshort] using hsample
            have hmem := shortestResult?_mem hshort
            unfold Transcript.growingSampleRemainingResults at hmem
            have hfiltered := List.mem_filter.mp hmem
            unfold Transcript.remainingTestResults at hfiltered
            have hremaining := List.mem_filter.mp hfiltered.1
            subst selected
            subst job
            refine ⟨result.2, hremaining.1, ?_⟩
            have hbool := hfiltered.2
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hbool
            exact hbool.2
    | none =>
        cases hlast : transcript.getLast? with
        | none =>
            simp [Transcript.growingObligatoryPending?, hsampleIncomplete,
              hsample, hlast] at hpending
        | some observation =>
            cases observation with
            | processed processed =>
                simp [Transcript.growingObligatoryPending?, hsampleIncomplete,
                  hsample, hlast] at hpending
            | rawCompleted raw =>
                simp [Transcript.growingObligatoryPending?, hsampleIncomplete,
                  hsample, hlast] at hpending
            | testResult tested p =>
                by_cases hselected : k < transcript.testResults.length &&
                    growingLearnedClassifiesEarly B d η hη
                      (transcript.testResults.take k) p
                · have hjob : tested = job := by
                    simpa [Transcript.growingObligatoryPending?,
                      hsampleIncomplete, hsample, hlast, hselected] using
                        hpending
                  subst tested
                  have hselected' := hselected
                  rw [Bool.and_eq_true] at hselected'
                  refine ⟨p, ?_, hselected'.2⟩
                  apply List.mem_filterMap.mpr
                  exact ⟨Observation.testResult job p,
                    List.mem_of_getLast? hlast, rfl⟩
                · simp [Transcript.growingObligatoryPending?,
                    hsampleIncomplete, hsample, hlast, hselected] at hpending

/-- Full terminal runtime package for the concrete sampled strategy. -/
theorem run_growingObligatoryStrategy_looseTrace_package
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let strategy := growingObligatoryStrategy n k d B η hη
    let result := run .infinite (fixedOracle processingTime)
      strategy (2 * n + 1)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      result.config.transcript.TestsMatch processingTime ∧
      result.config.FixedCompletionInvariant processingTime ∧
      LooseTestProcessTrace result.config.transcript ∧
      result.config.transcript.FollowsStrategy strategy ∧
      ∀ job, result.config.jobs job = .done := by
  dsimp only
  let pending := fun transcript : Transcript n =>
    transcript.growingObligatoryPending? n k d B η hη
  have hremaining := growingObligatoryPending_selectsRemaining n k d B η hη
  have hrun :=
    runFuel_testProcessStrategy_completed_with_completionInvariant_of_selectsRemaining
      (.infinite) processingTime hremaining 0
  have htrace :=
    runFuel_testProcessStrategy_looseTrace_of_selectsRemaining
      (.infinite) processingTime hremaining (2 * n + 1)
  have hfollow := run_followsStrategy (.infinite)
    (fixedOracle processingTime)
    (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
  unfold run growingObligatoryStrategy at hfollow ⊢
  exact ⟨hrun.1, hrun.2.1, hrun.2.2.1, hrun.2.2.2.1,
    htrace, hfollow, hrun.2.2.2.2⟩

/-- Exact post-test decision for every nonsample label in the completed
sampled run.  In particular, the learned predicate is computed from the
fixed first-`k` sample and never changes during the remainder phase. -/
theorem growingObligatoryPending_after_nonsample_test
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    (before ++ [Observation.testResult job p]).growingObligatoryPending?
        n k d B η hη =
      if growingLearnedClassifiesEarly B d η hη
          ((fixedTestResults processingTime).take k) p
        then some job else none := by
  let strategy := growingObligatoryStrategy n k d B η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hallTests : result.config.transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hbeforeLength : before.testResults.length = job.val :=
    hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
      hallTests job p (by simpa [result] using hdecomp)
  have hbeforeResults : before.testResults =
      (fixedTestResults processingTime).take job.val :=
    hpackage.2.2.2.2.1.testsBefore_eq_fixedTestResults_take
      hpackage.2.1 hpackage.2.2.1 hpackage.2.2.2.2.2.2
      job p (by simpa [result] using hdecomp)
  have haction := hpackage.2.2.2.2.2.1.action_at
    (before := before) (after := after)
    (observation := .testResult job p) (by simpa [result] using hdecomp)
  change testProcessStrategy
      (fun transcript => transcript.growingObligatoryPending? n k d B η hη)
      before = some (.test job) at haction
  have hpendingNone :
      before.growingObligatoryPending? n k d B η hη = none := by
    unfold testProcessStrategy at haction
    cases hpending : before.growingObligatoryPending? n k d B η hη with
    | none => rfl
    | some selected => simp [hpending] at haction
  have hnotSampleLt : ¬before.testResults.length < k := by omega
  have hsamplePendingNone :
      before.growingSamplePending? n k d B η hη = none := by
    cases hsample : before.growingSamplePending? n k d B η hη with
    | none => rfl
    | some selected =>
        simp [Transcript.growingObligatoryPending?, hnotSampleLt,
          hsample] at hpendingNone
  have hjobNotSample : ¬job.val < k := by omega
  have hsampleAfterNone :
      (before ++ [Observation.testResult job p]).growingSamplePending?
          n k d B η hη = none := by
    rw [Transcript.growingSamplePending_append_nonsample_test
      before job p k d B η hη (by omega) hjobNotSample]
    exact hsamplePendingNone
  have hsampleTake :
      (before ++ [Observation.testResult job p]).testResults.take k =
        (fixedTestResults processingTime).take k := by
    rw [Transcript.testResults_append_testResult,
      List.take_append_of_le_length (by omega), hbeforeResults,
      List.take_take, min_eq_left hk]
  have htestedCount :
      (before ++ [Observation.testResult job p]).testResults.length =
        job.val + 1 := by
    simp [hbeforeLength]
  have hkBefore : k ≤ before.testResults.length := by omega
  have hsampleTake' :
      (before.testResults ++ [(job, p)]).take k =
        (fixedTestResults processingTime).take k := by
    simpa [Transcript.testResults_append_testResult] using hsampleTake
  unfold Transcript.growingObligatoryPending?
  rw [if_neg (by omega), hsampleAfterNone]
  simp [Transcript.testResults_append_testResult, hsampleTake', hkBefore]

/-- Immediately before every nonsample test, the batch of positive sampled
early jobs is empty. -/
theorem growingSamplePending_none_before_nonsample_test
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    before.growingSamplePending? n k d B η hη = none := by
  let strategy := growingObligatoryStrategy n k d B η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hallTests : result.config.transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hbeforeLength : before.testResults.length = job.val :=
    hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
      hallTests job p (by simpa [result] using hdecomp)
  have haction := hpackage.2.2.2.2.2.1.action_at
    (before := before) (after := after)
    (observation := .testResult job p) (by simpa [result] using hdecomp)
  change testProcessStrategy
      (fun transcript => transcript.growingObligatoryPending? n k d B η hη)
      before = some (.test job) at haction
  have hpendingNone :
      before.growingObligatoryPending? n k d B η hη = none := by
    unfold testProcessStrategy at haction
    cases hpending : before.growingObligatoryPending? n k d B η hη with
    | none => rfl
    | some selected => simp [hpending] at haction
  have hnotSampleLt : ¬before.testResults.length < k := by omega
  cases hsample : before.growingSamplePending? n k d B η hη with
  | none => rfl
  | some selected =>
      simp [Transcript.growingObligatoryPending?, hnotSampleLt,
        hsample] at hpendingNone

/-- Every positive sampled job classified early has been processed before
the first later nonsample test displayed in the transcript. -/
theorem growing_positive_sample_early_processed_before_nonsample_test
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (hleftSample : left.val < k)
    (horder : left < right) (hright : k ≤ right.val)
    (hpLeft : 0 < processingTime left)
    (hearly : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = true)
    {before after : Transcript n}
    (hrightTest :
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult right (processingTime right) :: after) :
    left ∈ before.processedLabels := by
  by_contra hnotProcessed
  have hnone := growingSamplePending_none_before_nonsample_test
    n k d B η hη processingTime right (processingTime right) hright hrightTest
  unfold Transcript.growingSamplePending? at hnone
  have hremainingNonempty :
      before.growingSampleRemainingResults n k d B η hη ≠ [] := by
    intro hempty
    have hpackage := run_growingObligatoryStrategy_looseTrace_package
      n k d B η hη processingTime
    have hprefix : before <+:
        (run .infinite (fixedOracle processingTime)
          (growingObligatoryStrategy n k d B η hη)
          (2 * n + 1)).config.transcript :=
      ⟨Observation.testResult right (processingTime right) :: after,
        hrightTest.symm⟩
    have hbeforeResults : before.testResults =
        (fixedTestResults processingTime).take before.testResults.length :=
      Transcript.testResults_eq_fixed_take_of_prefix
        hpackage.2.1 hpackage.2.2.1 hpackage.2.2.2.2.2.2 hprefix
    have hallTests := hpackage.2.1.testResults_length_eq
      hpackage.2.2.2.2.2.2
    have hbeforeLength : before.testResults.length = right.val :=
      hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
        hallTests right (processingTime right) hrightTest
    have htestMem : (left, processingTime left) ∈ before.testResults := by
      rw [hbeforeResults, hbeforeLength]
      unfold fixedTestResults
      rw [List.mem_take_iff_getElem]
      refine ⟨left.val, ?_, ?_⟩
      · simp only [List.length_ofFn]
        omega
      · simp [List.getElem_ofFn]
    have hremMem : (left, processingTime left) ∈
        before.remainingTestResults := by
      unfold Transcript.remainingTestResults
      apply List.mem_filter.mpr
      exact ⟨htestMem, by simpa using hnotProcessed⟩
    have hsampleTake : before.testResults.take k =
        (fixedTestResults processingTime).take k := by
      rw [hbeforeResults, List.take_take, min_eq_left]
      omega
    have hmem : (left, processingTime left) ∈
        before.growingSampleRemainingResults n k d B η hη := by
      unfold Transcript.growingSampleRemainingResults
      apply List.mem_filter.mpr
      refine ⟨hremMem, ?_⟩
      simp [hleftSample, hpLeft, hsampleTake, hearly]
    rw [hempty] at hmem
    simpa using hmem
  have hshort : shortestResult?
      (before.growingSampleRemainingResults n k d B η hη) ≠ none := by
    intro hnoneShort
    exact hremainingNonempty ((shortestResult?_eq_none_iff _).mp hnoneShort)
  exact hshort (Option.map_eq_none_iff.mp hnone)

/-- A positive/zero nonsample outcome classified early is followed
immediately by its administrative process observation. -/
theorem growing_nonsample_early_next_processed
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hearly : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k) p = true)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    ∃ rest, after = .processed job :: rest := by
  let strategy := growingObligatoryStrategy n k d B η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hpending := growingObligatoryPending_after_nonsample_test
    n k d B η hη processingTime job p hk hdecomp
  rw [if_pos (by simpa using hearly)] at hpending
  have hnotBefore : job ∉ before.processedLabels := by
    intro hmem
    have hbeforeLength :=
      hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
        (hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2)
        job p (by simpa [result] using hdecomp)
    -- The stronger prefix version follows directly from the same loose
    -- grammar; use it on the displayed prefix by contradiction on lengths.
    have hprefixLt : job.val < before.testResults.length := by
      have hprefixTrace : LooseTestProcessTrace before := by
        -- `before` is a prefix of a loose trace; this follows by induction on
        -- the terminal grammar and is exposed by the prefix lemma below.
        apply hpackage.2.2.2.2.1.of_prefix
        exact ⟨Observation.testResult job p :: after,
          by simpa [result] using hdecomp.symm⟩
      exact hprefixTrace.processedLabel_lt_testResults_length hmem
    omega
  have hjobProcessed : job ∈ result.config.transcript.processedLabels :=
    (hpackage.2.1.done_iff job).mp (hpackage.2.2.2.2.2.2 job)
  apply follows_testProcessStrategy_next_processed
    (pending := fun transcript =>
      transcript.growingObligatoryPending? n k d B η hη)
    hpackage.2.2.2.2.2.1 (by simpa [result] using hdecomp)
    hpending hnotBefore hjobProcessed

/-- If the earlier-tested label is a nonsample early job, its pair word with
every later label is the immediate first word. -/
theorem growing_pairProjection_of_left_nonsample_early
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hk : k ≤ left.val)
    (hearly : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = true) :
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript
    transcript.pairProjection left right =
      [.testResult left (processingTime left), .processed left,
        .testResult right (processingTime right), .processed right] := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hallTests : transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hallProcessed : ∀ job, job ∈ transcript.processedLabels := by
    intro job
    exact (hpackage.2.1.done_iff job).mp (hpackage.2.2.2.2.2.2 job)
  have hleftTest :
      Observation.testResult left (processingTime left) ∈ transcript := by
    rw [← testResult_mem_iff_observation_mem]
    have hallResults := terminal_testResults_eq_fixedTestResults
      hpackage.2.1 hpackage.2.2.1 hpackage.2.2.2.2.2.2
    rw [hallResults]
    simp [fixedTestResults]
  obtain ⟨before, after, htest⟩ : ∃ before after : Transcript n,
      transcript = before ++
        Observation.testResult left (processingTime left) :: after :=
    List.mem_iff_append.mp hleftTest
  obtain ⟨rest, hafter⟩ := growing_nonsample_early_next_processed
    n k d B η hη processingTime left (processingTime left) hk hearly
      (by simpa [result, transcript] using htest)
  have hbeforeLength : before.testResults.length = left.val :=
    hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
      hallTests left (processingTime left) (by
        simpa [result, transcript] using htest)
  have hbeforePrefix : before <+: transcript :=
    ⟨Observation.testResult left (processingTime left) :: after, htest.symm⟩
  have hbeforeTrace : LooseTestProcessTrace before :=
    hpackage.2.2.2.2.1.of_prefix hbeforePrefix
  have hbeforeProjection : before.pairProjection left right = [] :=
    hbeforeTrace.pairProjection_eq_nil_before_left horder
      (by omega)
  have hpairPrefix :
      ([.testResult left (processingTime left), .processed left] :
          Transcript n) <+:
        transcript.pairProjection left right := by
    rw [htest, hafter, Transcript.pairProjection_append,
      hbeforeProjection]
    simp [Transcript.pairProjection, Observation.ownerLabel,
      ne_of_lt horder]
  rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
      hpackage.2.2.1 hallTests hallProcessed horder with
    himmediate | hrightFirst | hleftFirst
  · exact himmediate
  · rw [hrightFirst] at hpairPrefix
    simp at hpairPrefix
  · rw [hleftFirst] at hpairPrefix
    simp at hpairPrefix

/-- A label classified late can only be processed in the all-tests-complete
SPT tail; the sample-batch selector can never return it. -/
theorem growing_late_process_is_tail_shortest
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) (job : Label n)
    (hlate : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime job) = false)
    {before after : Transcript n}
    (hprocess :
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript =
        before ++ .processed job :: after) :
    before.testResults.length = n ∧
      before.shortestRemaining? = some job := by
  let strategy := growingObligatoryStrategy n k d B η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hprefix : before <+: result.config.transcript :=
    ⟨Observation.processed job :: after,
      by simpa [result] using hprocess.symm⟩
  have hbeforeTrace : LooseTestProcessTrace before :=
    hpackage.2.2.2.2.1.of_prefix hprefix
  have hbeforeResults : before.testResults =
      (fixedTestResults processingTime).take before.testResults.length :=
    Transcript.testResults_eq_fixed_take_of_prefix
      hpackage.2.1 hpackage.2.2.1 hpackage.2.2.2.2.2.2 hprefix
  have haction := hpackage.2.2.2.2.2.1.action_at
    (before := before) (after := after) (observation := .processed job)
    (by simpa [result] using hprocess)
  change testProcessStrategy
      (fun transcript => transcript.growingObligatoryPending? n k d B η hη)
      before = some (.process job) at haction
  have hpendingNot :
      before.growingObligatoryPending? n k d B η hη ≠ some job := by
    intro hpending
    have hkCount : k ≤ before.testResults.length := by
      by_contra hnot
      have hlt : before.testResults.length < k := by omega
      simp [Transcript.growingObligatoryPending?, hlt] at hpending
    obtain ⟨p, hpMem, hpEarly⟩ :=
      growingObligatoryPending_some_classifiedEarly
        before job k d B η hη hpending
    have hpEq : p = processingTime job :=
      hpackage.2.2.1 job p
        (by
          obtain ⟨suffix, hsuffix⟩ := hprefix
          rw [← hsuffix, Transcript.testResults_append]
          exact List.mem_append_left _ hpMem)
    have hsampleTake : before.testResults.take k =
        (fixedTestResults processingTime).take k := by
      rw [hbeforeResults, List.take_take, min_eq_left hkCount]
    rw [hsampleTake, hpEq, hlate] at hpEarly
    contradiction
  unfold testProcessStrategy at haction
  cases hpending : before.growingObligatoryPending? n k d B η hη with
  | some selected =>
      simp only [hpending, Option.some.injEq] at haction
      injection haction with hselected
      subst selected
      exact (hpendingNot hpending).elim
  | none =>
      simp only [hpending] at haction
      split at haction
      next hlt => simp at haction
      next hnotlt =>
        have hall : before.testResults.length = n := by
          have hbound := hbeforeTrace.testBound
          omega
        split at haction
        next selected hshort =>
          simp only [Option.some.injEq] at haction
          change Action.process selected = Action.process job at haction
          cases haction
          exact ⟨hall, hshort⟩
        next hnone => simp at haction

/-- Positive late/late pairs incur exactly `2 + min(p_i,p_j)`: both tests
precede both completions, and the operational tail selector enforces SPT. -/
theorem growing_positive_late_pairCharge_eq
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hpLeft : 0 < processingTime left)
    (hpRight : 0 < processingTime right)
    (hleftLate : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = false)
    (hrightLate : growingLearnedClassifiesEarly B d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime right) = false) :
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (growingObligatoryStrategy n k d B η hη) (2 * n + 1)).config.transcript
    tracePairCharge .infinite processingTime transcript left right =
      2 + min (processingTime left) (processingTime right) := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hallTests : transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hallProcessed : ∀ job, job ∈ transcript.processedLabels := by
    intro job
    exact (hpackage.2.1.done_iff job).mp (hpackage.2.2.2.2.2.2 job)
  have hne : left ≠ right := ne_of_lt horder
  rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
      hpackage.2.2.1 hallTests hallProcessed horder with
    himmediate | hrightFirst | hleftFirst
  · have hleftProcess : Observation.processed left ∈ transcript := by
      apply (processed_mem_iff_observation_mem transcript left).1
      exact hallProcessed left
    obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
        transcript = before ++ Observation.processed left :: after :=
      List.mem_iff_append.mp hleftProcess
    have htail := growing_late_process_is_tail_shortest
      n k d B η hη processingTime left hleftLate
        (by simpa [result, transcript] using hprocess)
    have hafterProjection := pairProjection_after_leftProcess_oneTest
      hne (processingTime left) (processingTime right)
      (by simpa [result, transcript] using hprocess) himmediate
    have hrightAfter :
        (right, processingTime right) ∈ after.testResults := by
      apply (testResult_mem_iff_observation_mem after right
        (processingTime right)).2
      have : Observation.testResult right (processingTime right) ∈
          after.pairProjection left right := by
        rw [hafterProjection]
        simp
      exact (List.mem_filter.mp this).1
    have hlength := congrArg (fun t : Transcript n => t.testResults.length)
      hprocess
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      List.length_append, List.length_cons] at hlength
    have hafterPos : 0 < after.testResults.length :=
      List.length_pos_of_mem hrightAfter
    rw [hallTests, htail.1] at hlength
    omega
  · have hrightProcess : Observation.processed right ∈ transcript := by
      apply (processed_mem_iff_observation_mem transcript right).1
      exact hallProcessed right
    obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
        transcript = before ++ Observation.processed right :: after :=
      List.mem_iff_append.mp hrightProcess
    have htail := growing_late_process_is_tail_shortest
      n k d B η hη processingTime right hrightLate
        (by simpa [result, transcript] using hprocess)
    have hbeforeProjection := pairProjection_before_rightProcess
      hne (processingTime left) (processingTime right)
      (by simpa [result, transcript] using hprocess) hrightFirst
    have hremaining := left_remaining_of_pairProjection_tests
      hne (processingTime left) (processingTime right) hbeforeProjection
    have hprefix : before <+: transcript :=
      ⟨Observation.processed right :: after, hprocess.symm⟩
    have hmatchTranscript : transcript.TestsMatch processingTime := by
      simpa [result, transcript] using hpackage.2.2.1
    have hmatchBefore : before.TestsMatch processingTime := by
      intro tested p hp
      apply hmatchTranscript tested p
      obtain ⟨suffix, hsuffix⟩ := hprefix
      rw [← hsuffix, Transcript.testResults_append]
      exact List.mem_append_left _ hp
    have hle := shortestRemaining_processing_le
      hmatchBefore htail.2 hremaining
    rw [tracePairCharge_eq_rightAfterTwoTests_all
      (.infinite) processingTime transcript left right
      (processingTime left) (processingTime right)
      hrightFirst hne rfl rfl]
    simp [hpLeft.ne', min_eq_right hle]
  · have hleftProcess : Observation.processed left ∈ transcript := by
      apply (processed_mem_iff_observation_mem transcript left).1
      exact hallProcessed left
    obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
        transcript = before ++ Observation.processed left :: after :=
      List.mem_iff_append.mp hleftProcess
    have htail := growing_late_process_is_tail_shortest
      n k d B η hη processingTime left hleftLate
        (by simpa [result, transcript] using hprocess)
    have hbeforeProjection := pairProjection_before_leftProcess
      hne (processingTime left) (processingTime right)
      (by simpa [result, transcript] using hprocess) hleftFirst
    have hremaining := right_remaining_of_pairProjection_tests
      hne (processingTime left) (processingTime right) hbeforeProjection
    have hprefix : before <+: transcript :=
      ⟨Observation.processed left :: after, hprocess.symm⟩
    have hmatchTranscript : transcript.TestsMatch processingTime := by
      simpa [result, transcript] using hpackage.2.2.1
    have hmatchBefore : before.TestsMatch processingTime := by
      intro tested p hp
      apply hmatchTranscript tested p
      obtain ⟨suffix, hsuffix⟩ := hprefix
      rw [← hsuffix, Transcript.testResults_append]
      exact List.mem_append_left _ hp
    have hle := shortestRemaining_processing_le
      hmatchBefore htail.2 hremaining
    rw [tracePairCharge_eq_leftAfterTwoTests_all
      (.infinite) processingTime transcript left right
      (processingTime left) (processingTime right)
      hleftFirst hne rfl rfl]
    simp [hpLeft.ne', hpRight.ne', min_eq_left hle]

/-- Exact diagonal-plus-pairs formula for the operational sampled run.  The
remaining upper-bound work is now purely to classify/average the three pair
words using the learned early predicate. -/
theorem run_growingObligatoryStrategy_cost_eq_self_add_pairCharges
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let result := run .infinite (fixedOracle processingTime)
      (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
    runCompletionCost .infinite processingTime result =
      (∑ job : Label n, (1 + processingTime job)) +
        ∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            tracePairCharge .infinite processingTime
              result.config.transcript left right := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
  have hpackage := run_growingObligatoryStrategy_looseTrace_package
    n k d B η hη processingTime
  have hperm := run_growingObligatoryStrategy_completionLabels_perm
    n k d B η hη processingTime
  have hallTests : result.config.transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hallProcessed : ∀ job,
      job ∈ result.config.transcript.processedLabels := by
    intro job
    exact (hpackage.2.1.done_iff job).mp
      (hpackage.2.2.2.2.2.2 job)
  have hself : ∀ job,
      traceSelfCharge .infinite processingTime result.config.transcript job =
        1 + processingTime job := by
    intro job
    apply traceSelfCharge_eq_one_add_of_projection
      (.infinite) processingTime result.config.transcript job
        (processingTime job)
    · exact hpackage.2.2.2.2.1.terminal_selfProjection
        hpackage.2.2.1 hallTests hallProcessed job
    · rfl
  unfold runCompletionCost
  rw [completionCost_eq_traceSelf_add_pairs
    (.infinite) processingTime result.config.transcript hperm]
  simp_rw [hself]
  rfl



end

end Online
end SchedulingPaper
