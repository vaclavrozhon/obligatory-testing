import SchedulingPaper.RandomizedLooseTestProcessTrace
import SchedulingPaper.RandomizedIdealSchedule
import SchedulingPaper.RandomizedLearnedThreshold
import Mathlib.Tactic

/-!
# Operational upper bound for the sampled obligatory policy

This file connects the literal terminating online run to the ideal
immediate/deferred pair objective.  The only discrepancy is caused by a
positive early job in the initial sample: processing that batch after all
sample tests costs at most seventeen per affected sample pair.
-/

namespace SchedulingPaper
namespace Online

open RandomizedObligatory

noncomputable section

private theorem not_mem_before_displayed_second_of_four
    {α : Type*} {prior suffix : List α} {a b c d x : α}
    (hba : b ≠ a) (hbc : b ≠ c) (hbd : b ≠ d)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (heq : prior ++ b :: suffix = [a, b, c, d]) :
    x ∉ prior := by
  intro hx
  cases prior with
  | nil => simp at hx
  | cons first prior =>
      cases prior with
      | nil => simp_all
      | cons second prior =>
          cases prior with
          | nil => simp_all
          | cons third prior =>
              cases prior with
              | nil => simp_all
              | cons fourth prior =>
                  have hlength := congrArg List.length heq
                  simp at hlength

/-- Every outcome classified early by the concrete learned branch has actual
processing time at most sixteen. -/
theorem learnedClassifiesEarly_processing_le_sixteen
    {n d : ℕ} {η p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (results : List (Label n × ℝ))
    (hearly : learnedClassifiesEarly d η hη results p = true) :
    p ≤ 16 := by
  unfold learnedClassifiesEarly at hearly
  cases hlearn : learnedThresholdFromResults? d η hη results with
  | none => simp [hlearn] at hearly
  | some θ =>
      have hselected :
          thresholdClosure (quantizedRepresentative d η) θ
            (quantizedCategory d η p hη) := by
        simpa [hlearn] using hearly
      have hcertificate :=
        learnedThresholdFromResults_closure_certificate
          d η hη results hlearn
      exact (quantized_early_actual_le_threshold d hη hp
        hcertificate.2.1 hselected).trans hcertificate.2.1

/-- If the right, late job is the first processed member of a pair, the SPT
tail makes it no longer than the still-pending left job. -/
theorem sampled_right_late_first_processing_le_left
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hrightLate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime right) = false)
    (hshape :
      let transcript :=
        (run .infinite (fixedOracle processingTime)
          (sampledObligatoryStrategy n k d η hη)
          (2 * n + 1)).config.transcript
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed right, .processed left]) :
    processingTime right ≤ processingTime left := by
  dsimp only at hshape
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hrightProcess : Observation.processed right ∈ transcript := by
    have hprocessed : right ∈ transcript.processedLabels :=
      (hpackage.2.1.done_iff right).mp (hpackage.2.2.2.2.2.2 right)
    exact (processed_mem_iff_observation_mem transcript right).1 hprocessed
  obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
      transcript = before ++ Observation.processed right :: after :=
    List.mem_iff_append.mp hrightProcess
  have htail := sampled_late_process_is_tail_shortest
    n k d η hη processingTime right hrightLate
      (by simpa [result, transcript] using hprocess)
  have hne : left ≠ right := ne_of_lt horder
  have hbeforeProjection := pairProjection_before_rightProcess
    hne (processingTime left) (processingTime right)
    hprocess hshape
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
  exact shortestRemaining_processing_le hmatchBefore htail.2 hremaining

/-- Symmetric SPT comparison when the left late job is processed first. -/
theorem sampled_left_late_first_processing_le_right
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hleftLate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = false)
    (hshape :
      let transcript :=
        (run .infinite (fixedOracle processingTime)
          (sampledObligatoryStrategy n k d η hη)
          (2 * n + 1)).config.transcript
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed left, .processed right]) :
    processingTime left ≤ processingTime right := by
  dsimp only at hshape
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hleftProcess : Observation.processed left ∈ transcript := by
    have hprocessed : left ∈ transcript.processedLabels :=
      (hpackage.2.1.done_iff left).mp (hpackage.2.2.2.2.2.2 left)
    exact (processed_mem_iff_observation_mem transcript left).1 hprocessed
  obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
      transcript = before ++ Observation.processed left :: after :=
    List.mem_iff_append.mp hleftProcess
  have htail := sampled_late_process_is_tail_shortest
    n k d η hη processingTime left hleftLate
      (by simpa [result, transcript] using hprocess)
  have hne : left ≠ right := ne_of_lt horder
  have hbeforeProjection := pairProjection_before_leftProcess
    hne (processingTime left) (processingTime right)
    hprocess hshape
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
  exact shortestRemaining_processing_le hmatchBefore htail.2 hremaining

/-- A positive late left job cannot have completed before the later label was
tested: its process operation belongs to the all-tests-complete tail. -/
theorem sampled_positive_left_late_not_immediate
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hpLeft : 0 < processingTime left)
    (hleftLate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = false)
    (hshape :
      let transcript :=
        (run .infinite (fixedOracle processingTime)
          (sampledObligatoryStrategy n k d η hη)
          (2 * n + 1)).config.transcript
      transcript.pairProjection left right =
        [.testResult left (processingTime left), .processed left,
          .testResult right (processingTime right), .processed right]) :
    False := by
  dsimp only at hshape
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hleftProcess : Observation.processed left ∈ transcript := by
    have hprocessed : left ∈ transcript.processedLabels :=
      (hpackage.2.1.done_iff left).mp (hpackage.2.2.2.2.2.2 left)
    exact (processed_mem_iff_observation_mem transcript left).1 hprocessed
  obtain ⟨before, after, hprocess⟩ : ∃ before after : Transcript n,
      transcript = before ++ Observation.processed left :: after :=
    List.mem_iff_append.mp hleftProcess
  have htail := sampled_late_process_is_tail_shortest
    n k d η hη processingTime left hleftLate
      (by simpa [result, transcript] using hprocess)
  have hne : left ≠ right := ne_of_lt horder
  have hafterProjection := pairProjection_after_leftProcess_oneTest
    hne (processingTime left) (processingTime right) hprocess hshape
  have hrightAfter : (right, processingTime right) ∈ after.testResults := by
    apply (testResult_mem_iff_observation_mem after right
      (processingTime right)).2
    have hmem : Observation.testResult right (processingTime right) ∈
        after.pairProjection left right := by
      rw [hafterProjection]
      simp
    exact (List.mem_filter.mp hmem).1
  have hlength := congrArg (fun t : Transcript n => t.testResults.length)
    hprocess
  simp only [Transcript.testResults_append,
    Transcript.testResults_processed_cons, List.length_append] at hlength
  have hallTests : transcript.testResults.length = n := by
    simpa [result, transcript] using
      hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hafterPos : 0 < after.testResults.length :=
    List.length_pos_of_mem hrightAfter
  rw [hallTests, htail.1] at hlength
  omega

/-- A positive early sample job is drained before the first nonsample test,
so its pair with every nonsample job has the literal immediate-first word. -/
theorem sampled_pairProjection_of_left_sample_early_right_nonsample
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hleftSample : left.val < k) (hright : k ≤ right.val)
    (hpLeft : 0 < processingTime left)
    (hearly : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = true) :
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη)
        (2 * n + 1)).config.transcript
    transcript.pairProjection left right =
      [.testResult left (processingTime left), .processed left,
        .testResult right (processingTime right), .processed right] := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hallTests : transcript.testResults.length = n := by
    simpa [result, transcript] using
      hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hallProcessed : ∀ job, job ∈ transcript.processedLabels := by
    intro job
    simpa [result, transcript] using
      (hpackage.2.1.done_iff job).mp (hpackage.2.2.2.2.2.2 job)
  have hrightTest : Observation.testResult right (processingTime right) ∈
      transcript := by
    rw [← testResult_mem_iff_observation_mem]
    have hallResults := terminal_testResults_eq_fixedTestResults
      hpackage.2.1 hpackage.2.2.1 hpackage.2.2.2.2.2.2
    rw [hallResults]
    simp [fixedTestResults]
  obtain ⟨before, after, htest⟩ : ∃ before after : Transcript n,
      transcript = before ++
        Observation.testResult right (processingTime right) :: after :=
    List.mem_iff_append.mp hrightTest
  have hleftProcessed :=
    positive_sample_early_processed_before_nonsample_test
      n k d η hη processingTime hleftSample horder hright hpLeft hearly
        (by simpa [result, transcript] using htest)
  have hleftObservation : Observation.processed left ∈ before :=
    (processed_mem_iff_observation_mem before left).1 hleftProcessed
  have hleftProjection : Observation.processed left ∈
      before.pairProjection left right := by
    exact List.mem_filter.mpr
      ⟨hleftObservation, by simp [Observation.ownerLabel]⟩
  have hne : left ≠ right := ne_of_lt horder
  rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
      hpackage.2.2.1 hallTests hallProcessed horder with
    himmediate | hrightFirst | hleftFirst
  · exact himmediate
  · exfalso
    have hrightFirst' : transcript.pairProjection left right =
        [Observation.testResult left (processingTime left),
          Observation.testResult right (processingTime right),
          Observation.processed right, Observation.processed left] := by
      simpa [result, transcript] using hrightFirst
    have heq : before.pairProjection left right ++
        Observation.testResult right (processingTime right) ::
          after.pairProjection left right =
        [Observation.testResult left (processingTime left),
          Observation.testResult right (processingTime right),
          Observation.processed right, Observation.processed left] := by
      rw [← hrightFirst', htest]
      simp [Transcript.pairProjection, Observation.ownerLabel,
        hne, Ne.symm hne]
    exact (not_mem_before_displayed_second_of_four
      (x := Observation.processed left)
      (a := Observation.testResult left (processingTime left))
      (b := Observation.testResult right (processingTime right))
      (c := Observation.processed right) (d := Observation.processed left)
      (by
        intro heq
        injection heq with hjob
        exact (Ne.symm hne) hjob)
      (by simp) (by simp)
      (by simp) (by simp) heq) hleftProjection
  · exfalso
    have hleftFirst' : transcript.pairProjection left right =
        [Observation.testResult left (processingTime left),
          Observation.testResult right (processingTime right),
          Observation.processed left, Observation.processed right] := by
      simpa [result, transcript] using hleftFirst
    have heq : before.pairProjection left right ++
        Observation.testResult right (processingTime right) ::
          after.pairProjection left right =
        [Observation.testResult left (processingTime left),
          Observation.testResult right (processingTime right),
          Observation.processed left, Observation.processed right] := by
      rw [← hleftFirst', htest]
      simp [Transcript.pairProjection, Observation.ownerLabel,
        hne, Ne.symm hne]
    exact (not_mem_before_displayed_second_of_four
      (x := Observation.processed left)
      (a := Observation.testResult left (processingTime left))
      (b := Observation.testResult right (processingTime right))
      (c := Observation.processed left) (d := Observation.processed right)
      (by
        intro heq
        injection heq with hjob
        exact (Ne.symm hne) hjob)
      (by simp) (by simp)
      (by simp) (by simp) heq) hleftProjection

/-- Pairwise operational comparison.  Away from a positive early job in the
initial sample, the literal policy is no more expensive than the ideal
immediate/deferred schedule.  Every exceptional sample pair costs at most
seventeen extra units. -/
theorem sampled_tracePairCharge_le_ideal_add_sample
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    (hp : ∀ job, 0 ≤ processingTime job)
    {left right : Label n} (horder : left < right) :
    let early := fun job => learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k) (processingTime job)
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη)
        (2 * n + 1)).config.transcript
    tracePairCharge .infinite processingTime transcript left right ≤
      idealPairCharge (processingTime left, early left)
        (processingTime right, early right) +
      if left.val < k ∧ right.val < k ∧ early left = true then 17 else 0 := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  let early : Label n → Bool := fun job =>
    learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k) (processingTime job)
  change tracePairCharge .infinite processingTime transcript left right ≤
    idealPairCharge (processingTime left, early left)
      (processingTime right, early right) +
    if left.val < k ∧ right.val < k ∧ early left = true then 17 else 0
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hallTests : transcript.testResults.length = n := by
    simpa [result, transcript] using
      hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hallProcessed : ∀ job, job ∈ transcript.processedLabels := by
    intro job
    simpa [result, transcript] using
      (hpackage.2.1.done_iff job).mp (hpackage.2.2.2.2.2.2 job)
  have hne : left ≠ right := ne_of_lt horder
  by_cases hleftEarly : early left = true
  · by_cases hleftSample : left.val < k
    · by_cases hrightSample : right.val < k
      · have hleft16 : processingTime left ≤ 16 :=
          learnedClassifiesEarly_processing_le_sixteen hη (hp left)
            ((fixedTestResults processingTime).take k) hleftEarly
        rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
            hpackage.2.2.1 hallTests hallProcessed horder with
          himmediate | hrightFirst | hleftFirst
        · rw [tracePairCharge_eq_leftAfterOneTest
            (.infinite) processingTime transcript left right
            (processingTime left) (processingTime right)
            (by simpa [result, transcript] using himmediate) hne rfl rfl]
          simp [idealPairCharge, early, hleftEarly, hleftSample,
            hrightSample]
        · have hright16 : processingTime right ≤ 16 := by
            by_cases hrightEarly : early right = true
            · exact learnedClassifiesEarly_processing_le_sixteen hη (hp right)
                ((fixedTestResults processingTime).take k) hrightEarly
            · have hrightLate : early right = false :=
                Bool.eq_false_of_not_eq_true hrightEarly
              have hrightLate' : learnedClassifiesEarly d η hη
                  ((fixedTestResults processingTime).take k)
                  (processingTime right) = false := by
                simpa [early] using hrightLate
              exact (sampled_right_late_first_processing_le_left
                n k d η hη processingTime horder hrightLate'
                  (by simpa [result, transcript] using hrightFirst)).trans hleft16
          rw [tracePairCharge_eq_rightAfterTwoTests_all
            (.infinite) processingTime transcript left right
            (processingTime left) (processingTime right)
            (by simpa [result, transcript] using hrightFirst) hne rfl rfl]
          by_cases hpLeft0 : processingTime left = 0
          · simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
          · simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
            linarith [hp left]
        · rw [tracePairCharge_eq_leftAfterTwoTests_all
            (.infinite) processingTime transcript left right
            (processingTime left) (processingTime right)
            (by simpa [result, transcript] using hleftFirst) hne rfl rfl]
          by_cases hpLeft0 : processingTime left = 0
          · simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
          · by_cases hpRight0 : processingTime right = 0
            · simp [idealPairCharge, early, hleftEarly, hleftSample,
                hrightSample, hpLeft0, hpRight0]
              linarith [hp left]
            · simp [idealPairCharge, early, hleftEarly, hleftSample,
                hrightSample, hpLeft0, hpRight0]
              linarith
      · have hrightNotSample : k ≤ right.val := by omega
        by_cases hpLeft0 : processingTime left = 0
        · rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
              hpackage.2.2.1 hallTests hallProcessed horder with
            himmediate | hrightFirst | hleftFirst
          · rw [tracePairCharge_eq_leftAfterOneTest
              (.infinite) processingTime transcript left right
              (processingTime left) (processingTime right)
              (by simpa [result, transcript] using himmediate) hne rfl rfl]
            simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
          · rw [tracePairCharge_eq_rightAfterTwoTests_all
              (.infinite) processingTime transcript left right
              (processingTime left) (processingTime right)
              (by simpa [result, transcript] using hrightFirst) hne rfl rfl]
            simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
          · rw [tracePairCharge_eq_leftAfterTwoTests_all
              (.infinite) processingTime transcript left right
              (processingTime left) (processingTime right)
              (by simpa [result, transcript] using hleftFirst) hne rfl rfl]
            simp [idealPairCharge, early, hleftEarly, hleftSample,
              hrightSample, hpLeft0]
        · have hpLeftPos : 0 < processingTime left :=
            lt_of_le_of_ne (hp left) (Ne.symm hpLeft0)
          have hprojection :=
            sampled_pairProjection_of_left_sample_early_right_nonsample
              n k d η hη processingTime horder hleftSample hrightNotSample
                hpLeftPos hleftEarly
          rw [tracePairCharge_eq_leftAfterOneTest
            (.infinite) processingTime transcript left right
            (processingTime left) (processingTime right)
            (by simpa [result, transcript] using hprojection) hne rfl rfl]
          simp [idealPairCharge, early, hleftEarly, hleftSample,
            hrightSample]
    · have hkLeft : k ≤ left.val := by omega
      have hprojection := sampled_pairProjection_of_left_nonsample_early
        n k d η hη processingTime horder hkLeft hleftEarly
      rw [tracePairCharge_eq_leftAfterOneTest
        (.infinite) processingTime transcript left right
        (processingTime left) (processingTime right)
        (by simpa [result, transcript] using hprojection) hne rfl rfl]
      simp [idealPairCharge, early, hleftEarly, hleftSample]
  · have hleftLate : early left = false :=
      Bool.eq_false_of_not_eq_true hleftEarly
    have hleftLate' : learnedClassifiesEarly d η hη
        ((fixedTestResults processingTime).take k)
        (processingTime left) = false := by
      simpa [early] using hleftLate
    rcases hpackage.2.2.2.2.1.terminal_pairProjection_shapes
        hpackage.2.2.1 hallTests hallProcessed horder with
      himmediate | hrightFirst | hleftFirst
    · by_cases hpLeft0 : processingTime left = 0
      · rw [tracePairCharge_eq_leftAfterOneTest
          (.infinite) processingTime transcript left right
          (processingTime left) (processingTime right)
          (by simpa [result, transcript] using himmediate) hne rfl rfl]
        by_cases hrightEarly : early right = true
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hp right]
          linarith [hp right]
        · have hmin : min (processingTime left) (processingTime right) = 0 := by
            simp [hpLeft0, hp right]
          simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hmin]
          norm_num [min_eq_left (hp right)]
      · have hpLeftPos : 0 < processingTime left :=
          lt_of_le_of_ne (hp left) (Ne.symm hpLeft0)
        exact (sampled_positive_left_late_not_immediate
          n k d η hη processingTime horder hpLeftPos hleftLate'
            (by simpa [result, transcript] using himmediate)).elim
    · rw [tracePairCharge_eq_rightAfterTwoTests_all
        (.infinite) processingTime transcript left right
        (processingTime left) (processingTime right)
        (by simpa [result, transcript] using hrightFirst) hne rfl rfl]
      by_cases hpLeft0 : processingTime left = 0
      · by_cases hrightEarly : early right = true
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hp right]
          linarith [hp right]
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hp right]
      · by_cases hrightEarly : early right = true
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0]
        · by_cases hpRight0 : processingTime right = 0
          · simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0, hp left]
          · have hle := sampled_right_late_first_processing_le_left
              n k d η hη processingTime horder
                (by
                  have hrightLate : early right = false :=
                    Bool.eq_false_of_not_eq_true hrightEarly
                  simpa [early] using hrightLate)
                (by simpa [result, transcript] using hrightFirst)
            simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0, min_eq_right hle]
    · rw [tracePairCharge_eq_leftAfterTwoTests_all
        (.infinite) processingTime transcript left right
        (processingTime left) (processingTime right)
        (by simpa [result, transcript] using hleftFirst) hne rfl rfl]
      by_cases hpLeft0 : processingTime left = 0
      · by_cases hrightEarly : early right = true
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hp right]
          linarith [hp right]
        · simp [idealPairCharge, early, hleftEarly, hrightEarly, hpLeft0,
            hp right]
      · by_cases hpRight0 : processingTime right = 0
        · by_cases hrightEarly : early right = true
          · simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0]
          · simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0, hp left]
        · have hle := sampled_left_late_first_processing_le_right
              n k d η hη processingTime horder hleftLate'
                (by simpa [result, transcript] using hleftFirst)
          by_cases hrightEarly : early right = true
          · simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0]
            linarith
          · simp [idealPairCharge, early, hleftEarly, hrightEarly,
              hpLeft0, hpRight0, min_eq_left hle]

theorem initialFin_indicator_sum
    {n k : ℕ} (hk : k < n) :
    (∑ i : Fin n, if i.val < k then (1 : ℝ) else 0) = k := by
  let bound : Fin n := ⟨k, hk⟩
  have hfilter : Finset.univ.filter (fun i : Fin n => i.val < k) =
      Finset.Iio bound := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    change i.val < k ↔ i.val < k
    rfl
  rw [← Finset.sum_filter]
  simp [hfilter, bound]

theorem sample_pair_penalty_sum_le
    {n k : ℕ} (hk : k < n) (early : Fin n → Bool) :
    (∑ left : Fin n, ∑ right ∈
        Finset.univ.filter (fun right => left < right),
      if left.val < k ∧ right.val < k ∧ early left = true
        then (17 : ℝ) else 0) ≤
      17 * (k : ℝ) ^ 2 := by
  simp_rw [Finset.sum_filter]
  have hpoint : ∀ left right : Fin n,
      (if left < right then
          if left.val < k ∧ right.val < k ∧ early left = true
            then (17 : ℝ) else 0
        else 0) ≤
      17 * (if left.val < k then (1 : ℝ) else 0) *
        (if right.val < k then (1 : ℝ) else 0) := by
    intro left right
    split_ifs <;> simp_all
  calc
    (∑ left : Fin n, ∑ right : Fin n,
        if left < right then
          (if left.val < k ∧ right.val < k ∧ early left = true
            then (17 : ℝ) else 0)
        else 0) ≤
        ∑ left : Fin n, ∑ right : Fin n,
          17 * (if left.val < k then (1 : ℝ) else 0) *
            (if right.val < k then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact hpoint left right
    _ = 17 *
        (∑ left : Fin n, if left.val < k then (1 : ℝ) else 0) *
        (∑ right : Fin n, if right.val < k then (1 : ℝ) else 0) := by
      calc
        (∑ left : Fin n, ∑ right : Fin n,
            17 * (if left.val < k then (1 : ℝ) else 0) *
              (if right.val < k then (1 : ℝ) else 0)) =
            ∑ left : Fin n,
              (17 * (if left.val < k then (1 : ℝ) else 0)) *
                (∑ right : Fin n,
                  if right.val < k then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro left _
          rw [Finset.mul_sum]
        _ = (∑ left : Fin n,
              17 * (if left.val < k then (1 : ℝ) else 0)) *
              (∑ right : Fin n,
                if right.val < k then (1 : ℝ) else 0) := by
          exact (Finset.sum_mul Finset.univ
            (fun left : Fin n =>
              17 * (if left.val < k then (1 : ℝ) else 0))
            (∑ right : Fin n,
              if right.val < k then (1 : ℝ) else 0)).symm
        _ = 17 *
              (∑ left : Fin n,
                if left.val < k then (1 : ℝ) else 0) *
              (∑ right : Fin n,
                if right.val < k then (1 : ℝ) else 0) := by
          congr 1
          exact (Finset.mul_sum Finset.univ
            (fun left : Fin n =>
              if left.val < k then (1 : ℝ) else 0) 17).symm
    _ = 17 * (k : ℝ) ^ 2 := by
      rw [initialFin_indicator_sum hk]
      ring

/-- The completed literal run is bounded by the finite ideal pair objective
plus exactly the delayed-sample budget `17 k²`. -/
theorem run_sampledObligatoryStrategy_cost_le_finiteIdeal_add
    (n k d : ℕ) (η : ℝ) (hη : 0 < η) (hk : k < n)
    (processingTime : Label n → ℝ)
    (hp : ∀ job, 0 ≤ processingTime job) :
    let early := fun job => learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k) (processingTime job)
    let result := run .infinite (fixedOracle processingTime)
      (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
    runCompletionCost .infinite processingTime result ≤
      finiteIdealPairCost processingTime early + 17 * (k : ℝ) ^ 2 := by
  dsimp only
  let early : Label n → Bool := fun job =>
    learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k) (processingTime job)
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  rw [run_sampledObligatoryStrategy_cost_eq_self_add_pairCharges]
  unfold finiteIdealPairCost
  have hpairs :
      (∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
        tracePairCharge .infinite processingTime
          result.config.transcript left right) ≤
      (∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
        idealPairCharge (processingTime left, early left)
          (processingTime right, early right)) +
        17 * (k : ℝ) ^ 2 := by
    calc
      (∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
        tracePairCharge .infinite processingTime
          result.config.transcript left right) ≤
        ∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
          (idealPairCharge (processingTime left, early left)
              (processingTime right, early right) +
            if left.val < k ∧ right.val < k ∧ early left = true
              then (17 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro left _
        apply Finset.sum_le_sum
        intro right hright
        exact sampled_tracePairCharge_le_ideal_add_sample
          n k d η hη processingTime hp
            (Finset.mem_filter.mp hright).2
      _ = (∑ left : Label n, ∑ right ∈
            Finset.univ.filter (fun right => left < right),
          idealPairCharge (processingTime left, early left)
            (processingTime right, early right)) +
          (∑ left : Label n, ∑ right ∈
            Finset.univ.filter (fun right => left < right),
          if left.val < k ∧ right.val < k ∧ early left = true
            then (17 : ℝ) else 0) := by
        simp_rw [Finset.sum_add_distrib]
      _ ≤ (∑ left : Label n, ∑ right ∈
            Finset.univ.filter (fun right => left < right),
          idealPairCharge (processingTime left, early left)
            (processingTime right, early right)) +
          17 * (k : ℝ) ^ 2 := by
        gcongr
        exact sample_pair_penalty_sum_le hk early
  linarith

end

end Online
end SchedulingPaper
