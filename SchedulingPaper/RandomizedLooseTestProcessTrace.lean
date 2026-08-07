import SchedulingPaper.RandomizedOperationalStrategy
import SchedulingPaper.TestProcessPairShape
import SchedulingPaper.TestProcessPolicyAccounting
import SchedulingPaper.AdaptiveRuntimeAccounting
import Mathlib.Tactic

/-!
# Canonical pair accounting with a pre-tail batch

The standard `TestProcessTrace` permits only the most recently tested job to
be processed before all tests finish.  The randomized sampled policy also
drains older tested sample jobs.  The looser grammar below allows any already
tested, unprocessed label; its two-label projection still has the same three
terminal linear extensions.
-/

namespace SchedulingPaper
namespace Online

noncomputable section

/-- Appending the process operation of any already-tested label preserves the
seven-state pair automaton. -/
theorem CanonicalPairPhase.afterGeneralProcess
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    {transcript : Transcript n} {job : Label n}
    (hphase : CanonicalPairPhase processingTime left right transcript)
    (htested : job.val < transcript.testResults.length)
    (hnotProcessed : job ∉ transcript.processedLabels) :
    CanonicalPairPhase processingTime left right
      (transcript ++ [.processed job]) := by
  have hne : left ≠ right := ne_of_lt horder
  have hne' : right ≠ left := Ne.symm hne
  have horderVal : left.val < right.val := horder
  by_cases hjobLeft : job = left
  · subst job
    have hnoProcess :
        Observation.processed left ∉
          transcript.pairProjection left right := by
      intro hmem
      exact hnotProcessed
        (Transcript.processedLabel_mem_of_processed_mem_pairProjection hmem)
    unfold CanonicalPairPhase at hphase ⊢
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      Transcript.testResults_nil, List.append_nil,
      Transcript.pairProjection_append]
    rcases hphase with hbefore | hmiddle | hafter
    · omega
    · refine Or.inr (Or.inl ⟨hmiddle.1, hmiddle.2.1, ?_⟩)
      rcases hmiddle.2.2 with hplain | hdone
      · right
        rw [hplain, Transcript.pairProjection_processed_left hne]
        simp
      · exfalso
        apply hnoProcess
        rw [hdone]
        simp
    · refine Or.inr (Or.inr ⟨hafter.1, ?_⟩)
      rcases hafter.2 with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
      · exfalso; apply hnoProcess; rw [h₁]; simp
      · exfalso; apply hnoProcess; rw [h₂]; simp
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          rw [h₃, Transcript.pairProjection_processed_left hne]
          simp)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          rw [h₄, Transcript.pairProjection_processed_left hne]
          simp))))))
      · exfalso; apply hnoProcess; rw [h₅]; simp
      · exfalso; apply hnoProcess; rw [h₆]; simp
      · exfalso; apply hnoProcess; rw [h₇]; simp
  · by_cases hjobRight : job = right
    · subst job
      have hnoProcess :
          Observation.processed right ∉
            transcript.pairProjection left right := by
        intro hmem
        exact hnotProcessed
          (Transcript.processedLabel_mem_of_processed_mem_pairProjection hmem)
      unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rcases hphase with hbefore | hmiddle | hafter
      · omega
      · omega
      · refine Or.inr (Or.inr ⟨hafter.1, ?_⟩)
        rcases hafter.2 with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
        · exact Or.inr (Or.inl (by
            rw [h₁, Transcript.pairProjection_processed_right hne]
            simp))
        · exfalso; apply hnoProcess; rw [h₂]; simp
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
            rw [h₃, Transcript.pairProjection_processed_right hne]
            simp))))
        · exfalso; apply hnoProcess; rw [h₄]; simp
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            rw [h₅, Transcript.pairProjection_processed_right hne]
            simp))))))
        · exfalso; apply hnoProcess; rw [h₆]; simp
        · exfalso; apply hnoProcess; rw [h₇]; simp
    · unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rw [Transcript.pairProjection_processed_other hjobLeft hjobRight]
      simpa using hphase

/-- Grammar of label-order tests and arbitrary legal processing operations. -/
inductive LooseTestProcessTrace : Transcript n → Prop
  | nil : LooseTestProcessTrace []
  | test
      {transcript : Transcript n}
      (htrace : LooseTestProcessTrace transcript)
      (hlt : transcript.testResults.length < n)
      (p : ℝ) :
      LooseTestProcessTrace
        (transcript ++ [.testResult
          ⟨transcript.testResults.length, hlt⟩ p])
  | process
      {transcript : Transcript n} {job : Label n}
      (htrace : LooseTestProcessTrace transcript)
      (htested : job.val < transcript.testResults.length)
      (hnotProcessed : job ∉ transcript.processedLabels) :
      LooseTestProcessTrace (transcript ++ [.processed job])

theorem LooseTestProcessTrace.testOrder
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript) :
    transcript.testResults.map (fun result => result.1.val) =
      List.range transcript.testResults.length := by
  induction htrace with
  | nil => simp
  | @test transcript htrace hlt p ih =>
      simp only [Transcript.testResults_append_testResult,
        List.map_append, List.map_singleton,
        List.length_append, List.length_singleton]
      rw [ih]
      simpa [Nat.add_comm] using
        (List.range_succ (n := transcript.testResults.length)).symm
  | process htrace htested hnot ih => simpa using ih

theorem LooseTestProcessTrace.testBound
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript) :
    transcript.testResults.length ≤ n := by
  induction htrace with
  | nil => simp
  | @test transcript htrace hlt p ih =>
      simp only [Transcript.testResults_append_testResult,
        List.length_append, List.length_singleton]
      omega
  | process htrace htested hnot ih => simpa using ih

theorem LooseTestProcessTrace.ownerLabel_lt_testResults_length
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    {observation : Observation n} (hmem : observation ∈ transcript) :
    observation.ownerLabel.val < transcript.testResults.length := by
  induction htrace with
  | nil => simp at hmem
  | @test transcript htrace hlt p ih =>
      rw [List.mem_append] at hmem
      simp only [List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · have := ih hold
        simp only [Transcript.testResults_append_testResult,
          List.length_append, List.length_singleton]
        omega
      · simp [Observation.ownerLabel]
  | @process transcript job htrace htested hnot ih =>
      rw [List.mem_append] at hmem
      simp only [List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · simpa using ih hold
      · simpa [Observation.ownerLabel] using htested

theorem LooseTestProcessTrace.pairProjection_eq_nil_before_left
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    {left right : Label n} (horder : left < right)
    (hbefore : transcript.testResults.length ≤ left.val) :
    transcript.pairProjection left right = [] := by
  unfold Transcript.pairProjection
  rw [List.filter_eq_nil_iff]
  intro observation hmem
  have howner := htrace.ownerLabel_lt_testResults_length hmem
  have hleft : observation.ownerLabel ≠ left := by
    intro heq
    rw [heq] at howner
    omega
  have hright : observation.ownerLabel ≠ right := by
    intro heq
    rw [heq] at howner
    have horderVal : left.val < right.val := horder
    omega
  simp [hleft, hright]

theorem LooseTestProcessTrace.processedLabels_nodup
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript) :
    transcript.processedLabels.Nodup := by
  induction htrace with
  | nil => simp [Transcript.processedLabels]
  | test htrace hlt p ih => simpa using ih
  | process htrace htested hnot ih =>
      rw [Transcript.processedLabels_append_processed,
        List.nodup_append_comm]
      simp [ih, hnot]

theorem LooseTestProcessTrace.processedLabel_lt_testResults_length
    {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    {job : Label n} (hmem : job ∈ transcript.processedLabels) :
    job.val < transcript.testResults.length := by
  induction htrace with
  | nil => simp [Transcript.processedLabels] at hmem
  | @test transcript htrace hlt p ih =>
      have hold : job ∈ transcript.processedLabels := by simpa using hmem
      have := ih hold
      simp only [Transcript.testResults_append_testResult,
        List.length_append, List.length_singleton]
      omega
  | @process transcript processed htrace htested hnot ih =>
      rw [Transcript.processedLabels_append_processed] at hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · simpa using ih hold
      · simp only [List.mem_singleton] at hnew
        subst processed
        simpa using htested

/-- Every list prefix of a loose trace is itself a loose trace. -/
theorem LooseTestProcessTrace.of_prefix
    {transcript pre : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hprefix : pre <+: transcript) :
    LooseTestProcessTrace pre := by
  induction htrace with
  | nil =>
      have : pre = [] := List.prefix_nil.mp hprefix
      subst pre
      exact .nil
  | @test transcript htrace hlt p ih =>
      by_cases hlen : pre.length ≤ transcript.length
      · exact ih ((List.isPrefix_append_of_length hlen).mp hprefix)
      · have hle := hprefix.length_le
        have heqLength :
            pre.length =
              (transcript ++ [Observation.testResult
                ⟨transcript.testResults.length, hlt⟩ p]).length := by
          simp only [List.length_append, List.length_singleton] at hle ⊢
          omega
        have heq := hprefix.eq_of_length heqLength
        subst pre
        exact htrace.test hlt p
  | @process transcript job htrace htested hnot ih =>
      by_cases hlen : pre.length ≤ transcript.length
      · exact ih ((List.isPrefix_append_of_length hlen).mp hprefix)
      · have hle := hprefix.length_le
        have heqLength :
            pre.length =
              (transcript ++ [Observation.processed job]).length := by
          simp only [List.length_append, List.length_singleton] at hle ⊢
          omega
        have heq := hprefix.eq_of_length heqLength
        subst pre
        exact htrace.process htested hnot

theorem LooseTestProcessTrace.canonicalPairPhase
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    {left right : Label n} (horder : left < right) :
    CanonicalPairPhase processingTime left right transcript := by
  induction htrace with
  | nil => simp [CanonicalPairPhase, Transcript.pairProjection]
  | @test transcript htrace hlt value ih =>
      have hmatchOld : transcript.TestsMatch processingTime := by
        intro job p hmem
        apply hmatch job p
        rw [Transcript.testResults_append_testResult]
        exact List.mem_append_left _ hmem
      have hvalue : value = processingTime
          ⟨transcript.testResults.length, hlt⟩ := by
        apply hmatch
        simp
      exact CanonicalPairPhase.afterTest processingTime horder
        (ih hmatchOld) hlt value hvalue
  | @process transcript job htrace htested hnot ih =>
      have hmatchOld : transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      exact CanonicalPairPhase.afterGeneralProcess processingTime horder
        (ih hmatchOld) htested hnot

/-- The terminal three-word pair classification, now for a sampled batch as
well as ordinary immediate/tail policies. -/
theorem LooseTestProcessTrace.terminal_pairProjection_shapes
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed : ∀ job, job ∈ transcript.processedLabels)
    {left right : Label n} (horder : left < right) :
    transcript.pairProjection left right =
        [.testResult left (processingTime left), .processed left,
          .testResult right (processingTime right), .processed right] ∨
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed right, .processed left] ∨
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed left, .processed right] := by
  have hne : left ≠ right := ne_of_lt horder
  have hphase := htrace.canonicalPairPhase hmatch horder
  have hrightBound : right.val < n := right.isLt
  have hleftProcessed : Observation.processed left ∈
      transcript.pairProjection left right :=
    Transcript.processed_mem_pairProjection_of_mem_processedLabels
      (Or.inl rfl) (hallProcessed left)
  have hrightProcessed : Observation.processed right ∈
      transcript.pairProjection left right :=
    Transcript.processed_mem_pairProjection_of_mem_processedLabels
      (Or.inr rfl) (hallProcessed right)
  unfold CanonicalPairPhase at hphase
  rcases hphase with hphase | hphase | hphase
  · omega
  · omega
  · rcases hphase.2 with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
    · rw [h₁] at hrightProcessed
      simp at hrightProcessed
      exact (hne hrightProcessed.symm).elim
    · exact Or.inl h₂
    · rw [h₃] at hleftProcessed
      simp at hleftProcessed
    · rw [h₄] at hleftProcessed
      simp at hleftProcessed
      exact (hne hleftProcessed).elim
    · rw [h₅] at hrightProcessed
      simp at hrightProcessed
      exact (hne hrightProcessed.symm).elim
    · exact Or.inr (Or.inl h₆)
    · exact Or.inr (Or.inr h₇)

theorem LooseTestProcessTrace.canonicalSelfPhase
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime) (job : Label n) :
    CanonicalSelfPhase processingTime job transcript := by
  induction htrace with
  | nil => simp [CanonicalSelfPhase, Transcript.pairProjection]
  | @test transcript htrace hlt value ih =>
      have hmatchOld : transcript.TestsMatch processingTime := by
        intro other p hmem
        apply hmatch other p
        rw [Transcript.testResults_append_testResult]
        exact List.mem_append_left _ hmem
      have hvalue : value = processingTime
          ⟨transcript.testResults.length, hlt⟩ := by
        apply hmatch
        simp
      exact CanonicalSelfPhase.afterTest processingTime job
        (ih hmatchOld) hlt value hvalue
  | @process transcript processed htrace htested hnot ih =>
      have hmatchOld : transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      exact CanonicalSelfPhase.afterProcess processingTime job
        (ih hmatchOld) (fun heq => by simpa [heq] using htested) hnot

theorem LooseTestProcessTrace.terminal_selfProjection
    {processingTime : Label n → ℝ} {transcript : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed : ∀ job, job ∈ transcript.processedLabels)
    (job : Label n) :
    transcript.pairProjection job job =
      [.testResult job (processingTime job), .processed job] := by
  have hphase := htrace.canonicalSelfPhase hmatch job
  have hbound : job.val < n := job.isLt
  have hprocess : Observation.processed job ∈
      transcript.pairProjection job job :=
    Transcript.processed_mem_pairProjection_of_mem_processedLabels
      (Or.inl rfl) (hallProcessed job)
  unfold CanonicalSelfPhase at hphase
  rcases hphase with hphase | hphase
  · omega
  · rcases hphase.2 with htested | hprocessed
    · rw [htested] at hprocess
      simp at hprocess
    · exact hprocessed

/-- Exact pair charge for the second terminal word, including the zero-left
case excluded by the older positive-only helper. -/
theorem tracePairCharge_eq_rightAfterTwoTests_all
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n) (p q : ℝ)
    (hprojection : transcript.pairProjection left right =
      [.testResult left p, .testResult right q,
        .processed right, .processed left])
    (hne : left ≠ right) (hp : processingTime left = p)
    (hq : processingTime right = q) :
    tracePairCharge cap processingTime transcript left right =
      if p = 0 then 1 else 2 + q := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl), hprojection]
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;>
    simp [ownedDurationUntilCompletion, Observation.ownerLabel,
      Observation.duration, Observation.completionLabel,
      hp, hq, hp0, hq0, hne, Ne.symm hne] <;> ring

/-- Exact pair charge for the third terminal word, including both zero
boundary cases. -/
theorem tracePairCharge_eq_leftAfterTwoTests_all
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n) (p q : ℝ)
    (hprojection : transcript.pairProjection left right =
      [.testResult left p, .testResult right q,
        .processed left, .processed right])
    (hne : left ≠ right) (hp : processingTime left = p)
    (hq : processingTime right = q) :
    tracePairCharge cap processingTime transcript left right =
      if p = 0 then 1 else if q = 0 then 2 else 2 + p := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl), hprojection]
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;>
    simp [ownedDurationUntilCompletion, Observation.ownerLabel,
      Observation.duration, Observation.completionLabel,
      hp, hq, hp0, hq0, hne, Ne.symm hne] <;> ring

/-- In a loose trace, the number of preceding tests at the displayed test of
`job` is still exactly its canonical label index. -/
theorem LooseTestProcessTrace.testsBefore_testResult_eq_label
    {transcript before after : Transcript n}
    (htrace : LooseTestProcessTrace transcript)
    (hallTests : transcript.testResults.length = n)
    (job : Label n) (p : ℝ)
    (hdecomp : transcript = before ++ .testResult job p :: after) :
    before.testResults.length = job.val := by
  subst transcript
  have htestOrder := htrace.testOrder
  have hindex : before.testResults.length <
      (before ++ .testResult job p :: after).testResults.length := by simp
  have hmappedIndex : before.testResults.length <
      ((before ++ .testResult job p :: after).testResults.map
        fun result => result.1.val).length := by simpa using hindex
  have hget := List.getElem_of_eq htestOrder hmappedIndex
  simp only [Transcript.testResults_append,
    Transcript.testResults_testResult_cons,
    List.map_append, List.map_cons, List.map_nil] at hget
  symm
  simpa [hallTests] using hget

theorem LooseTestProcessTrace.testsBefore_eq_fixedTestResults_take
    {processingTime : Label n → ℝ} {config : Config n}
    {before after : Transcript n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (htrace : LooseTestProcessTrace config.transcript)
    (hdone : ∀ job, config.jobs job = .done)
    (job : Label n) (p : ℝ)
    (hdecomp : config.transcript =
      before ++ .testResult job p :: after) :
    before.testResults = (fixedTestResults processingTime).take job.val := by
  have hall : config.transcript.testResults.length = n :=
    hstruct.testResults_length_eq hdone
  have hlength : before.testResults.length = job.val :=
    htrace.testsBefore_testResult_eq_label hall job p hdecomp
  have hallResults := terminal_testResults_eq_fixedTestResults
    hstruct hmatch hdone
  have htake := congrArg (List.take job.val) hallResults
  rw [hdecomp] at htake
  simp only [Transcript.testResults_append,
    Transcript.testResults_testResult_cons] at htake
  simpa [hlength, List.take_append_of_le_length] using htake

/-- A test of a nonsample label does not change the stock of pending sampled
early jobs. -/
theorem Transcript.learnedSampleRemainingResults_append_nonsample_test
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (k d : ℕ) (η : ℝ) (hη : 0 < η)
    (hk : k ≤ transcript.testResults.length)
    (hjob : ¬job.val < k) :
    (transcript ++ [Observation.testResult job p]).learnedSampleRemainingResults
        n k d η hη =
      transcript.learnedSampleRemainingResults n k d η hη := by
  unfold Transcript.learnedSampleRemainingResults
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

theorem Transcript.learnedSamplePending_append_nonsample_test
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (k d : ℕ) (η : ℝ) (hη : 0 < η)
    (hk : k ≤ transcript.testResults.length)
    (hjob : ¬job.val < k) :
    (transcript ++ [Observation.testResult job p]).learnedSamplePending?
        n k d η hη =
      transcript.learnedSamplePending? n k d η hη := by
  unfold Transcript.learnedSamplePending?
  rw [Transcript.learnedSampleRemainingResults_append_nonsample_test
    transcript job p k d η hη hk hjob]

/-- Every label returned by the sampled pending selector is classified early
by the fixed sample currently stored in the transcript. -/
theorem sampledObligatoryPending_some_classifiedEarly
    (transcript : Transcript n) (job : Label n)
    (k d : ℕ) (η : ℝ) (hη : 0 < η)
    (hpending : transcript.sampledObligatoryPending? n k d η hη = some job) :
    ∃ p, (job, p) ∈ transcript.testResults ∧
      learnedClassifiesEarly d η hη
        (transcript.testResults.take k) p = true := by
  by_cases hsampleIncomplete : transcript.testResults.length < k
  · simp [Transcript.sampledObligatoryPending?, hsampleIncomplete] at hpending
  · cases hsample : transcript.learnedSamplePending? n k d η hη with
    | some selected =>
        have hselected : selected = job := by
          simpa [Transcript.sampledObligatoryPending?, hsampleIncomplete,
            hsample] using hpending
        unfold Transcript.learnedSamplePending? at hsample
        cases hshort : shortestResult?
            (transcript.learnedSampleRemainingResults n k d η hη) with
        | none => simp [hshort] at hsample
        | some result =>
            have hlabel : result.1 = selected := by
              simpa [hshort] using hsample
            have hmem := shortestResult?_mem hshort
            unfold Transcript.learnedSampleRemainingResults at hmem
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
            simp [Transcript.sampledObligatoryPending?, hsampleIncomplete,
              hsample, hlast] at hpending
        | some observation =>
            cases observation with
            | processed processed =>
                simp [Transcript.sampledObligatoryPending?, hsampleIncomplete,
                  hsample, hlast] at hpending
            | rawCompleted raw =>
                simp [Transcript.sampledObligatoryPending?, hsampleIncomplete,
                  hsample, hlast] at hpending
            | testResult tested p =>
                by_cases hselected : k < transcript.testResults.length &&
                    learnedClassifiesEarly d η hη
                      (transcript.testResults.take k) p
                · have hjob : tested = job := by
                    simpa [Transcript.sampledObligatoryPending?,
                      hsampleIncomplete, hsample, hlast, hselected] using
                        hpending
                  subst tested
                  have hselected' := hselected
                  rw [Bool.and_eq_true] at hselected'
                  refine ⟨p, ?_, hselected'.2⟩
                  apply List.mem_filterMap.mpr
                  exact ⟨Observation.testResult job p,
                    List.mem_of_getLast? hlast, rfl⟩
                · simp [Transcript.sampledObligatoryPending?,
                    hsampleIncomplete, hsample, hlast, hselected] at hpending

theorem Transcript.testResults_eq_fixed_take_of_prefix
    {processingTime : Label n → ℝ} {config : Config n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (hdone : ∀ job, config.jobs job = .done)
    {pre : Transcript n} (hprefix : pre <+: config.transcript) :
    pre.testResults =
      (fixedTestResults processingTime).take pre.testResults.length := by
  obtain ⟨suffix, hsuffix⟩ := hprefix
  have hall := terminal_testResults_eq_fixedTestResults hstruct hmatch hdone
  rw [← hsuffix, Transcript.testResults_append] at hall
  have htake := congrArg (List.take pre.testResults.length) hall
  simpa using htake

/-- Any `testProcessStrategy` whose pending selector chooses a remaining
tested job generates the loose grammar. -/
theorem LooseTestProcessTrace.stepPackage
    (cap : Cap) (oracle : Oracle n)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending)
    {config next : Config n} {action : Action n}
    (hstruct : config.TestProcessInvariant)
    (htrace : LooseTestProcessTrace config.transcript)
    (haction : testProcessStrategy pending config.transcript = some action)
    (hstep : config.step cap oracle action = some next) :
    next.TestProcessInvariant ∧ LooseTestProcessTrace next.transcript := by
  unfold testProcessStrategy at haction
  cases hp : pending config.transcript with
  | some job =>
      simp only [hp, Option.some.injEq] at haction
      subst action
      obtain ⟨p, hjob⟩ :=
        hstruct.tested_of_selectsRemaining hpending hp
      have htestedMem := (hstruct.tested_iff job p).mp hjob |>.1
      have htestedVal : job.val < config.transcript.testResults.length := by
        have hmem : job.val ∈ List.range
            config.transcript.testResults.length := by
          rw [← hstruct.testOrder]
          exact List.mem_map.mpr ⟨(job, p), htestedMem, rfl⟩
        simpa using hmem
      have hnotProcessed := (hstruct.tested_iff job p).mp hjob |>.2
      simp only [Config.step, hjob, Option.some.injEq] at hstep
      subst next
      exact ⟨hstruct.afterProcess job p hjob,
        htrace.process htestedVal hnotProcessed⟩
  | none =>
      simp only [hp] at haction
      split at haction
      next hlt =>
        simp only [Option.some.injEq] at haction
        subst action
        let job : Label n :=
          ⟨config.transcript.testResults.length, hlt⟩
        have hjob : config.jobs job = .untouched :=
          hstruct.labelAtTestCount_untouched rfl
        dsimp [job] at hjob
        simp only [Config.step, hjob, Option.some.injEq] at hstep
        subst next
        exact ⟨hstruct.afterTest job rfl
            (oracle config.transcript job),
          htrace.test hlt (oracle config.transcript job)⟩
      next hnotlt =>
        split at haction
        next job hshort =>
          simp only [Option.some.injEq] at haction
          subst action
          obtain ⟨p, hjob⟩ := hstruct.shortestRemaining_tested hshort
          have htestedMem := (hstruct.tested_iff job p).mp hjob |>.1
          have htestedVal : job.val < config.transcript.testResults.length := by
            have hmem : job.val ∈ List.range
                config.transcript.testResults.length := by
              rw [← hstruct.testOrder]
              exact List.mem_map.mpr ⟨(job, p), htestedMem, rfl⟩
            simpa using hmem
          have hnotProcessed := (hstruct.tested_iff job p).mp hjob |>.2
          simp only [Config.step, hjob, Option.some.injEq] at hstep
          subst next
          exact ⟨hstruct.afterProcess job p hjob,
            htrace.process htestedVal hnotProcessed⟩
        next hnone => simp at haction

theorem runFuel_testProcessStrategy_looseTrace_of_selectsRemaining
    (cap : Cap) (processingTime : Label n → ℝ)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending) (fuel : ℕ) :
    LooseTestProcessTrace
      (runFuel cap (fixedOracle processingTime)
        (testProcessStrategy pending) fuel (Config.initial n)).config.transcript := by
  have hpreserve : ∀ (steps : ℕ) (config : Config n),
      config.TestProcessInvariant →
      LooseTestProcessTrace config.transcript →
      LooseTestProcessTrace
        (runFuel cap (fixedOracle processingTime)
          (testProcessStrategy pending) steps config).config.transcript := by
    intro steps
    induction steps with
    | zero =>
        intro config hstruct htrace
        simpa [runFuel] using htrace
    | succ steps ih =>
        intro config hstruct htrace
        cases haction : testProcessStrategy pending config.transcript with
        | none => simpa [runFuel, haction] using htrace
        | some action =>
            cases hstep : config.step cap (fixedOracle processingTime) action with
            | none => simpa [runFuel, haction, hstep] using htrace
            | some next =>
                have hnext := htrace.stepPackage cap
                  (fixedOracle processingTime) hpending hstruct haction hstep
                simpa [runFuel, haction, hstep] using
                  ih next hnext.1 hnext.2
  exact hpreserve fuel (Config.initial n)
    (Config.initial_testProcessInvariant n) LooseTestProcessTrace.nil

/-- Full terminal runtime package for the concrete sampled strategy. -/
theorem run_sampledObligatoryStrategy_looseTrace_package
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let strategy := sampledObligatoryStrategy n k d η hη
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
    transcript.sampledObligatoryPending? n k d η hη
  have hremaining := sampledObligatoryPending_selectsRemaining n k d η hη
  have hrun :=
    runFuel_testProcessStrategy_completed_with_completionInvariant_of_selectsRemaining
      (.infinite) processingTime hremaining 0
  have htrace :=
    runFuel_testProcessStrategy_looseTrace_of_selectsRemaining
      (.infinite) processingTime hremaining (2 * n + 1)
  have hfollow := run_followsStrategy (.infinite)
    (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  unfold run sampledObligatoryStrategy at hfollow ⊢
  exact ⟨hrun.1, hrun.2.1, hrun.2.2.1, hrun.2.2.2.1,
    htrace, hfollow, hrun.2.2.2.2⟩

/-- Exact post-test decision for every nonsample label in the completed
sampled run.  In particular, the learned predicate is computed from the
fixed first-`k` sample and never changes during the remainder phase. -/
theorem sampledObligatoryPending_after_nonsample_test
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    (before ++ [Observation.testResult job p]).sampledObligatoryPending?
        n k d η hη =
      if learnedClassifiesEarly d η hη
          ((fixedTestResults processingTime).take k) p
        then some job else none := by
  let strategy := sampledObligatoryStrategy n k d η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
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
      (fun transcript => transcript.sampledObligatoryPending? n k d η hη)
      before = some (.test job) at haction
  have hpendingNone :
      before.sampledObligatoryPending? n k d η hη = none := by
    unfold testProcessStrategy at haction
    cases hpending : before.sampledObligatoryPending? n k d η hη with
    | none => rfl
    | some selected => simp [hpending] at haction
  have hnotSampleLt : ¬before.testResults.length < k := by omega
  have hsamplePendingNone :
      before.learnedSamplePending? n k d η hη = none := by
    cases hsample : before.learnedSamplePending? n k d η hη with
    | none => rfl
    | some selected =>
        simp [Transcript.sampledObligatoryPending?, hnotSampleLt,
          hsample] at hpendingNone
  have hjobNotSample : ¬job.val < k := by omega
  have hsampleAfterNone :
      (before ++ [Observation.testResult job p]).learnedSamplePending?
          n k d η hη = none := by
    rw [Transcript.learnedSamplePending_append_nonsample_test
      before job p k d η hη (by omega) hjobNotSample]
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
  unfold Transcript.sampledObligatoryPending?
  rw [if_neg (by omega), hsampleAfterNone]
  simp [Transcript.testResults_append_testResult, hsampleTake', hkBefore]

/-- Immediately before every nonsample test, the batch of positive sampled
early jobs is empty. -/
theorem learnedSamplePending_none_before_nonsample_test
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    before.learnedSamplePending? n k d η hη = none := by
  let strategy := sampledObligatoryStrategy n k d η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hallTests : result.config.transcript.testResults.length = n :=
    hpackage.2.1.testResults_length_eq hpackage.2.2.2.2.2.2
  have hbeforeLength : before.testResults.length = job.val :=
    hpackage.2.2.2.2.1.testsBefore_testResult_eq_label
      hallTests job p (by simpa [result] using hdecomp)
  have haction := hpackage.2.2.2.2.2.1.action_at
    (before := before) (after := after)
    (observation := .testResult job p) (by simpa [result] using hdecomp)
  change testProcessStrategy
      (fun transcript => transcript.sampledObligatoryPending? n k d η hη)
      before = some (.test job) at haction
  have hpendingNone :
      before.sampledObligatoryPending? n k d η hη = none := by
    unfold testProcessStrategy at haction
    cases hpending : before.sampledObligatoryPending? n k d η hη with
    | none => rfl
    | some selected => simp [hpending] at haction
  have hnotSampleLt : ¬before.testResults.length < k := by omega
  cases hsample : before.learnedSamplePending? n k d η hη with
  | none => rfl
  | some selected =>
      simp [Transcript.sampledObligatoryPending?, hnotSampleLt,
        hsample] at hpendingNone

/-- Every positive sampled job classified early has been processed before
the first later nonsample test displayed in the transcript. -/
theorem positive_sample_early_processed_before_nonsample_test
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (hleftSample : left.val < k)
    (horder : left < right) (hright : k ≤ right.val)
    (hpLeft : 0 < processingTime left)
    (hearly : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = true)
    {before after : Transcript n}
    (hrightTest :
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult right (processingTime right) :: after) :
    left ∈ before.processedLabels := by
  by_contra hnotProcessed
  have hnone := learnedSamplePending_none_before_nonsample_test
    n k d η hη processingTime right (processingTime right) hright hrightTest
  unfold Transcript.learnedSamplePending? at hnone
  have hremainingNonempty :
      before.learnedSampleRemainingResults n k d η hη ≠ [] := by
    intro hempty
    have hpackage := run_sampledObligatoryStrategy_looseTrace_package
      n k d η hη processingTime
    have hprefix : before <+:
        (run .infinite (fixedOracle processingTime)
          (sampledObligatoryStrategy n k d η hη)
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
        before.learnedSampleRemainingResults n k d η hη := by
      unfold Transcript.learnedSampleRemainingResults
      apply List.mem_filter.mpr
      refine ⟨hremMem, ?_⟩
      simp [hleftSample, hpLeft, hsampleTake, hearly]
    rw [hempty] at hmem
    simpa using hmem
  have hshort : shortestResult?
      (before.learnedSampleRemainingResults n k d η hη) ≠ none := by
    intro hnoneShort
    exact hremainingNonempty ((shortestResult?_eq_none_iff _).mp hnoneShort)
  exact hshort (Option.map_eq_none_iff.mp hnone)

/-- A positive/zero nonsample outcome classified early is followed
immediately by its administrative process observation. -/
theorem sampled_nonsample_early_next_processed
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {before after : Transcript n} (job : Label n) (p : ℝ)
    (hk : k ≤ job.val)
    (hearly : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k) p = true)
    (hdecomp :
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript =
        before ++ .testResult job p :: after) :
    ∃ rest, after = .processed job :: rest := by
  let strategy := sampledObligatoryStrategy n k d η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hpending := sampledObligatoryPending_after_nonsample_test
    n k d η hη processingTime job p hk hdecomp
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
      transcript.sampledObligatoryPending? n k d η hη)
    hpackage.2.2.2.2.2.1 (by simpa [result] using hdecomp)
    hpending hnotBefore hjobProcessed

/-- If the earlier-tested label is a nonsample early job, its pair word with
every later label is the immediate first word. -/
theorem sampled_pairProjection_of_left_nonsample_early
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hk : k ≤ left.val)
    (hearly : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = true) :
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript
    transcript.pairProjection left right =
      [.testResult left (processingTime left), .processed left,
        .testResult right (processingTime right), .processed right] := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
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
  obtain ⟨rest, hafter⟩ := sampled_nonsample_early_next_processed
    n k d η hη processingTime left (processingTime left) hk hearly
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
theorem sampled_late_process_is_tail_shortest
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) (job : Label n)
    (hlate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime job) = false)
    {before after : Transcript n}
    (hprocess :
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript =
        before ++ .processed job :: after) :
    before.testResults.length = n ∧
      before.shortestRemaining? = some job := by
  let strategy := sampledObligatoryStrategy n k d η hη
  let result := run .infinite (fixedOracle processingTime)
    strategy (2 * n + 1)
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
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
      (fun transcript => transcript.sampledObligatoryPending? n k d η hη)
      before = some (.process job) at haction
  have hpendingNot :
      before.sampledObligatoryPending? n k d η hη ≠ some job := by
    intro hpending
    have hkCount : k ≤ before.testResults.length := by
      by_contra hnot
      have hlt : before.testResults.length < k := by omega
      simp [Transcript.sampledObligatoryPending?, hlt] at hpending
    obtain ⟨p, hpMem, hpEarly⟩ :=
      sampledObligatoryPending_some_classifiedEarly
        before job k d η hη hpending
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
  cases hpending : before.sampledObligatoryPending? n k d η hη with
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
theorem sampled_positive_late_pairCharge_eq
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    (hpLeft : 0 < processingTime left)
    (hpRight : 0 < processingTime right)
    (hleftLate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime left) = false)
    (hrightLate : learnedClassifiesEarly d η hη
      ((fixedTestResults processingTime).take k)
      (processingTime right) = false) :
    let transcript :=
      (run .infinite (fixedOracle processingTime)
        (sampledObligatoryStrategy n k d η hη) (2 * n + 1)).config.transcript
    tracePairCharge .infinite processingTime transcript left right =
      2 + min (processingTime left) (processingTime right) := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  let transcript := result.config.transcript
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
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
    have htail := sampled_late_process_is_tail_shortest
      n k d η hη processingTime left hleftLate
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
    have htail := sampled_late_process_is_tail_shortest
      n k d η hη processingTime right hrightLate
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
    have htail := sampled_late_process_is_tail_shortest
      n k d η hη processingTime left hleftLate
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
theorem run_sampledObligatoryStrategy_cost_eq_self_add_pairCharges
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let result := run .infinite (fixedOracle processingTime)
      (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
    runCompletionCost .infinite processingTime result =
      (∑ job : Label n, (1 + processingTime job)) +
        ∑ left : Label n, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            tracePairCharge .infinite processingTime
              result.config.transcript left right := by
  dsimp only
  let result := run .infinite (fixedOracle processingTime)
    (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
  have hpackage := run_sampledObligatoryStrategy_looseTrace_package
    n k d η hη processingTime
  have hperm := run_sampledObligatoryStrategy_completionLabels_perm
    n k d η hη processingTime
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
