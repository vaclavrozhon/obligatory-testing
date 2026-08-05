import SchedulingPaper.TestProcessCanonicalTrace
import Mathlib.Tactic

/-!
# Two-label projections of a canonical test/process trace

For two labels in increasing test order, every completed test/process trace
has one of the three familiar four-operation projections: the left job is
processed immediately, the right job is processed before a deferred left
job, or the deferred left job is processed before the deferred right job.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Every observation in a canonical trace belongs to a label that has
already been tested. -/
theorem TestProcessTrace.ownerLabel_lt_testResults_length
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    {observation : Observation n}
    (hmem : observation ∈ transcript) :
    observation.ownerLabel.val <
      transcript.testResults.length := by
  induction htrace with
  | nil =>
      simp at hmem
  | @test transcript htrace hlt p ih =>
      rw [List.mem_append] at hmem
      simp only [List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · have holdBound := ih hold
        simp only [Transcript.testResults_append_testResult,
          List.length_append, List.length_singleton]
        omega
      · simp [Observation.ownerLabel]
  | @immediate transcript job p htrace hlast hnotProcessed ih =>
      rw [List.mem_append] at hmem
      simp only [List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · simpa using ih hold
      · have htestMem :
            (job, p) ∈ transcript.testResults := by
          apply List.mem_filterMap.mpr
          exact
            ⟨.testResult job p, List.mem_of_getLast? hlast, rfl⟩
        have hvalueMem :
            job.val ∈
              transcript.testResults.map
                (fun result => result.1.val) :=
          List.mem_map.mpr
            ⟨(job, p), htestMem, rfl⟩
        rw [htrace.testOrder] at hvalueMem
        simpa [Observation.ownerLabel] using hvalueMem
  | @tail transcript job htrace hall hnotProcessed ih =>
      rw [List.mem_append] at hmem
      simp only [List.mem_singleton] at hmem
      rcases hmem with hold | rfl
      · simpa using ih hold
      · simpa [Observation.ownerLabel, hall] using job.isLt

@[simp] theorem Transcript.pairProjection_append
    (left right : Label n) (before after : Transcript n) :
    (before ++ after).pairProjection left right =
      before.pairProjection left right ++
        after.pairProjection left right := by
  simp [Transcript.pairProjection, List.filter_append]

@[simp] theorem Transcript.pairProjection_testResult_left
    {left right : Label n} (hne : left ≠ right) (p : ℝ) :
    Transcript.pairProjection left right
        ([Observation.testResult left p] : Transcript n) =
      [Observation.testResult left p] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

@[simp] theorem Transcript.pairProjection_testResult_right
    {left right : Label n} (hne : left ≠ right) (q : ℝ) :
    Transcript.pairProjection left right
        ([Observation.testResult right q] : Transcript n) =
      [Observation.testResult right q] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

@[simp] theorem Transcript.pairProjection_testResult_other
    {left right job : Label n}
    (hleft : job ≠ left) (hright : job ≠ right) (p : ℝ) :
    Transcript.pairProjection left right
        ([Observation.testResult job p] : Transcript n) = [] := by
  simp [Transcript.pairProjection, Observation.ownerLabel,
    hleft, hright]

@[simp] theorem Transcript.pairProjection_processed_left
    {left right : Label n} (hne : left ≠ right) :
    Transcript.pairProjection left right
        ([Observation.processed left] : Transcript n) =
      [Observation.processed left] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

@[simp] theorem Transcript.pairProjection_processed_right
    {left right : Label n} (hne : left ≠ right) :
    Transcript.pairProjection left right
        ([Observation.processed right] : Transcript n) =
      [Observation.processed right] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

@[simp] theorem Transcript.pairProjection_processed_other
    {left right job : Label n}
    (hleft : job ≠ left) (hright : job ≠ right) :
    Transcript.pairProjection left right
        ([Observation.processed job] : Transcript n) = [] := by
  simp [Transcript.pairProjection, Observation.ownerLabel,
    hleft, hright]

theorem Transcript.pairProjection_getLast?_eq
    {left right : Label n} {transcript : Transcript n}
    {observation : Observation n}
    (hlast : transcript.getLast? = some observation)
    (howner :
      observation.ownerLabel = left ∨
        observation.ownerLabel = right) :
    (transcript.pairProjection left right).getLast? =
      some observation := by
  rcases List.getLast?_eq_some_iff.mp hlast with
    ⟨before, rfl⟩
  have hkeep :
      Transcript.pairProjection left right
          ([observation] : Transcript n) =
        [observation] := by
    simp only [Transcript.pairProjection, List.filter_cons,
      List.filter_nil]
    have hdecide :
        decide
          (observation.ownerLabel = left ∨
            observation.ownerLabel = right) = true := by
      simp [howner]
    rw [if_pos hdecide]
  rw [Transcript.pairProjection_append]
  rw [hkeep]
  simp

theorem Transcript.processedLabel_mem_of_processed_mem_pairProjection
    {left right job : Label n} {transcript : Transcript n}
    (hmem :
      Observation.processed job ∈
        transcript.pairProjection left right) :
    job ∈ transcript.processedLabels := by
  have hobs :
      Observation.processed job ∈ transcript :=
    List.mem_of_mem_filter hmem
  apply List.mem_filterMap.mpr
  exact ⟨Observation.processed job, hobs, rfl⟩

/-- The complete finite-state language of a two-label projection, refined
by how many labels have already been tested. -/
def CanonicalPairPhase
    (processingTime : Label n → ℝ)
    (left right : Label n) (transcript : Transcript n) : Prop :=
  let p := processingTime left
  let q := processingTime right
  let projection := transcript.pairProjection left right
  let tested := transcript.testResults.length
  (tested ≤ left.val ∧ projection = []) ∨
  (left.val < tested ∧ tested ≤ right.val ∧
    (projection = [.testResult left p] ∨
      projection =
        [.testResult left p, .processed left])) ∨
  (right.val < tested ∧
    (projection =
        [.testResult left p, .processed left,
          .testResult right q] ∨
      projection =
        [.testResult left p, .processed left,
          .testResult right q, .processed right] ∨
      projection =
        [.testResult left p, .testResult right q] ∨
      projection =
        [.testResult left p, .testResult right q,
          .processed right] ∨
      projection =
        [.testResult left p, .testResult right q,
          .processed left] ∨
      projection =
        [.testResult left p, .testResult right q,
          .processed right, .processed left] ∨
      projection =
        [.testResult left p, .testResult right q,
          .processed left, .processed right]))

theorem CanonicalPairPhase.afterTest
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    {transcript : Transcript n}
    (hphase :
      CanonicalPairPhase processingTime left right transcript)
    (hlt : transcript.testResults.length < n) (value : ℝ)
    (hvalue :
      value =
        processingTime
          ⟨transcript.testResults.length, hlt⟩) :
    CanonicalPairPhase processingTime left right
      (transcript ++
        [.testResult
          ⟨transcript.testResults.length, hlt⟩ value]) := by
  have hne : left ≠ right := ne_of_lt horder
  have horderVal : left.val < right.val := horder
  let tested := transcript.testResults.length
  let job : Label n := ⟨tested, by simpa [tested] using hlt⟩
  have hjobVal : job.val = tested := rfl
  change
    CanonicalPairPhase processingTime left right
      (transcript ++ [.testResult job value])
  change value = processingTime job at hvalue
  unfold CanonicalPairPhase at hphase ⊢
  simp only [Transcript.testResults_append_testResult,
    List.length_append, List.length_singleton,
    Transcript.pairProjection_append]
  rcases lt_trichotomy tested left.val with
      hbefore | heqLeft | hafterLeft
  · have hjobLeft : job ≠ left := by
      intro heq
      have := congrArg Fin.val heq
      simp [job, tested] at this
      omega
    have hjobRight : job ≠ right := by
      intro heq
      have := congrArg Fin.val heq
      simp [job, tested] at this
      omega
    rcases hphase with hphase | hphase | hphase
    · refine Or.inl ⟨by omega, ?_⟩
      rw [hphase.2,
        Transcript.pairProjection_testResult_other
          hjobLeft hjobRight]
      simp
    · omega
    · omega
  · have hjobLeft : job = left := by
      apply Fin.ext
      simpa [job, tested] using heqLeft
    rw [hjobLeft] at hvalue
    subst value
    have hsingleton :
        Transcript.pairProjection left right
            ([Observation.testResult job
              (processingTime left)] : Transcript n) =
          [Observation.testResult left
            (processingTime left)] := by
      rw [hjobLeft]
      exact Transcript.pairProjection_testResult_left hne _
    rcases hphase with hphase | hphase | hphase
    · refine Or.inr (Or.inl ⟨by omega, by omega, Or.inl ?_⟩)
      rw [hphase.2, hsingleton]
      simp
    · omega
    · omega
  · rcases lt_trichotomy tested right.val with
        hbeforeRight | heqRight | hafterRight
    · have hjobLeft : job ≠ left := by
        intro heq
        have := congrArg Fin.val heq
        simp [job, tested] at this
        omega
      have hjobRight : job ≠ right := by
        intro heq
        have := congrArg Fin.val heq
        simp [job, tested] at this
        omega
      rcases hphase with hphase | hphase | hphase
      · omega
      · refine Or.inr (Or.inl
          ⟨by omega, by omega, ?_⟩)
        rcases hphase.2.2 with hdeferred | himmediate
        · left
          rw [hdeferred,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp

        · right
          rw [himmediate,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
      · omega
    · have hjobRight : job = right := by
        apply Fin.ext
        simpa [job, tested] using heqRight
      rw [hjobRight] at hvalue
      subst value
      have hsingleton :
          Transcript.pairProjection left right
              ([Observation.testResult job
                (processingTime right)] : Transcript n) =
            [Observation.testResult right
              (processingTime right)] := by
        rw [hjobRight]
        exact Transcript.pairProjection_testResult_right hne _
      rcases hphase with hphase | hphase | hphase
      · omega
      · refine Or.inr (Or.inr
          ⟨by omega, ?_⟩)
        rcases hphase.2.2 with hdeferred | himmediate
        · exact Or.inr (Or.inr (Or.inl (by
            rw [hdeferred, hsingleton]
            simp)))
        · exact Or.inl (by
            rw [himmediate, hsingleton]
            simp)
      · omega
    · have hjobLeft : job ≠ left := by
        intro heq
        have := congrArg Fin.val heq
        simp [job, tested] at this
        omega
      have hjobRight : job ≠ right := by
        intro heq
        have := congrArg Fin.val heq
        simp [job, tested] at this
        omega
      rcases hphase with hphase | hphase | hphase
      · omega
      · omega
      · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        rcases hphase.2 with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
        · refine Or.inl ?_
          rw [h₁,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inl ?_)
          rw [h₂,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inr (Or.inl ?_))
          rw [h₃,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          rw [h₄,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          rw [h₅,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          rw [h₆,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp
        · refine Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
          rw [h₇,
            Transcript.pairProjection_testResult_other
              hjobLeft hjobRight]
          simp

theorem CanonicalPairPhase.afterImmediate
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    {transcript : Transcript n} {job : Label n} {value : ℝ}
    (hphase :
      CanonicalPairPhase processingTime left right transcript)
    (hlast :
      transcript.getLast? =
        some (.testResult job value))
    (hnotProcessed : job ∉ transcript.processedLabels) :
    CanonicalPairPhase processingTime left right
      (transcript ++ [.processed job]) := by
  have hne : left ≠ right := ne_of_lt horder
  have hne' : right ≠ left := Ne.symm hne
  by_cases hjobLeft : job = left
  · subst job
    have hprojectionLast :
        (transcript.pairProjection left right).getLast? =
          some (.testResult left value) :=
      Transcript.pairProjection_getLast?_eq hlast (Or.inl rfl)
    have hnoProcess :
        Observation.processed left ∉
          transcript.pairProjection left right := by
      intro hmem
      exact hnotProcessed
        (Transcript.processedLabel_mem_of_processed_mem_pairProjection
          hmem)
    unfold CanonicalPairPhase at hphase ⊢
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      Transcript.testResults_nil, List.append_nil,
      Transcript.pairProjection_append]
    rcases hphase with hphase | hphase | hphase
    · rw [hphase.2] at hprojectionLast
      simp at hprojectionLast
    · rcases hphase.2.2 with hdeferred | himmediate
      · refine Or.inr (Or.inl
          ⟨hphase.1, hphase.2.1, Or.inr ?_⟩)
        rw [hdeferred,
          Transcript.pairProjection_processed_left hne]
        simp
      · exfalso
        apply hnoProcess
        rw [himmediate]
        simp
    · rcases hphase.2 with
        h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
      · rw [h₁] at hprojectionLast
        simp [hne, hne'] at hprojectionLast
      · exfalso
        apply hnoProcess
        rw [h₂]
        simp
      · rw [h₃] at hprojectionLast
        simp [hne, hne'] at hprojectionLast
      · rw [h₄] at hprojectionLast
        simp [hne, hne'] at hprojectionLast
      · exfalso
        apply hnoProcess
        rw [h₅]
        simp
      · exfalso
        apply hnoProcess
        rw [h₆]
        simp
      · exfalso
        apply hnoProcess
        rw [h₇]
        simp
  · by_cases hjobRight : job = right
    · subst job
      have hprojectionLast :
          (transcript.pairProjection left right).getLast? =
            some (.testResult right value) :=
        Transcript.pairProjection_getLast?_eq hlast (Or.inr rfl)
      have hnoProcess :
          Observation.processed right ∉
            transcript.pairProjection left right := by
        intro hmem
        exact hnotProcessed
          (Transcript.processedLabel_mem_of_processed_mem_pairProjection
            hmem)
      unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rcases hphase with hphase | hphase | hphase
      · rw [hphase.2] at hprojectionLast
        simp at hprojectionLast
      · rcases hphase.2.2 with h₁ | h₂
        · rw [h₁] at hprojectionLast
          simp [hne, hne'] at hprojectionLast
        · rw [h₂] at hprojectionLast
          simp [hne, hne'] at hprojectionLast
      · refine Or.inr (Or.inr ⟨hphase.1, ?_⟩)
        rcases hphase.2 with
          h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
        · refine Or.inr (Or.inl ?_)
          rw [h₁,
            Transcript.pairProjection_processed_right hne]
          simp
        · exfalso
          apply hnoProcess
          rw [h₂]
          simp
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          rw [h₃,
            Transcript.pairProjection_processed_right hne]
          simp
        · exfalso
          apply hnoProcess
          rw [h₄]
          simp
        · rw [h₅] at hprojectionLast
          simp [hne, hne'] at hprojectionLast
        · exfalso
          apply hnoProcess
          rw [h₆]
          simp
        · exfalso
          apply hnoProcess
          rw [h₇]
          simp
    · unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rw [Transcript.pairProjection_processed_other
        hjobLeft hjobRight]
      simpa using hphase

theorem CanonicalPairPhase.afterTail
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right)
    {transcript : Transcript n} {job : Label n}
    (hphase :
      CanonicalPairPhase processingTime left right transcript)
    (hall : transcript.testResults.length = n)
    (hnotProcessed : job ∉ transcript.processedLabels) :
    CanonicalPairPhase processingTime left right
      (transcript ++ [.processed job]) := by
  have hne : left ≠ right := ne_of_lt horder
  have hrightBound : right.val < n := right.isLt
  by_cases hjobLeft : job = left
  · subst job
    have hnoProcess :
        Observation.processed left ∉
          transcript.pairProjection left right := by
      intro hmem
      exact hnotProcessed
        (Transcript.processedLabel_mem_of_processed_mem_pairProjection
          hmem)
    unfold CanonicalPairPhase at hphase ⊢
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      Transcript.testResults_nil, List.append_nil,
      Transcript.pairProjection_append]
    rcases hphase with hphase | hphase | hphase
    · omega
    · omega
    · refine Or.inr (Or.inr ⟨hphase.1, ?_⟩)
      rcases hphase.2 with
        h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
      · exfalso
        apply hnoProcess
        rw [h₁]
        simp
      · exfalso
        apply hnoProcess
        rw [h₂]
        simp
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [h₃,
          Transcript.pairProjection_processed_left hne]
        simp
      · refine Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        rw [h₄,
          Transcript.pairProjection_processed_left hne]
        simp
      · exfalso
        apply hnoProcess
        rw [h₅]
        simp
      · exfalso
        apply hnoProcess
        rw [h₆]
        simp
      · exfalso
        apply hnoProcess
        rw [h₇]
        simp
  · by_cases hjobRight : job = right
    · subst job
      have hnoProcess :
          Observation.processed right ∉
            transcript.pairProjection left right := by
        intro hmem
        exact hnotProcessed
          (Transcript.processedLabel_mem_of_processed_mem_pairProjection
            hmem)
      unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rcases hphase with hphase | hphase | hphase
      · omega
      · omega
      · refine Or.inr (Or.inr ⟨hphase.1, ?_⟩)
        rcases hphase.2 with
          h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
        · refine Or.inr (Or.inl ?_)
          rw [h₁,
            Transcript.pairProjection_processed_right hne]
          simp
        · exfalso
          apply hnoProcess
          rw [h₂]
          simp
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          rw [h₃,
            Transcript.pairProjection_processed_right hne]
          simp
        · exfalso
          apply hnoProcess
          rw [h₄]
          simp
        · refine Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
          rw [h₅,
            Transcript.pairProjection_processed_right hne]
          simp
        · exfalso
          apply hnoProcess
          rw [h₆]
          simp
        · exfalso
          apply hnoProcess
          rw [h₇]
          simp
    · unfold CanonicalPairPhase at hphase ⊢
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        Transcript.testResults_nil, List.append_nil,
        Transcript.pairProjection_append]
      rw [Transcript.pairProjection_processed_other
        hjobLeft hjobRight]
      simpa using hphase

/-- Canonical traces whose published answers match a fixed vector satisfy
the two-label phase automaton. -/
theorem TestProcessTrace.canonicalPairPhase
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    {left right : Label n} (horder : left < right) :
    CanonicalPairPhase processingTime left right transcript := by
  induction htrace with
  | nil =>
      simp [CanonicalPairPhase, Transcript.pairProjection]
  | @test transcript htrace hlt value ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        intro job p hmem
        apply hmatch job p
        rw [Transcript.testResults_append_testResult]
        exact List.mem_append_left _ hmem
      have hvalue :
          value =
            processingTime
              ⟨transcript.testResults.length, hlt⟩ := by
        apply hmatch
        simp
      exact CanonicalPairPhase.afterTest processingTime horder
        (ih hmatchOld) hlt value hvalue
  | @immediate transcript job value htrace hlast hnotProcessed ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      exact CanonicalPairPhase.afterImmediate processingTime horder
        (ih hmatchOld) hlast hnotProcessed
  | @tail transcript job htrace hall hnotProcessed ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      exact CanonicalPairPhase.afterTail processingTime horder
        (ih hmatchOld) hall hnotProcessed

theorem Transcript.processed_mem_pairProjection_of_mem_processedLabels
    {left right job : Label n} {transcript : Transcript n}
    (howner : job = left ∨ job = right)
    (hmem : job ∈ transcript.processedLabels) :
    Observation.processed job ∈
      transcript.pairProjection left right := by
  rcases List.mem_filterMap.mp hmem with
    ⟨observation, hobs, hvalue⟩
  cases observation with
  | testResult tested p =>
      simp at hvalue
  | processed processed =>
      have heq : processed = job :=
        Option.some.inj hvalue
      subst processed
      apply List.mem_filter.mpr
      refine ⟨hobs, ?_⟩
      rcases howner with rfl | rfl <;>
        simp [Observation.ownerLabel]
  | rawCompleted raw =>
      simp at hvalue

/-- At completion, a two-label projection is exactly one of the three
four-operation words. -/
theorem TestProcessTrace.terminal_pairProjection_shapes
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed :
      ∀ job, job ∈ transcript.processedLabels)
    {left right : Label n} (horder : left < right) :
    transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .processed left,
          .testResult right (processingTime right),
          .processed right] ∨
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed right, .processed left] ∨
      transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed left, .processed right] := by
  have hne : left ≠ right := ne_of_lt horder
  have hphase :=
    htrace.canonicalPairPhase hmatch horder
  have hrightBound : right.val < n := right.isLt
  have hleftProcessed :
      Observation.processed left ∈
        transcript.pairProjection left right :=
    Transcript.processed_mem_pairProjection_of_mem_processedLabels
      (Or.inl rfl) (hallProcessed left)
  have hrightProcessed :
      Observation.processed right ∈
        transcript.pairProjection left right :=
    Transcript.processed_mem_pairProjection_of_mem_processedLabels
      (Or.inr rfl) (hallProcessed right)
  unfold CanonicalPairPhase at hphase
  rcases hphase with hphase | hphase | hphase
  · omega
  · omega
  · rcases hphase.2 with
      h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
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

@[simp] theorem Transcript.pairProjection_self_testResult
    (job : Label n) (p : ℝ) :
    Transcript.pairProjection job job
        ([Observation.testResult job p] : Transcript n) =
      [Observation.testResult job p] := by
  simp [Transcript.pairProjection, Observation.ownerLabel]

@[simp] theorem Transcript.pairProjection_self_processed
    (job : Label n) :
    Transcript.pairProjection job job
        ([Observation.processed job] : Transcript n) =
      [Observation.processed job] := by
  simp [Transcript.pairProjection, Observation.ownerLabel]

@[simp] theorem Transcript.pairProjection_self_other_testResult
    {job other : Label n} (hne : other ≠ job) (p : ℝ) :
    Transcript.pairProjection job job
        ([Observation.testResult other p] : Transcript n) = [] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

@[simp] theorem Transcript.pairProjection_self_other_processed
    {job other : Label n} (hne : other ≠ job) :
    Transcript.pairProjection job job
        ([Observation.processed other] : Transcript n) = [] := by
  simp [Transcript.pairProjection, Observation.ownerLabel, hne]

/-- The one-label projection before and after the label's unique test. -/
def CanonicalSelfPhase
    (processingTime : Label n → ℝ)
    (job : Label n) (transcript : Transcript n) : Prop :=
  let p := processingTime job
  let projection := transcript.pairProjection job job
  let tested := transcript.testResults.length
  (tested ≤ job.val ∧ projection = []) ∨
  (job.val < tested ∧
    (projection = [.testResult job p] ∨
      projection =
        [.testResult job p, .processed job]))

theorem CanonicalSelfPhase.afterTest
    (processingTime : Label n → ℝ) (job : Label n)
    {transcript : Transcript n}
    (hphase :
      CanonicalSelfPhase processingTime job transcript)
    (hlt : transcript.testResults.length < n) (value : ℝ)
    (hvalue :
      value =
        processingTime
          ⟨transcript.testResults.length, hlt⟩) :
    CanonicalSelfPhase processingTime job
      (transcript ++
        [.testResult
          ⟨transcript.testResults.length, hlt⟩ value]) := by
  let tested := transcript.testResults.length
  let testedJob : Label n :=
    ⟨tested, by simpa [tested] using hlt⟩
  change
    CanonicalSelfPhase processingTime job
      (transcript ++ [.testResult testedJob value])
  change value = processingTime testedJob at hvalue
  unfold CanonicalSelfPhase at hphase ⊢
  simp only [Transcript.testResults_append_testResult,
    List.length_append, List.length_singleton,
    Transcript.pairProjection_append]
  rcases lt_trichotomy tested job.val with
      hbefore | heq | hafter
  · have hne : testedJob ≠ job := by
      intro h
      have := congrArg Fin.val h
      simp [testedJob, tested] at this
      omega
    rcases hphase with hphase | hphase
    · refine Or.inl ⟨by omega, ?_⟩
      rw [hphase.2,
        Transcript.pairProjection_self_other_testResult hne]
      simp
    · omega
  · have heqJob : testedJob = job := by
      apply Fin.ext
      simpa [testedJob, tested] using heq
    rw [heqJob] at hvalue
    subst value
    rcases hphase with hphase | hphase
    · refine Or.inr ⟨by omega, Or.inl ?_⟩
      rw [hphase.2]
      have hsingleton :
          Transcript.pairProjection job job
              ([Observation.testResult testedJob
                (processingTime job)] : Transcript n) =
            [Observation.testResult job
              (processingTime job)] := by
        rw [heqJob]
        exact Transcript.pairProjection_self_testResult _ _
      rw [hsingleton]
      simp
    · omega
  · have hne : testedJob ≠ job := by
      intro h
      have := congrArg Fin.val h
      simp [testedJob, tested] at this
      omega
    rcases hphase with hphase | hphase
    · omega
    · refine Or.inr ⟨by omega, ?_⟩
      rcases hphase.2 with htested | hprocessed
      · left
        rw [htested,
          Transcript.pairProjection_self_other_testResult hne]
        simp
      · right
        rw [hprocessed,
          Transcript.pairProjection_self_other_testResult hne]
        simp

theorem CanonicalSelfPhase.afterProcess
    (processingTime : Label n → ℝ) (job : Label n)
    {transcript : Transcript n} {processed : Label n}
    (hphase :
      CanonicalSelfPhase processingTime job transcript)
    (hprocessedTested :
      processed = job →
        job.val < transcript.testResults.length)
    (hnotProcessed :
      processed ∉ transcript.processedLabels) :
    CanonicalSelfPhase processingTime job
      (transcript ++ [.processed processed]) := by
  by_cases heq : processed = job
  · subst processed
    have hnoProcess :
        Observation.processed job ∉
          transcript.pairProjection job job := by
      intro hmem
      exact hnotProcessed
        (Transcript.processedLabel_mem_of_processed_mem_pairProjection
          hmem)
    unfold CanonicalSelfPhase at hphase ⊢
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      Transcript.testResults_nil, List.append_nil,
      Transcript.pairProjection_append]
    rcases hphase with hphase | hphase
    · exact (not_lt_of_ge hphase.1 (hprocessedTested rfl)).elim
    · refine Or.inr ⟨hphase.1, ?_⟩
      rcases hphase.2 with htested | halready
      · right
        rw [htested,
          Transcript.pairProjection_self_processed]
        simp
      · exfalso
        apply hnoProcess
        rw [halready]
        simp
  · unfold CanonicalSelfPhase at hphase ⊢
    simp only [Transcript.testResults_append,
      Transcript.testResults_processed_cons,
      Transcript.testResults_nil, List.append_nil,
      Transcript.pairProjection_append]
    rw [Transcript.pairProjection_self_other_processed heq]
    simpa using hphase

theorem TestProcessTrace.canonicalSelfPhase
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (job : Label n) :
    CanonicalSelfPhase processingTime job transcript := by
  induction htrace with
  | nil =>
      simp [CanonicalSelfPhase, Transcript.pairProjection]
  | @test transcript htrace hlt value ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        intro tested p hmem
        apply hmatch tested p
        rw [Transcript.testResults_append_testResult]
        exact List.mem_append_left _ hmem
      have hvalue :
          value =
            processingTime
              ⟨transcript.testResults.length, hlt⟩ := by
        apply hmatch
        simp
      exact CanonicalSelfPhase.afterTest processingTime job
        (ih hmatchOld) hlt value hvalue
  | @immediate transcript processed value htrace hlast hnotProcessed ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      have htested :
          processed = job →
            job.val < transcript.testResults.length := by
        intro heq
        subst processed
        have hobs :
            Observation.testResult job value ∈ transcript :=
          List.mem_of_getLast? hlast
        exact htrace.ownerLabel_lt_testResults_length hobs
      exact CanonicalSelfPhase.afterProcess processingTime job
        (ih hmatchOld) htested hnotProcessed
  | @tail transcript processed htrace hall hnotProcessed ih =>
      have hmatchOld :
          transcript.TestsMatch processingTime := by
        simpa [Transcript.TestsMatch] using hmatch
      have htested :
          processed = job →
            job.val < transcript.testResults.length := by
        intro _heq
        rw [hall]
        exact job.isLt
      exact CanonicalSelfPhase.afterProcess processingTime job
        (ih hmatchOld) htested hnotProcessed

/-- Every completed canonical run has exactly the job's test followed by its
administrative process in the one-label projection. -/
theorem TestProcessTrace.terminal_selfProjection
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed :
      ∀ job, job ∈ transcript.processedLabels)
    (job : Label n) :
    transcript.pairProjection job job =
      [.testResult job (processingTime job),
        .processed job] := by
  have hphase := htrace.canonicalSelfPhase hmatch job
  have hbound : job.val < n := job.isLt
  have hprocess :
      Observation.processed job ∈
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

end

end SchedulingPaper.Online
