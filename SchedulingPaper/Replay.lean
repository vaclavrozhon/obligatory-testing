import SchedulingPaper.OnlineModel
import Mathlib.Tactic

/-!
# Replay of a finite adaptive interaction

An adaptive oracle may choose a value from the transcript whenever a fresh job
is tested.  This file records the test answers in a finite transcript and
compiles them into one fixed processing-time map.
-/

namespace SchedulingPaper.Online

noncomputable section

def Observation.testResult? : Observation n → Option (Label n × ℝ)
  | .testResult job p => some (job, p)
  | .processed _ | .rawCompleted _ => none

def Transcript.testResults (transcript : Transcript n) :
    List (Label n × ℝ) :=
  transcript.filterMap Observation.testResult?

@[simp] theorem Transcript.testResults_nil :
    (Transcript.testResults ([] : Transcript n)) = [] := rfl

@[simp] theorem Transcript.testResults_testResult_cons
    (job : Label n) (p : ℝ) (transcript : Transcript n) :
    Transcript.testResults (.testResult job p :: transcript) =
      (job, p) :: transcript.testResults := rfl

@[simp] theorem Transcript.testResults_processed_cons
    (job : Label n) (transcript : Transcript n) :
    Transcript.testResults (.processed job :: transcript) =
      transcript.testResults := rfl

@[simp] theorem Transcript.testResults_rawCompleted_cons
    (job : Label n) (transcript : Transcript n) :
    Transcript.testResults (.rawCompleted job :: transcript) =
      transcript.testResults := rfl

@[simp] theorem Transcript.testResults_append
    (left right : Transcript n) :
    (left ++ right).testResults = left.testResults ++ right.testResults := by
  simp [Transcript.testResults]

/-- Values committed by successful test operations. -/
abbrev PartialAssignment (n : ℕ) := Label n → Option ℝ

def emptyAssignment : PartialAssignment n :=
  fun _ => none

def AssignmentAdmissible (cap : Cap)
    (assignment : PartialAssignment n) : Prop :=
  ∀ job p, assignment job = some p → ValueAdmissible cap p

theorem emptyAssignment_admissible (cap : Cap) :
    AssignmentAdmissible cap (emptyAssignment : PartialAssignment n) := by
  intro job p h
  simp [emptyAssignment] at h

/-- Later assignments preserve every earlier commitment. -/
def Extends (earlier later : PartialAssignment n) : Prop :=
  ∀ job p, earlier job = some p → later job = some p

theorem Extends.refl (assignment : PartialAssignment n) :
    Extends assignment assignment :=
  fun _ _ h => h

theorem Extends.trans {first second third : PartialAssignment n}
    (h₁₂ : Extends first second) (h₂₃ : Extends second third) :
    Extends first third :=
  fun job p h => h₂₃ job p (h₁₂ job p h)

/-- Use a previous commitment if one exists; otherwise ask the adaptive
adversary at the current public transcript. -/
def adaptiveValue (adversary : Oracle n) (assignment : PartialAssignment n)
    (transcript : Transcript n) (job : Label n) : ℝ :=
  (assignment job).getD (adversary transcript job)

theorem adaptiveValue_admissible
    (cap : Cap) (adversary : Oracle n)
    (assignment : PartialAssignment n)
    (hadversary : adversary.Admissible cap)
    (hassignment : AssignmentAdmissible cap assignment)
    (transcript : Transcript n) (job : Label n) :
    ValueAdmissible cap
      (adaptiveValue adversary assignment transcript job) := by
  cases hjob : assignment job with
  | none =>
      simpa [adaptiveValue, hjob] using hadversary transcript job
  | some p =>
      simpa [adaptiveValue, hjob] using hassignment job p hjob

def adaptiveOracle (adversary : Oracle n)
    (assignment : PartialAssignment n) : Oracle n :=
  fun transcript job => adaptiveValue adversary assignment transcript job

/-- A test commits its answer.  Other operations do not touch the hidden
partial assignment. -/
def assignmentAfter (adversary : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) : Action n → PartialAssignment n
  | .test job =>
      Function.update assignment job
        (some (adaptiveValue adversary assignment config.transcript job))
  | .process _ | .raw _ => assignment

theorem assignmentAfter_extends (adversary : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n) :
    Extends assignment (assignmentAfter adversary config assignment action) := by
  cases action with
  | process job =>
      exact Extends.refl assignment
  | raw job =>
      exact Extends.refl assignment
  | test testedJob =>
      intro job p hjob
      by_cases heq : job = testedJob
      · subst job
        simp [assignmentAfter, adaptiveValue, hjob]
      · simpa [assignmentAfter, Function.update, heq] using hjob

theorem assignmentAfter_admissible
    (cap : Cap) (adversary : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n)
    (hadversary : adversary.Admissible cap)
    (hassignment : AssignmentAdmissible cap assignment) :
    AssignmentAdmissible cap
      (assignmentAfter adversary config assignment action) := by
  cases action with
  | process job =>
      exact hassignment
  | raw job =>
      exact hassignment
  | test testedJob =>
      intro job p hjob
      by_cases heq : job = testedJob
      · subst job
        have hp :
            adaptiveValue adversary assignment
              config.transcript testedJob = p := by
          simpa [assignmentAfter] using hjob
        rw [← hp]
        exact adaptiveValue_admissible cap adversary assignment
          hadversary hassignment config.transcript testedJob
      · apply hassignment job p
        simpa [assignmentAfter, Function.update, heq] using hjob

@[simp] theorem assignmentAfter_test_at (adversary : Oracle n)
    (config : Config n) (assignment : PartialAssignment n)
    (job : Label n) :
    assignmentAfter adversary config assignment (.test job) job =
      some (adaptiveValue adversary assignment config.transcript job) := by
  simp [assignmentAfter]

/-- One adaptive step, including the hidden commitment made by a test. -/
def adaptiveStep (cap : Cap) (adversary : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n) :
    Option (Config n × PartialAssignment n) :=
  match config.step cap (adaptiveOracle adversary assignment) action with
  | none => none
  | some next =>
      some (next, assignmentAfter adversary config assignment action)

theorem adaptiveStep_extends (cap : Cap) (adversary : Oracle n)
    (config next : Config n) (assignment nextAssignment : PartialAssignment n)
    (action : Action n)
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    Extends assignment nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase :
      config.step cap (adaptiveOracle adversary assignment) action with
  | none =>
      simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_extends adversary config assignment action

theorem adaptiveStep_admissible
    (cap : Cap) (adversary : Oracle n)
    (config next : Config n)
    (assignment nextAssignment : PartialAssignment n)
    (action : Action n)
    (hadversary : adversary.Admissible cap)
    (hassignment : AssignmentAdmissible cap assignment)
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    AssignmentAdmissible cap nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase :
      config.step cap (adaptiveOracle adversary assignment) action with
  | none =>
      simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_admissible cap adversary config assignment
        action hadversary hassignment

theorem adaptiveStep_eq_none_iff (cap : Cap) (adversary : Oracle n)
    (config : Config n) (assignment : PartialAssignment n)
    (action : Action n) :
    adaptiveStep cap adversary config assignment action = none ↔
      config.step cap (adaptiveOracle adversary assignment) action = none := by
  unfold adaptiveStep
  cases config.step cap (adaptiveOracle adversary assignment) action <;> simp

/-- Every test answer already present in the public transcript agrees with
the hidden partial assignment. -/
def MatchesTranscript (assignment : PartialAssignment n)
    (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults →
    assignment job = some p

/-- Conversely, every hidden commitment was created by a public test. -/
def SupportedByTranscript (assignment : PartialAssignment n)
    (transcript : Transcript n) : Prop :=
  ∀ job p, assignment job = some p →
    (job, p) ∈ transcript.testResults

theorem adaptiveStep_matchesTranscript
    (cap : Cap) (adversary : Oracle n)
    (config next : Config n)
    (assignment nextAssignment : PartialAssignment n)
    (action : Action n)
    (hmatch : MatchesTranscript assignment config.transcript)
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    MatchesTranscript nextAssignment next.transcript := by
  cases action with
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          subst nextAssignment
          simpa [MatchesTranscript] using hmatch
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [adaptiveStep, Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [adaptiveStep, Config.step, hjob] at hstep
              rcases hstep with ⟨hnext, hassignment⟩
              subst next
              subst nextAssignment
              simpa [MatchesTranscript] using hmatch
          | tested old =>
              simp [adaptiveStep, Config.step, hjob] at hstep
          | done =>
              simp [adaptiveStep, Config.step, hjob] at hstep
  | test testedJob =>
      cases hjob : config.jobs testedJob with
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          subst nextAssignment
          intro job p hmem
          rw [Transcript.testResults_append] at hmem
          rcases List.mem_append.mp hmem with hold | hnew
          · exact assignmentAfter_extends adversary config assignment
              (.test testedJob) job p (hmatch job p hold)
          · simp only [Transcript.testResults_testResult_cons,
              Transcript.testResults_nil, List.mem_singleton] at hnew
            cases hnew
            exact assignmentAfter_test_at adversary config assignment testedJob

theorem adaptiveStep_supportedByTranscript
    (cap : Cap) (adversary : Oracle n)
    (config next : Config n)
    (assignment nextAssignment : PartialAssignment n)
    (action : Action n)
    (hsupported : SupportedByTranscript assignment config.transcript)
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    SupportedByTranscript nextAssignment next.transcript := by
  cases action with
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          subst nextAssignment
          simpa [SupportedByTranscript] using hsupported
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [adaptiveStep, Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [adaptiveStep, Config.step, hjob] at hstep
              rcases hstep with ⟨hnext, hassignment⟩
              subst next
              subst nextAssignment
              simpa [SupportedByTranscript] using hsupported
          | tested old =>
              simp [adaptiveStep, Config.step, hjob] at hstep
          | done =>
              simp [adaptiveStep, Config.step, hjob] at hstep
  | test testedJob =>
      cases hjob : config.jobs testedJob with
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          subst nextAssignment
          intro job p hassigned
          rw [Transcript.testResults_append]
          apply List.mem_append.mpr
          by_cases heq : job = testedJob
          · subst job
            right
            have hp :
                adaptiveValue adversary assignment
                    config.transcript testedJob = p := by
              simpa [assignmentAfter] using hassigned
            simp [adaptiveOracle, hp]
          · left
            apply hsupported job p
            simpa [assignmentAfter, Function.update, heq] using hassigned

structure AdaptiveResult (n : ℕ) where
  result : RunResult n
  assigned : PartialAssignment n

/-- Fuelled execution against a transcript-dependent adversary. -/
def runAdaptiveFuel (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) :
    ℕ → Config n → PartialAssignment n → AdaptiveResult n
  | 0, config, assignment =>
      ⟨⟨config, .outOfFuel⟩, assignment⟩
  | fuel + 1, config, assignment =>
      match strategy config.transcript with
      | none => ⟨⟨config, .strategyStopped⟩, assignment⟩
      | some action =>
          match adaptiveStep cap adversary config assignment action with
          | none => ⟨⟨config, .invalidAction action⟩, assignment⟩
          | some (next, nextAssignment) =>
              runAdaptiveFuel cap adversary strategy fuel next nextAssignment

theorem runAdaptiveFuel_extends (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (fuel : ℕ) (config : Config n)
    (assignment : PartialAssignment n) :
    Extends assignment
      (runAdaptiveFuel cap adversary strategy fuel config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero =>
      exact Extends.refl assignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using Extends.refl assignment
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using
                Extends.refl assignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              simpa [runAdaptiveFuel, haction, hstep] using
                (adaptiveStep_extends cap adversary config next assignment
                  nextAssignment action hstep).trans
                  (ih next nextAssignment)

theorem runAdaptiveFuel_assignment_admissible
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n)
    (hadversary : adversary.Admissible cap)
    (hassignment : AssignmentAdmissible cap assignment) :
    AssignmentAdmissible cap
      (runAdaptiveFuel cap adversary strategy fuel config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hassignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hassignment
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hassignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                adaptiveStep_admissible cap adversary config next assignment
                  nextAssignment action hadversary hassignment hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem runAdaptiveFuel_matchesTranscript
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n)
    (hmatch : MatchesTranscript assignment config.transcript) :
    MatchesTranscript
      (runAdaptiveFuel cap adversary strategy fuel config assignment).assigned
      (runAdaptiveFuel cap adversary strategy fuel config assignment).result.config.transcript := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hmatch
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hmatch
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hmatch
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                adaptiveStep_matchesTranscript cap adversary config next
                  assignment nextAssignment action hmatch hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem runAdaptiveFuel_supportedByTranscript
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n)
    (hsupported : SupportedByTranscript assignment config.transcript) :
    SupportedByTranscript
      (runAdaptiveFuel cap adversary strategy fuel config assignment).assigned
      (runAdaptiveFuel cap adversary strategy fuel config assignment).result.config.transcript := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hsupported
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hsupported
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hsupported
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                adaptiveStep_supportedByTranscript cap adversary config next
                  assignment nextAssignment action hsupported hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

/-- Complete a partial assignment with arbitrary defaults on labels that were
never tested. -/
def completeAssignment (default : Label n → ℝ)
    (assignment : PartialAssignment n) : Label n → ℝ :=
  fun job => (assignment job).getD (default job)

theorem completeAssignment_admissible
    (cap : Cap) (default : Label n → ℝ)
    (assignment : PartialAssignment n)
    (hdefault : ∀ job, ValueAdmissible cap (default job))
    (hassignment : AssignmentAdmissible cap assignment) :
    ∀ job, ValueAdmissible cap (completeAssignment default assignment job) := by
  intro job
  cases hjob : assignment job with
  | none =>
      simpa [completeAssignment, hjob] using hdefault job
  | some p =>
      simpa [completeAssignment, hjob] using hassignment job p hjob

@[simp] theorem completeAssignment_eq_default
    (default : Label n → ℝ) (assignment : PartialAssignment n)
    (job : Label n) (hjob : assignment job = none) :
    completeAssignment default assignment job = default job := by
  simp [completeAssignment, hjob]

@[simp] theorem completeAssignment_eq_assigned
    (default : Label n → ℝ) (assignment : PartialAssignment n)
    (job : Label n) (p : ℝ) (hjob : assignment job = some p) :
    completeAssignment default assignment job = p := by
  simp [completeAssignment, hjob]

theorem fixedStep_eq_of_adaptiveStep_of_extends
    (cap : Cap) (adversary : Oracle n) (default : Label n → ℝ)
    (config next : Config n)
    (assignment nextAssignment finalAssignment : PartialAssignment n)
    (action : Action n)
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment))
    (hextends : Extends nextAssignment finalAssignment) :
    config.step cap
        (fixedOracle (completeAssignment default finalAssignment)) action =
      some next := by
  cases action with
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          simpa [Config.step, hjob] using hstep.1
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [adaptiveStep, Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [adaptiveStep, Config.step, hjob] at hstep
              simpa [Config.step, hjob] using hstep.1
          | tested old =>
              simp [adaptiveStep, Config.step, hjob] at hstep
          | done =>
              simp [adaptiveStep, Config.step, hjob] at hstep
  | test job =>
      cases hjob : config.jobs job with
      | tested old =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          have hcommitted :
              nextAssignment job =
                some (adaptiveValue adversary assignment
                  config.transcript job) := by
            rw [← hstep.2]
            exact assignmentAfter_test_at adversary config assignment job
          have hfinal :
              finalAssignment job =
                some (adaptiveValue adversary assignment
                  config.transcript job) :=
            hextends job _ hcommitted
          simp [Config.step, hjob, fixedOracle, completeAssignment, hfinal]
          simpa [adaptiveOracle] using hstep.1

/-- General replay theorem from an arbitrary public configuration and an
arbitrary pre-existing partial assignment. -/
theorem replay_from (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (default : Label n → ℝ)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n) :
    let adaptive :=
      runAdaptiveFuel cap adversary strategy fuel config assignment
    runFuel cap
        (fixedOracle (completeAssignment default adaptive.assigned))
        strategy fuel config =
      adaptive.result := by
  induction fuel generalizing config assignment with
  | zero =>
      rfl
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simp [runAdaptiveFuel, runFuel, haction]
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              have hadaptiveNone :
                  config.step cap (adaptiveOracle adversary assignment) action =
                    none :=
                (adaptiveStep_eq_none_iff cap adversary config assignment
                  action).mp hstep
              have hfixedNone :
                  config.step cap
                    (fixedOracle
                      (completeAssignment default assignment)) action = none :=
                (Config.step_eq_none_oracle_independent cap
                  (adaptiveOracle adversary assignment)
                  (fixedOracle (completeAssignment default assignment))
                  config action).mp hadaptiveNone
              simp [runAdaptiveFuel, runFuel, haction, hstep, hfixedNone]
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              let adaptiveTail :=
                runAdaptiveFuel cap adversary strategy fuel next nextAssignment
              have hextends : Extends nextAssignment adaptiveTail.assigned :=
                runAdaptiveFuel_extends cap adversary strategy fuel
                  next nextAssignment
              have hfixedStep :
                  config.step cap
                    (fixedOracle
                      (completeAssignment default adaptiveTail.assigned)) action =
                    some next :=
                fixedStep_eq_of_adaptiveStep_of_extends cap adversary default
                  config next assignment nextAssignment adaptiveTail.assigned
                  action hstep hextends
              simp only [runAdaptiveFuel, haction, hstep]
              dsimp [adaptiveTail] at hfixedStep
              rw [runFuel]
              simp only [haction]
              rw [hfixedStep]
              exact ih next nextAssignment

def adaptiveRun (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (fuel : ℕ) : AdaptiveResult n :=
  runAdaptiveFuel cap adversary strategy fuel
    (Config.initial n) emptyAssignment

/-- The static processing-time vector promised by replay. -/
def frozenProcessingTimes (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (default : Label n → ℝ)
    (fuel : ℕ) : Label n → ℝ :=
  completeAssignment default
    (adaptiveRun cap adversary strategy fuel).assigned

theorem frozenProcessingTimes_admissible
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (default : Label n → ℝ) (fuel : ℕ)
    (hadversary : adversary.Admissible cap)
    (hdefault : ∀ job, ValueAdmissible cap (default job)) :
    ∀ job,
      ValueAdmissible cap
        (frozenProcessingTimes cap adversary strategy default fuel job) := by
  apply completeAssignment_admissible cap default
  · exact hdefault
  · exact runAdaptiveFuel_assignment_admissible cap adversary strategy fuel
      (Config.initial n) emptyAssignment hadversary
      (emptyAssignment_admissible cap)

theorem adaptiveRun_assigned_of_testResult
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) {job : Label n} {p : ℝ}
    (hresult :
      (job, p) ∈
        (adaptiveRun cap adversary strategy fuel).result.config.transcript.testResults) :
    (adaptiveRun cap adversary strategy fuel).assigned job = some p := by
  apply runAdaptiveFuel_matchesTranscript cap adversary strategy fuel
    (Config.initial n) emptyAssignment
  · simp [MatchesTranscript, Config.initial]
  · exact hresult

/-- On every actually tested label the frozen input has exactly the value
published by that test. -/
theorem frozenProcessingTimes_eq_of_testResult
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (default : Label n → ℝ) (fuel : ℕ)
    {job : Label n} {p : ℝ}
    (hresult :
      (job, p) ∈
        (adaptiveRun cap adversary strategy fuel).result.config.transcript.testResults) :
    frozenProcessingTimes cap adversary strategy default fuel job = p := by
  exact completeAssignment_eq_assigned default _ job p
    (adaptiveRun_assigned_of_testResult cap adversary strategy fuel hresult)

theorem frozenProcessingTimes_eq_default_of_unassigned
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (default : Label n → ℝ) (fuel : ℕ) (job : Label n)
    (hjob : (adaptiveRun cap adversary strategy fuel).assigned job = none) :
    frozenProcessingTimes cap adversary strategy default fuel job =
      default job := by
  exact completeAssignment_eq_default default _ job hjob

theorem adaptiveRun_unassigned_of_not_tested
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (job : Label n)
    (hnot :
      ¬ ∃ p,
        (job, p) ∈
          (adaptiveRun cap adversary strategy fuel).result.config.transcript.testResults) :
    (adaptiveRun cap adversary strategy fuel).assigned job = none := by
  have hsupported :=
    runAdaptiveFuel_supportedByTranscript cap adversary strategy fuel
      (Config.initial n) emptyAssignment (by
        simp [SupportedByTranscript, Config.initial, emptyAssignment])
  cases hassigned :
      (adaptiveRun cap adversary strategy fuel).assigned job with
  | none =>
      rfl
  | some p =>
      exact (hnot ⟨p, hsupported job p hassigned⟩).elim

/-- A label never tested in the adaptive execution receives precisely its
chosen default value in the frozen input. -/
theorem frozenProcessingTimes_eq_default_of_not_tested
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (default : Label n → ℝ) (fuel : ℕ) (job : Label n)
    (hnot :
      ¬ ∃ p,
        (job, p) ∈
          (adaptiveRun cap adversary strategy fuel).result.config.transcript.testResults) :
    frozenProcessingTimes cap adversary strategy default fuel job =
      default job := by
  exact frozenProcessingTimes_eq_default_of_unassigned
    cap adversary strategy default fuel job
    (adaptiveRun_unassigned_of_not_tested cap adversary strategy fuel job hnot)

/-- Every finite adaptive execution is exactly reproduced by the same
deterministic strategy on one fixed processing-time vector. -/
theorem replay (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (default : Label n → ℝ) (fuel : ℕ) :
    run cap
        (fixedOracle
          (frozenProcessingTimes cap adversary strategy default fuel))
        strategy fuel =
      (adaptiveRun cap adversary strategy fuel).result := by
  exact replay_from cap adversary strategy default fuel
    (Config.initial n) emptyAssignment

end

end SchedulingPaper.Online
