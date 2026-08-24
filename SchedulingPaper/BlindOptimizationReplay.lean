import SchedulingPaper.BlindOptimizationModel
import Mathlib.Tactic

/-!
# Replay for blind optimization

An optimized block queries a transcript-dependent adversary only when the
block is started; a raw block never queries it.  This file records those
commitments and proves that every finite adaptive interaction is reproduced
exactly on one fixed labeled input.  It is the blind-block counterpart of
`SchedulingPaper.Replay`.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace Replay

open Online

noncomputable section

abbrev Oracle (n : ℕ) := Transcript n → Fin n → ℝ
abbrev PartialAssignment (n : ℕ) := Fin n → Option ℝ

def Oracle.Admissible (u : ℝ) (oracle : Oracle n) : Prop :=
  ∀ transcript job, oracle transcript job ∈ Set.Icc (0 : ℝ) u

def emptyAssignment : PartialAssignment n := fun _ ↦ none

def AssignmentAdmissible (u : ℝ) (assignment : PartialAssignment n) : Prop :=
  ∀ job p, assignment job = some p → p ∈ Set.Icc (0 : ℝ) u

def Extends (earlier later : PartialAssignment n) : Prop :=
  ∀ job p, earlier job = some p → later job = some p

theorem Extends.refl (assignment : PartialAssignment n) :
    Extends assignment assignment := fun _ _ h ↦ h

theorem Extends.trans {first second third : PartialAssignment n}
    (h₁₂ : Extends first second) (h₂₃ : Extends second third) :
    Extends first third := fun job p h ↦ h₂₃ job p (h₁₂ job p h)

def SupportedByTranscript (assignment : PartialAssignment n)
    (transcript : Transcript n) : Prop :=
  ∀ job p, assignment job = some p →
    Observation.optimizedCompleted job p ∈ transcript

def adaptiveValue (oracle : Oracle n) (assignment : PartialAssignment n)
    (transcript : Transcript n) (job : Fin n) : ℝ :=
  (assignment job).getD (oracle transcript job)

def adaptiveProcessing (oracle : Oracle n) (assignment : PartialAssignment n)
    (transcript : Transcript n) : Fin n → ℝ :=
  fun job ↦ adaptiveValue oracle assignment transcript job

def assignmentAfter (oracle : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n) :
    PartialAssignment n :=
  match action.mode with
  | .raw => assignment
  | .optimized => Function.update assignment action.job
      (some (adaptiveValue oracle assignment config.transcript action.job))

theorem assignmentAfter_extends (oracle : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n) :
    Extends assignment (assignmentAfter oracle config assignment action) := by
  intro job p hjob
  cases hmode : action.mode with
  | raw => simpa [assignmentAfter, hmode] using hjob
  | optimized =>
      by_cases heq : job = action.job
      · subst job
        simp [assignmentAfter, hmode, adaptiveValue, hjob]
      · simpa [assignmentAfter, hmode, Function.update, heq] using hjob

theorem adaptiveValue_admissible
    {u : ℝ} (oracle : Oracle n) (assignment : PartialAssignment n)
    (horacle : oracle.Admissible u)
    (hassignment : AssignmentAdmissible u assignment)
    (transcript : Transcript n) (job : Fin n) :
    adaptiveValue oracle assignment transcript job ∈ Set.Icc (0 : ℝ) u := by
  cases hjob : assignment job with
  | none => simpa [adaptiveValue, hjob] using horacle transcript job
  | some p => simpa [adaptiveValue, hjob] using hassignment job p hjob

theorem assignmentAfter_admissible
    {u : ℝ} (oracle : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n)
    (horacle : oracle.Admissible u)
    (hassignment : AssignmentAdmissible u assignment) :
    AssignmentAdmissible u (assignmentAfter oracle config assignment action) := by
  intro job p hjob
  cases hmode : action.mode with
  | raw => exact hassignment job p (by simpa [assignmentAfter, hmode] using hjob)
  | optimized =>
      by_cases heq : job = action.job
      · subst job
        have hp : adaptiveValue oracle assignment
            config.transcript action.job = p := by
          simpa [assignmentAfter, hmode] using hjob
        rw [← hp]
        exact adaptiveValue_admissible oracle assignment horacle hassignment _ _
      · exact hassignment job p (by
          simpa [assignmentAfter, hmode, Function.update, heq] using hjob)

def adaptiveStep (oracle : Oracle n) (config : Config n)
    (assignment : PartialAssignment n) (action : Action n) :
    Option (Config n × PartialAssignment n) :=
  match config.step (adaptiveProcessing oracle assignment config.transcript) action with
  | none => none
  | some next => some (next, assignmentAfter oracle config assignment action)

theorem adaptiveStep_extends
    (oracle : Oracle n) (config next : Config n)
    (assignment nextAssignment : PartialAssignment n) (action : Action n)
    (hstep : adaptiveStep oracle config assignment action =
      some (next, nextAssignment)) :
    Extends assignment nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase : config.step
      (adaptiveProcessing oracle assignment config.transcript) action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_extends oracle config assignment action

theorem adaptiveStep_admissible
    {u : ℝ} (oracle : Oracle n) (config next : Config n)
    (assignment nextAssignment : PartialAssignment n) (action : Action n)
    (horacle : oracle.Admissible u)
    (hassignment : AssignmentAdmissible u assignment)
    (hstep : adaptiveStep oracle config assignment action =
      some (next, nextAssignment)) :
    AssignmentAdmissible u nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase : config.step
      (adaptiveProcessing oracle assignment config.transcript) action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_admissible oracle config assignment action
        horacle hassignment

theorem adaptiveStep_supportedByTranscript
    (oracle : Oracle n) (config next : Config n)
    (assignment nextAssignment : PartialAssignment n) (action : Action n)
    (hsupported : SupportedByTranscript assignment config.transcript)
    (hstep : adaptiveStep oracle config assignment action =
      some (next, nextAssignment)) :
    SupportedByTranscript nextAssignment next.transcript := by
  unfold adaptiveStep at hstep
  cases hbase : config.step
      (adaptiveProcessing oracle assignment config.transcript) action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      have hfresh : action.job ∉ config.touched := by
        intro hmem
        simp [Config.step, hmem] at hbase
      cases hmode : action.mode with
      | raw =>
          have hnext : next.transcript =
              config.transcript ++ [.rawCompleted action.job] := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.rawCompleted action.job]⟩ := by
              simpa [Config.step, hfresh, hmode] using hbase.symm
            rw [this]
          intro job p hjob
          rw [hnext, List.mem_append]
          left
          exact hsupported job p (by
            simpa [assignmentAfter, hmode] using hjob)
      | optimized =>
          let value := adaptiveValue oracle assignment
            config.transcript action.job
          have hnext : next.transcript =
              config.transcript ++ [.optimizedCompleted action.job value] := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.optimizedCompleted action.job value]⟩ := by
              simpa [Config.step, hfresh, hmode, adaptiveProcessing, value] using
                hbase.symm
            rw [this]
          intro job p hjob
          rw [hnext, List.mem_append]
          by_cases heq : job = action.job
          · subst job
            right
            have hp : value = p := by
              simpa [assignmentAfter, hmode, value] using hjob
            simp [hp]
          · left
            apply hsupported job p
            simpa [assignmentAfter, hmode, Function.update, heq] using hjob

structure AdaptiveResult (n : ℕ) where
  result : RunResult n
  assigned : PartialAssignment n

def runAdaptiveFuel (oracle : Oracle n) (strategy : Strategy n) :
    ℕ → Config n → PartialAssignment n → AdaptiveResult n
  | 0, config, assignment =>
      ⟨⟨config, .outOfFuel⟩, assignment⟩
  | fuel + 1, config, assignment =>
      match strategy config.transcript with
      | none => ⟨⟨config, .strategyStopped⟩, assignment⟩
      | some action =>
          match adaptiveStep oracle config assignment action with
          | none => ⟨⟨config, .repeatedJob⟩, assignment⟩
          | some (next, nextAssignment) =>
              runAdaptiveFuel oracle strategy fuel next nextAssignment

theorem runAdaptiveFuel_extends
    (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : PartialAssignment n) :
    Extends assignment
      (runAdaptiveFuel oracle strategy fuel config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero => exact Extends.refl assignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runAdaptiveFuel, haction] using Extends.refl assignment
      | some action =>
          cases hstep : adaptiveStep oracle config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using Extends.refl assignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              simpa [runAdaptiveFuel, haction, hstep] using
                (adaptiveStep_extends oracle config next assignment
                  nextAssignment action hstep).trans (ih next nextAssignment)

theorem runAdaptiveFuel_assignment_admissible
    {u : ℝ} (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : PartialAssignment n)
    (horacle : oracle.Admissible u)
    (hassignment : AssignmentAdmissible u assignment) :
    AssignmentAdmissible u
      (runAdaptiveFuel oracle strategy fuel config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero => simpa [runAdaptiveFuel] using hassignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runAdaptiveFuel, haction] using hassignment
      | some action =>
          cases hstep : adaptiveStep oracle config assignment action with
          | none => simpa [runAdaptiveFuel, haction, hstep] using hassignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext := adaptiveStep_admissible oracle config next
                assignment nextAssignment action horacle hassignment hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem runAdaptiveFuel_supportedByTranscript
    (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : PartialAssignment n)
    (hsupported : SupportedByTranscript assignment config.transcript) :
    SupportedByTranscript
      (runAdaptiveFuel oracle strategy fuel config assignment).assigned
      (runAdaptiveFuel oracle strategy fuel config assignment).result.config.transcript := by
  induction fuel generalizing config assignment with
  | zero => simpa [runAdaptiveFuel] using hsupported
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runAdaptiveFuel, haction] using hsupported
      | some action =>
          cases hstep : adaptiveStep oracle config assignment action with
          | none => simpa [runAdaptiveFuel, haction, hstep] using hsupported
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext := adaptiveStep_supportedByTranscript oracle config next
                assignment nextAssignment action hsupported hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

def completeAssignment (default : Fin n → ℝ)
    (assignment : PartialAssignment n) : Fin n → ℝ :=
  fun job ↦ (assignment job).getD (default job)

theorem completeAssignment_admissible
    {u : ℝ} (default : Fin n → ℝ) (assignment : PartialAssignment n)
    (hdefault : ∀ job, default job ∈ Set.Icc (0 : ℝ) u)
    (hassignment : AssignmentAdmissible u assignment) :
    ∀ job, completeAssignment default assignment job ∈ Set.Icc (0 : ℝ) u := by
  intro job
  cases hjob : assignment job with
  | none => simpa [completeAssignment, hjob] using hdefault job
  | some p => simpa [completeAssignment, hjob] using hassignment job p hjob

@[simp] theorem completeAssignment_eq_assigned
    (default : Fin n → ℝ) (assignment : PartialAssignment n)
    (job : Fin n) (p : ℝ) (hjob : assignment job = some p) :
    completeAssignment default assignment job = p := by
  simp [completeAssignment, hjob]

theorem fixedStep_eq_of_adaptiveStep_of_extends
    (oracle : Oracle n) (default : Fin n → ℝ)
    (config next : Config n)
    (assignment nextAssignment finalAssignment : PartialAssignment n)
    (action : Action n)
    (hstep : adaptiveStep oracle config assignment action =
      some (next, nextAssignment))
    (hextends : Extends nextAssignment finalAssignment) :
    config.step (completeAssignment default finalAssignment) action = some next := by
  unfold adaptiveStep at hstep
  cases hbase : config.step
      (adaptiveProcessing oracle assignment config.transcript) action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      have hfresh : action.job ∉ config.touched := by
        intro hmem
        simp [Config.step, hmem] at hbase
      cases hmode : action.mode with
      | raw =>
          simpa [Config.step, hfresh, hmode] using hbase
      | optimized =>
          have hcommitted :
              assignmentAfter oracle config assignment action action.job =
                some (adaptiveValue oracle assignment
                  config.transcript action.job) := by
            simp [assignmentAfter, hmode]
          have hfinal := hextends action.job _ hcommitted
          simpa [Config.step, hfresh, hmode, adaptiveProcessing,
            completeAssignment, hfinal] using hbase

theorem Config.step_eq_none_processing_independent
    (left right : Fin n → ℝ) (config : Config n) (action : Action n) :
    config.step left action = none ↔ config.step right action = none := by
  cases action with
  | mk job mode => cases mode <;> simp [Config.step]

theorem replay_from
    (oracle : Oracle n) (strategy : Strategy n) (default : Fin n → ℝ)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n) :
    let adaptive := runAdaptiveFuel oracle strategy fuel config assignment
    runFuel (completeAssignment default adaptive.assigned)
        strategy fuel config = adaptive.result := by
  induction fuel generalizing config assignment with
  | zero => rfl
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simp [runAdaptiveFuel, runFuel, haction]
      | some action =>
          cases hstep : adaptiveStep oracle config assignment action with
          | none =>
              have hadaptiveNone : config.step
                  (adaptiveProcessing oracle assignment config.transcript) action =
                    none := by
                unfold adaptiveStep at hstep
                split at hstep <;> simp_all
              have hfixedNone : config.step
                  (completeAssignment default assignment) action = none := by
                exact (Config.step_eq_none_processing_independent
                  (adaptiveProcessing oracle assignment config.transcript)
                  (completeAssignment default assignment) config action).mp
                    hadaptiveNone
              simp [runAdaptiveFuel, runFuel, haction, hstep, hfixedNone]
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              let adaptiveTail :=
                runAdaptiveFuel oracle strategy fuel next nextAssignment
              have hextends : Extends nextAssignment adaptiveTail.assigned :=
                runAdaptiveFuel_extends oracle strategy fuel next nextAssignment
              have hfixedStep : config.step
                  (completeAssignment default adaptiveTail.assigned) action = some next :=
                fixedStep_eq_of_adaptiveStep_of_extends oracle default config next
                  assignment nextAssignment adaptiveTail.assigned action hstep hextends
              simp only [runAdaptiveFuel, haction, hstep]
              dsimp [adaptiveTail] at hfixedStep
              rw [runFuel]
              simp only [haction]
              rw [hfixedStep]
              exact ih next nextAssignment

def adaptiveRun (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ) :
    AdaptiveResult n :=
  runAdaptiveFuel oracle strategy fuel (Config.initial n) emptyAssignment

def frozenProcessing (oracle : Oracle n) (strategy : Strategy n)
    (default : Fin n → ℝ) (fuel : ℕ) : Fin n → ℝ :=
  completeAssignment default (adaptiveRun oracle strategy fuel).assigned

theorem replay (oracle : Oracle n) (strategy : Strategy n)
    (default : Fin n → ℝ) (fuel : ℕ) :
    run (frozenProcessing oracle strategy default fuel) strategy fuel =
      (adaptiveRun oracle strategy fuel).result := by
  exact replay_from oracle strategy default fuel
    (Config.initial n) emptyAssignment

theorem frozenProcessing_admissible
    {u : ℝ} (oracle : Oracle n) (strategy : Strategy n)
    (default : Fin n → ℝ) (fuel : ℕ)
    (horacle : oracle.Admissible u)
    (hdefault : ∀ job, default job ∈ Set.Icc (0 : ℝ) u) :
    ∀ job, frozenProcessing oracle strategy default fuel job ∈
      Set.Icc (0 : ℝ) u := by
  apply completeAssignment_admissible default
  · exact hdefault
  · exact runAdaptiveFuel_assignment_admissible oracle strategy fuel
      (Config.initial n) emptyAssignment horacle (by
        intro job p h
        simp [emptyAssignment] at h)

theorem adaptiveRun_supportedByTranscript
    (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ) :
    SupportedByTranscript (adaptiveRun oracle strategy fuel).assigned
      (adaptiveRun oracle strategy fuel).result.config.transcript := by
  exact runAdaptiveFuel_supportedByTranscript oracle strategy fuel
    (Config.initial n) emptyAssignment (by
      intro job p h
      simp [emptyAssignment] at h)

theorem frozenProcessing_eq_of_optimized
    (oracle : Oracle n) (strategy : Strategy n)
    (default : Fin n → ℝ) (fuel : ℕ) {job : Fin n} {p : ℝ}
    (hmem : Observation.optimizedCompleted job p ∈
      (adaptiveRun oracle strategy fuel).result.config.transcript) :
    frozenProcessing oracle strategy default fuel job = p := by
  have htruth := Online.run_truthful
    (frozenProcessing oracle strategy default fuel) strategy fuel
  have hreplay := replay oracle strategy default fuel
  rw [hreplay] at htruth
  exact (htruth job p hmem).symm

theorem frozenProcessing_eq_default_of_not_optimized
    (oracle : Oracle n) (strategy : Strategy n)
    (default : Fin n → ℝ) (fuel : ℕ) (job : Fin n)
    (hnot : ¬ ∃ p, Observation.optimizedCompleted job p ∈
      (adaptiveRun oracle strategy fuel).result.config.transcript) :
    frozenProcessing oracle strategy default fuel job = default job := by
  unfold frozenProcessing completeAssignment
  have hsupported := adaptiveRun_supportedByTranscript oracle strategy fuel
  cases hassigned : (adaptiveRun oracle strategy fuel).assigned job with
  | none => simp [hassigned]
  | some p => exact (hnot ⟨p, hsupported job p hassigned⟩).elim

end

end Replay
end BlindOptimization
end SchedulingPaper
