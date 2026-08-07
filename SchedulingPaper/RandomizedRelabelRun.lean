import SchedulingPaper.RandomizedOperationalStrategy
import SchedulingPaper.TranscriptPairAccounting
import Mathlib.Tactic

/-!
# Relabelling a randomized operational run

The sampled policy is written on virtual labels `0,...,n-1`; a permutation
seed sends those virtual labels to physical jobs.  This file proves that this
conjugation commutes exactly with the operational semantics and preserves the
sum of completion times.
-/

namespace SchedulingPaper
namespace Online

noncomputable section

@[simp] theorem Observation.relabel_symm_relabel
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).relabel order.symm = observation := by
  cases observation <;> simp [Observation.relabel]

@[simp] theorem Observation.relabel_relabel_symm
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order.symm).relabel order = observation := by
  cases observation <;> simp [Observation.relabel]

@[simp] theorem Action.relabel_symm_relabel
    (order : Equiv.Perm (Label n)) (action : Action n) :
    (action.relabel order).relabel order.symm = action := by
  cases action <;> simp [Action.relabel]

def Config.relabel (order : Equiv.Perm (Label n))
    (config : Config n) : Config n where
  jobs := fun physical => config.jobs (order.symm physical)
  transcript := config.transcript.map (Observation.relabel order)

@[simp] theorem Config.relabel_initial
    (order : Equiv.Perm (Label n)) :
    (Config.initial n).relabel order = Config.initial n := by
  rw [Config.mk.injEq]
  constructor
  · funext job
    rfl
  · rfl

@[simp] theorem Config.relabel_transcript_map_symm
    (order : Equiv.Perm (Label n)) (config : Config n) :
    (config.relabel order).transcript.map (Observation.relabel order.symm) =
      config.transcript := by
  simp [Config.relabel, List.map_map, Function.comp_def]

theorem Config.step_relabel
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (config : Config n)
    (action : Action n) :
    (config.relabel order).step cap (fixedOracle physicalProcessingTime)
        (action.relabel order) =
      (config.step cap
        (fixedOracle fun virtual => physicalProcessingTime (order virtual))
        action).map (Config.relabel order) := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Action.relabel, Config.step, Config.relabel,
            Equiv.symm_apply_apply, hstate, fixedOracle, Option.map_some]
          apply congrArg some
          rw [Config.mk.injEq]
          constructor
          · funext physical
            by_cases hphysical : physical = order job
            · subst physical
              simp [Function.update]
            · have hvirtual : order.symm physical ≠ job := by
                intro h
                apply hphysical
                simpa using congrArg order h
              simp [Function.update, hphysical, hvirtual]
          · simp [List.map_append, Observation.relabel]
      | tested p =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
      | done =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
  | process job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
      | tested p =>
          simp only [Action.relabel, Config.step, Config.relabel,
            Equiv.symm_apply_apply, hstate, Option.map_some]
          apply congrArg some
          rw [Config.mk.injEq]
          constructor
          · funext physical
            by_cases hphysical : physical = order job
            · subst physical
              simp [Function.update]
            · have hvirtual : order.symm physical ≠ job := by
                intro h
                apply hphysical
                simpa using congrArg order h
              simp [Function.update, hphysical, hvirtual]
          · simp [List.map_append, Observation.relabel]
      | done =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
  | raw job =>
      cases cap with
      | infinite =>
          simp [Action.relabel, Config.step]
      | finite u =>
          cases hstate : config.jobs job with
          | untouched =>
              simp only [Action.relabel, Config.step, Config.relabel,
                Equiv.symm_apply_apply, hstate, Option.map_some]
              apply congrArg some
              rw [Config.mk.injEq]
              constructor
              · funext physical
                by_cases hphysical : physical = order job
                · subst physical
                  simp [Function.update]
                · have hvirtual : order.symm physical ≠ job := by
                    intro h
                    apply hphysical
                    simpa using congrArg order h
                  simp [Function.update, hphysical, hvirtual]
              · simp [List.map_append, Observation.relabel]
          | tested p =>
              simp [Action.relabel, Config.step, Config.relabel, hstate]
          | done =>
              simp [Action.relabel, Config.step, Config.relabel, hstate]

theorem runFuel_relabel_config
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) :
    (runFuel cap (fixedOracle physicalProcessingTime)
      (strategy.relabel order) fuel (config.relabel order)).config =
      ((runFuel cap
        (fixedOracle fun virtual => physicalProcessingTime (order virtual))
        strategy fuel config).config.relabel order) := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFuel, Strategy.relabel,
        Config.relabel_transcript_map_symm]
      cases haction : strategy config.transcript with
      | none => simp [haction]
      | some action =>
          simp only [haction, Option.map_some]
          rw [Config.step_relabel]
          cases hstep : config.step cap
              (fixedOracle fun virtual => physicalProcessingTime (order virtual))
              action with
          | none => simp [hstep]
          | some next =>
              simp only [hstep, Option.map_some]
              exact ih next

theorem run_relabel_config
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) (fuel : ℕ) :
    (run cap (fixedOracle physicalProcessingTime)
      (strategy.relabel order) fuel).config =
      ((run cap
        (fixedOracle fun virtual => physicalProcessingTime (order virtual))
        strategy fuel).config.relabel order) := by
  unfold run
  rw [← Config.relabel_initial order]
  exact runFuel_relabel_config cap physicalProcessingTime order strategy fuel
    (Config.initial n)

@[simp] theorem Observation.duration_relabel
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).duration cap physicalProcessingTime =
      observation.duration cap
        (fun virtual => physicalProcessingTime (order virtual)) := by
  cases observation <;> simp [Observation.relabel, Observation.duration]

@[simp] theorem Observation.completionLabel_relabel
    (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).completionLabel physicalProcessingTime =
      (observation.completionLabel
        (fun virtual => physicalProcessingTime (order virtual))).map order := by
  cases observation with
  | testResult job p =>
      by_cases hp : p = 0 <;>
        simp [Observation.relabel, Observation.completionLabel, hp]
  | processed job =>
      by_cases hp : physicalProcessingTime (order job) = 0 <;>
        simp [Observation.relabel, Observation.completionLabel, hp]
  | rawCompleted job =>
      simp [Observation.relabel, Observation.completionLabel]

theorem completionCostFrom_map_relabel
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (time : ℝ)
    (transcript : Transcript n) :
    completionCostFrom cap physicalProcessingTime time
        (transcript.map (Observation.relabel order)) =
      completionCostFrom cap
        (fun virtual => physicalProcessingTime (order virtual)) time transcript := by
  induction transcript generalizing time with
  | nil => rfl
  | cons observation rest ih =>
      simp only [List.map_cons, completionCostFrom,
        Observation.duration_relabel, Observation.completionLabel_relabel]
      rw [ih]
      cases hcompletion : observation.completionLabel
          (fun virtual => physicalProcessingTime (order virtual)) <;>
        simp [hcompletion]

theorem completionCost_map_relabel
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (transcript : Transcript n) :
    completionCost cap physicalProcessingTime
        (transcript.map (Observation.relabel order)) =
      completionCost cap
        (fun virtual => physicalProcessingTime (order virtual)) transcript := by
  unfold completionCost
  exact completionCostFrom_map_relabel
    cap physicalProcessingTime order 0 transcript

theorem runCompletionCost_relabel
    (cap : Cap) (physicalProcessingTime : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) (fuel : ℕ) :
    runCompletionCost cap physicalProcessingTime
        (run cap (fixedOracle physicalProcessingTime)
          (strategy.relabel order) fuel) =
      runCompletionCost cap
        (fun virtual => physicalProcessingTime (order virtual))
        (run cap
          (fixedOracle fun virtual => physicalProcessingTime (order virtual))
          strategy fuel) := by
  unfold runCompletionCost
  rw [run_relabel_config]
  exact completionCost_map_relabel
    cap physicalProcessingTime order _

end

end Online
end SchedulingPaper
