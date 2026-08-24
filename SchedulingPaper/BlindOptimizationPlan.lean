import SchedulingPaper.BlindOptimizationModel
import Mathlib.Tactic

/-!
# Executing finite blind-optimization plans

This file is the operational bridge used by randomized finite-seed policies.
It proves once that any transcript-dependent strategy which agrees with a
fresh-label action plan on every truthful prefix literally executes that
plan.  The plan may be chosen only for the proof; `AgreesWithPlan` is the
condition that prevents it from smuggling future processing times into the
online strategy.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace Online

noncomputable section

def Action.observation (processing : Fin n → ℝ) (action : Action n) :
    Observation n :=
  match action.mode with
  | .raw => .rawCompleted action.job
  | .optimized => .optimizedCompleted action.job (processing action.job)

def executePlan (processing : Fin n → ℝ) (plan : List (Action n)) :
    Transcript n :=
  plan.map (Action.observation processing)

def planConfig (processing : Fin n → ℝ) (done : List (Action n)) : Config n :=
  { touched := (done.map Action.job).toFinset
    transcript := executePlan processing done }

/-- The online strategy selects the next planned action after every truthful
prefix of the plan.  Quantifying over all splittings makes the induction
independent of a particular indexing convention. -/
def AgreesWithPlan (processing : Fin n → ℝ) (strategy : Strategy n)
    (plan : List (Action n)) : Prop :=
  ∀ done todo, plan = done ++ todo →
    strategy (executePlan processing done) = todo.head?

/-- It is enough to check agreement on the canonical `take`/`drop` split at
each index.  This is the convenient interface for executable strategies
whose next job is selected from a fixed private order. -/
theorem agreesWithPlan_of_indexed
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (plan : List (Action n))
    (hindexed : ∀ k ≤ plan.length,
      strategy (executePlan processing (plan.take k)) =
        (plan.drop k).head?) :
    AgreesWithPlan processing strategy plan := by
  intro done todo hsplit
  have hk : done.length ≤ plan.length := by
    rw [hsplit]
    simp
  have hdone : plan.take done.length = done := by
    rw [hsplit]
    simp
  have htodo : plan.drop done.length = todo := by
    rw [hsplit]
    simp
  simpa [hdone, htodo] using hindexed done.length hk

@[simp] theorem executePlan_length
    (processing : Fin n → ℝ) (plan : List (Action n)) :
    (executePlan processing plan).length = plan.length := by
  simp [executePlan]

@[simp] theorem executePlan_append
    (processing : Fin n → ℝ) (left right : List (Action n)) :
    executePlan processing (left ++ right) =
      executePlan processing left ++ executePlan processing right := by
  simp [executePlan]

theorem planConfig_step
    (processing : Fin n → ℝ) (done : List (Action n)) (action : Action n)
    (hfresh : action.job ∉ done.map Action.job) :
    (planConfig processing done).step processing action =
      some (planConfig processing (done ++ [action])) := by
  classical
  have hfreshSet : action.job ∉ (done.map Action.job).toFinset := by
    simpa using hfresh
  cases action with
  | mk job mode =>
      cases mode <;>
        simp [Config.step, planConfig, executePlan, Action.observation,
          hfreshSet]

private theorem fresh_head_of_plan_nodup
    {plan done : List (Action n)} {action : Action n} {todo : List (Action n)}
    (hsplit : plan = done ++ action :: todo)
    (hnodup : (plan.map Action.job).Nodup) :
    action.job ∉ done.map Action.job := by
  rw [hsplit, List.map_append, List.map_cons] at hnodup
  have hseparate := (List.nodup_append.mp hnodup).2.2
  intro hmem
  exact hseparate action.job hmem action.job (by simp) rfl

private theorem runFuel_agreesFrom
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (plan : List (Action n))
    (hnodup : (plan.map Action.job).Nodup)
    (hagree : AgreesWithPlan processing strategy plan)
    (done todo : List (Action n)) (hsplit : plan = done ++ todo) :
    (runFuel processing strategy todo.length
      (planConfig processing done)).config = planConfig processing plan := by
  induction todo generalizing done with
  | nil =>
      simp only [List.append_nil] at hsplit
      subst plan
      simp [runFuel]
  | cons action rest ih =>
      have haction : strategy (executePlan processing done) = some action := by
        simpa using hagree done (action :: rest) hsplit
      have haction' :
          strategy (planConfig processing done).transcript = some action := by
        simpa [planConfig] using haction
      have hfresh : action.job ∉ done.map Action.job :=
        fresh_head_of_plan_nodup hsplit hnodup
      have hstep : (planConfig processing done).step processing action =
          some (planConfig processing (done ++ [action])) :=
        planConfig_step processing done action hfresh
      have hsplitNext : plan = (done ++ [action]) ++ rest := by
        simpa [List.append_assoc] using hsplit
      have hrec := ih (done ++ [action]) hsplitNext
      simp only [List.length_cons, runFuel, haction', hstep]
      exact hrec

/-- A strategy agreeing with a no-repeated-label plan executes its exact
truthful observation list. -/
theorem run_transcript_eq_executePlan
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (plan : List (Action n))
    (hnodup : (plan.map Action.job).Nodup)
    (hagree : AgreesWithPlan processing strategy plan) :
    (run processing strategy plan.length).config.transcript =
      executePlan processing plan := by
  unfold run
  have hrun := runFuel_agreesFrom processing strategy plan hnodup hagree
    [] plan (by simp)
  simpa [planConfig] using congrArg Config.transcript hrun

/-- If the plan contains every label exactly once, agreement also proves the
usual operational completion predicate. -/
theorem completes_of_agreesWithPlan
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (plan : List (Action n))
    (hlength : plan.length = n)
    (hnodup : (plan.map Action.job).Nodup)
    (hall : (plan.map Action.job).toFinset = Finset.univ)
    (hagree : AgreesWithPlan processing strategy plan) :
    Completes processing strategy := by
  have hrun := runFuel_agreesFrom processing strategy plan hnodup hagree
    [] plan (by simp)
  have hrunN :
      (run processing strategy n).config = planConfig processing plan := by
    unfold run
    simpa [hlength, planConfig, Config.initial] using hrun
  unfold Completes
  rw [hrunN]
  simp [planConfig, hall]

end

end Online
end BlindOptimization
end SchedulingPaper
