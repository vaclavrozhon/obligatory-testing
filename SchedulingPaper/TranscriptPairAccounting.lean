import SchedulingPaper.TimedOnline

/-!
# Pair accounting for an arbitrary timed transcript

Every operation contributes its duration to the completion time of each job
that completes at that operation or later.  This file records that elementary
identity directly for the operational semantics.  It is the common bridge
from an actual transcript to the diagonal-plus-ordered-pairs calculations
used throughout the upper and lower proofs.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Number of completion observations in a transcript. -/
def completionCount
    (processingTime : Label n → ℝ) : Transcript n → ℕ
  | [] => 0
  | observation :: rest =>
      (if (observation.completionLabel processingTime).isSome
        then 1 else 0) +
      completionCount processingTime rest

@[simp] theorem completionCount_nil
    (processingTime : Label n → ℝ) :
    completionCount processingTime [] = 0 := rfl

@[simp] theorem completionCount_cons
    (processingTime : Label n → ℝ)
    (observation : Observation n) (rest : Transcript n) :
    completionCount processingTime (observation :: rest) =
      (if (observation.completionLabel processingTime).isSome
        then 1 else 0) +
      completionCount processingTime rest := rfl

/-- Duration of each operation multiplied by the number of completions at
or after that operation. -/
def suffixWeightedDuration
    (cap : Cap) (processingTime : Label n → ℝ) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.duration cap processingTime *
          completionCount processingTime (observation :: rest) +
        suffixWeightedDuration cap processingTime rest

@[simp] theorem suffixWeightedDuration_nil
    (cap : Cap) (processingTime : Label n → ℝ) :
    suffixWeightedDuration cap processingTime [] = 0 := rfl

@[simp] theorem suffixWeightedDuration_cons
    (cap : Cap) (processingTime : Label n → ℝ)
    (observation : Observation n) (rest : Transcript n) :
    suffixWeightedDuration cap processingTime (observation :: rest) =
      observation.duration cap processingTime *
          completionCount processingTime (observation :: rest) +
        suffixWeightedDuration cap processingTime rest := rfl

/-- Exact carried-time formula for an arbitrary transcript. -/
theorem completionCostFrom_eq_count_mul_add_suffixWeighted
    (cap : Cap) (processingTime : Label n → ℝ)
    (time : ℝ) (transcript : Transcript n) :
    completionCostFrom cap processingTime time transcript =
      completionCount processingTime transcript * time +
        suffixWeightedDuration cap processingTime transcript := by
  induction transcript generalizing time with
  | nil =>
      simp [completionCostFrom]
  | cons observation rest ih =>
      simp only [completionCostFrom, completionCount_cons,
        suffixWeightedDuration_cons]
      rw [ih]
      by_cases hcompletion :
          (observation.completionLabel processingTime).isSome
      · simp only [if_pos hcompletion, Nat.cast_add, Nat.cast_one]
        ring
      · simp only [if_neg hcompletion, zero_add]
        ring

/-- At initial time zero, total completion cost is literally the
suffix-weighted operation-duration sum. -/
theorem completionCost_eq_suffixWeightedDuration
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) :
    completionCost cap processingTime transcript =
      suffixWeightedDuration cap processingTime transcript := by
  unfold completionCost
  rw [completionCostFrom_eq_count_mul_add_suffixWeighted]
  ring

/-- The same formula at the level of a completed or partial run result. -/
theorem runCompletionCost_eq_suffixWeightedDuration
    (cap : Cap) (processingTime : Label n → ℝ)
    (result : RunResult n) :
    runCompletionCost cap processingTime result =
      suffixWeightedDuration cap processingTime
        result.config.transcript := by
  exact completionCost_eq_suffixWeightedDuration _ _ _

/-- Appending an observation updates the completion count by exactly its
completion indicator. -/
theorem completionCount_append_singleton
    (processingTime : Label n → ℝ)
    (transcript : Transcript n) (observation : Observation n) :
    completionCount processingTime (transcript ++ [observation]) =
      completionCount processingTime transcript +
        if (observation.completionLabel processingTime).isSome
          then 1 else 0 := by
  induction transcript with
  | nil =>
      simp [completionCount]
  | cons head tail ih =>
      simp only [List.cons_append, completionCount_cons]
      rw [ih]
      split_ifs <;> omega

/-- A useful separation of the old transcript from one appended operation:
the new duration is charged once for every completion in the enlarged
transcript, while an appended completion also charges the elapsed prefix. -/
theorem suffixWeightedDuration_append_singleton
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (observation : Observation n) :
    suffixWeightedDuration cap processingTime
        (transcript ++ [observation]) =
      suffixWeightedDuration cap processingTime transcript +
        (if (observation.completionLabel processingTime).isSome
          then transcriptElapsed cap processingTime transcript else 0) +
        (if (observation.completionLabel processingTime).isSome
          then observation.duration cap processingTime else 0) := by
  by_cases hcompletion :
      (observation.completionLabel processingTime).isSome
  · induction transcript with
    | nil =>
        simp [suffixWeightedDuration, transcriptElapsed,
          completionCount, hcompletion]
    | cons head tail ih =>
        simp only [List.cons_append, suffixWeightedDuration_cons,
          transcriptElapsed_cons, completionCount_cons]
        rw [ih, completionCount_append_singleton]
        simp only [if_pos hcompletion, Nat.cast_add, Nat.cast_one]
        ring
  · induction transcript with
    | nil =>
        simp [suffixWeightedDuration,
          completionCount, hcompletion]
    | cons head tail ih =>
        simp only [List.cons_append, suffixWeightedDuration_cons,
          transcriptElapsed_cons, completionCount_cons]
        rw [ih, completionCount_append_singleton]
        simp only [if_neg hcompletion, add_zero]

end

end SchedulingPaper.Online
