import SchedulingPaper.RandomizedOptionalBlockEnvelope
import Mathlib.Tactic

/-!
# From prefix completion bounds to completion-time area

This file is independent of the scheduler semantics.  A finite execution is
represented by steps carrying a nonnegative duration and the number of jobs
completed at the end of that step.  The main theorem says that a pointwise
upper bound on completed mass at every operation prefix integrates to a lower
bound on the exact suffix-weighted completion cost.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

structure CompletionStep where
  duration : ℝ
  completions : ℕ

def completionStepsTime : List CompletionStep → ℝ
  | [] => 0
  | step :: rest => step.duration + completionStepsTime rest

def completionStepsCount : List CompletionStep → ℕ
  | [] => 0
  | step :: rest => step.completions + completionStepsCount rest

/-- The duration of each step is charged to every job completed at that step
or later.  This is the exact list-level analogue of sum of completion times. -/
def completionStepsCost : List CompletionStep → ℝ
  | [] => 0
  | step :: rest =>
      step.duration * completionStepsCount (step :: rest) +
        completionStepsCost rest

@[simp] theorem completionStepsTime_append
    (left right : List CompletionStep) :
    completionStepsTime (left ++ right) =
      completionStepsTime left + completionStepsTime right := by
  induction left with
  | nil => simp [completionStepsTime]
  | cons step rest ih =>
      simp [completionStepsTime, ih]
      ring

@[simp] theorem completionStepsCount_append
    (left right : List CompletionStep) :
    completionStepsCount (left ++ right) =
      completionStepsCount left + completionStepsCount right := by
  induction left with
  | nil => simp [completionStepsCount]
  | cons step rest ih => simp [completionStepsCount, ih, Nat.add_assoc]

theorem completionStepsTime_nonneg
    {steps : List CompletionStep}
    (hduration : ∀ step ∈ steps, 0 ≤ step.duration) :
    0 ≤ completionStepsTime steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      exact add_nonneg (hduration step (by simp))
        (ih (fun next hnext => hduration next (by simp [hnext])))

theorem completionStepsCost_nonneg
    {steps : List CompletionStep}
    (hduration : ∀ step ∈ steps, 0 ≤ step.duration) :
    0 ≤ completionStepsCost steps := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      exact add_nonneg
        (mul_nonneg (hduration step (by simp)) (by positivity))
        (ih (fun next hnext => hduration next (by simp [hnext])))

private theorem completionSteps_integral_aux
    {n : ℕ} (hn : 0 < n) (curve : ℝ → ℝ)
    (hcurveContinuous : Continuous curve) (hcurveMono : Monotone curve)
    (ζ ε : ℝ) (done suffix : List CompletionStep)
    (hduration : ∀ step ∈ done ++ suffix, 0 ≤ step.duration)
    (hcomplete : completionStepsCount (done ++ suffix) = n)
    (hprefix : ∀ pre, pre <+: done ++ suffix →
      (completionStepsCount pre : ℝ) / n ≤
        curve (completionStepsTime pre / n + ζ) + ε) :
    (∫ x in completionStepsTime done / n..
        completionStepsTime (done ++ suffix) / n,
        (1 - curve (x + ζ) - ε)) ≤
      completionStepsCost suffix / (n : ℝ) ^ 2 := by
  induction suffix generalizing done with
  | nil => simp [completionStepsCost]
  | cons step rest ih =>
      let middle := completionStepsTime (done ++ [step]) / (n : ℝ)
      let finish := completionStepsTime (done ++ step :: rest) / (n : ℝ)
      let remaining : ℝ := completionStepsCount (step :: rest) / (n : ℝ)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hstep0 : 0 ≤ step.duration :=
        hduration step (by simp)
      have hstartMiddle : completionStepsTime done / (n : ℝ) ≤ middle := by
        dsimp [middle]
        rw [completionStepsTime_append]
        simp only [completionStepsTime]
        rw [div_le_div_iff_of_pos_right hnR]
        linarith
      have hmiddleFinish : middle ≤ finish := by
        dsimp [middle, finish]
        rw [completionStepsTime_append, completionStepsTime_append]
        simp only [completionStepsTime]
        have hrest0 : 0 ≤ completionStepsTime rest :=
          completionStepsTime_nonneg (fun next hnext =>
            hduration next (by simp [hnext]))
        exact div_le_div_of_nonneg_right (by linarith) hnR.le
      have hprefixAtStart := hprefix done (by simp)
      have hcountSplit :
          (completionStepsCount done : ℝ) +
              completionStepsCount (step :: rest) = n := by
        have hcount := hcomplete
        rw [completionStepsCount_append] at hcount
        exact_mod_cast hcount
      have hremainingAtStart :
          1 - curve (completionStepsTime done / (n : ℝ) + ζ) - ε ≤
            remaining := by
        dsimp [remaining]
        rw [le_div_iff₀ hnR]
        rw [div_le_iff₀ hnR] at hprefixAtStart
        nlinarith
      have hpointwise : ∀ x ∈ Set.Icc
          (completionStepsTime done / (n : ℝ)) middle,
          1 - curve (x + ζ) - ε ≤ remaining := by
        intro x hx
        have hmono : curve (completionStepsTime done / (n : ℝ) + ζ) ≤
            curve (x + ζ) := hcurveMono (by linarith [hx.1])
        linarith
      have hremainingContinuous : Continuous (fun x : ℝ =>
          1 - curve (x + ζ) - ε) :=
        (continuous_const.sub
          (hcurveContinuous.comp (continuous_id.add continuous_const))).sub
            continuous_const
      have hfirst :
          (∫ x in completionStepsTime done / (n : ℝ)..middle,
              (1 - curve (x + ζ) - ε)) ≤
            step.duration * completionStepsCount (step :: rest) /
              (n : ℝ) ^ 2 := by
        calc
          (∫ x in completionStepsTime done / (n : ℝ)..middle,
              (1 - curve (x + ζ) - ε)) ≤
              ∫ _x in completionStepsTime done / (n : ℝ)..middle,
                remaining :=
            intervalIntegral.integral_mono_on hstartMiddle
              (hremainingContinuous.intervalIntegrable _ _)
              intervalIntegrable_const hpointwise
          _ = step.duration * completionStepsCount (step :: rest) /
                (n : ℝ) ^ 2 := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]
            dsimp [middle, remaining]
            rw [completionStepsTime_append]
            simp only [completionStepsTime]
            field_simp [hnR.ne']
            ring
      have hdurationRest : ∀ next ∈ done ++ [step] ++ rest,
          0 ≤ next.duration := by
        intro next hnext
        apply hduration next
        simpa [List.append_assoc] using hnext
      have hcompleteRest :
          completionStepsCount ((done ++ [step]) ++ rest) = n := by
        simpa [List.append_assoc] using hcomplete
      have hprefixRest : ∀ pre, pre <+: (done ++ [step]) ++ rest →
          (completionStepsCount pre : ℝ) / n ≤
            curve (completionStepsTime pre / n + ζ) + ε := by
        intro pre hpre
        apply hprefix pre
        simpa [List.append_assoc] using hpre
      have hrest := ih (done := done ++ [step]) hdurationRest
        hcompleteRest hprefixRest
      have hleftInt : IntervalIntegrable
          (fun x : ℝ => 1 - curve (x + ζ) - ε) MeasureTheory.volume
          (completionStepsTime done / (n : ℝ)) middle :=
        hremainingContinuous.intervalIntegrable _ _
      have hrightInt : IntervalIntegrable
          (fun x : ℝ => 1 - curve (x + ζ) - ε) MeasureTheory.volume
          middle finish :=
        hremainingContinuous.intervalIntegrable _ _
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        hleftInt hrightInt
      change (∫ x in completionStepsTime done / (n : ℝ)..finish,
          (1 - curve (x + ζ) - ε)) ≤ _
      rw [← hsplit]
      change _ ≤
        (step.duration * completionStepsCount (step :: rest) +
          completionStepsCost rest) / (n : ℝ) ^ 2
      rw [add_div]
      have hrest' :
          (∫ x in middle..finish, (1 - curve (x + ζ) - ε)) ≤
            completionStepsCost rest / (n : ℝ) ^ 2 := by
        simpa [middle, finish, List.append_assoc] using hrest
      exact add_le_add hfirst hrest'

/-- Prefix completion domination integrates to a lower bound on the exact
completion-time area of the finite execution. -/
theorem completionStepsCost_ge_remaining_integral
    {n : ℕ} (hn : 0 < n) (curve : ℝ → ℝ)
    (hcurveContinuous : Continuous curve) (hcurveMono : Monotone curve)
    (ζ ε : ℝ) (steps : List CompletionStep)
    (hduration : ∀ step ∈ steps, 0 ≤ step.duration)
    (hcomplete : completionStepsCount steps = n)
    (hprefix : ∀ pre, pre <+: steps →
      (completionStepsCount pre : ℝ) / n ≤
        curve (completionStepsTime pre / n + ζ) + ε) :
    (∫ x in 0..completionStepsTime steps / n,
        (1 - curve (x + ζ) - ε)) ≤
      completionStepsCost steps / (n : ℝ) ^ 2 := by
  simpa [completionStepsTime] using
    completionSteps_integral_aux hn curve hcurveContinuous hcurveMono ζ ε
      [] steps (by simpa using hduration) (by simpa using hcomplete)
      (by simpa using hprefix)

end

end RandomizedOptional
end SchedulingPaper
