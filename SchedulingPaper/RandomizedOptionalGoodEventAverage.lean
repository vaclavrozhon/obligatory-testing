import SchedulingPaper.RandomizedOptionalObservedGlobalGood
import Mathlib.Tactic

/-!
# Averaging a pathwise lower bound off a small bad set

This is the finite-probability bookkeeping used after the simultaneous urn
event.  It is deliberately independent of the scheduling model.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

theorem uniformProbability_not
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Bad : Ω → Prop) [DecidablePred Bad] :
    uniformProbability (fun ω => ¬ Bad ω) = 1 - uniformProbability Bad := by
  unfold uniformProbability
  let f : Ω → ℝ := fun ω => if ¬ Bad ω then 1 else 0
  let g : Ω → ℝ := fun ω => if Bad ω then 1 else 0
  have hpoint : (fun ω => f ω + g ω) = fun _ : Ω => (1 : ℝ) := by
    funext ω
    by_cases h : Bad ω <;> simp [f, g, h]
  have hadd := uniformAverage_add f g
  rw [hpoint, uniformAverage_const] at hadd
  dsimp [f, g] at hadd ⊢
  linarith

/-- If a nonnegative cost is at least `B` outside a bad event of probability
at most `δ`, and `B` is no larger than a nonnegative crude upper scale `U`,
then its uniform average is at least `B-Uδ`.  The `max B 0` in the proof
keeps the lemma valid when the repaired pathwise bound is negative. -/
theorem uniformAverage_ge_of_good_event
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (cost : Ω → ℝ) (Bad : Ω → Prop) [DecidablePred Bad]
    {B U δ : ℝ}
    (hcost0 : ∀ ω, 0 ≤ cost ω)
    (hgood : ∀ ω, ¬ Bad ω → B ≤ cost ω)
    (hBU : B ≤ U) (hU0 : 0 ≤ U)
    (hbad : uniformProbability Bad ≤ δ) :
    B - U * δ ≤ uniformAverage cost := by
  let B0 := max B 0
  have hB0 : 0 ≤ B0 := by simp [B0]
  have hBB0 : B ≤ B0 := le_max_left _ _
  have hB0U : B0 ≤ U := by
    dsimp [B0]
    exact max_le hBU hU0
  have hpoint : ∀ ω,
      B0 * (if ¬ Bad ω then (1 : ℝ) else 0) ≤ cost ω := by
    intro ω
    by_cases h : Bad ω
    · simp [h, hcost0 ω]
    · simp [h]
      exact max_le (hgood ω h) (hcost0 ω)
  have haverage :
      B0 * uniformProbability (fun ω => ¬ Bad ω) ≤ uniformAverage cost := by
    rw [uniformProbability, ← uniformAverage_smul]
    exact uniformAverage_mono hpoint
  rw [uniformProbability_not Bad] at haverage
  have hprob0 : 0 ≤ uniformProbability Bad := by
    apply uniformAverage_nonneg
    intro ω
    positivity
  have hloss1 : B0 * uniformProbability Bad ≤
      U * uniformProbability Bad :=
    mul_le_mul_of_nonneg_right hB0U hprob0
  have hloss2 : U * uniformProbability Bad ≤ U * δ :=
    mul_le_mul_of_nonneg_left hbad hU0
  linarith

end

end RandomizedOptional
end SchedulingPaper
