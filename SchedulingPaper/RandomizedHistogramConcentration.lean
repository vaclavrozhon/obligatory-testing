import SchedulingPaper.RandomizedHistogramL1
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace SchedulingPaper.Randomized
noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

def categoryClass (c : α → β) (b : β) : Finset α :=
  Finset.univ.filter fun a => c a = b

omit [DecidableEq α] in
lemma sum_categoryClass_card (c : α → β) :
    ∑ b, (categoryClass c b).card = Fintype.card α := by
  classical
  simp_rw [Finset.card_eq_sum_ones]
  simp_rw [categoryClass, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

def histogramL1Error (S : Finset α) (c : α → β)
    (σ : Equiv.Perm α) : ℝ :=
  ∑ b, |sampleCategoryFraction S (categoryClass c b) σ -
    ((categoryClass c b).card : ℝ) / Fintype.card α|

theorem uniformAverage_histogramL1Error_sq_le
    [Nonempty α] (S : Finset α) (c : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α) :
    (uniformAverage (histogramL1Error S c)) ^ 2 ≤
      (Fintype.card β : ℝ) / S.card := by
  let A : β → ℝ := fun b => uniformAverage (fun σ : Equiv.Perm α =>
    |sampleCategoryFraction S (categoryClass c b) σ -
      ((categoryClass c b).card : ℝ) / Fintype.card α|)
  have hA0 : ∀ b, 0 ≤ A b := by
    intro b
    exact uniformAverage_nonneg (fun _ => abs_nonneg _)
  have hA2 : ∀ b, (A b) ^ 2 ≤
      (((categoryClass c b).card : ℝ) / Fintype.card α) / S.card := by
    intro b
    exact uniformAverage_abs_categoryFraction_error_sq_le
      S (categoryClass c b) hS hn
  have hsumA2 : (∑ b, (A b) ^ 2) ≤ 1 / (S.card : ℝ) := by
    calc
      (∑ b, (A b) ^ 2) ≤
          ∑ b, ((((categoryClass c b).card : ℝ) / Fintype.card α) /
            S.card) := Finset.sum_le_sum fun b _ => hA2 b
      _ = 1 / (S.card : ℝ) := by
        rw [← Finset.sum_div, ← Finset.sum_div]
        rw [show (∑ b, ((categoryClass c b).card : ℝ)) =
            (Fintype.card α : ℝ) by exact_mod_cast sum_categoryClass_card c]
        have hn0 : (Fintype.card α : ℝ) ≠ 0 := by positivity
        field_simp
  have hcs : (∑ b, A b) ^ 2 ≤
      (Fintype.card β : ℝ) * ∑ b, (A b) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset β)) (f := A))
  calc
    (uniformAverage (histogramL1Error S c)) ^ 2 =
        (∑ b, A b) ^ 2 := by
      rw [show uniformAverage (histogramL1Error S c) = ∑ b, A b by
        unfold histogramL1Error A
        exact uniformAverage_sum _]
    _ ≤ (Fintype.card β : ℝ) * ∑ b, (A b) ^ 2 := hcs
    _ ≤ (Fintype.card β : ℝ) * (1 / (S.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsumA2 (by positivity)
    _ = (Fintype.card β : ℝ) / S.card := by ring

theorem uniformAverage_histogramL1Error_le_sqrt
    [Nonempty α] (S : Finset α) (c : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α) :
    uniformAverage (histogramL1Error S c) ≤
      Real.sqrt ((Fintype.card β : ℝ) / S.card) := by
  apply Real.le_sqrt_of_sq_le
  exact uniformAverage_histogramL1Error_sq_le S c hS hn

/-- Probability of an event under a finite uniform seed space. -/
def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  uniformAverage fun ω => if P ω then 1 else 0

/-- Finite uniform form of Markov's inequality. -/
theorem uniformProbability_lt_le_average_div
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) {τ : ℝ} (hτ : 0 < τ) :
    uniformProbability (fun ω => τ < f ω) ≤ uniformAverage f / τ := by
  have hpoint : ∀ ω, τ * (if τ < f ω then 1 else 0) ≤ f ω := by
    intro ω
    by_cases h : τ < f ω
    · simp [h, h.le]
    · simp [h, hf ω]
  have hscaled : τ * uniformProbability (fun ω => τ < f ω) ≤
      uniformAverage f := by
    rw [uniformProbability, ← uniformAverage_smul]
    exact uniformAverage_mono hpoint
  exact (le_div_iff₀ hτ).2 (by simpa [mul_comm] using hscaled)

/-- The bad-histogram event satisfies the Markov bound (5.3). -/
theorem uniformProbability_histogramL1Error_gt_le
    [Nonempty α] (S : Finset α) (c : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    {τ : ℝ} (hτ : 0 < τ) :
    uniformProbability (fun σ : Equiv.Perm α =>
        τ < histogramL1Error S c σ) ≤
      Real.sqrt ((Fintype.card β : ℝ) / S.card) / τ := by
  calc
    uniformProbability (fun σ : Equiv.Perm α =>
        τ < histogramL1Error S c σ) ≤
      uniformAverage (histogramL1Error S c) / τ := by
        exact uniformProbability_lt_le_average_div
          (histogramL1Error S c)
          (fun σ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hτ
    _ ≤ Real.sqrt ((Fintype.card β : ℝ) / S.card) / τ := by
      exact div_le_div_of_nonneg_right
        (uniformAverage_histogramL1Error_le_sqrt S c hS hn) hτ.le

end
end SchedulingPaper.Randomized
