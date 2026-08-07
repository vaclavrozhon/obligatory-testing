import SchedulingPaper.RandomizedHistogram
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev

namespace SchedulingPaper.Randomized
noncomputable section

theorem uniformAverage_abs_sq_le_uniformAverage_sq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniformAverage fun ω => |f ω|) ^ 2 ≤
      uniformAverage fun ω => (f ω) ^ 2 := by
  let N : ℝ := Fintype.card Ω
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have hcs :
      (∑ ω, |f ω|) ^ 2 ≤ N * ∑ ω, (f ω) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset Ω)) (f := fun ω => |f ω|)
    simpa [N, sq_abs] using h
  unfold uniformAverage
  calc
    ((∑ ω, |f ω|) / (Fintype.card Ω : ℝ)) ^ 2 =
        (∑ ω, |f ω|) ^ 2 / N ^ 2 := by
      dsimp [N]
      ring
    _ ≤ (N * ∑ ω, (f ω) ^ 2) / N ^ 2 :=
      (div_le_div_iff_of_pos_right hN2).2 hcs
    _ = (∑ ω, (f ω) ^ 2) / Fintype.card Ω := by
      dsimp [N]
      field_simp

def sampleCategoryFraction {α : Type*} [Fintype α] [DecidableEq α]
    (S C : Finset α) (σ : Equiv.Perm α) : ℝ :=
  permutationSampleSum S (categoryIndicator C) σ / S.card

theorem uniformAverage_categoryFraction_variance
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (S C : Finset α) (hS : S.Nonempty) (hn : 1 < Fintype.card α) :
    uniformAverage (fun σ : Equiv.Perm α =>
        (sampleCategoryFraction S C σ -
          (C.card : ℝ) / Fintype.card α) ^ 2) =
      (((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) - 1)) *
        ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α) /
        S.card := by
  let k : ℝ := S.card
  let μ : ℝ := (C.card : ℝ) / Fintype.card α
  have hk : k ≠ 0 := by
    dsimp [k]
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  calc
    uniformAverage (fun σ : Equiv.Perm α =>
        (sampleCategoryFraction S C σ -
          (C.card : ℝ) / Fintype.card α) ^ 2) =
      uniformAverage (fun σ : Equiv.Perm α =>
        (1 / k ^ 2) *
          (permutationSampleSum S (categoryIndicator C) σ - k * μ) ^ 2) := by
        congr 1
        funext σ
        dsimp [sampleCategoryFraction, k, μ]
        field_simp
    _ = (1 / k ^ 2) * uniformAverage (fun σ : Equiv.Perm α =>
          (permutationSampleSum S (categoryIndicator C) σ - k * μ) ^ 2) := by
      rw [uniformAverage_smul]
    _ = (1 / k ^ 2) *
        (((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) - 1)) *
        ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α)) := by
      rw [uniformAverage_categoryCount_variance S C hn]
    _ = (((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) - 1)) *
        ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α) /
        S.card := by
      dsimp [k]
      field_simp

theorem uniformAverage_categoryFraction_variance_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (S C : Finset α) (hS : S.Nonempty) (hn : 1 < Fintype.card α) :
    uniformAverage (fun σ : Equiv.Perm α =>
        (sampleCategoryFraction S C σ -
          (C.card : ℝ) / Fintype.card α) ^ 2) ≤
      ((C.card : ℝ) / Fintype.card α) / S.card := by
  rw [uniformAverage_categoryFraction_variance S C hS hn]
  let n : ℝ := Fintype.card α
  let k : ℝ := S.card
  let μ : ℝ := (C.card : ℝ) / Fintype.card α
  have hn0 : 0 < n := by dsimp [n]; positivity
  have hn1 : 0 < n - 1 := by
    dsimp [n]
    exact sub_pos.mpr (by exact_mod_cast hn)
  have hk1 : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (Finset.one_le_card.mpr hS)
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk1
  have hkn : k ≤ n := by
    dsimp [k, n]
    exact_mod_cast Finset.card_le_univ S
  have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
  have hμ1 : μ ≤ 1 := by
    dsimp [μ]
    rw [div_le_one (by positivity : (0 : ℝ) < Fintype.card α)]
    exact_mod_cast Finset.card_le_univ C
  have hcorr0 : 0 ≤ (n - k) / (n - 1) :=
    div_nonneg (sub_nonneg.mpr hkn) hn1.le
  have hcorr1 : (n - k) / (n - 1) ≤ 1 := by
    rw [div_le_one hn1]
    linarith
  change ((n - k) / (n - 1)) * μ * (1 - μ) / k ≤ μ / k
  apply (div_le_div_iff_of_pos_right hk0).2
  nlinarith [mul_nonneg hcorr0 hμ0,
    mul_nonneg (mul_nonneg hcorr0 hμ0) (sub_nonneg.mpr hμ1)]

theorem uniformAverage_abs_categoryFraction_error_sq_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (S C : Finset α) (hS : S.Nonempty) (hn : 1 < Fintype.card α) :
    (uniformAverage (fun σ : Equiv.Perm α =>
        |sampleCategoryFraction S C σ -
          (C.card : ℝ) / Fintype.card α|)) ^ 2 ≤
      ((C.card : ℝ) / Fintype.card α) / S.card := by
  exact (uniformAverage_abs_sq_le_uniformAverage_sq
      (fun σ : Equiv.Perm α => sampleCategoryFraction S C σ -
        (C.card : ℝ) / Fintype.card α)).trans
    (uniformAverage_categoryFraction_variance_le S C hS hn)

end
end SchedulingPaper.Randomized
