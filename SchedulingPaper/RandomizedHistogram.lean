import SchedulingPaper.RandomizedHypergeometric
import Mathlib.Tactic

namespace SchedulingPaper.Randomized
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def categoryIndicator (C : Finset α) (a : α) : ℝ :=
  if a ∈ C then 1 else 0

lemma sum_categoryIndicator (C : Finset α) :
    ∑ a, categoryIndicator C a = C.card := by
  classical
  simp [categoryIndicator]

lemma populationMean_categoryIndicator [Nonempty α] (C : Finset α) :
    populationMean (categoryIndicator C) =
      (C.card : ℝ) / Fintype.card α := by
  rw [populationMean, sum_categoryIndicator]

lemma sum_centeredCategory_sq [Nonempty α] (C : Finset α) :
    ∑ a, centeredPopulation (categoryIndicator C) a ^ 2 =
      (Fintype.card α : ℝ) * ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α) := by
  classical
  let n : ℝ := Fintype.card α
  let c : ℝ := C.card
  have hn0 : n ≠ 0 := by
    dsimp [n]
    positivity
  rw [show (∑ a, centeredPopulation (categoryIndicator C) a ^ 2) =
      c * (1 - c / n) ^ 2 + (n - c) * (c / n) ^ 2 by
    simp only [centeredPopulation, populationMean_categoryIndicator,
      categoryIndicator]
    rw [show (∑ a, ((if a ∈ C then (1 : ℝ) else 0) - c / n) ^ 2) =
        ∑ a, if a ∈ C then (1 - c / n) ^ 2 else (c / n) ^ 2 by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ C <;> simp [ha]]
    rw [Finset.sum_ite]
    have hmem : (Finset.univ.filter fun a : α => a ∈ C) = C := by
      ext a
      simp
    have hnot : (Finset.univ.filter fun a : α => a ∉ C) = Finset.univ \ C := by
      ext a
      simp
    rw [Finset.sum_const, Finset.sum_const, hmem, hnot]
    simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      nsmul_eq_mul]
    rw [Nat.cast_sub (Finset.card_le_univ C)]]
  dsimp [c, n]
  field_simp
  ring

/-- Exact hypergeometric variance of the count of one category in the sample
positions `S`. -/
theorem uniformAverage_categoryCount_variance [Nonempty α]
    (S C : Finset α) (hn : 1 < Fintype.card α) :
    uniformAverage (fun σ : Equiv.Perm α =>
        (permutationSampleSum S (categoryIndicator C) σ -
          (S.card : ℝ) * ((C.card : ℝ) / Fintype.card α)) ^ 2) =
      ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) - 1)) *
        ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α) := by
  calc
    uniformAverage (fun σ : Equiv.Perm α =>
        (permutationSampleSum S (categoryIndicator C) σ -
          (S.card : ℝ) * ((C.card : ℝ) / Fintype.card α)) ^ 2) =
      uniformAverage (fun σ : Equiv.Perm α =>
        (permutationSampleSum S (categoryIndicator C) σ -
          (S.card : ℝ) * populationMean (categoryIndicator C)) ^ 2) := by
        rw [populationMean_categoryIndicator]
    _ = ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) *
        ∑ a, centeredPopulation (categoryIndicator C) a ^ 2 :=
      uniformAverage_permutationSampleSum_variance S (categoryIndicator C) hn
    _ = ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) - 1)) *
        ((C.card : ℝ) / Fintype.card α) *
        (1 - (C.card : ℝ) / Fintype.card α) := by
      rw [sum_centeredCategory_sq C]
      have hn0 : (Fintype.card α : ℝ) ≠ 0 := by positivity
      field_simp

end
end SchedulingPaper.Randomized
