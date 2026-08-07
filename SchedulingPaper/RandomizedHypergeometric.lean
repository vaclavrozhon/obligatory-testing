import SchedulingPaper.RandomPermutation
import Mathlib.Tactic

namespace SchedulingPaper.Randomized
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def orderedDistinctEquivOffDiag :
    OrderedDistinct α ≃ ↥((Finset.univ : Finset α).offDiag) where
  toFun z := ⟨z.val, Finset.mem_offDiag.mpr ⟨by simp, by simp, z.property⟩⟩
  invFun z := ⟨z.val, (Finset.mem_offDiag.mp z.property).2.2⟩
  left_inv z := by simp
  right_inv z := by simp

lemma orderedDistinct_card :
    Fintype.card (OrderedDistinct α) =
      Fintype.card α * (Fintype.card α - 1) := by
  rw [Fintype.card_congr (orderedDistinctEquivOffDiag (α := α))]
  rw [Fintype.card_coe, Finset.offDiag_card]
  simp only [Finset.card_univ]
  rw [Nat.mul_sub_left_distrib]
  simp

lemma sum_orderedDistinct_mul_of_sum_eq_zero (y : α → ℝ)
    (hy : ∑ a, y a = 0) :
    (∑ z : OrderedDistinct α, y z.val.1 * y z.val.2) =
      -(∑ a, y a ^ 2) := by
  classical
  have hdecomp :
      (∑ z ∈ (Finset.univ : Finset α).diag, y z.1 * y z.2) +
          (∑ z ∈ (Finset.univ : Finset α).offDiag, y z.1 * y z.2) = 0 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ)]
    rw [Finset.diag_union_offDiag]
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    simp [hy]
  have hdiag :
      (∑ z ∈ (Finset.univ : Finset α).diag, y z.1 * y z.2) =
        ∑ a, y a ^ 2 := by
    rw [Finset.sum_diag]
    simp [pow_two]
  have hoff :
      (∑ z ∈ (Finset.univ : Finset α).offDiag, y z.1 * y z.2) =
        -(∑ a, y a ^ 2) := by
    linarith
  rw [← hoff]
  symm
  apply Finset.sum_subtype
  intro z
  simp [Finset.mem_offDiag]

lemma uniformAverage_centered_pair [Nonempty α] (y : α → ℝ)
    (hy : ∑ a, y a = 0) {i j : α} (hij : i ≠ j) :
    uniformAverage (fun σ : Equiv.Perm α => y (σ i) * y (σ j)) =
      -(∑ a, y a ^ 2) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  rw [uniformAverage_perm_apply₂ (fun a b => y a * y b) hij]
  rw [sum_orderedDistinct_mul_of_sum_eq_zero y hy]
  rw [orderedDistinct_card]
  rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_iff.mpr Fintype.card_pos)]
  norm_num

omit [Fintype α] in
lemma sum_pair_ite (S : Finset α) (diag off : ℝ) :
    (∑ i : ↥S, ∑ j : ↥S, if i = j then diag else off) =
      (S.card : ℝ) * ((S.card : ℝ) * off + diag - off) := by
  classical
  calc
    (∑ i : ↥S, ∑ j : ↥S, if i = j then diag else off) =
        ∑ _i : ↥S, ((S.card : ℝ) * off + diag - off) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j : ↥S, if i = j then diag else off) =
            ∑ j : ↥S, (off + if i = j then diag - off else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
        _ = (∑ _j : ↥S, off) +
              ∑ j : ↥S, if i = j then diag - off else 0 := by
          rw [← Finset.sum_add_distrib]
        _ = (S.card : ℝ) * off + diag - off := by
          rw [Fintype.sum_ite_eq]
          simp
          ring
    _ = (S.card : ℝ) * ((S.card : ℝ) * off + diag - off) := by
      simp
      ring

/-- Sum of population values seen in the positions `S` of a permutation. -/
def permutationSampleSum (S : Finset α) (y : α → ℝ)
    (σ : Equiv.Perm α) : ℝ :=
  ∑ i : ↥S, y (σ i.val)

/-- Empirical mean of a finite population. -/
def populationMean (x : α → ℝ) : ℝ :=
  (∑ a, x a) / Fintype.card α

/-- Center a finite population by its empirical mean. -/
def centeredPopulation (x : α → ℝ) (a : α) : ℝ :=
  x a - populationMean x

omit [DecidableEq α] in
lemma sum_centeredPopulation [Nonempty α] (x : α → ℝ) :
    ∑ a, centeredPopulation x a = 0 := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  simp only [centeredPopulation, Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul, populationMean]
  field_simp
  ring

omit [DecidableEq α] in
lemma permutationSampleSum_centered [Nonempty α]
    (S : Finset α) (x : α → ℝ) (σ : Equiv.Perm α) :
    permutationSampleSum S (centeredPopulation x) σ =
      permutationSampleSum S x σ - (S.card : ℝ) * populationMean x := by
  simp only [permutationSampleSum, centeredPopulation, Finset.sum_sub_distrib]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

/-- Exact finite-population second moment for a sample without replacement,
written for an already centered population. -/
theorem uniformAverage_permutationSampleSum_sq [Nonempty α]
    (S : Finset α) (y : α → ℝ) (hy : ∑ a, y a = 0)
    (hn : 1 < Fintype.card α) :
    uniformAverage (fun σ : Equiv.Perm α => (permutationSampleSum S y σ) ^ 2) =
      ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) *
        ∑ a, y a ^ 2 := by
  let V : ℝ := ∑ a, y a ^ 2
  let n : ℝ := Fintype.card α
  let k : ℝ := S.card
  have hn0 : n ≠ 0 := by
    dsimp [n]
    positivity
  have hn1 : n - 1 ≠ 0 := by
    dsimp [n]
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hn))
  calc
    uniformAverage (fun σ : Equiv.Perm α => (permutationSampleSum S y σ) ^ 2) =
        uniformAverage (fun σ : Equiv.Perm α =>
          ∑ i : ↥S, ∑ j : ↥S, y (σ i.val) * y (σ j.val)) := by
      congr 1
      funext σ
      rw [permutationSampleSum, pow_two, Fintype.sum_mul_sum]
    _ = ∑ i : ↥S, ∑ j : ↥S,
          uniformAverage (fun σ : Equiv.Perm α => y (σ i.val) * y (σ j.val)) := by
      rw [uniformAverage_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [uniformAverage_sum]
    _ = ∑ i : ↥S, ∑ j : ↥S,
          if i = j then V / n else -V / (n * (n - 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [if_pos]
        dsimp [V, n]
        simpa [pow_two] using
          (uniformAverage_perm_apply (fun a => y a * y a) i.val)
      · simp only [if_neg hij]
        have hval : i.val ≠ j.val := by
          intro h
          exact hij (Subtype.ext h)
        simpa [V, n] using uniformAverage_centered_pair y hy hval
    _ = k * (k * (-V / (n * (n - 1))) + V / n - (-V / (n * (n - 1))) ) := by
      simpa [k] using
        sum_pair_ite S (V / n) (-V / (n * (n - 1)))
    _ = (k * (n - k) / (n * (n - 1))) * V := by
      field_simp [hn0, hn1]
      ring
    _ = ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) *
        ∑ a, y a ^ 2 := by rfl

/-- Exact variance of a fixed-size sample without replacement from an
arbitrary real-valued finite population. -/
theorem uniformAverage_permutationSampleSum_variance [Nonempty α]
    (S : Finset α) (x : α → ℝ) (hn : 1 < Fintype.card α) :
    uniformAverage (fun σ : Equiv.Perm α =>
        (permutationSampleSum S x σ - (S.card : ℝ) * populationMean x) ^ 2) =
      ((S.card : ℝ) * ((Fintype.card α : ℝ) - S.card) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) *
        ∑ a, centeredPopulation x a ^ 2 := by
  simpa only [permutationSampleSum_centered] using
    uniformAverage_permutationSampleSum_sq S (centeredPopulation x)
      (sum_centeredPopulation x) hn

end
end SchedulingPaper.Randomized
