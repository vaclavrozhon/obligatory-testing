import SchedulingPaper.RandomizedOptionalKernel
import Mathlib.Tactic

/-!
# Optional testing: uniform finite operation-word kernels

A fixed canonical operation word has one bounded self contribution for each
position and one bounded interaction kernel for each ordered pair of distinct
positions.  The kernels may depend on the positions (tested/blind status,
block, and order), but not on the random labels occupying them.

This file proves the uniform `O(n)` replacement (27a): after averaging over a
uniform permutation, all one-position terms contribute only `O(n)`, while
every two-position term may be replaced by its empirical product expectation
with total error `O(n)`.  The bound is independent of the grid size and of
the particular fixed template.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

def positionKernelCost
    {α : Type*} [Fintype α] [DecidableEq α]
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ)
    (σ : Equiv.Perm α) : ℝ :=
  (∑ i, single i (σ i)) +
    ∑ z : OrderedDistinct α, pair z (σ z.val.1) (σ z.val.2)

def empiricalSingleAverage
    {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

def positionKernelPairProductValue
    {α : Type*} [Fintype α] [DecidableEq α]
    (pair : OrderedDistinct α → α → α → ℝ) : ℝ :=
  ∑ z : OrderedDistinct α, empiricalProductPairAverage (pair z)

def positionKernelProductValue
    {α : Type*} [Fintype α] [DecidableEq α]
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ) : ℝ :=
  (∑ i, empiricalSingleAverage (single i)) +
    positionKernelPairProductValue pair

/-- Exact expansion before applying any bounded-kernel estimate. -/
theorem uniformAverage_positionKernelCost
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ) :
    uniformAverage (positionKernelCost single pair) =
      (∑ i, empiricalSingleAverage (single i)) +
        ∑ z : OrderedDistinct α,
          uniformAverage (fun σ : Equiv.Perm α =>
            pair z (σ z.val.1) (σ z.val.2)) := by
  unfold positionKernelCost
  rw [uniformAverage_add, uniformAverage_fintype_sum,
    uniformAverage_fintype_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact uniformAverage_perm_apply (single i) i

/-- Uniform finite-kernel replacement with an explicit unnormalized error.
The right side is `O(Bsingle*n + Bpair*n)`. -/
theorem positionKernel_product_replacement_error
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ)
    {Bsingle Bpair : ℝ}
    (hsingle : ∀ i x, |single i x| ≤ Bsingle)
    (hpair : ∀ z x y, |pair z x y| ≤ Bpair) :
    |uniformAverage (positionKernelCost single pair) -
        positionKernelPairProductValue pair| ≤
      Fintype.card α * Bsingle +
        Fintype.card (OrderedDistinct α) *
          (2 * Bpair / Fintype.card α) := by
  rw [uniformAverage_positionKernelCost]
  unfold positionKernelPairProductValue
  rw [show
      (∑ i, empiricalSingleAverage (single i)) +
            (∑ z : OrderedDistinct α,
              uniformAverage (fun σ : Equiv.Perm α =>
                pair z (σ z.val.1) (σ z.val.2))) -
          ∑ z : OrderedDistinct α, empiricalProductPairAverage (pair z) =
        (∑ i, empiricalSingleAverage (single i)) +
          ∑ z : OrderedDistinct α,
            (uniformAverage (fun σ : Equiv.Perm α =>
                pair z (σ z.val.1) (σ z.val.2)) -
              empiricalProductPairAverage (pair z)) by
        rw [Finset.sum_sub_distrib]
        ring]
  calc
    |(∑ i, empiricalSingleAverage (single i)) +
        ∑ z : OrderedDistinct α,
          (uniformAverage (fun σ : Equiv.Perm α =>
              pair z (σ z.val.1) (σ z.val.2)) -
            empiricalProductPairAverage (pair z))| ≤
      |∑ i, empiricalSingleAverage (single i)| +
        |∑ z : OrderedDistinct α,
          (uniformAverage (fun σ : Equiv.Perm α =>
              pair z (σ z.val.1) (σ z.val.2)) -
            empiricalProductPairAverage (pair z))| := abs_add_le _ _
    _ ≤ (∑ _i : α, Bsingle) +
        ∑ _z : OrderedDistinct α,
          (2 * Bpair / Fintype.card α) := by
      apply add_le_add
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => by
            unfold empiricalSingleAverage
            have hN : (0 : ℝ) < Fintype.card α := by positivity
            calc
              |(∑ x, single i x) / Fintype.card α| =
                  |∑ x, single i x| / Fintype.card α := by
                    rw [abs_div, abs_of_pos hN]
              _ ≤ (Fintype.card α * Bsingle) /
                    Fintype.card α := by
                  exact div_le_div_of_nonneg_right
                    (abs_fintype_sum_le_card_mul (hsingle i)) hN.le
              _ = Bsingle := by
                  field_simp [hN.ne'])
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun z _ =>
            uniformPermutationPair_empiricalProduct_error
              z.property (pair z) (hpair z))
    _ = Fintype.card α * Bsingle +
        Fintype.card (OrderedDistinct α) *
          (2 * Bpair / Fintype.card α) := by simp

/-- Sharpened replacement retaining the exact one-position contribution.
This is the useful form when a single operation, such as a unit test, has a
leading-order interaction with all other jobs but only a bounded self term. -/
theorem positionKernel_product_replacement_error_with_single
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ)
    {Bpair : ℝ}
    (hpair : ∀ z x y, |pair z x y| ≤ Bpair) :
    |uniformAverage (positionKernelCost single pair) -
        positionKernelProductValue single pair| ≤
      Fintype.card (OrderedDistinct α) *
        (2 * Bpair / Fintype.card α) := by
  rw [uniformAverage_positionKernelCost]
  unfold positionKernelProductValue positionKernelPairProductValue
  rw [show
      (∑ i, empiricalSingleAverage (single i)) +
            (∑ z : OrderedDistinct α,
              uniformAverage (fun σ : Equiv.Perm α =>
                pair z (σ z.val.1) (σ z.val.2))) -
          ((∑ i, empiricalSingleAverage (single i)) +
            ∑ z : OrderedDistinct α, empiricalProductPairAverage (pair z)) =
        ∑ z : OrderedDistinct α,
          (uniformAverage (fun σ : Equiv.Perm α =>
              pair z (σ z.val.1) (σ z.val.2)) -
            empiricalProductPairAverage (pair z)) by
        rw [Finset.sum_sub_distrib]
        ring]
  calc
    |∑ z : OrderedDistinct α,
        (uniformAverage (fun σ : Equiv.Perm α =>
            pair z (σ z.val.1) (σ z.val.2)) -
          empiricalProductPairAverage (pair z))| ≤
        ∑ z : OrderedDistinct α,
          |uniformAverage (fun σ : Equiv.Perm α =>
              pair z (σ z.val.1) (σ z.val.2)) -
            empiricalProductPairAverage (pair z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : OrderedDistinct α,
        (2 * Bpair / Fintype.card α) :=
      Finset.sum_le_sum fun z _ =>
        uniformPermutationPair_empiricalProduct_error
          z.property (pair z) (hpair z)
    _ = Fintype.card (OrderedDistinct α) *
        (2 * Bpair / Fintype.card α) := by simp

/-- Normalized sharpened replacement: only pair sampling contributes an
`O(Bpair/n)` error. -/
theorem positionKernel_product_replacement_normalized_with_single
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (hcard : 1 < Fintype.card α)
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ)
    {Bpair : ℝ} (hBpair : 0 ≤ Bpair)
    (hpair : ∀ z x y, |pair z x y| ≤ Bpair) :
    |uniformAverage (positionKernelCost single pair) /
          (Fintype.card α : ℝ) ^ 2 -
        positionKernelProductValue single pair /
          (Fintype.card α : ℝ) ^ 2| ≤
      2 * Bpair / Fintype.card α := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by dsimp [N]; positivity
  have hraw := positionKernel_product_replacement_error_with_single
    single pair hpair
  have hpairCard : Fintype.card (OrderedDistinct α) =
      Fintype.card α * (Fintype.card α - 1) :=
    orderedDistinct_card (α := α)
  have hcastSub : ((Fintype.card α - 1 : ℕ) : ℝ) = N - 1 := by
    rw [Nat.cast_sub hcard.le]
    simp [N]
  rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hN)]
  calc
    |uniformAverage (positionKernelCost single pair) -
          positionKernelProductValue single pair| / N ^ 2 ≤
        (Fintype.card (OrderedDistinct α) *
          (2 * Bpair / Fintype.card α)) / N ^ 2 :=
      div_le_div_of_nonneg_right hraw (sq_nonneg N)
    _ ≤ 2 * Bpair / N := by
      rw [hpairCard]
      push_cast
      rw [hcastSub]
      field_simp [hN.ne']
      nlinarith [show (1 : ℝ) ≤ N by
        dsimp [N]
        exact_mod_cast (show 1 ≤ Fintype.card α by omega)]
    _ = 2 * Bpair / Fintype.card α := rfl

/-- Normalized form: the fixed-word/product-law discrepancy is at most
`Bsingle/n + 2 Bpair/n`. -/
theorem positionKernel_product_replacement_normalized
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (hcard : 1 < Fintype.card α)
    (single : α → α → ℝ)
    (pair : OrderedDistinct α → α → α → ℝ)
    {Bsingle Bpair : ℝ}
    (hBpair : 0 ≤ Bpair)
    (hsingle : ∀ i x, |single i x| ≤ Bsingle)
    (hpair : ∀ z x y, |pair z x y| ≤ Bpair) :
    |uniformAverage (positionKernelCost single pair) /
          (Fintype.card α : ℝ) ^ 2 -
        positionKernelPairProductValue pair /
          (Fintype.card α : ℝ) ^ 2| ≤
      Bsingle / Fintype.card α + 2 * Bpair / Fintype.card α := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by dsimp [N]; positivity
  have hraw := positionKernel_product_replacement_error
    single pair hsingle hpair
  have hpairCard : Fintype.card (OrderedDistinct α) =
      Fintype.card α * (Fintype.card α - 1) :=
    orderedDistinct_card (α := α)
  have hcastSub : ((Fintype.card α - 1 : ℕ) : ℝ) = N - 1 := by
    rw [Nat.cast_sub hcard.le]
    simp [N]
  rw [← sub_div] 
  rw [abs_div, abs_of_pos (sq_pos_of_pos hN)]
  calc
    |uniformAverage (positionKernelCost single pair) -
          positionKernelPairProductValue pair| / N ^ 2 ≤
      (Fintype.card α * Bsingle +
          Fintype.card (OrderedDistinct α) *
            (2 * Bpair / Fintype.card α)) / N ^ 2 :=
        div_le_div_of_nonneg_right hraw (sq_nonneg N)
    _ ≤ Bsingle / N + 2 * Bpair / N := by
      rw [hpairCard]
      push_cast
      rw [hcastSub]
      have hN1 : 1 ≤ N := by
        dsimp [N]
        exact_mod_cast (show 1 ≤ Fintype.card α by omega)
      field_simp [hN.ne']
      nlinarith
    _ = Bsingle / Fintype.card α +
        2 * Bpair / Fintype.card α := rfl

end

end RandomizedOptional
end SchedulingPaper
