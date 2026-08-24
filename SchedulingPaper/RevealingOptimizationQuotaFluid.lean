import SchedulingPaper.RevealingOptimizationQuotaCanonicalTrace
import SchedulingPaper.RandomizedOptionalPilotKernel
import SchedulingPaper.RandomizedOptionalCanonicalKernel
import Mathlib.Tactic

/-!
# From the finite revealing quota kernel to its fluid template

The random-placement kernel differs from the empirical fluid objective only
by the without-replacement correction and the `O(n)` self/diagonal terms.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace QuotaFluid

open Randomized
open RandomizedOptional
open InstanceLearning
open QuotaKernel

noncomputable section

def empiricalQuotaFluidValue
    {n : ℕ} (u x : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) : ℝ :=
  empiricalProductPairAverage
    (fun left right => fluidPairCharge u x low
      (processing left) (processing right)) / 2

theorem empiricalProductPairAverage_swap
    {α : Type*} [Fintype α] (f : α → α → ℝ) :
    empiricalProductPairAverage f =
      empiricalProductPairAverage (fun x y => f y x) := by
  unfold empiricalProductPairAverage
  rw [Finset.sum_comm]

theorem empiricalProductPairAverage_half_add
    {α : Type*} [Fintype α] (f g : α → α → ℝ) :
    (empiricalProductPairAverage f + empiricalProductPairAverage g) / 2 =
      empiricalProductPairAverage (fun x y => (f x y + g x y) / 2) := by
  unfold empiricalProductPairAverage
  rw [show (∑ x : α, ∑ y : α, (f x y + g x y) / 2) =
      ((∑ x : α, ∑ y : α, f x y) +
        ∑ x : α, ∑ y : α, g x y) / 2 by
        simp_rw [add_div, Finset.sum_add_distrib]
        simp only [Finset.sum_div]]
  ring

theorem empiricalProductPairAverage_add
    {α : Type*} [Fintype α] (f g : α → α → ℝ) :
    empiricalProductPairAverage (fun x y => f x y + g x y) =
      empiricalProductPairAverage f + empiricalProductPairAverage g := by
  unfold empiricalProductPairAverage
  rw [show (∑ x : α, ∑ y : α, (f x y + g x y)) =
      (∑ x : α, ∑ y : α, f x y) + ∑ x : α, ∑ y : α, g x y by
        simp_rw [Finset.sum_add_distrib]]
  ring

theorem empiricalProductPairAverage_const_mul
    {α : Type*} [Fintype α] (c : ℝ) (f : α → α → ℝ) :
    empiricalProductPairAverage (fun x y => c * f x y) =
      c * empiricalProductPairAverage f := by
  unfold empiricalProductPairAverage
  simp_rw [← Finset.mul_sum]
  ring

theorem empiricalProductPairAverage_separable
    {α : Type*} [Fintype α]
    (f g : α → ℝ) :
    empiricalProductPairAverage (fun x y => f x * g y) =
      empiricalSingleAverage f * empiricalSingleAverage g := by
  unfold empiricalProductPairAverage empiricalSingleAverage
  rw [show (∑ x : α, ∑ y : α, f x * g y) =
      (∑ x : α, f x) * ∑ y : α, g y by
        calc
          (∑ x : α, ∑ y : α, f x * g y) =
              ∑ x : α, f x * ∑ y : α, g y := by
                apply Finset.sum_congr rfl
                intro x _
                rw [Finset.mul_sum]
          _ = (∑ x : α, f x) * ∑ y : α, g y := by
                rw [Finset.sum_mul]]
  ring

theorem empiricalProductPairAverage_const
    {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    empiricalProductPairAverage (fun _ _ : α => c) = c := by
  unfold empiricalProductPairAverage
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp
  field_simp [hcard]

theorem empiricalProductPairAverage_left
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    empiricalProductPairAverage (fun x _ => f x) =
      empiricalSingleAverage f := by
  rw [show (fun x : α => fun _y : α => f x) =
      (fun x y => f x * (fun _ : α => (1 : ℝ)) y) by
        funext x y
        simp,
    empiricalProductPairAverage_separable]
  have hone : empiricalSingleAverage (fun _ : α => (1 : ℝ)) = 1 := by
    unfold empiricalSingleAverage
    simp
  rw [hone, mul_one]

theorem empiricalProductPairAverage_right
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    empiricalProductPairAverage (fun _ y => f y) =
      empiricalSingleAverage f := by
  rw [empiricalProductPairAverage_swap]
  exact empiricalProductPairAverage_left f

theorem empiricalProduct_testedPairChargeOrdered
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    (low : ℝ → Bool) :
    empiricalProductPairAverage (fun left right =>
        testedPairChargeOrdered (low (processing left))
          (low (processing right)) (processing left) (processing right)) =
      empiricalProductPairAverage (fun left right =>
        testedPairChargeFlags (low (processing left))
          (low (processing right)) (processing left) (processing right)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let f := fun left right : Fin n =>
    testedPairChargeOrdered (low (processing left))
      (low (processing right)) (processing left) (processing right)
  let g := fun left right : Fin n =>
    testedPairChargeFlags (low (processing left))
      (low (processing right)) (processing left) (processing right)
  calc
    empiricalProductPairAverage f =
        (empiricalProductPairAverage f +
          empiricalProductPairAverage (fun x y => f y x)) / 2 := by
      rw [← empiricalProductPairAverage_swap f]
      ring
    _ = empiricalProductPairAverage
          (fun x y => (f x y + f y x) / 2) :=
      empiricalProductPairAverage_half_add _ _
    _ = empiricalProductPairAverage g := by
      apply congrArg empiricalProductPairAverage
      funext left right
      exact testedPairChargeOrdered_symmetrized _ _ _ _

theorem empiricalProduct_quotaPairCharge_indicator
    {n q : ℕ} (hn : 0 < n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    (i j : Fin n) :
    empiricalProductPairAverage (fun left right =>
        quotaPairCharge q u low i j
          (processing left) (processing right)) =
      testedPosition q i * testedPosition q j *
          empiricalProductPairAverage (fun left right =>
            testedPairChargeFlags (low (processing left))
              (low (processing right)) (processing left) (processing right)) +
        testedPosition q i * (1 - testedPosition q j) *
          empiricalSingleAverage (fun left => 1 + processing left) +
        (1 - testedPosition q i) * testedPosition q j *
          empiricalSingleAverage (fun right => 1 + processing right) +
        (1 - testedPosition q i) * (1 - testedPosition q j) * u := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  by_cases hi : i.val < q <;> by_cases hj : j.val < q
  · by_cases hij : i.val < j.val
    · simp [quotaPairCharge, testedPosition, hi, hj, hij,
        empiricalProduct_testedPairChargeOrdered hn processing low]
    · have hreverse :
          empiricalProductPairAverage (fun left right =>
              testedPairChargeOrdered (low (processing right))
                (low (processing left)) (processing right) (processing left)) =
            empiricalProductPairAverage (fun left right =>
              testedPairChargeFlags (low (processing left))
                (low (processing right)) (processing left) (processing right)) := by
        rw [← empiricalProductPairAverage_swap]
        exact empiricalProduct_testedPairChargeOrdered hn processing low
      simp [quotaPairCharge, testedPosition, hi, hj, hij, hreverse]
  · simp [quotaPairCharge, testedPosition, hi, hj,
      empiricalProductPairAverage_left]
  · simp [quotaPairCharge, testedPosition, hi, hj,
      empiricalProductPairAverage_right]
  · simp [quotaPairCharge, testedPosition, hi, hj,
      empiricalProductPairAverage_const]

theorem doubleSum_scaled_separable
    {α : Type*} [Fintype α] (c : ℝ) (f g : α → ℝ) :
    (∑ i : α, ∑ j : α, c * f i * g j) =
      c * (∑ i : α, f i) * ∑ j : α, g j := by
  calc
    (∑ i : α, ∑ j : α, c * f i * g j) =
        ∑ i : α, (c * f i) * ∑ j : α, g j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = c * (∑ i : α, f i) * ∑ j : α, g j := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem doubleSum_indicator_formula
    {n q : ℕ} (hq : q ≤ n) (A B u : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (testedPosition q i * testedPosition q j * A +
        testedPosition q i * (1 - testedPosition q j) * B +
        (1 - testedPosition q i) * testedPosition q j * B +
        (1 - testedPosition q i) * (1 - testedPosition q j) * u)) =
      (q : ℝ) ^ 2 * A +
        2 * q * (n - q) * B + (n - q : ℝ) ^ 2 * u := by
  let tested := fun i : Fin n => testedPosition q i
  let raw := fun i : Fin n => 1 - testedPosition q i
  have htested : (∑ i : Fin n, tested i) = (q : ℝ) := by
    simpa [tested] using sum_testedPosition hq
  have hraw : (∑ i : Fin n, raw i) = (n - q : ℝ) := by
    simpa [raw] using sum_one_sub_testedPosition hq
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      (testedPosition q i * testedPosition q j * A +
        testedPosition q i * (1 - testedPosition q j) * B +
        (1 - testedPosition q i) * testedPosition q j * B +
        (1 - testedPosition q i) * (1 - testedPosition q j) * u)) =
        (∑ i : Fin n, ∑ j : Fin n, A * tested i * tested j) +
        (∑ i : Fin n, ∑ j : Fin n, B * tested i * raw j) +
        (∑ i : Fin n, ∑ j : Fin n, B * raw i * tested j) +
        (∑ i : Fin n, ∑ j : Fin n, u * raw i * raw j) := by
      simp only [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·)
        · apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            dsimp [tested]
            ring
          · apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            dsimp [tested, raw]
            ring
        · apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [tested, raw]
          ring
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [raw]
        ring
    _ = A * (∑ i : Fin n, tested i) * (∑ j : Fin n, tested j) +
        B * (∑ i : Fin n, tested i) * (∑ j : Fin n, raw j) +
        B * (∑ i : Fin n, raw i) * (∑ j : Fin n, tested j) +
        u * (∑ i : Fin n, raw i) * (∑ j : Fin n, raw j) := by
      rw [doubleSum_scaled_separable, doubleSum_scaled_separable,
        doubleSum_scaled_separable, doubleSum_scaled_separable]
    _ = (q : ℝ) ^ 2 * A +
        2 * q * (n - q) * B + (n - q : ℝ) ^ 2 * u := by
      rw [htested, hraw]
      ring

theorem empiricalProduct_fluid_formula
    {n : ℕ} (hn : 0 < n) (u x : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    empiricalProductPairAverage (fun left right =>
        fluidPairCharge u x low (processing left) (processing right)) =
      x ^ 2 * empiricalProductPairAverage (fun left right =>
          testedPairChargeFlags (low (processing left))
            (low (processing right)) (processing left) (processing right)) +
        2 * x * (1 - x) *
          empiricalSingleAverage (fun job => 1 + processing job) +
        (1 - x) ^ 2 * u := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold fluidPairCharge fluidPairChargeFlags
  repeat rw [empiricalProductPairAverage_add]
  rw [empiricalProductPairAverage_const_mul]
  rw [show (fun left right : Fin n => x * (1 - x) * (1 + processing left)) =
      (fun left right => (x * (1 - x)) * (1 + processing left)) by rfl,
    empiricalProductPairAverage_const_mul,
    empiricalProductPairAverage_left]
  rw [show (fun left right : Fin n => x * (1 - x) * (1 + processing right)) =
      (fun left right => (x * (1 - x)) * (1 + processing right)) by rfl,
    empiricalProductPairAverage_const_mul,
    empiricalProductPairAverage_right]
  rw [empiricalProductPairAverage_const]
  ring

theorem fullPositionProduct_eq_fluid
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    (∑ i : Fin n, ∑ j : Fin n,
        empiricalProductPairAverage (fun left right =>
          quotaPairCharge q u low i j
            (processing left) (processing right)) / 2) =
      (n : ℝ) ^ 2 *
        empiricalQuotaFluidValue u (q / n) processing low := by
  let A := empiricalProductPairAverage (fun left right : Fin n =>
    testedPairChargeFlags (low (processing left))
      (low (processing right)) (processing left) (processing right))
  let B := empiricalSingleAverage (fun job : Fin n => 1 + processing job)
  simp_rw [empiricalProduct_quotaPairCharge_indicator hn u processing low]
  rw [show (∑ i : Fin n, ∑ j : Fin n,
      (testedPosition q i * testedPosition q j * A +
        testedPosition q i * (1 - testedPosition q j) * B +
        (1 - testedPosition q i) * testedPosition q j * B +
        (1 - testedPosition q i) * (1 - testedPosition q j) * u) / 2) =
      (∑ i : Fin n, ∑ j : Fin n,
        (testedPosition q i * testedPosition q j * A +
          testedPosition q i * (1 - testedPosition q j) * B +
          (1 - testedPosition q i) * testedPosition q j * B +
          (1 - testedPosition q i) * (1 - testedPosition q j) * u)) / 2 by
        simp_rw [Finset.sum_div]]
  rw [doubleSum_indicator_formula hq]
  unfold empiricalQuotaFluidValue
  rw [empiricalProduct_fluid_formula hn]
  dsimp [A, B]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnR]

theorem empiricalSingleAverage_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ empiricalSingleAverage f := by
  unfold empiricalSingleAverage
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)

theorem empiricalSingleAverage_le
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) (hf : ∀ x, f x ≤ c) :
    empiricalSingleAverage f ≤ c := by
  unfold empiricalSingleAverage
  have hcard : (0 : ℝ) < Fintype.card α := by positivity
  calc
    (∑ x : α, f x) / Fintype.card α ≤
        ((Fintype.card α : ℝ) * c) / Fintype.card α := by
      apply div_le_div_of_nonneg_right _ hcard.le
      simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset α)
        f c (fun x _ => hf x)
    _ = c := by field_simp

theorem empiricalProductPairAverage_nonneg
    {α : Type*} [Fintype α]
    (f : α → α → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    0 ≤ empiricalProductPairAverage f := by
  unfold empiricalProductPairAverage
  exact div_nonneg
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hf x y)
    (sq_nonneg _)

theorem empiricalProductPairAverage_le
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → α → ℝ) (c : ℝ) (hf : ∀ x y, f x y ≤ c) :
    empiricalProductPairAverage f ≤ c := by
  unfold empiricalProductPairAverage
  have hcard : (0 : ℝ) < Fintype.card α := by positivity
  have hsum : (∑ x : α, ∑ y : α, f x y) ≤
      (Fintype.card α : ℝ) ^ 2 * c := by
    calc
      (∑ x : α, ∑ y : α, f x y) ≤
          ∑ _x : α, (Fintype.card α : ℝ) * c := by
        apply Finset.sum_le_sum
        intro x _
        simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset α)
          (f x) c (fun y _ => hf x y)
      _ = (Fintype.card α : ℝ) ^ 2 * c := by
        simp [pow_two]
        ring
  calc
    (∑ x : α, ∑ y : α, f x y) / (Fintype.card α : ℝ) ^ 2 ≤
        ((Fintype.card α : ℝ) ^ 2 * c) /
          (Fintype.card α : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = c := by field_simp [hcard.ne']

theorem positionKernelPairProductValue_add_diagonal
    {n q : ℕ} (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) :
    positionKernelPairProductValue (quotaPairKernel q u processing low) +
        (∑ i : Fin n, empiricalProductPairAverage (fun left right =>
          quotaPairCharge q u low i i
            (processing left) (processing right)) / 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        empiricalProductPairAverage (fun left right =>
          quotaPairCharge q u low i j
            (processing left) (processing right)) / 2 := by
  let g := fun i j : Fin n => empiricalProductPairAverage (fun left right =>
    quotaPairCharge q u low i j
      (processing left) (processing right)) / 2
  have hdecomp := orderedDistinct_add_diagonal g
  unfold positionKernelPairProductValue
  rw [show (∑ z : OrderedDistinct (Fin n),
      empiricalProductPairAverage (quotaPairKernel q u processing low z)) =
      ∑ z : OrderedDistinct (Fin n), g z.val.1 z.val.2 by
        apply Finset.sum_congr rfl
        intro z _
        unfold quotaPairKernel
        dsimp [g]
        rw [show (fun left right : Fin n =>
            quotaPairCharge q u low z.val.1 z.val.2
              (processing left) (processing right) / 2) =
            (fun left right => (1 / 2 : ℝ) *
              quotaPairCharge q u low z.val.1 z.val.2
                (processing left) (processing right)) by
              funext left right
              ring,
          empiricalProductPairAverage_const_mul]
        ring]
  exact hdecomp

theorem positionKernelProductValue_eq_fluid_add_correction
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    positionKernelProductValue (quotaSingleKernel q u processing)
        (quotaPairKernel q u processing low) =
      (n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low +
        (∑ i : Fin n,
          empiricalSingleAverage (quotaSingleKernel q u processing i)) -
        (∑ i : Fin n, empiricalProductPairAverage (fun left right =>
          quotaPairCharge q u low i i
            (processing left) (processing right)) / 2) := by
  have hpair := positionKernelPairProductValue_add_diagonal
    (q := q) u processing low
  have hfull := fullPositionProduct_eq_fluid hn hq u processing low
  unfold positionKernelProductValue
  linarith

theorem positionKernelProductValue_fluid_error
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n)
    (u : ℝ) (hu0 : 0 ≤ u) (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) :
    |positionKernelProductValue (quotaSingleKernel q u processing)
          (quotaPairKernel q u processing low) -
        (n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low| ≤
      (n : ℝ) * (3 * u + 4) / 2 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let singleValue := ∑ i : Fin n,
    empiricalSingleAverage (quotaSingleKernel q u processing i)
  let diagonalValue := ∑ i : Fin n,
    empiricalProductPairAverage (fun left right =>
      quotaPairCharge q u low i i
        (processing left) (processing right)) / 2
  have hsingleNonneg : 0 ≤ singleValue := by
    dsimp [singleValue]
    apply Finset.sum_nonneg
    intro i _
    apply empiricalSingleAverage_nonneg
    intro actual
    unfold quotaSingleKernel
    split <;> linarith [hp0 actual]
  have hsingleUpper : singleValue ≤ (n : ℝ) * (u + 1) := by
    dsimp [singleValue]
    calc
      (∑ i : Fin n,
          empiricalSingleAverage (quotaSingleKernel q u processing i)) ≤
          ∑ _i : Fin n, (u + 1) := by
        apply Finset.sum_le_sum
        intro i _
        apply empiricalSingleAverage_le
        intro actual
        unfold quotaSingleKernel
        split <;> linarith [hpu actual]
      _ = (n : ℝ) * (u + 1) := by simp; ring
  have hdiagonalNonneg : 0 ≤ diagonalValue := by
    dsimp [diagonalValue]
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg
      (empiricalProductPairAverage_nonneg _ fun left right =>
        quotaPairCharge_nonneg hu0 low i i (hp0 left) (hp0 right))
      (by norm_num)
  have hdiagonalUpper : diagonalValue ≤ (n : ℝ) * (u + 2) / 2 := by
    dsimp [diagonalValue]
    calc
      (∑ i : Fin n, empiricalProductPairAverage (fun left right =>
          quotaPairCharge q u low i i
            (processing left) (processing right)) / 2) ≤
          ∑ _i : Fin n, ((u + 2) / 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply empiricalProductPairAverage_le
        intro left right
        exact quotaPairCharge_le hu0 low i i
          (hp0 left) (hpu left) (hp0 right) (hpu right)
      _ = (n : ℝ) * (u + 2) / 2 := by simp; ring
  rw [positionKernelProductValue_eq_fluid_add_correction hn hq]
  rw [show (n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low +
          (∑ i : Fin n,
            empiricalSingleAverage (quotaSingleKernel q u processing i)) -
          (∑ i : Fin n, empiricalProductPairAverage (fun left right =>
            quotaPairCharge q u low i i
              (processing left) (processing right)) / 2) -
          (n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low =
        singleValue - diagonalValue by
      dsimp [singleValue, diagonalValue]
      ring]
  calc
    |singleValue - diagonalValue| ≤ |singleValue| + |diagonalValue| :=
      abs_sub singleValue diagonalValue
    _ = singleValue + diagonalValue := by
      rw [abs_of_nonneg hsingleNonneg, abs_of_nonneg hdiagonalNonneg]
    _ ≤ (n : ℝ) * (u + 1) + (n : ℝ) * (u + 2) / 2 :=
      add_le_add hsingleUpper hdiagonalUpper
    _ = (n : ℝ) * (3 * u + 4) / 2 := by ring

theorem positionKernelProductValue_fluid_normalized_error
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n)
    (u : ℝ) (hu0 : 0 ≤ u) (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) :
    |positionKernelProductValue (quotaSingleKernel q u processing)
          (quotaPairKernel q u processing low) / (n : ℝ) ^ 2 -
        empiricalQuotaFluidValue u (q / n) processing low| ≤
      (3 * u + 4) / (2 * n) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hraw := positionKernelProductValue_fluid_error hn hq u hu0
    processing hp0 hpu low
  rw [show empiricalQuotaFluidValue u (q / n) processing low =
      ((n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low) /
        (n : ℝ) ^ 2 by field_simp [hnR.ne']]
  rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hnR)]
  calc
    |positionKernelProductValue (quotaSingleKernel q u processing)
          (quotaPairKernel q u processing low) -
        (n : ℝ) ^ 2 * empiricalQuotaFluidValue u (q / n) processing low| /
          (n : ℝ) ^ 2 ≤
        ((n : ℝ) * (3 * u + 4) / 2) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hraw (sq_nonneg _)
    _ = (3 * u + 4) / (2 * n) := by field_simp [hnR.ne']

/-- The literal finite random-placement quota kernel converges uniformly to
its empirical fluid objective, with all finite corrections explicit. -/
theorem quotaKernelCost_fluid_normalized_error
    {n q : ℕ} (hn : 1 < n) (hq : q ≤ n)
    (u : ℝ) (hu0 : 0 ≤ u) (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) :
    |uniformAverage (quotaKernelCost q u processing low) / (n : ℝ) ^ 2 -
        empiricalQuotaFluidValue u (q / n) processing low| ≤
      (5 * u + 8) / (2 * n) := by
  have hkernel := quotaKernelCost_product_normalized (q := q) hn u hu0
    processing hp0 hpu low
  have hfluid := positionKernelProductValue_fluid_normalized_error
    (by omega) hq u hu0 processing hp0 hpu low
  calc
    |uniformAverage (quotaKernelCost q u processing low) / (n : ℝ) ^ 2 -
        empiricalQuotaFluidValue u (q / n) processing low| ≤
      |uniformAverage (quotaKernelCost q u processing low) / (n : ℝ) ^ 2 -
          positionKernelProductValue (quotaSingleKernel q u processing)
            (quotaPairKernel q u processing low) / (n : ℝ) ^ 2| +
      |positionKernelProductValue (quotaSingleKernel q u processing)
            (quotaPairKernel q u processing low) / (n : ℝ) ^ 2 -
          empiricalQuotaFluidValue u (q / n) processing low| :=
        abs_sub_le _ _ _
    _ ≤ (u + 2) / n + (3 * u + 4) / (2 * n) :=
      add_le_add hkernel hfluid
    _ = (5 * u + 8) / (2 * n) := by ring

/-- Pushing the empirical population through a finite category map turns the
quota fluid objective into exactly the categorical grid objective. -/
theorem empiricalQuotaFluidValue_eq_gridTemplateValue
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : Fin n → Option ι) (price : ι → ℝ) (u : ℝ)
    (T : InstanceLearning.Template ι n)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    (hprice : ∀ job,
      positiveGridPrice price (category job) = processing job)
    (hlow : ∀ job,
      low (processing job) = T.lowWithZero (category job)) :
    empiricalQuotaFluidValue u T.fraction processing low =
      InstanceLearning.gridTemplateValue
        (populationHistogram category) price u T := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold empiricalQuotaFluidValue InstanceLearning.gridTemplateValue
  rw [finiteProductExpectation_populationHistogram]
  apply congrArg (fun z : ℝ => z / 2)
  apply congrArg empiricalProductPairAverage
  funext left right
  unfold gridPairCharge fluidPairCharge
  rw [hprice left, hprice right, hlow left, hlow right]

/-- The executable value selector induced by a finite revealing template.
Zero is always low; positive values inherit the unique grid-cell flag. -/
def templateLowSelector
    {ι : Type*} [Fintype ι] {n : ℕ}
    (price : ι → ℝ) (T : InstanceLearning.Template ι n)
    (value : ℝ) : Bool := by
  classical
  exact decide (value = 0 ∨
    ∃ i, price i = value ∧ T.low i = true)

@[simp] theorem templateLowSelector_zero
    {ι : Type*} [Fintype ι] {n : ℕ}
    (price : ι → ℝ) (T : InstanceLearning.Template ι n) :
    templateLowSelector price T 0 = true := by
  classical
  simp [templateLowSelector]

theorem templateLowSelector_at_cell
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (price : ι → ℝ) (hprice0 : ∀ i, 0 < price i)
    (hprice : Function.Injective price)
    (T : InstanceLearning.Template ι n) (cell : Option ι) :
    templateLowSelector price T (positiveGridPrice price cell) =
      T.lowWithZero cell := by
  classical
  cases cell with
  | none => simp [positiveGridPrice, InstanceLearning.Template.lowWithZero]
  | some i =>
      cases hlow : T.low i with
      | false =>
          simp only [positiveGridPrice, InstanceLearning.Template.lowWithZero,
            hlow]
          apply Bool.eq_false_of_not_eq_true
          intro htrue
          have hex : price i = 0 ∨
              ∃ j, price j = price i ∧ T.low j = true := by
            simpa [templateLowSelector, positiveGridPrice] using htrue
          rcases hex with hzero | ⟨j, hj, hjlow⟩
          · exact (ne_of_gt (hprice0 i)) hzero
          · have hji : j = i := hprice hj
            subst j
            simp [hlow] at hjlow
      | true =>
          simp only [positiveGridPrice, InstanceLearning.Template.lowWithZero,
            hlow]
          apply Bool.eq_true_of_not_eq_false
          intro hfalse
          have hnot : ¬(price i = 0 ∨
              ∃ j, price j = price i ∧ T.low j = true) := by
            simpa [templateLowSelector, positiveGridPrice] using hfalse
          exact hnot (Or.inr ⟨i, rfl, hlow⟩)

theorem quotaKernelCost_gridTemplate_normalized_error
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : Fin n → Option ι) (price : ι → ℝ)
    (u : ℝ) (hu0 : 0 ≤ u)
    (T : InstanceLearning.Template ι n)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool)
    (hprice : ∀ job,
      positiveGridPrice price (category job) = processing job)
    (hlow : ∀ job,
      low (processing job) = T.lowWithZero (category job)) :
    |uniformAverage
          (quotaKernelCost T.quota.val u processing low) / (n : ℝ) ^ 2 -
        InstanceLearning.gridTemplateValue
          (populationHistogram category) price u T| ≤
      (5 * u + 8) / (2 * n) := by
  rw [← empiricalQuotaFluidValue_eq_gridTemplateValue
    (by omega) category price u T processing low hprice hlow]
  simpa [InstanceLearning.Template.fraction] using
    quotaKernelCost_fluid_normalized_error hn T.quota_le u hu0
      processing hp0 hpu low

/-- Executing the privately relabelled strategy has exactly the finite kernel
cost indexed by that relabelling permutation. -/
theorem randomizedQuotaRun_completionCost_eq_quotaKernelCost
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    (hzero : low 0 = true) (order : Equiv.Perm (Fin n)) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n q low order)
          (2 * n + 1)) =
      quotaKernelCost q u processing low order := by
  rw [QuotaStrategy.randomizedQuotaStrategy,
    Online.runCompletionCost_relabel]
  change Online.completionCost (.finite u)
      (fun virtual => processing (order virtual))
      (QuotaStrategy.quotaRun q u
        (fun virtual => processing (order virtual)) low).config.transcript = _
  rw [QuotaStrategy.quotaRun_completionCost_eq_quotaKernelCost
    hq u (fun virtual => processing (order virtual)) low hzero]
  rfl

/-- End-to-end fixed-template statement: the expected completion cost of the
literal randomized quota run is within the explicit finite correction of its
categorical fluid value. -/
theorem randomizedQuotaRun_gridTemplate_normalized_error
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : Fin n → Option ι) (price : ι → ℝ)
    (u : ℝ) (hu0 : 0 ≤ u)
    (T : InstanceLearning.Template ι n)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) (hzero : low 0 = true)
    (hprice : ∀ job,
      positiveGridPrice price (category job) = processing job)
    (hlow : ∀ job,
      low (processing job) = T.lowWithZero (category job)) :
    |uniformAverage (fun order : Equiv.Perm (Fin n) =>
          Online.runCompletionCost (.finite u) processing
            (Online.run (.finite u) (Online.fixedOracle processing)
              (QuotaStrategy.randomizedQuotaStrategy n T.quota.val low order)
              (2 * n + 1))) / (n : ℝ) ^ 2 -
        InstanceLearning.gridTemplateValue
          (populationHistogram category) price u T| ≤
      (5 * u + 8) / (2 * n) := by
  rw [show (fun order : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n T.quota.val low order)
          (2 * n + 1))) =
      quotaKernelCost T.quota.val u processing low by
        funext order
        exact randomizedQuotaRun_completionCost_eq_quotaKernelCost
          T.quota_le u processing low hzero order]
  exact quotaKernelCost_gridTemplate_normalized_error hn category price
    u hu0 T processing hp0 hpu low hprice hlow

/-- Pilot learning followed by an independent literal quota run.  This
theorem performs the complete finite averaging composition: histogram
learning error plus the explicit operational/kernel correction. -/
theorem learnedRandomizedQuotaRun_le
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (category : Fin n → Option ι)
    (price : ι → ℝ) (hprice0 : ∀ i, 0 < price i)
    (hprice : Function.Injective price)
    (u : ℝ) (hu0 : 0 ≤ u) (hpriceu : ∀ i, price i ≤ u)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (hcategory : ∀ job,
      positiveGridPrice price (category job) = processing job)
    (target : InstanceLearning.Template ι n) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      let learned := InstanceLearning.minimizingTemplate (n := n)
        (sampleHistogram pilotPositions category pilotOrder) price u
      let low := templateLowSelector price learned
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (QuotaStrategy.randomizedQuotaStrategy n learned.quota.val
              low mainOrder) (2 * n + 1))) / (n : ℝ) ^ 2) ≤
      InstanceLearning.gridTemplateValue
          (populationHistogram category) price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) /
            pilotPositions.card) +
        (5 * u + 8) / (2 * n) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let learned := fun pilotOrder : Equiv.Perm (Fin n) =>
    InstanceLearning.minimizingTemplate (n := n)
      (sampleHistogram pilotPositions category pilotOrder) price u
  let conditionalCost := fun pilotOrder : Equiv.Perm (Fin n) =>
    uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n
            (learned pilotOrder).quota.val
            (templateLowSelector price (learned pilotOrder)) mainOrder)
          (2 * n + 1))) / (n : ℝ) ^ 2
  let finiteError := (5 * u + 8) / (2 * (n : ℝ))
  have hconditional : ∀ pilotOrder, conditionalCost pilotOrder ≤
      InstanceLearning.gridTemplateValue
        (populationHistogram category) price u (learned pilotOrder) +
        finiteError := by
    intro pilotOrder
    have hlow : ∀ job,
        templateLowSelector price (learned pilotOrder) (processing job) =
          (learned pilotOrder).lowWithZero (category job) := by
      intro job
      rw [← hcategory job]
      exact templateLowSelector_at_cell price hprice0 hprice
        (learned pilotOrder) (category job)
    have herr := randomizedQuotaRun_gridTemplate_normalized_error hn
      category price u hu0 (learned pilotOrder) processing hp0 hpu
      (templateLowSelector price (learned pilotOrder))
      (templateLowSelector_zero price (learned pilotOrder))
      hcategory hlow
    have hupper := (abs_le.mp herr).2
    dsimp [conditionalCost, finiteError]
    linarith
  have hlearn := InstanceLearning.uniformSample_minimizingTemplate_le
    (by omega : 0 < n) pilotPositions category hpilot
    (by simpa using hn) price hu0 (fun i => (hprice0 i).le)
    hpriceu target
  calc
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      let learned := InstanceLearning.minimizingTemplate (n := n)
        (sampleHistogram pilotPositions category pilotOrder) price u
      let low := templateLowSelector price learned
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (QuotaStrategy.randomizedQuotaStrategy n learned.quota.val
              low mainOrder) (2 * n + 1))) / (n : ℝ) ^ 2) =
        uniformAverage conditionalCost := by rfl
    _ ≤ uniformAverage (fun pilotOrder =>
        InstanceLearning.gridTemplateValue
          (populationHistogram category) price u (learned pilotOrder) +
          finiteError) := uniformAverage_mono hconditional
    _ = uniformAverage (fun pilotOrder =>
          InstanceLearning.gridTemplateValue
            (populationHistogram category) price u (learned pilotOrder)) +
        finiteError := by
      rw [uniformAverage_add, uniformAverage_const]
    _ ≤ (InstanceLearning.gridTemplateValue
          (populationHistogram category) price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) /
            pilotPositions.card)) + finiteError := by
      linarith
    _ = InstanceLearning.gridTemplateValue
          (populationHistogram category) price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) /
            pilotPositions.card) +
        (5 * u + 8) / (2 * n) := by
      dsimp [finiteError]

end

end QuotaFluid
end RevealingOptimization
end SchedulingPaper
