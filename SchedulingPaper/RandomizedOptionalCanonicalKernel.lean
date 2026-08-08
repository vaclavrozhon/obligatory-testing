import SchedulingPaper.RandomizedOptionalFiniteKernel
import SchedulingPaper.RandomizedOptionalObservedStrategyCompletion
import Mathlib.Tactic

/-!
# Pair kernels for the finite canonical optional schedule

The kernel records exactly the delay relations of the four blocks.  Unit
tests are charged to every unfinished job; earlier low completions remove
the corresponding ordered pair.  Medium, blind, and high work are then
charged according to their block order, with SPT interactions represented by
`min`.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

def boolWeight (b : Bool) : ℝ := if b then 1 else 0

def testedPosition {n : ℕ} (q : ℕ) (i : Fin n) : ℝ :=
  if i.val < q then 1 else 0

def beforePosition {n : ℕ} (i j : Fin n) : ℝ :=
  if i.val < j.val then 1 else 0

theorem boolWeight_mem_Icc (b : Bool) : boolWeight b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> simp [boolWeight]

theorem testedPosition_mem_Icc {n q : ℕ} (i : Fin n) :
    testedPosition q i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold testedPosition
  split <;> simp

theorem beforePosition_mem_Icc {n : ℕ} (i j : Fin n) :
    beforePosition i j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold beforePosition
  split <;> simp

/-- Bounded self terms of a canonical schedule.  All leading test delay is
represented by pair terms; only the tested job's own delay remains here. -/
def canonicalSingleKernel
    {n : ℕ} (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) (i x : Fin n) : ℝ :=
  let t := testedPosition q i
  let b := 1 - t
  let l := boolWeight (low (p x))
  let m := boolWeight (medium (p x))
  let h := boolWeight (high (p x))
  t * (1 + p x * l) +
    t * m * p x + b * p x + t * h * p x

/-- Ordered-pair delay kernel of the canonical schedule. -/
def canonicalPairKernel
    {n : ℕ} (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool)
    (z : OrderedDistinct (Fin n)) (x y : Fin n) : ℝ :=
  let i := z.val.1
  let j := z.val.2
  let ti := testedPosition q i
  let tj := testedPosition q j
  let bi := 1 - ti
  let bj := 1 - tj
  let lx := boolWeight (low (p x))
  let ly := boolWeight (low (p y))
  let mx := boolWeight (medium (p x))
  let my := boolWeight (medium (p y))
  let hx := boolWeight (high (p x))
  let hy := boolWeight (high (p y))
  ti * (1 + p x * lx) -
    ti * tj * beforePosition j i * ly * (1 + p x * lx) +
    ti * bj * mx * p x +
    ti * tj * mx * hy * p x +
    ti * tj * mx * my * min (p x) (p y) / 2 +
    bi * tj * hy * p x +
    bi * bj * beforePosition i j * p x +
    ti * tj * hx * hy * min (p x) (p y) / 2

def canonicalKernelCost
    {n : ℕ} (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) (σ : Equiv.Perm (Fin n)) : ℝ :=
  positionKernelCost
    (canonicalSingleKernel q p low medium high)
    (canonicalPairKernel q p low medium high) σ

private theorem product01_le_one
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ a * b ∧ a * b ≤ 1 := by
  constructor
  · exact mul_nonneg ha.1 hb.1
  · nlinarith [mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0 : ℝ) ≤ 1)]

private theorem product01_three_le_one
    {a b c : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ a * b * c ∧ a * b * c ≤ 1 := by
  have hab := product01_le_one ha hb
  exact product01_le_one ⟨hab.1, hab.2⟩ hc

private theorem product01_four_le_one
    {a b c d : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ a * b * c * d ∧ a * b * c * d ≤ 1 := by
  have habc := product01_three_le_one ha hb hc
  exact product01_le_one ⟨habc.1, habc.2⟩ hd

private theorem product01_five_le_one
    {a b c d e : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ a * b * c * d * e ∧ a * b * c * d * e ≤ 1 := by
  have habcd := product01_four_le_one ha hb hc hd
  exact product01_le_one ⟨habcd.1, habcd.2⟩ he

private theorem product01_mul_le
    {a x L : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    0 ≤ a * x ∧ a * x ≤ L := by
  constructor
  · exact mul_nonneg ha.1 hx0
  · calc
      a * x ≤ 1 * L := mul_le_mul ha.2 hxL hx0 (by norm_num)
      _ = L := one_mul L

/-- Uniform boundedness of every canonical pair interaction. -/
theorem canonicalPairKernel_abs_le
    {n : ℕ} (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) {L : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpL : ∀ x, p x ≤ L)
    (z : OrderedDistinct (Fin n)) (x y : Fin n) :
    |canonicalPairKernel q p low medium high z x y| ≤ 2 + 7 * L := by
  let ti := testedPosition q z.val.1
  let tj := testedPosition q z.val.2
  let bi := 1 - ti
  let bj := 1 - tj
  let beforeJI := beforePosition z.val.2 z.val.1
  let beforeIJ := beforePosition z.val.1 z.val.2
  let lx := boolWeight (low (p x))
  let ly := boolWeight (low (p y))
  let mx := boolWeight (medium (p x))
  let my := boolWeight (medium (p y))
  let hx := boolWeight (high (p x))
  let hy := boolWeight (high (p y))
  have hti : ti ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [ti] using testedPosition_mem_Icc (q := q) z.val.1
  have htj : tj ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [tj] using testedPosition_mem_Icc (q := q) z.val.2
  have hbi : bi ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [bi]
    exact ⟨by linarith [hti.2], by linarith [hti.1]⟩
  have hbj : bj ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [bj]
    exact ⟨by linarith [htj.2], by linarith [htj.1]⟩
  have hbeforeJI : beforeJI ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [beforeJI] using beforePosition_mem_Icc z.val.2 z.val.1
  have hbeforeIJ : beforeIJ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [beforeIJ] using beforePosition_mem_Icc z.val.1 z.val.2
  have hlx : lx ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [lx] using boolWeight_mem_Icc (low (p x))
  have hly : ly ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [ly] using boolWeight_mem_Icc (low (p y))
  have hmx : mx ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [mx] using boolWeight_mem_Icc (medium (p x))
  have hmy : my ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [my] using boolWeight_mem_Icc (medium (p y))
  have hhx : hx ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [hx] using boolWeight_mem_Icc (high (p x))
  have hhy : hy ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [hy] using boolWeight_mem_Icc (high (p y))
  have hL0 : 0 ≤ L := (hp0 x).trans (hpL x)
  have hmin0 : 0 ≤ min (p x) (p y) := le_min (hp0 x) (hp0 y)
  have hminL : min (p x) (p y) ≤ L :=
    (min_le_left _ _).trans (hpL x)
  let A := ti * (1 + p x * lx)
  let B := ti * tj * beforeJI * ly * (1 + p x * lx)
  let C := ti * bj * mx * p x
  let D := ti * tj * mx * hy * p x
  let E := ti * tj * mx * my * min (p x) (p y) / 2
  let F := bi * tj * hy * p x
  let G := bi * bj * beforeIJ * p x
  let H := ti * tj * hx * hy * min (p x) (p y) / 2
  have hA : 0 ≤ A ∧ A ≤ 1 + L := by
    dsimp [A]
    have hpxlx := product01_mul_le hlx (hp0 x) (hpL x)
    constructor
    · exact mul_nonneg hti.1 (by linarith [hpxlx.1])
    · calc
        ti * (1 + p x * lx) ≤ 1 * (1 + L) :=
          mul_le_mul hti.2 (by linarith [hpxlx.2])
            (by linarith [hpxlx.1]) (by norm_num)
        _ = 1 + L := one_mul _
  have hB : 0 ≤ B ∧ B ≤ 1 + L := by
    dsimp [B]
    have hprod := product01_four_le_one hti htj hbeforeJI hly
    have hpxlx := product01_mul_le hlx (hp0 x) (hpL x)
    constructor
    · exact mul_nonneg hprod.1 (by linarith [hpxlx.1])
    · calc
        ti * tj * beforeJI * ly * (1 + p x * lx) ≤
            1 * (1 + L) :=
          mul_le_mul hprod.2 (by linarith [hpxlx.2])
            (by linarith [hpxlx.1]) (by norm_num)
        _ = 1 + L := one_mul _
  have hC : 0 ≤ C ∧ C ≤ L := by
    dsimp [C]
    have hprod := product01_three_le_one hti hbj hmx
    exact product01_mul_le ⟨hprod.1, hprod.2⟩ (hp0 x) (hpL x)
  have hD : 0 ≤ D ∧ D ≤ L := by
    dsimp [D]
    have hprod := product01_four_le_one hti htj hmx hhy
    exact product01_mul_le ⟨hprod.1, hprod.2⟩ (hp0 x) (hpL x)
  have hE : 0 ≤ E ∧ E ≤ L / 2 := by
    dsimp [E]
    have hprod := product01_four_le_one hti htj hmx hmy
    have hmul := product01_mul_le ⟨hprod.1, hprod.2⟩ hmin0 hminL
    constructor
    · exact div_nonneg hmul.1 (by norm_num)
    · exact div_le_div_of_nonneg_right hmul.2 (by norm_num)
  have hF : 0 ≤ F ∧ F ≤ L := by
    dsimp [F]
    have hprod := product01_three_le_one hbi htj hhy
    exact product01_mul_le ⟨hprod.1, hprod.2⟩ (hp0 x) (hpL x)
  have hG : 0 ≤ G ∧ G ≤ L := by
    dsimp [G]
    have hprod := product01_three_le_one hbi hbj hbeforeIJ
    exact product01_mul_le ⟨hprod.1, hprod.2⟩ (hp0 x) (hpL x)
  have hH : 0 ≤ H ∧ H ≤ L / 2 := by
    dsimp [H]
    have hprod := product01_four_le_one hti htj hhx hhy
    have hmul := product01_mul_le ⟨hprod.1, hprod.2⟩ hmin0 hminL
    constructor
    · exact div_nonneg hmul.1 (by norm_num)
    · exact div_le_div_of_nonneg_right hmul.2 (by norm_num)
  have htriangle : |A - B + C + D + E + F + G + H| ≤
      |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| := by
    calc
      |A - B + C + D + E + F + G + H| ≤
          |A - B + C + D + E + F + G| + |H| := abs_add_le _ _
      _ ≤ |A - B + C + D + E + F| + |G| + |H| := by
        linarith [abs_add_le (A - B + C + D + E + F) G]
      _ ≤ |A - B + C + D + E| + |F| + |G| + |H| := by
        linarith [abs_add_le (A - B + C + D + E) F]
      _ ≤ |A - B + C + D| + |E| + |F| + |G| + |H| := by
        linarith [abs_add_le (A - B + C + D) E]
      _ ≤ |A - B + C| + |D| + |E| + |F| + |G| + |H| := by
        linarith [abs_add_le (A - B + C) D]
      _ ≤ |A - B| + |C| + |D| + |E| + |F| + |G| + |H| := by
        linarith [abs_add_le (A - B) C]
      _ ≤ |A| + |B| + |C| + |D| + |E| + |F| + |G| + |H| := by
        linarith [abs_sub A B]
  change |A - B + C + D + E + F + G + H| ≤ 2 + 7 * L
  have hAabs : |A| ≤ 1 + L := by rw [abs_of_nonneg hA.1]; exact hA.2
  have hBabs : |B| ≤ 1 + L := by rw [abs_of_nonneg hB.1]; exact hB.2
  have hCabs : |C| ≤ L := by rw [abs_of_nonneg hC.1]; exact hC.2
  have hDabs : |D| ≤ L := by rw [abs_of_nonneg hD.1]; exact hD.2
  have hEabs : |E| ≤ L / 2 := by rw [abs_of_nonneg hE.1]; exact hE.2
  have hFabs : |F| ≤ L := by rw [abs_of_nonneg hF.1]; exact hF.2
  have hGabs : |G| ≤ L := by rw [abs_of_nonneg hG.1]; exact hG.2
  have hHabs : |H| ≤ L / 2 := by rw [abs_of_nonneg hH.1]; exact hH.2
  exact htriangle.trans (by linarith)

/-- The expected finite canonical kernel differs from its empirical-product
evaluation by only `O_L(1/n)`, uniformly in the quota and classifiers. -/
theorem canonicalKernelCost_product_normalized
    {n : ℕ} (hn : 1 < n) (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) {L : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpL : ∀ x, p x ≤ L) :
    |uniformAverage (canonicalKernelCost q p low medium high) / (n : ℝ) ^ 2 -
        positionKernelProductValue
          (canonicalSingleKernel q p low medium high)
          (canonicalPairKernel q p low medium high) / (n : ℝ) ^ 2| ≤
      2 * (2 + 7 * L) / n := by
  let x₀ : Fin n := ⟨0, by omega⟩
  letI : Nonempty (Fin n) := ⟨x₀⟩
  have hB : 0 ≤ 2 + 7 * L := by
    linarith [(hp0 x₀).trans (hpL x₀)]
  have h := positionKernel_product_replacement_normalized_with_single
    (α := Fin n) (by simpa using hn)
    (canonicalSingleKernel q p low medium high)
    (canonicalPairKernel q p low medium high) hB
    (canonicalPairKernel_abs_le q p low medium high hp0 hpL)
  simpa [canonicalKernelCost] using h

/-! ## Position coefficients -/

theorem sum_testedPosition
    {n q : ℕ} (hq : q ≤ n) :
    (∑ i : Fin n, testedPosition q i) = q := by
  by_cases hqn : q = n
  · subst q
    simp [testedPosition, Fin.isLt]
  · have hqLt : q < n := lt_of_le_of_ne hq hqn
    let bound : Fin n := ⟨q, hqLt⟩
    have hfilter : Finset.univ.filter (fun i : Fin n => i.val < q) =
        Finset.Iio bound := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Iio]
      change i.val < q ↔ i.val < q
      rfl
    unfold testedPosition
    rw [← Finset.sum_filter]
    simp [hfilter, bound]

theorem sum_one_sub_testedPosition
    {n q : ℕ} (hq : q ≤ n) :
    (∑ i : Fin n, (1 - testedPosition q i)) = n - q := by
  rw [Finset.sum_sub_distrib, sum_testedPosition hq]
  simp

def swapOrderedDistinct {α : Type*} [DecidableEq α] :
    OrderedDistinct α ≃ OrderedDistinct α where
  toFun z := ⟨(z.val.2, z.val.1), Ne.symm z.property⟩
  invFun z := ⟨(z.val.2, z.val.1), Ne.symm z.property⟩
  left_inv z := by rcases z with ⟨⟨i, j⟩, hij⟩; rfl
  right_inv z := by rcases z with ⟨⟨i, j⟩, hij⟩; rfl

theorem sum_orderedDistinct_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → ℝ) :
    (∑ z : OrderedDistinct α, f z.val.1 * g z.val.2) =
      (∑ i, f i) * (∑ j, g j) - ∑ i, f i * g i := by
  have h := orderedDistinct_add_diagonal (fun i j => f i * g j)
  rw [← Fintype.sum_mul_sum] at h
  linarith

theorem sum_testedPosition_sq
    {n q : ℕ} (hq : q ≤ n) :
    (∑ z : OrderedDistinct (Fin n),
      testedPosition q z.val.1 * testedPosition q z.val.2) =
        q * (q - 1) := by
  rw [sum_orderedDistinct_mul, sum_testedPosition hq]
  have hdiag : (∑ i : Fin n,
      testedPosition q i * testedPosition q i) = q := by
    calc
      (∑ i : Fin n, testedPosition q i * testedPosition q i) =
          ∑ i : Fin n, testedPosition q i := by
        apply Finset.sum_congr rfl
        intro i _
        unfold testedPosition
        split <;> norm_num
      _ = q := sum_testedPosition hq
  rw [hdiag]
  push_cast
  have hqR : (0 : ℝ) ≤ q := by positivity
  ring

theorem sum_testedPosition_one_sub
    {n q : ℕ} (hq : q ≤ n) :
    (∑ z : OrderedDistinct (Fin n),
      testedPosition q z.val.1 * (1 - testedPosition q z.val.2)) =
        q * (n - q) := by
  rw [sum_orderedDistinct_mul
    (fun i : Fin n => testedPosition q i)
    (fun i : Fin n => 1 - testedPosition q i),
    sum_testedPosition hq, sum_one_sub_testedPosition hq]
  have hdiag : (∑ i : Fin n,
      testedPosition q i * (1 - testedPosition q i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    unfold testedPosition
    split <;> norm_num
  rw [hdiag]
  push_cast
  ring

theorem sum_one_sub_testedPosition_sq
    {n q : ℕ} (hq : q ≤ n) :
    (∑ z : OrderedDistinct (Fin n),
      (1 - testedPosition q z.val.1) *
        (1 - testedPosition q z.val.2)) =
      (n - q) * (n - q - 1) := by
  rw [sum_orderedDistinct_mul
    (fun i : Fin n => 1 - testedPosition q i)
    (fun i : Fin n => 1 - testedPosition q i),
    sum_one_sub_testedPosition hq]
  have hdiag : (∑ i : Fin n,
      (1 - testedPosition q i) * (1 - testedPosition q i)) = n - q := by
    calc
      (∑ i : Fin n,
          (1 - testedPosition q i) * (1 - testedPosition q i)) =
          ∑ i : Fin n, (1 - testedPosition q i) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold testedPosition
        split <;> norm_num
      _ = n - q := sum_one_sub_testedPosition hq
  rw [hdiag]
  push_cast
  have hqR : (q : ℝ) ≤ n := by exact_mod_cast hq
  ring

theorem beforePosition_add_reverse
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    beforePosition i j + beforePosition j i = 1 := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · simp [beforePosition, hlt, not_lt_of_ge hlt.le]
  · exact (hij (Fin.ext heq)).elim
  · simp [beforePosition, hgt, not_lt_of_ge hgt.le]

theorem sum_testedPosition_before
    {n q : ℕ} (hq : q ≤ n) :
    2 * (∑ z : OrderedDistinct (Fin n),
      testedPosition q z.val.1 * testedPosition q z.val.2 *
        beforePosition z.val.2 z.val.1) = q * (q - 1) := by
  let f : OrderedDistinct (Fin n) → ℝ := fun z =>
    testedPosition q z.val.1 * testedPosition q z.val.2 *
      beforePosition z.val.2 z.val.1
  have hswap : (∑ z : OrderedDistinct (Fin n), f (swapOrderedDistinct z)) =
      ∑ z : OrderedDistinct (Fin n), f z := by
    simpa using Equiv.sum_comp (swapOrderedDistinct (α := Fin n)) f
  have hpair : ∀ z : OrderedDistinct (Fin n),
      f z + f (swapOrderedDistinct z) =
        testedPosition q z.val.1 * testedPosition q z.val.2 := by
    intro z
    dsimp [f, swapOrderedDistinct]
    have hbefore : beforePosition z.val.2 z.val.1 +
        beforePosition z.val.1 z.val.2 = 1 :=
      beforePosition_add_reverse z.val.2 z.val.1 (Ne.symm z.property)
    calc
      testedPosition q z.val.1 * testedPosition q z.val.2 *
            beforePosition z.val.2 z.val.1 +
          testedPosition q z.val.2 * testedPosition q z.val.1 *
            beforePosition z.val.1 z.val.2 =
          (testedPosition q z.val.1 * testedPosition q z.val.2) *
            (beforePosition z.val.2 z.val.1 +
              beforePosition z.val.1 z.val.2) := by ring
      _ = testedPosition q z.val.1 * testedPosition q z.val.2 := by
        rw [hbefore]
        ring
  calc
    2 * (∑ z : OrderedDistinct (Fin n),
        testedPosition q z.val.1 * testedPosition q z.val.2 *
          beforePosition z.val.2 z.val.1) =
        (∑ z : OrderedDistinct (Fin n), f z) +
          ∑ z : OrderedDistinct (Fin n), f (swapOrderedDistinct z) := by
            change 2 * (∑ z : OrderedDistinct (Fin n), f z) = _
            rw [hswap]
            ring
    _ = ∑ z : OrderedDistinct (Fin n),
        testedPosition q z.val.1 * testedPosition q z.val.2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hpair z
    _ = q * (q - 1) := sum_testedPosition_sq hq

theorem sum_one_sub_testedPosition_before
    {n q : ℕ} (hq : q ≤ n) :
    2 * (∑ z : OrderedDistinct (Fin n),
      (1 - testedPosition q z.val.1) *
        (1 - testedPosition q z.val.2) *
        beforePosition z.val.1 z.val.2) =
      (n - q) * (n - q - 1) := by
  let f : OrderedDistinct (Fin n) → ℝ := fun z =>
    (1 - testedPosition q z.val.1) *
      (1 - testedPosition q z.val.2) *
      beforePosition z.val.1 z.val.2
  have hswap : (∑ z : OrderedDistinct (Fin n), f (swapOrderedDistinct z)) =
      ∑ z : OrderedDistinct (Fin n), f z := by
    simpa using Equiv.sum_comp (swapOrderedDistinct (α := Fin n)) f
  have hpair : ∀ z : OrderedDistinct (Fin n),
      f z + f (swapOrderedDistinct z) =
        (1 - testedPosition q z.val.1) *
          (1 - testedPosition q z.val.2) := by
    intro z
    dsimp [f, swapOrderedDistinct]
    have hbefore : beforePosition z.val.1 z.val.2 +
        beforePosition z.val.2 z.val.1 = 1 :=
      beforePosition_add_reverse z.val.1 z.val.2 z.property
    calc
      (1 - testedPosition q z.val.1) *
            (1 - testedPosition q z.val.2) *
            beforePosition z.val.1 z.val.2 +
          (1 - testedPosition q z.val.2) *
            (1 - testedPosition q z.val.1) *
            beforePosition z.val.2 z.val.1 =
          ((1 - testedPosition q z.val.1) *
            (1 - testedPosition q z.val.2)) *
            (beforePosition z.val.1 z.val.2 +
              beforePosition z.val.2 z.val.1) := by ring
      _ = (1 - testedPosition q z.val.1) *
          (1 - testedPosition q z.val.2) := by
        rw [hbefore]
        ring
  calc
    2 * (∑ z : OrderedDistinct (Fin n),
        (1 - testedPosition q z.val.1) *
          (1 - testedPosition q z.val.2) *
          beforePosition z.val.1 z.val.2) =
        (∑ z : OrderedDistinct (Fin n), f z) +
          ∑ z : OrderedDistinct (Fin n), f (swapOrderedDistinct z) := by
            change 2 * (∑ z : OrderedDistinct (Fin n), f z) = _
            rw [hswap]
            ring
    _ = ∑ z : OrderedDistinct (Fin n),
        (1 - testedPosition q z.val.1) *
          (1 - testedPosition q z.val.2) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => hpair z
    _ = (n - q) * (n - q - 1) :=
      sum_one_sub_testedPosition_sq hq

/-! ## Exact empirical-product evaluation -/

/-- Empirical moments of a fixed Boolean four-block classification. -/
def canonicalEmpiricalMoments
    {n : ℕ} (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) : FluidMoments where
  lowMass := empiricalSingleAverage fun x => boolWeight (low (p x))
  lowMoment := empiricalSingleAverage fun x =>
    p x * boolWeight (low (p x))
  mediumMoment := empiricalSingleAverage fun x =>
    p x * boolWeight (medium (p x))
  highMass := empiricalSingleAverage fun x => boolWeight (high (p x))
  mean := empiricalSingleAverage p
  mediumMinPair := empiricalProductPairAverage fun x y =>
    min (p x) (p y) * boolWeight (medium (p x)) *
      boolWeight (medium (p y))
  highMinPair := empiricalProductPairAverage fun x y =>
    min (p x) (p y) * boolWeight (high (p x)) *
      boolWeight (high (p y))

def canonicalEmpiricalHighMoment
    {n : ℕ} (p : Fin n → ℝ) (high : ℝ → Bool) : ℝ :=
  empiricalSingleAverage fun x => p x * boolWeight (high (p x))

private theorem empiricalSingleAverage_add
    {α : Type*} [Fintype α] [Nonempty α] (f g : α → ℝ) :
    empiricalSingleAverage (fun x => f x + g x) =
      empiricalSingleAverage f + empiricalSingleAverage g := by
  unfold empiricalSingleAverage
  rw [Finset.sum_add_distrib]
  ring

private theorem empiricalSingleAverage_const_mul
    {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) (f : α → ℝ) :
    empiricalSingleAverage (fun x => c * f x) =
      c * empiricalSingleAverage f := by
  unfold empiricalSingleAverage
  rw [← Finset.mul_sum]
  ring

private theorem empiricalSingleAverage_const
    {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    empiricalSingleAverage (fun _x : α => c) = c := by
  unfold empiricalSingleAverage
  have hN : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp [hN]

private theorem empiricalProductPairAverage_add
    {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → α → ℝ) :
    empiricalProductPairAverage (fun x y => f x y + g x y) =
      empiricalProductPairAverage f + empiricalProductPairAverage g := by
  unfold empiricalProductPairAverage
  simp_rw [Finset.sum_add_distrib]
  ring

private theorem empiricalProductPairAverage_sub
    {α : Type*} [Fintype α] [Nonempty α]
    (f g : α → α → ℝ) :
    empiricalProductPairAverage (fun x y => f x y - g x y) =
      empiricalProductPairAverage f - empiricalProductPairAverage g := by
  unfold empiricalProductPairAverage
  simp_rw [Finset.sum_sub_distrib]
  ring

private theorem empiricalProductPairAverage_const_mul
    {α : Type*} [Fintype α] [Nonempty α]
    (c : ℝ) (f : α → α → ℝ) :
    empiricalProductPairAverage (fun x y => c * f x y) =
      c * empiricalProductPairAverage f := by
  unfold empiricalProductPairAverage
  simp_rw [← Finset.mul_sum]
  ring

private theorem empiricalProductPairAverage_separable
    {α : Type*} [Fintype α] [Nonempty α]
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

private theorem empiricalProductPairAverage_left
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) :
    empiricalProductPairAverage (fun x _y => f x) =
      empiricalSingleAverage f := by
  rw [show (fun x : α => fun _y : α => f x) =
      (fun x y => f x * (fun _ : α => (1 : ℝ)) y) by
        funext x y; simp,
    empiricalProductPairAverage_separable]
  have hone : empiricalSingleAverage (fun _ : α => (1 : ℝ)) = 1 := by
    unfold empiricalSingleAverage
    simp
  rw [hone, mul_one]

private theorem empiricalProductPairAverage_right
    {α : Type*} [Fintype α] [Nonempty α]
    (g : α → ℝ) :
    empiricalProductPairAverage (fun _x y => g y) =
      empiricalSingleAverage g := by
  rw [show (fun _x : α => fun y : α => g y) =
      (fun x y => (fun _ : α => (1 : ℝ)) x * g y) by
        funext x y; simp,
    empiricalProductPairAverage_separable]
  have hone : empiricalSingleAverage (fun _ : α => (1 : ℝ)) = 1 := by
    unfold empiricalSingleAverage
    simp
  rw [hone, one_mul]

private theorem canonicalSingleKernel_productAverage
    {n : ℕ} [Nonempty (Fin n)] (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) (i : Fin n) :
    empiricalSingleAverage
        (canonicalSingleKernel q p low medium high i) =
      testedPosition q i *
          (1 + (canonicalEmpiricalMoments p low medium high).lowMoment) +
        testedPosition q i *
          (canonicalEmpiricalMoments p low medium high).mediumMoment +
        (1 - testedPosition q i) *
          (canonicalEmpiricalMoments p low medium high).mean +
        testedPosition q i * canonicalEmpiricalHighMoment p high := by
  unfold canonicalSingleKernel
  simp only [canonicalEmpiricalMoments, canonicalEmpiricalHighMoment]
  rw [show (fun x : Fin n =>
      testedPosition q i * (1 + p x * boolWeight (low (p x))) +
        testedPosition q i * boolWeight (medium (p x)) * p x +
        (1 - testedPosition q i) * p x +
        testedPosition q i * boolWeight (high (p x)) * p x) =
      (fun x =>
        testedPosition q i +
        testedPosition q i * (p x * boolWeight (low (p x))) +
        testedPosition q i * (p x * boolWeight (medium (p x))) +
        (1 - testedPosition q i) * p x +
        testedPosition q i * (p x * boolWeight (high (p x)))) by
      funext x; ring]
  simp_rw [empiricalSingleAverage_add, empiricalSingleAverage_const_mul]
  have hconst : empiricalSingleAverage
      (fun _x : Fin n => testedPosition q i) = testedPosition q i := by
    exact empiricalSingleAverage_const _
  rw [hconst]
  ring

private theorem canonicalPairKernel_productAverage
    {n : ℕ} [Nonempty (Fin n)] (q : ℕ) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) (z : OrderedDistinct (Fin n)) :
    let M := canonicalEmpiricalMoments p low medium high
    empiricalProductPairAverage
        (canonicalPairKernel q p low medium high z) =
      testedPosition q z.val.1 * (1 + M.lowMoment) -
      testedPosition q z.val.1 * testedPosition q z.val.2 *
        beforePosition z.val.2 z.val.1 * M.lowMass * (1 + M.lowMoment) +
      testedPosition q z.val.1 * (1 - testedPosition q z.val.2) *
        M.mediumMoment +
      testedPosition q z.val.1 * testedPosition q z.val.2 *
        M.mediumMoment * M.highMass +
      testedPosition q z.val.1 * testedPosition q z.val.2 *
        M.mediumMinPair / 2 +
      (1 - testedPosition q z.val.1) * testedPosition q z.val.2 *
        M.mean * M.highMass +
      (1 - testedPosition q z.val.1) *
        (1 - testedPosition q z.val.2) *
        beforePosition z.val.1 z.val.2 * M.mean +
      testedPosition q z.val.1 * testedPosition q z.val.2 *
        M.highMinPair / 2 := by
  dsimp only
  simp only [canonicalEmpiricalMoments]
  let ti := testedPosition q z.val.1
  let tj := testedPosition q z.val.2
  let bi := 1 - ti
  let bj := 1 - tj
  let beforeJI := beforePosition z.val.2 z.val.1
  let beforeIJ := beforePosition z.val.1 z.val.2
  let l : Fin n → ℝ := fun x => boolWeight (low (p x))
  let m : Fin n → ℝ := fun x => boolWeight (medium (p x))
  let h : Fin n → ℝ := fun x => boolWeight (high (p x))
  let pl : Fin n → ℝ := fun x => p x * l x
  let pm : Fin n → ℝ := fun x => p x * m x
  let kM : Fin n → Fin n → ℝ := fun x y =>
    min (p x) (p y) * m x * m y
  let kH : Fin n → Fin n → ℝ := fun x y =>
    min (p x) (p y) * h x * h y
  have hkernel : canonicalPairKernel q p low medium high z = (fun x y =>
      ti * (1 + pl x) -
      (ti * tj * beforeJI) * ((1 + pl x) * l y) +
      (ti * bj) * pm x + (ti * tj) * (pm x * h y) +
      (ti * tj / 2) * kM x y + (bi * tj) * (p x * h y) +
      (bi * bj * beforeIJ) * p x + (ti * tj / 2) * kH x y) := by
    funext x y
    simp only [canonicalPairKernel]
    dsimp [ti, tj, bi, bj, beforeJI, beforeIJ, l, m, h, pl, pm, kM, kH]
    ring
  rw [hkernel]
  simp_rw [empiricalProductPairAverage_add,
    empiricalProductPairAverage_sub,
    empiricalProductPairAverage_const_mul,
    empiricalProductPairAverage_left,
    empiricalProductPairAverage_separable,
    empiricalSingleAverage_add, empiricalSingleAverage_const]
  change _ =
    ti * (1 + empiricalSingleAverage pl) -
      ti * tj * beforeJI * empiricalSingleAverage l *
        (1 + empiricalSingleAverage pl) +
      ti * bj * empiricalSingleAverage pm +
      ti * tj * empiricalSingleAverage pm * empiricalSingleAverage h +
      ti * tj * empiricalProductPairAverage kM / 2 +
      bi * tj * empiricalSingleAverage p * empiricalSingleAverage h +
      bi * bj * beforeIJ * empiricalSingleAverage p +
      ti * tj * empiricalProductPairAverage kH / 2
  ring

/-- Exact empirical-product evaluation before dividing by `n^2`. -/
def canonicalFiniteProductFormula
    (n q : ℕ) (M : FluidMoments) (highMoment : ℝ) : ℝ :=
  q * (1 + M.lowMoment) + q * M.mediumMoment +
    (n - q) * M.mean + q * highMoment +
    q * (n - 1) * (1 + M.lowMoment) -
    q * (q - 1) / 2 * M.lowMass * (1 + M.lowMoment) +
    q * (n - q) * M.mediumMoment +
    q * (q - 1) * M.mediumMoment * M.highMass +
    q * (q - 1) / 2 * M.mediumMinPair +
    (n - q) * q * M.mean * M.highMass +
    (n - q) * (n - q - 1) / 2 * M.mean +
    q * (q - 1) / 2 * M.highMinPair

theorem positionKernelProductValue_canonical_eq
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) :
    positionKernelProductValue
        (canonicalSingleKernel q p low medium high)
        (canonicalPairKernel q p low medium high) =
      canonicalFiniteProductFormula n q
        (canonicalEmpiricalMoments p low medium high)
        (canonicalEmpiricalHighMoment p high) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let M := canonicalEmpiricalMoments p low medium high
  let hM := canonicalEmpiricalHighMoment p high
  have hsingle :
      (∑ i : Fin n, empiricalSingleAverage
          (canonicalSingleKernel q p low medium high i)) =
        q * (1 + M.lowMoment) + q * M.mediumMoment +
          (n - q) * M.mean + q * hM := by
    simp_rw [canonicalSingleKernel_productAverage]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    simp_rw [← Finset.sum_mul]
    rw [sum_testedPosition hq, sum_one_sub_testedPosition hq]
  have hbaseline :
      (∑ z : OrderedDistinct (Fin n), testedPosition q z.val.1) =
        q * (n - 1) := by
    rw [show (∑ z : OrderedDistinct (Fin n), testedPosition q z.val.1) =
        ∑ z : OrderedDistinct (Fin n),
          testedPosition q z.val.1 * (1 : Fin n → ℝ) z.val.2 by simp,
      sum_orderedDistinct_mul, sum_testedPosition hq]
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [sum_testedPosition hq]
    simp [Fintype.card_fin]
    ring
  have hpair :
      (∑ z : OrderedDistinct (Fin n), empiricalProductPairAverage
          (canonicalPairKernel q p low medium high z)) =
        q * (n - 1) * (1 + M.lowMoment) -
        q * (q - 1) / 2 * M.lowMass * (1 + M.lowMoment) +
        q * (n - q) * M.mediumMoment +
        q * (q - 1) * M.mediumMoment * M.highMass +
        q * (q - 1) / 2 * M.mediumMinPair +
        (n - q) * q * M.mean * M.highMass +
        (n - q) * (n - q - 1) / 2 * M.mean +
        q * (q - 1) / 2 * M.highMinPair := by
    simp_rw [canonicalPairKernel_productAverage]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.sum_div]
    simp_rw [← Finset.sum_mul]
    have htt := sum_testedPosition_sq hq
    have htb := sum_testedPosition_one_sub hq
    have hbeforeT := sum_testedPosition_before hq
    have hbeforeB := sum_one_sub_testedPosition_before hq
    have hbeforeT' : (∑ z : OrderedDistinct (Fin n),
        testedPosition q z.val.1 * testedPosition q z.val.2 *
          beforePosition z.val.2 z.val.1) = q * (q - 1) / 2 := by
      linarith
    have hbeforeB' : (∑ z : OrderedDistinct (Fin n),
        (1 - testedPosition q z.val.1) *
          (1 - testedPosition q z.val.2) *
          beforePosition z.val.1 z.val.2) =
        (n - q) * (n - q - 1) / 2 := by
      linarith
    have hbt' : (∑ z : OrderedDistinct (Fin n),
        (1 - testedPosition q z.val.1) * testedPosition q z.val.2) =
        (n - q) * q := by
      calc
        (∑ z : OrderedDistinct (Fin n),
            (1 - testedPosition q z.val.1) * testedPosition q z.val.2) =
            (∑ i : Fin n, (1 - testedPosition q i)) *
              (∑ j : Fin n, testedPosition q j) -
              (∑ i : Fin n,
                (1 - testedPosition q i) * testedPosition q i) :=
          sum_orderedDistinct_mul
            (fun i : Fin n => 1 - testedPosition q i)
            (fun j : Fin n => testedPosition q j)
        _ = (n - q) * q := by
          rw [sum_one_sub_testedPosition hq, sum_testedPosition hq]
          have hdiag : (∑ i : Fin n,
              (1 - testedPosition q i) * testedPosition q i) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            unfold testedPosition
            split <;> norm_num
          rw [hdiag]
          ring
    rw [hbaseline, hbeforeT', htb, htt, hbt', hbeforeB']
    dsimp [M]
    ring
  unfold positionKernelProductValue positionKernelPairProductValue
  rw [hsingle, hpair]
  unfold canonicalFiniteProductFormula
  dsimp [M, hM]
  ring

/-- Exact diagonal correction between the finite empirical-product formula
and the fluid quadratic. -/
theorem canonicalFiniteProductFormula_eq_fluid_add_correction
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n)
    (M : FluidMoments) (highMoment : ℝ) :
    canonicalFiniteProductFormula n q M highMoment =
      (n : ℝ) ^ 2 * canonicalFluidCost M (q / n) +
      (q / 2 * M.lowMass * (1 + M.lowMoment) +
        q * M.mediumMoment * (1 - M.highMass) -
        q * M.mediumMinPair / 2 +
        (n - q) * M.mean / 2 +
        q * highMoment - q * M.highMinPair / 2) := by
  unfold canonicalFiniteProductFormula canonicalFluidCost testLowArea
    mediumArea blindArea highArea
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR]
  ring

private theorem mul_le_mul_box
    {a b A B : ℝ} (ha0 : 0 ≤ a) (haA : a ≤ A)
    (hb0 : 0 ≤ b) (hbB : b ≤ B) :
    a * b ≤ A * B := by
  exact mul_le_mul haA hbB hb0 (ha0.trans haA)

/-- The finite diagonal correction is uniformly `O_L(n)`.  The deliberately
round constant keeps the later composition readable. -/
theorem canonicalFiniteProductFormula_fluid_error
    {n q : ℕ} (hn : 0 < n) (hq : q ≤ n)
    (M : FluidMoments) (highMoment L : ℝ)
    (hM : M.InBox L) (hhigh0 : 0 ≤ highMoment)
    (hhighL : highMoment ≤ L) :
    |canonicalFiniteProductFormula n q M highMoment /
          (n : ℝ) ^ 2 - canonicalFluidCost M (q / n)| ≤
      (1 + 4 * L) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hqN : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hnq0 : (0 : ℝ) ≤ n - q := sub_nonneg.mpr hqN
  have hnqN : (n : ℝ) - q ≤ n := by linarith
  have hL0 : 0 ≤ L := hM.mean_nonneg.trans hM.mean_le
  let A := (q : ℝ) / 2 * M.lowMass * (1 + M.lowMoment)
  let B := (q : ℝ) * M.mediumMoment * (1 - M.highMass)
  let C := (q : ℝ) * M.mediumMinPair / 2
  let D := ((n : ℝ) - q) * M.mean / 2
  let E := (q : ℝ) * highMoment
  let F := (q : ℝ) * M.highMinPair / 2
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (div_nonneg hq0 (by norm_num)) hM.lowMass_nonneg)
      (by linarith [hM.lowMoment_nonneg])
  have hAle : A ≤ (n : ℝ) / 2 * (1 + L) := by
    dsimp [A]
    have hqa : (q : ℝ) / 2 * M.lowMass ≤ n / 2 := by
      have := mul_le_mul_box (div_nonneg hq0 (by norm_num))
        (by linarith : (q : ℝ) / 2 ≤ n / 2)
        hM.lowMass_nonneg hM.lowMass_le_one
      nlinarith
    exact mul_le_mul hqa (by linarith [hM.lowMoment_le])
      (by linarith [hM.lowMoment_nonneg]) (div_nonneg hn0.le (by norm_num))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hq0 hM.mediumMoment_nonneg)
      (sub_nonneg.mpr hM.highMass_le_one)
  have hBle : B ≤ (n : ℝ) * L := by
    dsimp [B]
    have hqm : (q : ℝ) * M.mediumMoment ≤ n * L :=
      mul_le_mul_box hq0 hqN hM.mediumMoment_nonneg hM.mediumMoment_le
    exact (mul_le_mul_of_nonneg_right hqm
      (sub_nonneg.mpr hM.highMass_le_one)).trans (by
        have hfactor : 1 - M.highMass ≤ 1 := by linarith [hM.highMass_nonneg]
        nlinarith [mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg hn0.le hL0)])
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg hq0 hM.mediumMinPair_nonneg) (by norm_num)
  have hCle : C ≤ (n : ℝ) * L / 2 := by
    dsimp [C]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_box hq0 hqN hM.mediumMinPair_nonneg
        hM.mediumMinPair_le) (by norm_num)
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (mul_nonneg hnq0 hM.mean_nonneg) (by norm_num)
  have hDle : D ≤ (n : ℝ) * L / 2 := by
    dsimp [D]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_box hnq0 hnqN hM.mean_nonneg hM.mean_le)
      (by norm_num)
  have hE0 : 0 ≤ E := by dsimp [E]; exact mul_nonneg hq0 hhigh0
  have hEle : E ≤ (n : ℝ) * L := by
    dsimp [E]
    exact mul_le_mul_box hq0 hqN hhigh0 hhighL
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact div_nonneg (mul_nonneg hq0 hM.highMinPair_nonneg) (by norm_num)
  have hFle : F ≤ (n : ℝ) * L / 2 := by
    dsimp [F]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_box hq0 hqN hM.highMinPair_nonneg hM.highMinPair_le)
      (by norm_num)
  have htriangle : |A + B - C + D + E - F| ≤ A + B + C + D + E + F := by
    calc
      |A + B - C + D + E - F| ≤
          |A + B - C + D + E| + |F| := abs_sub _ _
      _ ≤ |A + B - C + D| + |E| + |F| := by
        linarith [abs_add_le (A + B - C + D) E]
      _ ≤ |A + B - C| + |D| + |E| + |F| := by
        linarith [abs_add_le (A + B - C) D]
      _ ≤ |A + B| + |C| + |D| + |E| + |F| := by
        linarith [abs_sub (A + B) C]
      _ ≤ |A| + |B| + |C| + |D| + |E| + |F| := by
        linarith [abs_add_le A B]
      _ = A + B + C + D + E + F := by
        rw [abs_of_nonneg hA0, abs_of_nonneg hB0, abs_of_nonneg hC0,
          abs_of_nonneg hD0, abs_of_nonneg hE0, abs_of_nonneg hF0]
  rw [canonicalFiniteProductFormula_eq_fluid_add_correction hn hq]
  change |((n : ℝ) ^ 2 * canonicalFluidCost M (q / n) +
      (A + B - C + D + E - F)) / (n : ℝ) ^ 2 -
        canonicalFluidCost M (q / n)| ≤ _
  rw [show ((n : ℝ) ^ 2 * canonicalFluidCost M (q / n) +
        (A + B - C + D + E - F)) / (n : ℝ) ^ 2 -
      canonicalFluidCost M (q / n) =
        (A + B - C + D + E - F) / (n : ℝ) ^ 2 by
      field_simp [ne_of_gt hn0]
      ring,
    abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
  have hsum : A + B + C + D + E + F ≤ n * (1 + 4 * L) := by
    linarith
  calc
    |A + B - C + D + E - F| / (n : ℝ) ^ 2 ≤
        (n * (1 + 4 * L)) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (htriangle.trans hsum) (sq_nonneg _)
    _ = (1 + 4 * L) / n := by field_simp [ne_of_gt hn0]

private theorem empiricalSingleAverage_nonneg
    {α : Type*} [Fintype α] [Nonempty α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ empiricalSingleAverage f := by
  unfold empiricalSingleAverage
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)

private theorem empiricalSingleAverage_le
    {α : Type*} [Fintype α] [Nonempty α] {f : α → ℝ} {B : ℝ}
    (hf : ∀ x, f x ≤ B) : empiricalSingleAverage f ≤ B := by
  unfold empiricalSingleAverage
  have hN : (0 : ℝ) < Fintype.card α := by positivity
  calc
    (∑ x, f x) / Fintype.card α ≤
        (Fintype.card α * B) / Fintype.card α := by
      exact div_le_div_of_nonneg_right
        (by simpa using Finset.sum_le_sum fun x (_hx : x ∈ Finset.univ) => hf x)
        hN.le
    _ = B := by field_simp [ne_of_gt hN]

private theorem empiricalProductPairAverage_nonneg
    {α : Type*} [Fintype α] [Nonempty α] {f : α → α → ℝ}
    (hf : ∀ x y, 0 ≤ f x y) :
    0 ≤ empiricalProductPairAverage f := by
  unfold empiricalProductPairAverage
  exact div_nonneg
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hf x y)
    (sq_nonneg _)

private theorem empiricalProductPairAverage_le
    {α : Type*} [Fintype α] [Nonempty α] {f : α → α → ℝ} {B : ℝ}
    (hf : ∀ x y, f x y ≤ B) : empiricalProductPairAverage f ≤ B := by
  unfold empiricalProductPairAverage
  have hN : (0 : ℝ) < Fintype.card α := by positivity
  have hsum : (∑ x : α, ∑ y : α, f x y) ≤
      (Fintype.card α : ℝ) ^ 2 * B := by
    calc
      (∑ x : α, ∑ y : α, f x y) ≤
          ∑ _x : α, ∑ _y : α, B :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hf x y
      _ = (Fintype.card α : ℝ) ^ 2 * B := by
        simp
        ring
  calc
    (∑ x : α, ∑ y : α, f x y) / (Fintype.card α : ℝ) ^ 2 ≤
        ((Fintype.card α : ℝ) ^ 2 * B) /
          (Fintype.card α : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = B := by field_simp [ne_of_gt hN]

theorem canonicalEmpiricalMoments_inBox
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) {L : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpL : ∀ x, p x ≤ L) :
    (canonicalEmpiricalMoments p low medium high).InBox L := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hL0 : 0 ≤ L := (hp0 ⟨0, hn⟩).trans (hpL ⟨0, hn⟩)
  have hweight0 (f : ℝ → Bool) (x : Fin n) :
      0 ≤ boolWeight (f (p x)) := (boolWeight_mem_Icc _).1
  have hweight1 (f : ℝ → Bool) (x : Fin n) :
      boolWeight (f (p x)) ≤ 1 := (boolWeight_mem_Icc _).2
  have hmoment0 (f : ℝ → Bool) (x : Fin n) :
      0 ≤ p x * boolWeight (f (p x)) :=
    mul_nonneg (hp0 x) (hweight0 f x)
  have hmomentL (f : ℝ → Bool) (x : Fin n) :
      p x * boolWeight (f (p x)) ≤ L := by
    calc
      p x * boolWeight (f (p x)) ≤ L * 1 :=
        mul_le_mul (hpL x) (hweight1 f x) (hweight0 f x) hL0
      _ = L := mul_one _
  have hpair0 (f : ℝ → Bool) (x y : Fin n) :
      0 ≤ min (p x) (p y) * boolWeight (f (p x)) *
        boolWeight (f (p y)) :=
    mul_nonneg
      (mul_nonneg (le_min (hp0 x) (hp0 y)) (hweight0 f x))
      (hweight0 f y)
  have hpairL (f : ℝ → Bool) (x y : Fin n) :
      min (p x) (p y) * boolWeight (f (p x)) *
          boolWeight (f (p y)) ≤ L := by
    have hfirst : min (p x) (p y) * boolWeight (f (p x)) ≤ L := by
      calc
        min (p x) (p y) * boolWeight (f (p x)) ≤ L * 1 :=
          mul_le_mul ((min_le_left _ _).trans (hpL x))
            (hweight1 f x) (hweight0 f x) hL0
        _ = L := mul_one _
    calc
      min (p x) (p y) * boolWeight (f (p x)) *
          boolWeight (f (p y)) ≤ L * 1 :=
        mul_le_mul hfirst (hweight1 f y) (hweight0 f y)
          hL0
      _ = L := mul_one _
  constructor
  · exact empiricalSingleAverage_nonneg (hweight0 low)
  · exact empiricalSingleAverage_le (hweight1 low)
  · exact empiricalSingleAverage_nonneg (hmoment0 low)
  · exact empiricalSingleAverage_le (hmomentL low)
  · exact empiricalSingleAverage_nonneg (hmoment0 medium)
  · exact empiricalSingleAverage_le (hmomentL medium)
  · exact empiricalSingleAverage_nonneg (hweight0 high)
  · exact empiricalSingleAverage_le (hweight1 high)
  · exact empiricalSingleAverage_nonneg hp0
  · exact empiricalSingleAverage_le hpL
  · exact empiricalProductPairAverage_nonneg (hpair0 medium)
  · exact empiricalProductPairAverage_le (hpairL medium)
  · exact empiricalProductPairAverage_nonneg (hpair0 high)
  · exact empiricalProductPairAverage_le (hpairL high)

theorem canonicalEmpiricalHighMoment_mem
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (high : ℝ → Bool) {L : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpL : ∀ x, p x ≤ L) :
    canonicalEmpiricalHighMoment p high ∈ Set.Icc 0 L := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  constructor
  · exact empiricalSingleAverage_nonneg fun x =>
      mul_nonneg (hp0 x) (boolWeight_mem_Icc _).1
  · exact empiricalSingleAverage_le fun x => by
      have hL0 : 0 ≤ L := (hp0 x).trans (hpL x)
      calc
        p x * boolWeight (high (p x)) ≤ L * 1 :=
          mul_le_mul (hpL x) (boolWeight_mem_Icc _).2
            (boolWeight_mem_Icc _).1 hL0
        _ = L := mul_one _

/-- Complete finite-kernel statement: the expected canonical interaction
word has the fluid value up to an explicit uniform `O_L(1/n)` error. -/
theorem canonicalKernelCost_fluid_normalized
    {n q : ℕ} (hn : 1 < n) (hq : q ≤ n) (p : Fin n → ℝ)
    (low medium high : ℝ → Bool) {L : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hpL : ∀ x, p x ≤ L) :
    |uniformAverage (canonicalKernelCost q p low medium high) /
          (n : ℝ) ^ 2 -
        canonicalFluidCost (canonicalEmpiricalMoments p low medium high)
          (q / n)| ≤
      (5 + 18 * L) / n := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let M := canonicalEmpiricalMoments p low medium high
  let h := canonicalEmpiricalHighMoment p high
  have hkernel := canonicalKernelCost_product_normalized hn q p
    low medium high hp0 hpL
  have hproduct := canonicalFiniteProductFormula_fluid_error
    hnPos hq M h L (canonicalEmpiricalMoments_inBox hnPos p low medium high hp0 hpL)
    (canonicalEmpiricalHighMoment_mem hnPos p high hp0 hpL).1
    (canonicalEmpiricalHighMoment_mem hnPos p high hp0 hpL).2
  rw [positionKernelProductValue_canonical_eq hnPos hq] at hkernel
  have htriangle := abs_sub_le
    (uniformAverage (canonicalKernelCost q p low medium high) / (n : ℝ) ^ 2)
    (canonicalFiniteProductFormula n q M h / (n : ℝ) ^ 2)
    (canonicalFluidCost M (q / n))
  dsimp [M, h] at hkernel hproduct htriangle ⊢
  calc
    |uniformAverage (canonicalKernelCost q p low medium high) / (n : ℝ) ^ 2 -
        canonicalFluidCost (canonicalEmpiricalMoments p low medium high) (q / n)| ≤
      |uniformAverage (canonicalKernelCost q p low medium high) / (n : ℝ) ^ 2 -
          canonicalFiniteProductFormula n q
            (canonicalEmpiricalMoments p low medium high)
            (canonicalEmpiricalHighMoment p high) / (n : ℝ) ^ 2| +
      |canonicalFiniteProductFormula n q
            (canonicalEmpiricalMoments p low medium high)
            (canonicalEmpiricalHighMoment p high) / (n : ℝ) ^ 2 -
          canonicalFluidCost (canonicalEmpiricalMoments p low medium high)
            (q / n)| := htriangle
    _ ≤ 2 * (2 + 7 * L) / n + (1 + 4 * L) / n :=
      add_le_add hkernel hproduct
    _ = (5 + 18 * L) / n := by field_simp [ne_of_gt hnR]; ring

end

end RandomizedOptional
end SchedulingPaper
