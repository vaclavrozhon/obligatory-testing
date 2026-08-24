import SchedulingPaper.BlindOptimizationAlgebra
import Mathlib.Tactic

/-!
# Finite-distribution reduction for blind optimization

This file checks the reduction from an arbitrary empirical processing-time
distribution to the one-parameter binary envelope used by the randomized
blind-optimization curve.  Unlike the paper's layer-cake proof, the finite
argument is pointwise: for `p,q ∈ [0,u]`, the minimum of the two effective
lengths is bounded below by a constant times `p*q`.  Averaging then factors
the product exactly.
-/

namespace SchedulingPaper
namespace BlindOptimization

noncomputable section

def effectiveLength (u p : ℝ) : ℝ := 1 + min (u - 1) p

def empiricalMean {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  (∑ i, p i) / Fintype.card α

def empiricalOfflinePair {α : Type*} [Fintype α]
    (u : ℝ) (p : α → ℝ) : ℝ :=
  (∑ i, ∑ j, min (effectiveLength u (p i)) (effectiveLength u (p j))) /
    (Fintype.card α : ℝ) ^ 2

def randomizedDistributionRatio {α : Type*} [Fintype α]
    (u : ℝ) (p : α → ℝ) : ℝ :=
  min u (1 + empiricalMean p) / empiricalOfflinePair u p

/-- Ordered-pair leading coefficient of `OptimizeAll` under its worst label
order. -/
def deterministicOnlinePair {α : Type*} [Fintype α]
    (p : α → ℝ) : ℝ :=
  (∑ i, ∑ j, max (1 + p i) (1 + p j)) /
    (Fintype.card α : ℝ) ^ 2

def deterministicDistributionRatio {α : Type*} [Fintype α]
    (u : ℝ) (p : α → ℝ) : ℝ :=
  deterministicOnlinePair p / empiricalOfflinePair u p

theorem min_le_product_div {u p q : ℝ}
    (hu : 0 < u) (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u) :
    p * q / u ≤ min p q := by
  by_cases hpq : p ≤ q
  · rw [min_eq_left hpq]
    rw [div_le_iff₀ hu]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hqu)]
  · have hqp : q ≤ p := le_of_not_ge hpq
    rw [min_eq_right hqp]
    rw [div_le_iff₀ hu]
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hpu)]

theorem truncated_ge_scaled {u p : ℝ} (hu : 1 < u)
    (hp0 : 0 ≤ p) (hpu : p ≤ u) :
    (u - 1) / u * p ≤ min (u - 1) p := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  by_cases hp : p ≤ u - 1
  · rw [min_eq_right hp]
    have hfrac : (u - 1) / u ≤ 1 := by
      rw [div_le_one hu0]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hfrac) hp0]
  · rw [min_eq_left (le_of_not_ge hp)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hu0]
    nlinarith [mul_nonneg (by linarith : 0 ≤ u - 1)
      (sub_nonneg.mpr hpu)]

/-- Pointwise certificate behind the survival-function reduction in the
paper. -/
theorem min_effectiveLength_ge_product {u p q : ℝ} (hu : 1 < u)
    (hp0 : 0 ≤ p) (hpu : p ≤ u) (hq0 : 0 ≤ q) (hqu : q ≤ u) :
    1 + (u - 1) / u ^ 2 * (p * q) ≤
      min (effectiveLength u p) (effectiveLength u q) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hp := truncated_ge_scaled hu hp0 hpu
  have hq := truncated_ge_scaled hu hq0 hqu
  have hminpq := min_le_product_div hu0 hp0 hpu hq0 hqu
  have hscale : 0 ≤ (u - 1) / u := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hminpq hscale
  have hminscaled :
      (u - 1) / u * min p q ≤
        min (min (u - 1) p) (min (u - 1) q) := by
    rw [le_min_iff]
    constructor
    · exact (mul_le_mul_of_nonneg_left (min_le_left p q) hscale).trans hp
    · exact (mul_le_mul_of_nonneg_left (min_le_right p q) hscale).trans hq
  have hproduct :
      (u - 1) / u ^ 2 * (p * q) ≤
        min (min (u - 1) p) (min (u - 1) q) := by
    calc
      (u - 1) / u ^ 2 * (p * q) =
          (u - 1) / u * (p * q / u) := by field_simp
      _ ≤ (u - 1) / u * min p q := hscaled
      _ ≤ min (min (u - 1) p) (min (u - 1) q) := hminscaled
  simpa [effectiveLength, min_add_add_left] using add_le_add_left hproduct 1

theorem max_one_add_le_mean_product {u p q : ℝ}
    (hu : 0 < u) (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u) :
    max (1 + p) (1 + q) ≤ 1 + p + q - p * q / u := by
  have hmin := min_le_product_div hu hp0 hpu hq0 hqu
  have hmaxmin := max_add_min p q
  rw [max_add_add_left]
  linarith

/-- The worst-order OptimizeAll pair coefficient is controlled by the
empirical mean.  This finite pointwise proof replaces the layer-cake and
Cauchy--Schwarz paragraph in the paper. -/
theorem deterministicOnlinePair_le_mean
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 0 < u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    deterministicOnlinePair p ≤
      1 + 2 * empiricalMean p - empiricalMean p ^ 2 / u := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by dsimp [N]; positivity
  have hpoint : ∀ i j,
      max (1 + p i) (1 + p j) ≤
        1 + p i + p j - p i * p j / u := by
    intro i j
    exact max_one_add_le_mean_product hu
      (hp i).1 (hp i).2 (hp j).1 (hp j).2
  have hsum :
      (∑ i, ∑ j, max (1 + p i) (1 + p j)) ≤
        ∑ i, ∑ j, (1 + p i + p j - p i * p j / u) :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpoint i j
  have hproduct :
      (∑ i, ∑ j, p i * p j * u⁻¹) = (∑ i, p i) ^ 2 * u⁻¹ := by
    calc
      (∑ i, ∑ j, p i * p j * u⁻¹) =
          (∑ i, ∑ j, p i * p j) * u⁻¹ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_mul]
      _ = ((∑ i, p i) * ∑ j, p j) * u⁻¹ := by
            rw [Fintype.sum_mul_sum]
      _ = (∑ i, p i) ^ 2 * u⁻¹ := by ring
  have hfactor :
      (∑ i, ∑ j, (1 + p i + p j - p i * p j / u)) =
        N ^ 2 + 2 * N * (∑ i, p i) - (∑ i, p i) ^ 2 / u := by
    dsimp [N]
    simp_rw [div_eq_mul_inv]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hproduct]
    rw [← Finset.mul_sum]
    ring
  unfold deterministicOnlinePair empiricalMean
  change (∑ i, ∑ j, max (1 + p i) (1 + p j)) / N ^ 2 ≤
    1 + 2 * ((∑ i, p i) / N) - ((∑ i, p i) / N) ^ 2 / u
  rw [div_le_iff₀ (sq_pos_of_pos hN)]
  calc
    _ ≤ ∑ i, ∑ j, (1 + p i + p j - p i * p j / u) := hsum
    _ = _ := by
      rw [hfactor]
      field_simp [hN.ne', hu.ne']

/-- The empirical offline pair coefficient is controlled by the empirical
mean alone.  This is the finite-distribution version of equations
`(bo-survival-mean)`--`(bo-survival-square)` in the paper. -/
theorem empiricalOfflinePair_ge_mean_square
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 1 < u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    1 + (u - 1) * (empiricalMean p / u) ^ 2 ≤
      empiricalOfflinePair u p := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hpoint : ∀ i j,
      1 + (u - 1) / u ^ 2 * (p i * p j) ≤
        min (effectiveLength u (p i)) (effectiveLength u (p j)) := by
    intro i j
    exact min_effectiveLength_ge_product hu
      (hp i).1 (hp i).2 (hp j).1 (hp j).2
  have hsum :
      ∑ i, ∑ j, (1 + (u - 1) / u ^ 2 * (p i * p j)) ≤
        ∑ i, ∑ j,
          min (effectiveLength u (p i)) (effectiveLength u (p j)) := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hproductSum :
      (∑ i, ∑ j, (u - 1) / u ^ 2 * (p i * p j)) =
        (u - 1) / u ^ 2 * (∑ i, p i) ^ 2 := by
    have hreassoc : ∀ i j,
        (u - 1) / u ^ 2 * (p i * p j) =
          ((u - 1) / u ^ 2 * p i) * p j := by
      intros
      ring
    simp_rw [hreassoc]
    rw [← Fintype.sum_mul_sum, ← Finset.mul_sum]
    ring
  have hfactor :
      (∑ i, ∑ j, (1 + (u - 1) / u ^ 2 * (p i * p j))) =
        N ^ 2 + (u - 1) / u ^ 2 * (∑ i, p i) ^ 2 := by
    dsimp [N]
    simp [Finset.sum_add_distrib]
    rw [hproductSum]
    ring
  unfold empiricalOfflinePair empiricalMean
  change 1 + (u - 1) * (((∑ i, p i) / N) / u) ^ 2 ≤
    (∑ i, ∑ j,
      min (effectiveLength u (p i)) (effectiveLength u (p j))) / N ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hN)).2
  calc
    (1 + (u - 1) * ((∑ i, p i) / N / u) ^ 2) * N ^ 2 =
        ∑ i, ∑ j, (1 + (u - 1) / u ^ 2 * (p i * p j)) := by
          rw [hfactor]
          field_simp [hN.ne']
    _ ≤ _ := hsum

theorem empiricalMean_mem_Icc
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (_hu0 : 0 ≤ u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    empiricalMean p ∈ Set.Icc (0 : ℝ) u := by
  have hcard : 0 < (Fintype.card α : ℝ) := by positivity
  constructor
  · unfold empiricalMean
    exact div_nonneg (Finset.sum_nonneg fun i _ => (hp i).1) hcard.le
  · unfold empiricalMean
    rw [div_le_iff₀ hcard]
    calc
      ∑ i, p i ≤ ∑ _i : α, u :=
        Finset.sum_le_sum fun i _ => (hp i).2
      _ = u * Fintype.card α := by simp [mul_comm]

/-- Every finite empirical distribution lies below the checked binary
envelope with parameter `b = mean/u`. -/
theorem randomizedDistributionRatio_le_binaryEnvelope
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 1 < u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    randomizedDistributionRatio u p ≤
      randomizedBinaryEnvelope u (empiricalMean p / u) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hmean := empiricalMean_mem_Icc p hu0.le hp
  have hdenLower := empiricalOfflinePair_ge_mean_square p hu hp
  have hbase : 0 < 1 + (u - 1) * (empiricalMean p / u) ^ 2 := by
    have hnonneg : 0 ≤ (u - 1) * (empiricalMean p / u) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hoff : 0 < empiricalOfflinePair u p := hbase.trans_le hdenLower
  have hnum : 0 ≤ min u (1 + empiricalMean p) := by
    exact le_min hu0.le (by linarith [hmean.1])
  unfold randomizedDistributionRatio randomizedBinaryEnvelope
  have hdenRatio :
      min u (1 + empiricalMean p) / empiricalOfflinePair u p ≤
        min u (1 + empiricalMean p) /
          (1 + (u - 1) * (empiricalMean p / u) ^ 2) :=
    div_le_div_of_nonneg_left hnum hbase hdenLower
  convert hdenRatio using 1 <;> (field_simp)

/-- Combining the finite-distribution reduction with the scalar maximum
gives the randomized blind-optimization curve upper bound. -/
theorem randomizedDistributionRatio_le_curve
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 1 < u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    randomizedDistributionRatio u p ≤ randomizedCurve u := by
  apply (randomizedDistributionRatio_le_binaryEnvelope p hu hp).trans
  apply randomizedBinaryEnvelope_le_curve hu
  · exact div_nonneg
      (empiricalMean_mem_Icc p (by linarith) hp).1 (by linarith)
  · rw [div_le_one (by linarith : 0 < u)]
    exact (empiricalMean_mem_Icc p (by linarith) hp).2

/-- Every empirical distribution lies below the exact deterministic
`OptimizeAll` envelope with `b = mean/u`. -/
theorem deterministicDistributionRatio_le_binaryEnvelope
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 2 ≤ u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    deterministicDistributionRatio u p ≤
      deterministicOptimizeAllEnvelope u (empiricalMean p / u) := by
  have hu0 : 0 < u := by linarith
  have honline := deterministicOnlinePair_le_mean p hu0 hp
  have hoffline := empiricalOfflinePair_ge_mean_square p (by linarith) hp
  have hbase : 0 < 1 + (u - 1) * (empiricalMean p / u) ^ 2 := by
    have hnonneg : 0 ≤ (u - 1) * (empiricalMean p / u) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hofflinePos : 0 < empiricalOfflinePair u p := hbase.trans_le hoffline
  have hnum : 0 ≤ deterministicOnlinePair p := by
    unfold deterministicOnlinePair
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
        exact (show 0 ≤ 1 + p i by linarith [(hp i).1]).trans
          (le_max_left _ _)
    · positivity
  unfold deterministicDistributionRatio deterministicOptimizeAllEnvelope
  have hfirst :
      deterministicOnlinePair p / empiricalOfflinePair u p ≤
        (1 + 2 * empiricalMean p - empiricalMean p ^ 2 / u) /
          (1 + (u - 1) * (empiricalMean p / u) ^ 2) := by
    exact (div_le_div_of_nonneg_left hnum hbase hoffline).trans
      (div_le_div_of_nonneg_right honline hbase.le)
  convert hfirst using 1 <;> field_simp [hu0.ne'] <;> ring

theorem deterministicDistributionRatio_le_curve
    {α : Type*} [Fintype α] [Nonempty α]
    {u : ℝ} (p : α → ℝ) (hu : 2 ≤ u)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) u) :
    deterministicDistributionRatio u p ≤
      deterministicOptimizeAllRatio u := by
  apply (deterministicDistributionRatio_le_binaryEnvelope p hu hp).trans
  exact deterministicOptimizeAllEnvelope_le_ratio hu

end

end BlindOptimization
end SchedulingPaper
