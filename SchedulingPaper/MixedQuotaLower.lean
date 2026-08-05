import SchedulingPaper.HarmonicOperational
import SchedulingPaper.MixedCurve
import Mathlib.Tactic

/-!
# The mixed-quota lower construction

This module supplies the lower-bound construction on the mixed finite-cap
branch.  The first section identifies the exact cap mass and harmonic scale
carried by the implicit mixed-curve parameters.
-/

namespace SchedulingPaper

noncomputable section

open Set

namespace LowerBound

/-- The ratio parameter belonging to a mixed cap. -/
def mixedLowerC (u : MixedUpperDomain) : ℝ :=
  mixedRatioAtUpper u

/-- The capped mass belonging to a mixed cap. -/
def mixedLowerM (u : MixedUpperDomain) : ℝ :=
  mixedMass (mixedRatioAtUpper u)

/-- The logarithm of the harmonic scale in the mixed construction. -/
def mixedLowerLogT (u : MixedUpperDomain) : ℝ :=
  1 / mixedLowerC u - mixedLowerM u - 1

/-- The harmonic scale `t`; its positive-type ratio is `t - 1`. -/
def mixedLowerT (u : MixedUpperDomain) : ℝ :=
  Real.exp (mixedLowerLogT u)

theorem mixedLowerC_mem (u : MixedUpperDomain) :
    mixedLowerC u ∈ Icc rhoStar (1 / goldenRatio) :=
  (mixedRatioAtUpper u).property

theorem mixedLowerC_pos (u : MixedUpperDomain) :
    0 < mixedLowerC u :=
  rhoStar_pos.trans_le (mixedLowerC_mem u).1

theorem mixedLowerM_mem (u : MixedUpperDomain) :
    mixedLowerM u ∈ Icc 0 (1 / goldenRatio) :=
  (mixedMass (mixedRatioAtUpper u)).property

theorem mixedLowerM_lt_one (u : MixedUpperDomain) :
    mixedLowerM u < 1 :=
  (mixedLowerM_mem u).2.trans_lt inv_goldenRatio_lt_one

theorem mixedLower_upper_equation (u : MixedUpperDomain) :
    1 + 2 / mixedLowerC u - mixedLowerM u = (u : ℝ) := by
  simpa [mixedLowerC, mixedLowerM, mixedUpperCurve,
    mixedUpperParameter] using mixedRatioAtUpper_equation u

theorem mixedLower_mass_equation (u : MixedUpperDomain) :
    mixedMassSide (mixedLowerM u) =
      mixedRatioSide (mixedLowerC u) := by
  simpa [mixedLowerC, mixedLowerM] using
    mixedMass_equation (mixedRatioAtUpper u)

theorem mixedLowerLogT_nonneg (u : MixedUpperDomain) :
    0 ≤ mixedLowerLogT u := by
  have hcUpper := (mixedLowerC_mem u).2
  have hcPos := mixedLowerC_pos u
  have hinv :
      1 / (1 / goldenRatio) ≤ 1 / mixedLowerC u :=
    one_div_le_one_div_of_le hcPos hcUpper
  rw [one_div_inv_goldenRatio] at hinv
  have hmUpper := (mixedLowerM_mem u).2
  rw [inv_goldenRatio_eq_sub_one] at hmUpper
  unfold mixedLowerLogT
  linarith

theorem mixedLowerT_pos (u : MixedUpperDomain) :
    0 < mixedLowerT u :=
  Real.exp_pos _

theorem mixedLowerT_one_le (u : MixedUpperDomain) :
    1 ≤ mixedLowerT u := by
  simpa [mixedLowerT] using
    Real.exp_monotone (mixedLowerLogT_nonneg u)

theorem mixedLower_log_t (u : MixedUpperDomain) :
    Real.log (mixedLowerT u) = mixedLowerLogT u := by
  simp [mixedLowerT]

/-- The implicit mixed equation is equivalent to the second stationary
equation for the harmonic scale. -/
theorem mixedLowerT_sq (u : MixedUpperDomain) :
    mixedLowerT u ^ 2 =
      (1 - mixedLowerM u) / (1 + mixedLowerM u) *
        (1 + 2 / mixedLowerC u) := by
  let c := mixedLowerC u
  let m := mixedLowerM u
  have hc : 0 < c := mixedLowerC_pos u
  have hm0 : 0 ≤ m := (mixedLowerM_mem u).1
  have hm1 : m < 1 := mixedLowerM_lt_one u
  have hplus : 0 < 1 + m := by linarith
  have hminus : 0 < 1 - m := by linarith
  have harg : 0 < 1 + 2 / c := by positivity
  have hmInterval : m ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith, hm1.le⟩
  have heq := mixedLower_mass_equation u
  rw [mixedMassSide_eq_half_log hmInterval] at heq
  unfold mixedRatioSide at heq
  change
    1 / 2 * Real.log ((1 + m) / (1 - m)) - m =
      1 - 1 / c + 1 / 2 * Real.log (1 + 2 / c) at heq
  rw [Real.log_div hplus.ne' hminus.ne'] at heq
  have hlog :
      Real.log ((1 - m) / (1 + m) * (1 + 2 / c)) =
        2 * (1 / c - m - 1) := by
    rw [Real.log_mul (div_pos hminus hplus).ne' harg.ne',
      Real.log_div hminus.ne' hplus.ne']
    linarith
  change
    Real.exp (mixedLowerLogT u) ^ 2 =
      (1 - m) / (1 + m) * (1 + 2 / c)
  have hlogDef :
      mixedLowerLogT u = 1 / c - m - 1 := by
    rfl
  rw [hlogDef]
  calc
    Real.exp (1 / c - m - 1) ^ 2 =
        Real.exp (2 * (1 / c - m - 1)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp
        (Real.log ((1 - m) / (1 + m) * (1 + 2 / c))) := by
      rw [hlog]
    _ = (1 - m) / (1 + m) * (1 + 2 / c) :=
      Real.exp_log (mul_pos (div_pos hminus hplus) harg)

/-- Extra online mass supplied by the capped block and the scaled harmonic
core, after subtracting the common offline term. -/
def mixedLowerAdvantage (m t : ℝ) : ℝ :=
  m + (1 - m) ^ 2 / 2 * (1 - t⁻¹ ^ 2)

/-- The limiting offline coefficient of the mixed capped/harmonic block. -/
def mixedLowerOffline (u m t : ℝ) : ℝ :=
  (1 - m) ^ 2 / 4 *
      (1 + t⁻¹ ^ 2 + 2 * Real.log t) +
    m * (1 - m) * (1 + Real.log t) +
    u / 2 * m ^ 2

/-- The two-parameter lower ratio displayed in the paper. -/
def mixedLowerBenchmark (u m t : ℝ) : ℝ :=
  1 + mixedLowerAdvantage m t / mixedLowerOffline u m t

private theorem mixedLower_inv_t_sq
    {c m t : ℝ} (hc : c ≠ 0) (ht : t ≠ 0)
    (hmPlus : 1 + m ≠ 0) (hmMinus : 1 - m ≠ 0)
    (htsq :
      t ^ 2 = (1 - m) / (1 + m) * (1 + 2 / c)) :
    t⁻¹ ^ 2 =
      c * (1 + m) / ((1 - m) * (c + 2)) := by
  have hcTwo : c + 2 ≠ 0 := by
    intro h
    have : c = -2 := by linarith
    subst c
    norm_num at htsq
    exact ht htsq
  field_simp [ht, hc, hmPlus, hmMinus, hcTwo] at htsq ⊢
  nlinarith

/-- Pure algebra behind the stationary mixed benchmark. -/
theorem mixedLowerAdvantage_eq_c_mul_offline
    {u c m t : ℝ}
    (hc : c ≠ 0) (ht : t ≠ 0)
    (hmPlus : 1 + m ≠ 0) (hmMinus : 1 - m ≠ 0)
    (hu : u = 1 + 2 / c - m)
    (hlog : Real.log t = 1 / c - m - 1)
    (htsq :
      t ^ 2 = (1 - m) / (1 + m) * (1 + 2 / c)) :
    mixedLowerAdvantage m t =
      c * mixedLowerOffline u m t := by
  have hinv :=
    mixedLower_inv_t_sq hc ht hmPlus hmMinus htsq
  unfold mixedLowerAdvantage mixedLowerOffline
  rw [hu, hlog, hinv]
  have hcTwo : c + 2 ≠ 0 := by
    intro h
    have : c = -2 := by linarith
    subst c
    norm_num at htsq
    exact ht htsq
  field_simp [hc, hmPlus, hmMinus, hcTwo]
  ring

theorem mixedLowerOffline_pos (u : MixedUpperDomain) :
    0 <
      mixedLowerOffline (u : ℝ) (mixedLowerM u) (mixedLowerT u) := by
  let m := mixedLowerM u
  let t := mixedLowerT u
  have huPos : 0 < (u : ℝ) := by
    linarith [goldenRatio_pos, u.property.1]
  have hm0 : 0 ≤ m := (mixedLowerM_mem u).1
  have hm1 : m < 1 := mixedLowerM_lt_one u
  have ht1 : 1 ≤ t := mixedLowerT_one_le u
  have ht0 : 0 < t := mixedLowerT_pos u
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hinv0 : 0 ≤ t⁻¹ ^ 2 := sq_nonneg _
  have hfirst :
      0 < (1 - m) ^ 2 / 4 *
        (1 + t⁻¹ ^ 2 + 2 * Real.log t) := by
    have hleft : 0 < (1 - m) ^ 2 / 4 := by positivity
    have hright : 0 < 1 + t⁻¹ ^ 2 + 2 * Real.log t := by
      positivity
    exact mul_pos hleft hright
  have hsecond :
      0 ≤ m * (1 - m) * (1 + Real.log t) := by positivity
  have hthird : 0 ≤ (u : ℝ) / 2 * m ^ 2 := by positivity
  unfold mixedLowerOffline
  linarith

/-- At the implicit mixed parameters the explicit benchmark is exactly the
mixed competitive curve. -/
theorem mixedLowerBenchmark_eq_curve (u : MixedUpperDomain) :
    mixedLowerBenchmark (u : ℝ) (mixedLowerM u) (mixedLowerT u) =
      mixedFiniteCurve u := by
  have hc := (mixedLowerC_pos u).ne'
  have ht := (mixedLowerT_pos u).ne'
  have hmPlus : 1 + mixedLowerM u ≠ 0 := by
    linarith [(mixedLowerM_mem u).1]
  have hmMinus : 1 - mixedLowerM u ≠ 0 := by
    linarith [mixedLowerM_lt_one u]
  have hidentity :=
    mixedLowerAdvantage_eq_c_mul_offline
      hc ht hmPlus hmMinus
      (mixedLower_upper_equation u).symm
      (by
        rw [mixedLower_log_t]
        rfl)
      (mixedLowerT_sq u)
  have hoffline :=
    mixedLowerOffline_pos u
  unfold mixedLowerBenchmark mixedFiniteCurve
  rw [hidentity]
  unfold mixedLowerC
  field_simp [hoffline.ne']

/-! ## Finite mixed benchmarks and the harmonic processing-mass limit -/

/-- The processing-mass kernel of the scaled harmonic block. -/
def mixedProcessingIntegrand (α x : ℝ) : ℝ :=
  (α - x) / (1 + x)

private def mixedProcessingPrimitive (α x : ℝ) : ℝ :=
  (1 + α) * Real.log (1 + x) - x

private theorem mixedProcessingPrimitive_hasDerivAt
    {α x : ℝ} (hx : 1 + x ≠ 0) :
    HasDerivAt (mixedProcessingPrimitive α)
      (mixedProcessingIntegrand α x) x := by
  have hone :
      HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa only [Pi.add_apply, zero_add, id_eq] using
      (hasDerivAt_const x 1).add (hasDerivAt_id x)
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y))
        (1 / (1 + x)) x := by
    simpa [one_div] using
      (Real.hasDerivAt_log hx).comp x hone
  have h :=
    ((hasDerivAt_const x (1 + α)).mul hlog).sub
      (hasDerivAt_id x)
  convert h using 1
  unfold mixedProcessingIntegrand
  field_simp [hx]
  ring

theorem mixedProcessingIntegral_eq
    {α : ℝ} (hα : 0 ≤ α) :
    (∫ x in 0..α, mixedProcessingIntegrand α x) =
      (1 + α) * Real.log (1 + α) - α := by
  have hint :
      IntervalIntegrable (mixedProcessingIntegrand α)
        MeasureTheory.volume 0 α := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hα] at hx
    exact
      ((continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.add continuousAt_id)
        (by
          simp only [Pi.add_apply, id_eq]
          linarith [hx.1])).continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) α,
        HasDerivAt (mixedProcessingPrimitive α)
          (mixedProcessingIntegrand α x) x := by
    intro x hx
    rw [Set.uIcc_of_le hα] at hx
    exact mixedProcessingPrimitive_hasDerivAt
      (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [mixedProcessingPrimitive]

theorem mixedProcessingIntegrand_antitoneOn
    {α : ℝ} :
    AntitoneOn (mixedProcessingIntegrand α) (Icc 0 α) := by
  intro x hx y hy hxy
  have hnum : 0 ≤ α - y := by linarith [hy.2]
  have hdx : 0 < 1 + x := by linarith [hx.1]
  have hdy : 0 < 1 + y := by linarith [hy.1]
  unfold mixedProcessingIntegrand
  calc
    (α - y) / (1 + y) ≤ (α - y) / (1 + x) :=
      div_le_div_of_nonneg_left hnum hdx (by linarith)
    _ ≤ (α - x) / (1 + x) :=
      div_le_div_of_nonneg_right (by linarith) hdx.le

/-- Right Riemann sum for the harmonic processing mass. -/
def mixedProcessingRiemannSum (α : ℝ) (n : ℕ) : ℝ :=
  α / (n + 1 : ℝ) *
    ∑ k ∈ Finset.range (n + 1),
      mixedProcessingIntegrand α
        (α * (k + 1 : ℝ) / (n + 1 : ℝ))

private theorem mixed_sum_range_shift_sub
    (q : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, q k) -
        ∑ k ∈ Finset.range n, q (k + 1) =
      q 0 - q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [ih]

theorem mixedProcessingRiemannSum_error_le
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    |mixedProcessingRiemannSum α n -
        ∫ x in 0..α, mixedProcessingIntegrand α x| ≤
      α ^ 2 / (n + 1 : ℝ) := by
  let N : ℕ := n + 1
  let c : ℝ := α / N
  let f : ℝ → ℝ := mixedProcessingIntegrand α
  let g : ℝ → ℝ := fun x => c * f (c * x)
  have hN : 0 < N := by simp [N]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := div_pos hα hNc
  have hcN : c * (N : ℝ) = α := by
    dsimp [c]
    field_simp
  have hf : AntitoneOn f (Icc 0 α) := by
    simpa [f] using
      (mixedProcessingIntegrand_antitoneOn (α := α))
  have hg : AntitoneOn g (Icc 0 (N : ℝ)) := by
    intro x hx y hy hxy
    have hcx : c * x ∈ Icc (0 : ℝ) α := by
      constructor
      · exact mul_nonneg hc.le hx.1
      · rw [← hcN]
        exact mul_le_mul_of_nonneg_left hx.2 hc.le
    have hcy : c * y ∈ Icc (0 : ℝ) α := by
      constructor
      · exact mul_nonneg hc.le hy.1
      · rw [← hcN]
        exact mul_le_mul_of_nonneg_left hy.2 hc.le
    exact mul_le_mul_of_nonneg_left
      (hf hcx hcy (mul_le_mul_of_nonneg_left hxy hc.le)) hc.le
  have hg' : AntitoneOn g (Icc 0 (0 + (N : ℝ))) := by
    simpa only [zero_add] using hg
  have hrightRaw :
      (∑ k ∈ Finset.range N, g (k + 1 : ℕ)) ≤
        ∫ x in 0..(N : ℝ), g x := by
    simpa using (hg'.sum_le_integral (x₀ := 0) (a := N))
  have hleftRaw :
      (∫ x in 0..(N : ℝ), g x) ≤
        ∑ k ∈ Finset.range N, g k := by
    simpa using (hg'.integral_le_sum (x₀ := 0) (a := N))
  have hchange :
      (∫ x in 0..(N : ℝ), g x) =
        ∫ y in 0..α, mixedProcessingIntegrand α y := by
    calc
      (∫ x in 0..(N : ℝ), g x) =
          c * ∫ x in 0..(N : ℝ), f (c * x) := by
            simp only [g, intervalIntegral.integral_const_mul]
      _ = ∫ y in c * 0..c * (N : ℝ), f y := by
            exact intervalIntegral.mul_integral_comp_mul_left c
      _ = ∫ y in 0..α, mixedProcessingIntegrand α y := by
            simp only [mul_zero, hcN, f]
  have hsumRight :
      (∑ k ∈ Finset.range N, g (k + 1 : ℕ)) =
        mixedProcessingRiemannSum α n := by
    unfold mixedProcessingRiemannSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr
    · simp [N]
    · intro k hk
      dsimp [g, f, c, N]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 2 <;> ring
  have hright :
      mixedProcessingRiemannSum α n ≤
        ∫ y in 0..α, mixedProcessingIntegrand α y := by
    rw [← hsumRight, ← hchange]
    exact hrightRaw
  have hleft :
      (∫ y in 0..α, mixedProcessingIntegrand α y) ≤
        ∑ k ∈ Finset.range N, g k := by
    rw [← hchange]
    exact hleftRaw
  have htel :
      (∑ k ∈ Finset.range N, g k) -
          ∑ k ∈ Finset.range N, g (k + 1 : ℕ) =
        α ^ 2 / (N : ℝ) := by
    rw [mixed_sum_range_shift_sub (fun k : ℕ => g k) N]
    dsimp [g, f]
    rw [hcN]
    unfold mixedProcessingIntegrand
    dsimp [c]
    field_simp
    ring
  have hgap :
      (∫ y in 0..α, mixedProcessingIntegrand α y) -
          mixedProcessingRiemannSum α n ≤
        α ^ 2 / (n + 1 : ℝ) := by
    rw [← hsumRight]
    rw [show (n + 1 : ℝ) = (N : ℝ) by simp [N]]
    linarith [hleft, htel]
  rw [abs_of_nonpos (sub_nonpos.mpr hright)]
  linarith

theorem mixedProcessingRiemannSum_tendsto
    {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (mixedProcessingRiemannSum α) Filter.atTop
      (nhds (∫ x in 0..α, mixedProcessingIntegrand α x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero
    (g := fun n : ℕ => α ^ 2 / (n + 1 : ℝ))
    (fun _ => dist_nonneg) (fun n => ?_) ?_
  · simpa [Real.dist_eq] using
      mixedProcessingRiemannSum_error_le hα n
  · have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat (α ^ 2)).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun n : ℕ => α ^ 2 / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem harmonicFutureLevels_sum_div_eq
    {K Z : ℕ} (hK : 0 < K) (hZ : 0 < Z) :
    (harmonicFutureLevels (Z : ℝ) 0 K).sum / (Z : ℝ) =
      (K : ℝ) / (Z : ℝ) +
        mixedProcessingRiemannSum ((K : ℝ) / (Z : ℝ))
          (K - 1) := by
  rw [harmonicFutureLevels_sum_zeroSlack]
  unfold mixedProcessingRiemannSum
  have hKsub : K - 1 + 1 = K := by omega
  rw [hKsub]
  rw [add_div]
  congr 1
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrK : r < K := Finset.mem_range.mp hr
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hZreal : (Z : ℝ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hsubCast :
      ((K - r - 1 : ℕ) : ℝ) =
        (K : ℝ) - (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hKminusCast :
      ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  push_cast
  rw [hKminusCast]
  have hKden : (K : ℝ) - 1 + 1 = (K : ℝ) := by ring
  rw [hKden]
  have hcoef :
      ((K : ℝ) / (Z : ℝ)) / (K : ℝ) =
        1 / (Z : ℝ) := by
    field_simp [hKreal, hZreal]
  have harg :
      ((K : ℝ) / (Z : ℝ)) * ((r : ℝ) + 1) /
          (K : ℝ) =
        ((r : ℝ) + 1) / (Z : ℝ) := by
    field_simp [hKreal, hZreal]
  rw [hcoef, harg]
  have hZr : (Z : ℝ) + (r : ℝ) + 1 ≠ 0 := by positivity
  have hinter :
      mixedProcessingIntegrand ((K : ℝ) / (Z : ℝ))
          (((r : ℝ) + 1) / (Z : ℝ)) =
        ((K : ℝ) - (r : ℝ) - 1) /
          ((Z : ℝ) + (r : ℝ) + 1) := by
    unfold mixedProcessingIntegrand
    field_simp [hZreal, hZr]
    ring
  rw [hinter, hsubCast]
  ring

theorem harmonicFutureLevels_sum_scale_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun q : ℕ =>
        (harmonicFutureLevels
          ((B * (q + 1) : ℕ) : ℝ) 0
          (A * (q + 1))).sum /
            ((B * (q + 1) : ℕ) : ℝ))
      Filter.atTop
      (nhds
        ((1 + (A : ℝ) / (B : ℝ)) *
          Real.log (1 + (A : ℝ) / (B : ℝ)))) := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hindex :
      Filter.Tendsto
        (fun q : ℕ => A * (q + 1) - 1)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with q hq
    have hscale : q + 1 ≤ A * (q + 1) :=
      Nat.le_mul_of_pos_left (q + 1) hA
    omega
  have hriemann :=
    (mixedProcessingRiemannSum_tendsto hα).comp hindex
  have hconst :
      Filter.Tendsto (fun _q : ℕ => α)
        Filter.atTop (nhds α) :=
    tendsto_const_nhds
  have hadd := hconst.add hriemann
  convert hadd using 1
  · funext q
    have hK : 0 < A * (q + 1) :=
      Nat.mul_pos hA (by omega)
    have hZ : 0 < B * (q + 1) :=
      Nat.mul_pos hB (by omega)
    rw [harmonicFutureLevels_sum_div_eq hK hZ]
    have hratio :
        ((A * (q + 1) : ℕ) : ℝ) /
            ((B * (q + 1) : ℕ) : ℝ) =
          α := by
      dsimp [α]
      have hs : (q + 1 : ℝ) ≠ 0 := by positivity
      have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      push_cast
      field_simp [hs, hBreal]
    simp only [Function.comp_apply]
    rw [hratio]
  · rw [mixedProcessingIntegral_eq hα.le]
    apply congrArg nhds
    dsimp [α]
    ring

/-- Exact offline benchmark for `C` capped jobs followed by a finite
harmonic block with `K` positive and `Z` zero jobs. -/
def mixedFiniteOffline (u : ℝ) (C K Z : ℕ) : ℝ :=
  harmonicFiniteOffline K Z 0 +
    C * ((K + Z : ℕ) +
      (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
    u * triangular C

/-- Exact lower benchmark obtained by adding the harmonic advantage and one
unit for each capped-job/whole-instance pair. -/
def mixedFiniteOnline (u : ℝ) (C K Z : ℕ) : ℝ :=
  harmonicFiniteOnline K Z 0 +
    C * ((K + Z : ℕ) +
      (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
    u * triangular C +
    C * (C + K + Z : ℕ)

theorem mixedFiniteOnline_eq_offline_add_advantage
    (u : ℝ) (C K Z : ℕ) :
    mixedFiniteOnline u C K Z =
      mixedFiniteOffline u C K Z +
        harmonicFiniteAdvantage K Z +
        C * (C + K + Z : ℕ) := by
  rw [mixedFiniteOnline, mixedFiniteOffline,
    harmonicFiniteOnline_eq]
  ring

/-- Offline coefficient when cap mass and harmonic masses are normalized by
the zero-block mass. -/
def mixedScaledOffline (u μ α : ℝ) : ℝ :=
  harmonicLimitDenominator α +
    μ * (1 + α) * (1 + Real.log (1 + α)) +
    u / 2 * μ ^ 2

/-- Corresponding excess over the common offline term. -/
def mixedScaledAdvantage (μ α : ℝ) : ℝ :=
  α + α ^ 2 / 2 + μ * (μ + 1 + α)

def mixedScaledBenchmark (u μ α : ℝ) : ℝ :=
  1 + mixedScaledAdvantage μ α / mixedScaledOffline u μ α

theorem mixedScaledOffline_pos
    {u μ α : ℝ} (hu : 0 < u) (hμ : 0 ≤ μ) (hα : 0 < α) :
    0 < mixedScaledOffline u μ α := by
  have hD := harmonicLimitDenominator_pos hα
  have hlog : 0 ≤ Real.log (1 + α) :=
    Real.log_nonneg (by linarith)
  unfold mixedScaledOffline
  have hcross :
      0 ≤ μ * (1 + α) * (1 + Real.log (1 + α)) := by
    positivity
  have hcap : 0 ≤ u / 2 * μ ^ 2 := by positivity
  linarith

theorem harmonicLimitDenominator_scale_identity
    {t : ℝ} (ht : t ≠ 0) :
    harmonicLimitDenominator (t - 1) =
      t ^ 2 / 4 * (1 + t⁻¹ ^ 2 + 2 * Real.log t) := by
  unfold harmonicLimitDenominator
  field_simp [ht]
  ring

theorem mixedScaledOffline_eq_rescaled
    {u m t : ℝ} (hm : 1 - m ≠ 0) (ht : t ≠ 0) :
    mixedScaledOffline u (m * t / (1 - m)) (t - 1) =
      (t / (1 - m)) ^ 2 * mixedLowerOffline u m t := by
  unfold mixedScaledOffline mixedLowerOffline
  rw [harmonicLimitDenominator_scale_identity ht]
  field_simp [hm, ht]
  ring

theorem mixedScaledAdvantage_eq_rescaled
    {m t : ℝ} (hm : 1 - m ≠ 0) (ht : t ≠ 0) :
    mixedScaledAdvantage (m * t / (1 - m)) (t - 1) =
      (t / (1 - m)) ^ 2 * mixedLowerAdvantage m t := by
  unfold mixedScaledAdvantage mixedLowerAdvantage
  field_simp [hm, ht]
  ring

theorem mixedScaledBenchmark_eq_mixedLower
    {u m t : ℝ} (hm : 1 - m ≠ 0) (ht : t ≠ 0)
    (hoffline : mixedLowerOffline u m t ≠ 0) :
    mixedScaledBenchmark u (m * t / (1 - m)) (t - 1) =
      mixedLowerBenchmark u m t := by
  unfold mixedScaledBenchmark mixedLowerBenchmark
  rw [mixedScaledOffline_eq_rescaled hm ht,
    mixedScaledAdvantage_eq_rescaled hm ht]
  have hscale : (t / (1 - m)) ^ 2 ≠ 0 := by positivity
  field_simp [hscale, hoffline]

/-- The normalized cap-triangle term at a fixed integral scale. -/
theorem mixed_cap_triangular_scale_tendsto
    {M B : ℕ} (hM : 0 < M) (hB : 0 < B) :
    Filter.Tendsto
      (fun q : ℕ =>
        triangular (M * (q + 1)) /
          ((B * (q + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds (((M : ℝ) / (B : ℝ)) ^ 2 / 2)) := by
  let base : ℝ := (M : ℝ) ^ 2 / (2 * (B : ℝ) ^ 2)
  let correction : ℝ := (M : ℝ) / (2 * (B : ℝ) ^ 2)
  have hzero :
      Filter.Tendsto
        (fun q : ℕ => correction / (q + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat correction).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun q : ℕ => correction / ((q + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hbase :
      Filter.Tendsto (fun _q : ℕ => base)
        Filter.atTop (nhds base) :=
    tendsto_const_nhds
  have hadd := hbase.add hzero
  convert hadd using 1
  · funext q
    unfold triangular
    dsimp [base, correction]
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  · dsimp [base]
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp [hBreal]
    ring

theorem mixedFiniteOffline_scale_tendsto
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun q : ℕ =>
        mixedFiniteOffline u
            (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) /
          ((B * (q + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (mixedScaledOffline u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hoffline := harmonicFiniteOffline_scale_tendsto hA hB
  have hprocessing :=
    harmonicFutureLevels_sum_scale_tendsto hA hB
  have htailConst :
      Filter.Tendsto
        (fun _q : ℕ => 1 + α)
        Filter.atTop (nhds (1 + α)) :=
    tendsto_const_nhds
  have htail :=
    htailConst.add hprocessing
  have hcapConst :
      Filter.Tendsto
        (fun _q : ℕ => μ)
        Filter.atTop (nhds μ) :=
    tendsto_const_nhds
  have hcross := hcapConst.mul htail
  have htriangle :=
    (mixed_cap_triangular_scale_tendsto hM hB).const_mul u
  have hsum := (hoffline.add hcross).add htriangle
  convert hsum using 1
  · funext q
    unfold mixedFiniteOffline
    rw [add_div, add_div]
    congr 1
    · congr 1
      have hscale : (q + 1 : ℝ) ≠ 0 := by positivity
      have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
      have hcap :
          ((M * (q + 1) : ℕ) : ℝ) /
              ((B * (q + 1) : ℕ) : ℝ) =
            μ := by
        dsimp [μ]
        push_cast
        field_simp [hscale, hBreal]
      have htailSize :
          (((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) +
              (harmonicFutureLevels
                ((B * (q + 1) : ℕ) : ℝ) 0
                (A * (q + 1))).sum) /
                ((B * (q + 1) : ℕ) : ℝ) =
            (1 + α) +
              (harmonicFutureLevels
                ((B * (q + 1) : ℕ) : ℝ) 0
                (A * (q + 1))).sum /
                ((B * (q + 1) : ℕ) : ℝ) := by
        dsimp [α]
        have hden :
            ((B * (q + 1) : ℕ) : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp [hscale, hBreal, hden]
        ring
      rw [← hcap, ← htailSize]
      have hden :
          ((B * (q + 1) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hden]
    · ring
  · unfold mixedScaledOffline
    dsimp [μ, α]
    congr 1
    ring

theorem mixedFiniteAdvantage_scale_tendsto
    {M A B : ℕ} (hM : 0 < M) (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun q : ℕ =>
        (harmonicFiniteAdvantage
            (A * (q + 1)) (B * (q + 1)) +
          (M * (q + 1) : ℕ) *
            (M * (q + 1) + A * (q + 1) +
              B * (q + 1) : ℕ)) /
          ((B * (q + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (mixedScaledAdvantage
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hharmonic :=
    harmonicFiniteAdvantage_scale_tendsto hA hB
  have hcap :
      Filter.Tendsto
        (fun _q : ℕ => μ * (μ + 1 + α))
        Filter.atTop (nhds (μ * (μ + 1 + α))) :=
    tendsto_const_nhds
  have hadd := hharmonic.add hcap
  convert hadd using 1
  · funext q
    rw [add_div]
    congr 1
    dsimp [μ, α]
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
    ring

theorem eventually_mixedFinite_ratio
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u) :
    ∀ᶠ q : ℕ in Filter.atTop,
      target *
          mixedFiniteOffline u
            (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) ≤
        mixedFiniteOnline u
          (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let D : ℝ := mixedScaledOffline u μ α
  let G : ℝ := mixedScaledAdvantage μ α
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hD : 0 < D :=
    mixedScaledOffline_pos hu hμ.le hα
  have hoffline :=
    mixedFiniteOffline_scale_tendsto
      (u := u) hM hA hB
  have hadvantage :=
    mixedFiniteAdvantage_scale_tendsto hM hA hB
  have honline :
      Filter.Tendsto
        (fun q : ℕ =>
          mixedFiniteOnline u
              (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) /
            ((B * (q + 1) : ℕ) : ℝ) ^ 2)
        Filter.atTop (nhds (D + G)) := by
    have hadd := hoffline.add hadvantage
    convert hadd using 1
    · funext q
      rw [mixedFiniteOnline_eq_offline_add_advantage,
        add_div, add_div]
      ring
  have htargetScaled :
      Filter.Tendsto
        (fun q : ℕ =>
          target *
            (mixedFiniteOffline u
                (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) /
              ((B * (q + 1) : ℕ) : ℝ) ^ 2))
        Filter.atTop (nhds (target * D)) := by
    exact hoffline.const_mul target
  have hdiff := honline.sub htargetScaled
  have hgap : target - 1 < G / D := by
    dsimp [mixedScaledBenchmark, μ, α, D, G] at htarget ⊢
    linarith
  have hlimitPos : 0 < (D + G) - target * D := by
    have := (lt_div_iff₀ hD).mp hgap
    nlinarith
  have hevent :
      ∀ᶠ q : ℕ in Filter.atTop,
        0 <
          mixedFiniteOnline u
              (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) /
              ((B * (q + 1) : ℕ) : ℝ) ^ 2 -
            target *
              (mixedFiniteOffline u
                  (M * (q + 1)) (A * (q + 1))
                    (B * (q + 1)) /
                ((B * (q + 1) : ℕ) : ℝ) ^ 2) := by
    exact hdiff (Ioi_mem_nhds hlimitPos)
  filter_upwards [hevent] with q hq
  have hden :
      0 < ((B * (q + 1) : ℕ) : ℝ) ^ 2 := by
    positivity
  have hquot :
      0 <
        (mixedFiniteOnline u
            (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) -
          target *
            mixedFiniteOffline u
              (M * (q + 1)) (A * (q + 1)) (B * (q + 1))) /
          ((B * (q + 1) : ℕ) : ℝ) ^ 2 := by
    convert hq using 1 <;> ring
  have hnum :
      0 <
        mixedFiniteOnline u
            (M * (q + 1)) (A * (q + 1)) (B * (q + 1)) -
          target *
            mixedFiniteOffline u
              (M * (q + 1)) (A * (q + 1))
                (B * (q + 1)) := by
    exact (div_pos_iff.mp hquot).resolve_right
      (fun hneg => (not_lt_of_ge hden.le hneg.2))
      |>.1
  exact (sub_pos.mp hnum).le

/-! ## Exact finite feasibility -/

/-- Every level of a zero-slack harmonic block is bounded by the coarse
endpoint `1 + K / Z`.  This estimate is deliberately elementary: after one
more unit for testing it turns the rational raw margin into a pointwise cap
bound. -/
theorem harmonicLevel_le_one_add_ratio
    {K Z L : ℕ} (hZ : 0 < Z) (hLK : L ≤ K) :
    harmonicLevel (Z : ℝ) 0 L ≤
      1 + (K : ℝ) / (Z : ℝ) := by
  have hZreal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hterm :
      ∀ r ∈ Finset.range L,
        1 / ((Z : ℝ) + (r + 1 : ℕ)) ≤ 1 / (Z : ℝ) := by
    intro r hr
    apply one_div_le_one_div_of_le hZreal
    exact le_add_of_nonneg_right (by positivity)
  have hsum :
      (∑ r ∈ Finset.range L,
          1 / ((Z : ℝ) + (r + 1 : ℕ))) ≤
        (K : ℝ) / (Z : ℝ) := by
    calc
      (∑ r ∈ Finset.range L,
          1 / ((Z : ℝ) + (r + 1 : ℕ))) ≤
          ∑ _r ∈ Finset.range L, 1 / (Z : ℝ) :=
        Finset.sum_le_sum hterm
      _ = (L : ℝ) / (Z : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ (K : ℝ) / (Z : ℝ) :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast hLK) hZreal.le
  simpa [harmonicLevel] using add_le_add_left hsum (1 : ℝ)

theorem mixedFinite_rawSafe
    {u : ℝ} {A B q L : ℕ}
    (hB : 0 < B) (hLK : L ≤ A * (q + 1))
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    1 +
        harmonicLevel ((B * (q + 1) : ℕ) : ℝ) 0 L ≤ u := by
  have hZ : 0 < B * (q + 1) :=
    Nat.mul_pos hB (by omega)
  have hlevel :=
    harmonicLevel_le_one_add_ratio hZ hLK
  have hratio :
      ((A * (q + 1) : ℕ) : ℝ) /
          ((B * (q + 1) : ℕ) : ℝ) =
        (A : ℝ) / (B : ℝ) := by
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  rw [hratio] at hlevel
  linarith

/-- The strict limiting deferral margin survives at every sufficiently
large common integral scale. -/
theorem eventually_mixedFinite_deferral
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∀ᶠ q : ℕ in Filter.atTop,
      0 ≤
        ((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) *
            (u - 1) -
          (harmonicFutureLevels
            ((B * (q + 1) : ℕ) : ℝ) 0
            (A * (q + 1))).sum -
          (M * (q + 1) : ℕ) := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  have hprocessing :=
    harmonicFutureLevels_sum_scale_tendsto hA hB
  have hleft :
      Filter.Tendsto
        (fun _q : ℕ => (1 + α) * (u - 1))
        Filter.atTop (nhds ((1 + α) * (u - 1))) :=
    tendsto_const_nhds
  have hcap :
      Filter.Tendsto (fun _q : ℕ => μ)
        Filter.atTop (nhds μ) :=
    tendsto_const_nhds
  have htotal := (hleft.sub hprocessing).sub hcap
  have hlimit :
      0 <
        (1 + α) * (u - 1) -
          (1 + α) * Real.log (1 + α) - μ := by
    dsimp [α, μ]
    linarith
  have hevent :
      ∀ᶠ q : ℕ in Filter.atTop,
        0 <
          (1 + α) * (u - 1) -
            (harmonicFutureLevels
              ((B * (q + 1) : ℕ) : ℝ) 0
              (A * (q + 1))).sum /
                ((B * (q + 1) : ℕ) : ℝ) -
            μ :=
    htotal (Ioi_mem_nhds hlimit)
  filter_upwards [hevent] with q hq
  let Z : ℕ := B * (q + 1)
  have hZ : 0 < Z := Nat.mul_pos hB (by omega)
  have hZreal : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hratioA :
      ((A * (q + 1) : ℕ) : ℝ) / (Z : ℝ) = α := by
    dsimp [Z, α]
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  have hratioM :
      ((M * (q + 1) : ℕ) : ℝ) / (Z : ℝ) = μ := by
    dsimp [Z, μ]
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  have hquot :
      0 <
        (((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) *
              (u - 1) -
            (harmonicFutureLevels
              ((B * (q + 1) : ℕ) : ℝ) 0
              (A * (q + 1))).sum -
            (M * (q + 1) : ℕ)) /
          (Z : ℝ) := by
    have hself : ((B * (q + 1) : ℕ) : ℝ) / (Z : ℝ) = 1 := by
      dsimp [Z]
      exact div_self (ne_of_gt hZreal)
    have hsize :
        ((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) / (Z : ℝ) =
      1 + α := by
      rw [Nat.cast_add, add_div, hratioA, hself]
      ring
    have heq :
        (((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) *
              (u - 1) -
            (harmonicFutureLevels
              ((B * (q + 1) : ℕ) : ℝ) 0
              (A * (q + 1))).sum -
            (M * (q + 1) : ℕ)) /
            (Z : ℝ) =
          (1 + α) * (u - 1) -
            (harmonicFutureLevels
              ((B * (q + 1) : ℕ) : ℝ) 0
              (A * (q + 1))).sum /
                ((B * (q + 1) : ℕ) : ℝ) -
            μ := by
      rw [sub_div, sub_div, hratioM]
      have hmul :
          ((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) *
                (u - 1) /
              (Z : ℝ) =
            (((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) /
                (Z : ℝ)) * (u - 1) := by ring
      rw [hmul, hsize]
    rw [heq]
    simpa [Z] using hq
  have hnum :
      0 <
        ((A * (q + 1) + B * (q + 1) : ℕ) : ℝ) *
            (u - 1) -
          (harmonicFutureLevels
            ((B * (q + 1) : ℕ) : ℝ) 0
            (A * (q + 1))).sum -
          (M * (q + 1) : ℕ) := by
    rcases (div_pos_iff.mp hquot) with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hZreal.le hneg.2).elim
  exact hnum.le

/-! ## Strict feasibility and rational parameters -/

theorem zStar_lt_five : zStar < 5 := by
  have hexpFive : (5 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hlogFive : Real.log 5 < 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hexpFive
  have hrootFive : 0 < zRootFunction 5 := by
    unfold zRootFunction
    linarith
  have hrootStar : zRootFunction zStar = 0 := by
    unfold zRootFunction
    linarith [zStar_equation]
  by_contra hnot
  have hle : (5 : ℝ) ≤ zStar := le_of_not_gt hnot
  rcases hle.eq_or_lt with heq | hlt
  · have hrootFiveZero := hrootStar
    rw [← heq] at hrootFiveZero
    linarith
  · have hmono :=
      zRootFunction_strictMonoOn
        (by norm_num : (5 : ℝ) ∈ Ioi 1)
        zStar_gt_one hlt
    rw [hrootStar] at hmono
    linarith

theorem mixedLowerLogT_lt_one (u : MixedUpperDomain) :
    mixedLowerLogT u < 1 := by
  have hcLower := (mixedLowerC_mem u).1
  have hcPos := mixedLowerC_pos u
  have hinv :
      1 / mixedLowerC u ≤ 1 / rhoStar :=
    one_div_le_one_div_of_le rhoStar_pos hcLower
  rw [one_div_rhoStar] at hinv
  have hm0 := (mixedLowerM_mem u).1
  have hzlog : Real.log zStar < 2 := by
    rw [← zStar_equation]
    linarith [zStar_lt_five]
  unfold mixedLowerLogT
  linarith [zStar_equation]

theorem mixedLower_raw_simulation_strict
    (u : MixedUpperDomain) :
    2 + Real.log (mixedLowerT u) < (u : ℝ) := by
  rw [mixedLower_log_t]
  have huLower := u.property.1
  linarith [mixedLowerLogT_lt_one u, goldenRatio_gt_one]

/-- A slightly stronger, purely algebraic raw-simulation margin.  It is
convenient for finite harmonic blocks because their largest level is at
most `1 + K / Z`. -/
theorem mixedLowerT_lt_goldenRatio_add_one
    (u : MixedUpperDomain) :
    mixedLowerT u < goldenRatio + 1 := by
  let c := mixedLowerC u
  let m := mixedLowerM u
  let t := mixedLowerT u
  have hc : 0 < c := mixedLowerC_pos u
  have hcLower : rhoStar ≤ c := (mixedLowerC_mem u).1
  have hm0 : 0 ≤ m := (mixedLowerM_mem u).1
  have hm1 : m < 1 := mixedLowerM_lt_one u
  have hden : 0 < 1 + m := by linarith
  have hfactor0 : 0 ≤ (1 - m) / (1 + m) := by positivity
  have hfactor1 : (1 - m) / (1 + m) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  have hinv :
      1 / c ≤ 1 / rhoStar :=
    one_div_le_one_div_of_le rhoStar_pos hcLower
  have hsecond : 1 + 2 / c ≤ zStar := by
    rw [one_div_rhoStar] at hinv
    calc
      1 + 2 / c = 1 + 2 * (1 / c) := by ring
      _ ≤ 1 + 2 * ((zStar - 1) / 2) := by gcongr
      _ = zStar := by ring
  have hsecond0 : 0 ≤ 1 + 2 / c := by positivity
  have htSq : t ^ 2 ≤ zStar := by
    rw [show t ^ 2 =
      (1 - m) / (1 + m) * (1 + 2 / c) by
        simpa [t, c, m] using mixedLowerT_sq u]
    calc
      (1 - m) / (1 + m) * (1 + 2 / c) ≤
          1 * (1 + 2 / c) :=
        mul_le_mul_of_nonneg_right hfactor1 hsecond0
      _ = 1 + 2 / c := by ring
      _ ≤ zStar := hsecond
  have ht0 : 0 < t := mixedLowerT_pos u
  have hgold : 0 < goldenRatio + 1 := by
    linarith [goldenRatio_pos]
  have hgoldSq : 5 < (goldenRatio + 1) ^ 2 := by
    nlinarith [goldenRatio_sq, goldenRatio_gt_one]
  have htSqStrict : t ^ 2 < (goldenRatio + 1) ^ 2 :=
    htSq.trans_lt (zStar_lt_five.trans hgoldSq)
  nlinarith

theorem mixedLower_raw_ratio_strict
    (u : MixedUpperDomain) :
    1 + mixedLowerT u < (u : ℝ) := by
  have huLower := u.property.1
  linarith [mixedLowerT_lt_goldenRatio_add_one u]

theorem mixedLower_deferral_strict
    (u : MixedUpperDomain) :
    0 <
      mixedLowerT u *
          ((u : ℝ) - 1 - Real.log (mixedLowerT u)) -
        mixedLowerM u * mixedLowerT u /
          (1 - mixedLowerM u) := by
  let m := mixedLowerM u
  let t := mixedLowerT u
  have hmUpper := (mixedLowerM_mem u).2
  have hm1 : m < 1 := mixedLowerM_lt_one u
  have hremain : 0 < 1 - m := by linarith
  have hlog : Real.log t < 1 := by
    simpa [t, mixedLower_log_t] using mixedLowerLogT_lt_one u
  have huLower := u.property.1
  have hspan :
      goldenRatio <
        (u : ℝ) - 1 - Real.log t := by
    linarith
  have hmRewritten : m ≤ goldenRatio - 1 := by
    rw [← inv_goldenRatio_eq_sub_one]
    exact hmUpper
  have hbase : 2 - goldenRatio ≤ 1 - m := by
    linarith
  have hmul :=
    mul_le_mul_of_nonneg_right hbase goldenRatio_pos.le
  have hgold :
      (2 - goldenRatio) * goldenRatio =
        goldenRatio - 1 := by
    nlinarith [goldenRatio_sq]
  rw [hgold] at hmul
  have hcapLower :
      m ≤ (1 - m) * goldenRatio := by
    exact hmRewritten.trans hmul
  have hstrictMul :=
    mul_lt_mul_of_pos_left hspan hremain
  have hbracket :
      0 <
        (1 - m) *
            ((u : ℝ) - 1 - Real.log t) - m := by
    linarith
  have ht : 0 < t := mixedLowerT_pos u
  have hidentity :
      t * ((u : ℝ) - 1 - Real.log t) -
          m * t / (1 - m) =
        t / (1 - m) *
          ((1 - m) *
            ((u : ℝ) - 1 - Real.log t) - m) := by
    field_simp [hremain.ne']
  rw [hidentity]
  exact mul_pos (div_pos ht hremain) hbracket

theorem mixedLowerM_pos_of_interior
    (u : MixedUpperDomain)
    (huUpper : (u : ℝ) < zStar) :
    0 < mixedLowerM u := by
  have huSubtype :
      u < mixedUpperUpperEndpoint := by
    exact huUpper
  have hc :
      mixedRatioLower < mixedRatioAtUpper u := by
    rw [← mixedRatioAtUpper_upperEndpoint]
    exact mixedRatioAtUpper_strictAnti huSubtype
  have hm :=
    mixedMass_strictMono hc
  have hmReal :
      (mixedMass mixedRatioLower : ℝ) <
        (mixedMass (mixedRatioAtUpper u) : ℝ) :=
    hm
  rw [mixedMass_lower] at hmReal
  simpa [mixedLowerM] using hmReal

theorem mixedLowerLogT_pos_of_interior
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ)) :
    0 < mixedLowerLogT u := by
  have huSubtype :
      mixedUpperLowerEndpoint < u := by
    exact huLower
  have hc :
      mixedRatioAtUpper u < mixedRatioUpper := by
    rw [← mixedRatioAtUpper_lowerEndpoint]
    exact mixedRatioAtUpper_strictAnti huSubtype
  have hcReal :
      mixedLowerC u < 1 / goldenRatio := by
    exact hc
  have hinv :
      goldenRatio < 1 / mixedLowerC u := by
    rw [← one_div_inv_goldenRatio]
    exact one_div_lt_one_div_of_lt
      (mixedLowerC_pos u) hcReal
  have hmUpper := (mixedLowerM_mem u).2
  rw [inv_goldenRatio_eq_sub_one] at hmUpper
  unfold mixedLowerLogT
  linarith

theorem mixedLowerT_gt_one_of_interior
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ)) :
    1 < mixedLowerT u := by
  have hlog := mixedLowerLogT_pos_of_interior u huLower
  have :=
    Real.exp_lt_exp.mpr hlog
  simpa [mixedLowerT] using this

theorem mixedScaledBenchmark_continuousAt
    {u μ α : ℝ} (hα : -1 < α)
    (hD : mixedScaledOffline u μ α ≠ 0) :
    ContinuousAt
      (fun p : ℝ × ℝ =>
        mixedScaledBenchmark u p.1 p.2) (μ, α) := by
  have hlogArg : 1 + α ≠ 0 := by linarith
  have hlog :
      ContinuousAt
        (fun p : ℝ × ℝ => Real.log (1 + p.2)) (μ, α) := by
    have hargCont :
        ContinuousAt (fun p : ℝ × ℝ => 1 + p.2) (μ, α) :=
      continuousAt_const.add continuousAt_snd
    exact
      ContinuousAt.comp'
        (f := fun p : ℝ × ℝ => 1 + p.2)
        (x := (μ, α)) (g := Real.log)
        (Real.continuousAt_log (x := 1 + α) hlogArg)
        hargCont
  have hden :
      ContinuousAt
        (fun p : ℝ × ℝ =>
          mixedScaledOffline u p.1 p.2) (μ, α) := by
    unfold mixedScaledOffline harmonicLimitDenominator
    fun_prop
  have hnum :
      ContinuousAt
        (fun p : ℝ × ℝ =>
          mixedScaledAdvantage p.1 p.2) (μ, α) := by
    unfold mixedScaledAdvantage
    fun_prop
  unfold mixedScaledBenchmark
  exact continuousAt_const.add (hnum.div hden hD)

/-- Every interior mixed cap admits positive rational cap and harmonic
ratios that retain the strict raw-simulation and cap-deferral inequalities
and attain any prescribed epsilon below the mixed curve. -/
theorem exists_integral_mixed_parameters
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ))
    (huUpper : (u : ℝ) < zStar)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M A B : ℕ,
      0 < M ∧ 0 < A ∧ 0 < B ∧
      mixedFiniteCurve u - ε <
        mixedScaledBenchmark (u : ℝ)
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)) ∧
      2 + (A : ℝ) / (B : ℝ) < (u : ℝ) ∧
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            ((u : ℝ) - 1 -
              Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ) := by
  let m := mixedLowerM u
  let t := mixedLowerT u
  let μ := m * t / (1 - m)
  let α := t - 1
  let point : ℝ × ℝ := (μ, α)
  let benchmark : ℝ × ℝ → ℝ :=
    fun p => mixedScaledBenchmark (u : ℝ) p.1 p.2
  let rawGap : ℝ × ℝ → ℝ :=
    fun p => (u : ℝ) - (2 + p.2)
  let deferralGap : ℝ × ℝ → ℝ :=
    fun p =>
      (1 + p.2) *
          ((u : ℝ) - 1 - Real.log (1 + p.2)) - p.1
  have hm0 : 0 < m :=
    mixedLowerM_pos_of_interior u huUpper
  have hm1 : m < 1 := mixedLowerM_lt_one u
  have ht1 : 1 < t :=
    mixedLowerT_gt_one_of_interior u huLower
  have ht0 : 0 < t := ht1.trans' zero_lt_one
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hα : 0 < α := by
    dsimp [α]
    linarith
  have hu0 : 0 < (u : ℝ) := by
    linarith [goldenRatio_pos, u.property.1]
  have hD :
      0 < mixedScaledOffline (u : ℝ) μ α :=
    mixedScaledOffline_pos hu0 hμ.le hα
  have hbenchmark :
      benchmark point = mixedFiniteCurve u := by
    calc
      benchmark point =
          mixedLowerBenchmark (u : ℝ) m t := by
        dsimp [benchmark, point, μ, α]
        exact mixedScaledBenchmark_eq_mixedLower
          (by linarith : 1 - m ≠ 0) ht0.ne'
          (mixedLowerOffline_pos u).ne'
      _ = mixedFiniteCurve u :=
        mixedLowerBenchmark_eq_curve u
  have hbenchmarkValue :
      mixedFiniteCurve u - ε < benchmark point := by
    rw [hbenchmark]
    linarith
  have hbenchmarkCont :
      ContinuousAt benchmark point := by
    dsimp [benchmark, point]
    exact mixedScaledBenchmark_continuousAt
      (by dsimp [α]; linarith)
      hD.ne'
  have hbenchmarkNhds :
      benchmark ⁻¹' Ioi (mixedFiniteCurve u - ε) ∈ nhds point :=
    hbenchmarkCont
      (isOpen_Ioi.mem_nhds hbenchmarkValue)
  have hrawValue : 0 < rawGap point := by
    dsimp [rawGap, point, α]
    have ht : 1 + t < (u : ℝ) := by
      simpa [t] using mixedLower_raw_ratio_strict u
    linarith
  have hrawCont : ContinuousAt rawGap point := by
    dsimp [rawGap, point]
    fun_prop
  have hrawNhds :
      rawGap ⁻¹' Ioi 0 ∈ nhds point :=
    hrawCont (isOpen_Ioi.mem_nhds hrawValue)
  have hdeferralValue : 0 < deferralGap point := by
    dsimp [deferralGap, point, α, μ]
    simpa [show 1 + (t - 1) = t by ring] using
      mixedLower_deferral_strict u
  have hdeferralCont : ContinuousAt deferralGap point := by
    have hlog :
        ContinuousAt
          (fun p : ℝ × ℝ => Real.log (1 + p.2))
          (μ, α) := by
      have hargCont :
          ContinuousAt (fun p : ℝ × ℝ => 1 + p.2)
            (μ, α) :=
        continuousAt_const.add continuousAt_snd
      exact
        ContinuousAt.comp'
          (f := fun p : ℝ × ℝ => 1 + p.2)
          (x := (μ, α)) (g := Real.log)
          (Real.continuousAt_log (x := 1 + α)
            (by linarith : 1 + α ≠ 0))
          hargCont
    dsimp [deferralGap, point]
    exact
      ((continuousAt_const.add continuousAt_snd).mul
        (((continuousAt_const.sub continuousAt_const).sub hlog))).sub
          continuousAt_fst
  have hdeferralNhds :
      deferralGap ⁻¹' Ioi 0 ∈ nhds point :=
    hdeferralCont
      (isOpen_Ioi.mem_nhds hdeferralValue)
  have hpositiveNhds :
      Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) ∈ nhds point :=
    (isOpen_Ioi.prod isOpen_Ioi).mem_nhds ⟨hμ, hα⟩
  have hall :
      benchmark ⁻¹' Ioi (mixedFiniteCurve u - ε) ∩
          (rawGap ⁻¹' Ioi 0 ∩
            (deferralGap ⁻¹' Ioi 0 ∩
              (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))) ∈
        nhds point :=
    Filter.inter_mem hbenchmarkNhds
      (Filter.inter_mem hrawNhds
        (Filter.inter_mem hdeferralNhds hpositiveNhds))
  have hdense :
      DenseRange
        (fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) := by
    simpa using
      ((Rat.denseRange_cast :
        DenseRange ((↑) : ℚ → ℝ)).prodMap
          (Rat.denseRange_cast :
            DenseRange ((↑) : ℚ → ℝ)))
  obtain ⟨q, hq⟩ := hdense.mem_nhds hall
  have hqBenchmark :
      mixedFiniteCurve u - ε <
        mixedScaledBenchmark (u : ℝ) (q.1 : ℝ) (q.2 : ℝ) :=
    hq.1
  have hqRaw :
      2 + (q.2 : ℝ) < (u : ℝ) := by
    have := hq.2.1
    change
      0 < (u : ℝ) -
        (2 + (q.2 : ℝ)) at this
    linarith
  have hqDeferral :
      0 <
        (1 + (q.2 : ℝ)) *
            ((u : ℝ) - 1 - Real.log (1 + (q.2 : ℝ))) -
          (q.1 : ℝ) := by
    have := hq.2.2.1
    change
      0 <
        (1 + (q.2 : ℝ)) *
            ((u : ℝ) - 1 - Real.log (1 + (q.2 : ℝ))) -
          (q.1 : ℝ) at this
    exact this
  have hqμ : 0 < (q.1 : ℝ) := hq.2.2.2.1
  have hqα : 0 < (q.2 : ℝ) := hq.2.2.2.2
  obtain ⟨M₀, B₀, hM₀, hB₀, hqμEq⟩ :=
    positive_rational_as_nat_ratio q.1 hqμ
  obtain ⟨A₀, B₁, hA₀, hB₁, hqαEq⟩ :=
    positive_rational_as_nat_ratio q.2 hqα
  let M := M₀ * B₁
  let A := A₀ * B₀
  let B := B₀ * B₁
  have hM : 0 < M := Nat.mul_pos hM₀ hB₁
  have hA : 0 < A := Nat.mul_pos hA₀ hB₀
  have hB : 0 < B := Nat.mul_pos hB₀ hB₁
  have hμEq :
      (M : ℝ) / (B : ℝ) = (q.1 : ℝ) := by
    rw [hqμEq]
    dsimp [M, B]
    have hB₀real : (B₀ : ℝ) ≠ 0 := by exact_mod_cast hB₀.ne'
    have hB₁real : (B₁ : ℝ) ≠ 0 := by exact_mod_cast hB₁.ne'
    push_cast
    field_simp [hB₀real, hB₁real]
  have hαEq :
      (A : ℝ) / (B : ℝ) = (q.2 : ℝ) := by
    rw [hqαEq]
    dsimp [A, B]
    have hB₀real : (B₀ : ℝ) ≠ 0 := by exact_mod_cast hB₀.ne'
    have hB₁real : (B₁ : ℝ) ≠ 0 := by exact_mod_cast hB₁.ne'
    push_cast
    field_simp [hB₀real, hB₁real]
  refine ⟨M, A, B, hM, hA, hB, ?_, ?_, ?_⟩
  · simpa [hμEq, hαEq] using hqBenchmark
  · simpa [hαEq] using hqRaw
  · simpa [hμEq, hαEq] using hqDeferral

/-- The complete finite numerical certificate for an interior mixed point:
arbitrarily large positive cap/harmonic blocks simultaneously attain the
target ratio, defer every cap, and fit every virtual harmonic raw block
strictly under the finite cap. -/
theorem exists_finite_mixed_benchmark
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ))
    (huUpper : (u : ℝ) < zStar)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ C K Z : ℕ,
      0 < C ∧ 0 < K ∧ 0 < Z ∧
      N ≤ C + K + Z ∧
      (mixedFiniteCurve u - ε) *
          mixedFiniteOffline (u : ℝ) C K Z ≤
        mixedFiniteOnline (u : ℝ) C K Z ∧
      0 ≤
        ((K + Z : ℕ) : ℝ) * ((u : ℝ) - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum - C ∧
      ∀ L ≤ K,
        1 + harmonicLevel (Z : ℝ) 0 L ≤ (u : ℝ) := by
  obtain ⟨M, A, B, hM, hA, hB, hbenchmark, hraw, hdeferral⟩ :=
    exists_integral_mixed_parameters
      u huLower huUpper hε
  have hu0 : 0 < (u : ℝ) := by
    linarith [goldenRatio_pos]
  have hratioEvent :=
    eventually_mixedFinite_ratio
      hM hA hB hbenchmark hu0
  have hdeferralEvent :=
    eventually_mixedFinite_deferral
      hM hA hB hdeferral
  obtain ⟨qRatio, hqRatio⟩ :=
    Filter.eventually_atTop.1 hratioEvent
  obtain ⟨qDeferral, hqDeferral⟩ :=
    Filter.eventually_atTop.1 hdeferralEvent
  let q : ℕ := max (max qRatio qDeferral) N
  let C : ℕ := M * (q + 1)
  let K : ℕ := A * (q + 1)
  let Z : ℕ := B * (q + 1)
  have hqRatioLe : qRatio ≤ q :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hqDeferralLe : qDeferral ≤ q :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hNq : N ≤ q := le_max_right _ _
  have hC : 0 < C := Nat.mul_pos hM (by omega)
  have hK : 0 < K := Nat.mul_pos hA (by omega)
  have hZ : 0 < Z := Nat.mul_pos hB (by omega)
  have hsize : N ≤ C + K + Z := by
    have hscale : q + 1 ≤ Z := by
      dsimp [Z]
      exact Nat.le_mul_of_pos_left (q + 1) hB
    omega
  have hratio :
      (mixedFiniteCurve u - ε) *
          mixedFiniteOffline (u : ℝ) C K Z ≤
        mixedFiniteOnline (u : ℝ) C K Z := by
    simpa [C, K, Z] using hqRatio q hqRatioLe
  have hdefer :
      0 ≤
        ((K + Z : ℕ) : ℝ) * ((u : ℝ) - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum - C := by
    simpa [C, K, Z] using hqDeferral q hqDeferralLe
  have hsafe :
      ∀ L ≤ K,
        1 + harmonicLevel (Z : ℝ) 0 L ≤ (u : ℝ) := by
    intro L hLK
    dsimp [K, Z] at hLK ⊢
    exact mixedFinite_rawSafe hB hLK hraw
  exact ⟨C, K, Z, hC, hK, hZ, hsize,
    hratio, hdefer, hsafe⟩

end LowerBound

end

end SchedulingPaper
