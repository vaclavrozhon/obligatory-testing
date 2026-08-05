import SchedulingPaper.Constants
import SchedulingPaper.HarmonicCore

/-!
# The analytic limit of the harmonic lower bound

This file checks the analytic calculation in equation `lower-I` and the
substitution used immediately afterwards.  In particular, the integrals below
are genuine `intervalIntegral`s rather than names for their claimed closed
forms.
-/

namespace SchedulingPaper

noncomputable section

/-- The rational integrand occurring in the first line of `lower-I`. -/
def harmonicRationalIntegrand (α t : ℝ) : ℝ :=
  (α - t) ^ 2 / (1 + t)

/-- The integrand in the integration-by-parts form of `lower-I`. -/
def harmonicLogIntegrand (α t : ℝ) : ℝ :=
  (α - t) * (1 + Real.log (1 + t))

/-- The integral quantity denoted by `I(α)` in the manuscript. -/
def harmonicIntegral (α : ℝ) : ℝ :=
  α ^ 2 / 2 +
    (1 / 2 : ℝ) * ∫ t in 0..α, harmonicRationalIntegrand α t

/-- The second, integration-by-parts, representation of `I(α)`. -/
def harmonicLogIntegral (α : ℝ) : ℝ :=
  ∫ t in 0..α, harmonicLogIntegrand α t

/-- The closed form displayed in equation `lower-I`. -/
def harmonicIntegralClosedForm (α : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + α) ^ 2 * Real.log (1 + α) -
    α / 2 - α ^ 2 / 4

private def harmonicRationalPrimitive (α t : ℝ) : ℝ :=
  t ^ 2 / 2 - (2 * α + 1) * t +
    (1 + α) ^ 2 * Real.log (1 + t)

private theorem harmonicRationalPrimitive_hasDerivAt
    {α t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (harmonicRationalPrimitive α)
      (harmonicRationalIntegrand α t) t := by
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 t :=
    by
      simpa only [Pi.add_apply, zero_add, id_eq] using
        (hasDerivAt_const t 1).add (hasDerivAt_id t)
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht).comp t hu
  have h :=
    (((hasDerivAt_id t).pow 2).div_const 2).sub
      ((hasDerivAt_const t (2 * α + 1)).mul (hasDerivAt_id t)) |>.add
      ((hasDerivAt_const t ((1 + α) ^ 2)).mul hlog)
  convert h using 1
  · unfold harmonicRationalIntegrand
    simp only [id_eq, Nat.cast_ofNat, zero_mul, zero_add]
    field_simp [ht]
    ring

theorem harmonicRationalIntegrand_continuousOn {α : ℝ} :
    ContinuousOn (harmonicRationalIntegrand α) (Set.Icc 0 α) := by
  intro t ht
  have ht0 : 1 + t ≠ 0 := by linarith [ht.1]
  exact
    (((continuousAt_const.sub continuousAt_id).pow 2).div
      (continuousAt_const.add continuousAt_id) ht0).continuousWithinAt

/-- Evaluation of the non-polynomial integral in the first representation
of `I(α)`. -/
theorem harmonicRationalIntegral_eq {α : ℝ} (hα : 0 ≤ α) :
    (∫ t in 0..α, harmonicRationalIntegrand α t) =
      (1 + α) ^ 2 * Real.log (1 + α) - α -
        3 * α ^ 2 / 2 := by
  have hint :
      IntervalIntegrable (harmonicRationalIntegrand α)
        MeasureTheory.volume 0 α :=
    by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hα] using
        (harmonicRationalIntegrand_continuousOn (α := α))
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) α,
        HasDerivAt (harmonicRationalPrimitive α)
          (harmonicRationalIntegrand α t) t := by
    intro t ht
    rw [Set.uIcc_of_le hα] at ht
    exact harmonicRationalPrimitive_hasDerivAt (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [harmonicRationalPrimitive, Real.log_one, mul_zero, add_zero]
  ring

private def harmonicLogPrimitive (α t : ℝ) : ℝ :=
  (1 + α) * (1 + t) * Real.log (1 + t) -
    (1 + t) ^ 2 / 4 -
    ((1 + t) ^ 2 / 2) * Real.log (1 + t)

private theorem harmonicLogPrimitive_hasDerivAt
    {α t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (harmonicLogPrimitive α) (harmonicLogIntegrand α t) t := by
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 t :=
    by
      simpa only [Pi.add_apply, zero_add, id_eq] using
        (hasDerivAt_const t 1).add (hasDerivAt_id t)
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
    simpa [one_div] using (Real.hasDerivAt_log ht).comp t hu
  have huLog :
      HasDerivAt
        (fun x : ℝ => (1 + x) * Real.log (1 + x))
        (Real.log (1 + t) + (1 + t) * (1 / (1 + t))) t :=
    by
      simpa only [Pi.mul_apply, one_mul] using hu.mul hlog
  have huSq :
      HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + t)) t := by
    convert hu.pow 2 using 1
    all_goals ring
  have hfirst :=
    (hasDerivAt_const t (1 + α)).mul huLog
  have hsecond := huSq.div_const 4
  have hthird := (huSq.div_const 2).mul hlog
  have h := (hfirst.sub hsecond).sub hthird
  convert h using 1
  · funext x
    simp only [harmonicLogPrimitive, Pi.sub_apply, Pi.mul_apply]
    ring
  · unfold harmonicLogIntegrand
    simp only [zero_mul, zero_add]
    field_simp [ht]
    ring

theorem harmonicLogIntegrand_continuousOn {α : ℝ} :
    ContinuousOn (harmonicLogIntegrand α) (Set.Icc 0 α) := by
  intro t ht
  have ht0 : 1 + t ≠ 0 := by linarith [ht.1]
  exact
    ((continuousAt_const.sub continuousAt_id).mul
      (continuousAt_const.add
        ((Real.continuousAt_log ht0).comp
          (continuousAt_const.add continuousAt_id)))).continuousWithinAt

/-- Evaluation of the integration-by-parts representation in `lower-I`. -/
theorem harmonicLogIntegral_eq {α : ℝ} (hα : 0 ≤ α) :
    harmonicLogIntegral α = harmonicIntegralClosedForm α := by
  have hint :
      IntervalIntegrable (harmonicLogIntegrand α)
        MeasureTheory.volume 0 α :=
    by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hα] using
        (harmonicLogIntegrand_continuousOn (α := α))
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) α,
        HasDerivAt (harmonicLogPrimitive α)
          (harmonicLogIntegrand α t) t := by
    intro t ht
    rw [Set.uIcc_of_le hα] at ht
    exact harmonicLogPrimitive_hasDerivAt (by linarith [ht.1])
  unfold harmonicLogIntegral
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold harmonicLogPrimitive harmonicIntegralClosedForm
  simp only [Real.log_one, mul_zero, add_zero]
  ring

/-- The first interval-integral representation in `lower-I` has the claimed
closed form. -/
theorem harmonicIntegral_eq_closedForm {α : ℝ} (hα : 0 ≤ α) :
    harmonicIntegral α = harmonicIntegralClosedForm α := by
  unfold harmonicIntegral
  rw [harmonicRationalIntegral_eq hα]
  unfold harmonicIntegralClosedForm
  ring

/-- The two actual interval integrals displayed in `lower-I` agree. -/
theorem harmonicIntegral_eq_logIntegral {α : ℝ} (hα : 0 ≤ α) :
    harmonicIntegral α = harmonicLogIntegral α := by
  rw [harmonicIntegral_eq_closedForm hα, harmonicLogIntegral_eq hα]

/-- On the integration interval, the rational kernel decreases. -/
theorem harmonicRationalIntegrand_antitoneOn {α : ℝ} :
    AntitoneOn (harmonicRationalIntegrand α) (Set.Icc 0 α) := by
  intro x hx y hy hxy
  have hax : 0 ≤ α - x := by linarith [hx.2]
  have hay : 0 ≤ α - y := by linarith [hy.2]
  have hsq : (α - y) ^ 2 ≤ (α - x) ^ 2 :=
    (sq_le_sq₀ hay hax).2 (by linarith)
  have hdx : 0 < 1 + x := by linarith [hx.1]
  have hdy : 0 < 1 + y := by linarith [hy.1]
  unfold harmonicRationalIntegrand
  calc
    (α - y) ^ 2 / (1 + y) ≤ (α - y) ^ 2 / (1 + x) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hdx (by linarith)
    _ ≤ (α - x) ^ 2 / (1 + x) :=
      div_le_div_of_nonneg_right hsq hdx.le

/-- Right-endpoint Riemann sum for the rational integral.  It uses `n + 1`
subintervals, avoiding a special value at division by zero. -/
def harmonicRiemannSum (α : ℝ) (n : ℕ) : ℝ :=
  α / (n + 1 : ℝ) *
    ∑ k ∈ Finset.range (n + 1),
      harmonicRationalIntegrand α
        (α * (k + 1 : ℝ) / (n + 1 : ℝ))

private theorem sum_range_shift_sub (q : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, q k) -
        ∑ k ∈ Finset.range n, q (k + 1) =
      q 0 - q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith [ih]

/-- Quantitative right-Riemann-sum error.  Monotonicity sandwiches the
integral between the left and right sums, whose difference telescopes. -/
theorem harmonicRiemannSum_error_le {α : ℝ} (hα : 0 < α) (n : ℕ) :
    |harmonicRiemannSum α n -
        ∫ t in 0..α, harmonicRationalIntegrand α t| ≤
      α ^ 3 / (n + 1 : ℝ) := by
  let N : ℕ := n + 1
  let c : ℝ := α / N
  let f : ℝ → ℝ := harmonicRationalIntegrand α
  let g : ℝ → ℝ := fun x => c * f (c * x)
  have hN : 0 < N := by simp [N]
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := div_pos hα hNc
  have hcN : c * (N : ℝ) = α := by
    dsimp [c]
    field_simp
  have hf : AntitoneOn f (Set.Icc 0 α) := by
    simpa [f] using (harmonicRationalIntegrand_antitoneOn (α := α))
  have hg : AntitoneOn g (Set.Icc 0 (N : ℝ)) := by
    intro x hx y hy hxy
    have hcx : c * x ∈ Set.Icc (0 : ℝ) α := by
      constructor
      · exact mul_nonneg hc.le hx.1
      · rw [← hcN]
        exact mul_le_mul_of_nonneg_left hx.2 hc.le
    have hcy : c * y ∈ Set.Icc (0 : ℝ) α := by
      constructor
      · exact mul_nonneg hc.le hy.1
      · rw [← hcN]
        exact mul_le_mul_of_nonneg_left hy.2 hc.le
    exact mul_le_mul_of_nonneg_left
      (hf hcx hcy (mul_le_mul_of_nonneg_left hxy hc.le)) hc.le
  have hg' : AntitoneOn g (Set.Icc 0 (0 + (N : ℝ))) := by
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
        ∫ t in 0..α, harmonicRationalIntegrand α t := by
    calc
      (∫ x in 0..(N : ℝ), g x) =
          c * ∫ x in 0..(N : ℝ), f (c * x) := by
            simp only [g, intervalIntegral.integral_const_mul]
      _ = ∫ t in c * 0..c * (N : ℝ), f t := by
            exact intervalIntegral.mul_integral_comp_mul_left c
      _ = ∫ t in 0..α, harmonicRationalIntegrand α t := by
            simp only [mul_zero, hcN, f]
  have hsumRight :
      (∑ k ∈ Finset.range N, g (k + 1 : ℕ)) =
        harmonicRiemannSum α n := by
    unfold harmonicRiemannSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr
    · simp [N]
    · intro k hk
      dsimp [g, f, c, N]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 2
      all_goals ring
  have hright :
      harmonicRiemannSum α n ≤
        ∫ t in 0..α, harmonicRationalIntegrand α t := by
    rw [← hsumRight, ← hchange]
    exact hrightRaw
  have hleft :
      (∫ t in 0..α, harmonicRationalIntegrand α t) ≤
        ∑ k ∈ Finset.range N, g k := by
    rw [← hchange]
    exact hleftRaw
  have htel :
      (∑ k ∈ Finset.range N, g k) -
          ∑ k ∈ Finset.range N, g (k + 1 : ℕ) =
        α ^ 3 / (N : ℝ) := by
    rw [sum_range_shift_sub (fun k : ℕ => g k) N]
    dsimp [g, f]
    rw [hcN]
    unfold harmonicRationalIntegrand
    dsimp [c]
    field_simp
    ring
  have hgap :
      (∫ t in 0..α, harmonicRationalIntegrand α t) -
          harmonicRiemannSum α n ≤ α ^ 3 / (n + 1 : ℝ) := by
    rw [← hsumRight]
    rw [show (n + 1 : ℝ) = (N : ℝ) by simp [N]]
    linarith [hleft, htel]
  rw [abs_of_nonpos (sub_nonpos.mpr hright)]
  linarith

/-- The standard right Riemann sums converge to the actual interval
integral. -/
theorem harmonicRiemannSum_tendsto {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (harmonicRiemannSum α) Filter.atTop
      (nhds (∫ t in 0..α, harmonicRationalIntegrand α t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero
    (g := fun n : ℕ => α ^ 3 / (n + 1 : ℝ))
    (fun n => dist_nonneg) (fun n => ?_) ?_
  · simpa [Real.dist_eq] using harmonicRiemannSum_error_le hα n
  · have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat (α ^ 3)).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun n : ℕ => α ^ 3 / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht

/-- The full normalized processing contribution in `lower-P-exact`. -/
def harmonicIntegralApproximation (α : ℝ) (n : ℕ) : ℝ :=
  α ^ 2 / 2 + (1 / 2 : ℝ) * harmonicRiemannSum α n

theorem harmonicIntegralApproximation_tendsto {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (harmonicIntegralApproximation α) Filter.atTop
      (nhds (harmonicIntegral α)) := by
  have hsum := harmonicRiemannSum_tendsto hα
  have hcont :
      ContinuousAt
        (fun x : ℝ => α ^ 2 / 2 + (1 / 2 : ℝ) * x)
        (∫ t in 0..α, harmonicRationalIntegrand α t) := by
    fun_prop
  have ht := hcont.tendsto.comp hsum
  change Filter.Tendsto
    (fun n : ℕ =>
      α ^ 2 / 2 + (1 / 2 : ℝ) * harmonicRiemannSum α n)
    Filter.atTop
    (nhds (α ^ 2 / 2 +
      (1 / 2 : ℝ) * ∫ t in 0..α, harmonicRationalIntegrand α t)) at ht
  simpa only [harmonicIntegralApproximation, harmonicIntegral] using ht

/-- The normalized expression `P_K / ξ²` from `lower-P-exact`, after
substituting `K = n + 1` and `ξ = K / α`.  The last term is the right
Riemann sum above; its zero endpoint permits including `h = K`. -/
def harmonicNormalizedProcessing (α γ : ℝ) (n : ℕ) : ℝ :=
  α ^ 2 / 2 * (1 + γ * α / (n + 1 : ℝ)) +
    (1 / 2 : ℝ) * harmonicRiemannSum α n

theorem harmonicNormalizedProcessing_eq (α γ : ℝ) (n : ℕ) :
    harmonicNormalizedProcessing α γ n =
      harmonicIntegralApproximation α n +
        γ * α ^ 3 / (2 * (n + 1 : ℝ)) := by
  unfold harmonicNormalizedProcessing harmonicIntegralApproximation
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Consequently, the full normalized expression from `lower-P-exact`
converges to `I(α)`; the slack parameter `γ` contributes only `O(1/K)`. -/
theorem harmonicNormalizedProcessing_tendsto
    {α γ : ℝ} (hα : 0 < α) :
    Filter.Tendsto (harmonicNormalizedProcessing α γ) Filter.atTop
      (nhds (harmonicIntegral α)) := by
  have hmain := harmonicIntegralApproximation_tendsto hα
  have hcorrection :
      Filter.Tendsto
        (fun n : ℕ => γ * α ^ 3 / (2 * (n + 1 : ℝ)))
        Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat
        (γ * α ^ 3 / 2)).comp (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun n : ℕ => (γ * α ^ 3 / 2) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    convert ht using 1
    funext n
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn]
    push_cast
    ring
  have hadd := hmain.add hcorrection
  convert hadd using 1
  · funext n
    rw [harmonicNormalizedProcessing_eq]
  · simp

/-- The denominator in the limiting ratio `R(α)`. -/
def harmonicLimitDenominator (α : ℝ) : ℝ :=
  1 / 2 + α / 2 + α ^ 2 / 4 +
    (1 / 2 : ℝ) * (1 + α) ^ 2 * Real.log (1 + α)

/-- Equation `lower-Ralpha`, the limiting lower-bound ratio. -/
def harmonicLimitRatio (α : ℝ) : ℝ :=
  1 + (α + α ^ 2 / 2) / harmonicLimitDenominator α

theorem harmonicLimitDenominator_pos {α : ℝ} (hα : 0 < α) :
    0 < harmonicLimitDenominator α := by
  have hlog : 0 < Real.log (1 + α) := Real.log_pos (by linarith)
  have hsquare : 0 < (1 + α) ^ 2 := sq_pos_of_pos (by linarith)
  unfold harmonicLimitDenominator
  nlinarith [mul_pos hsquare hlog]

/-- This is the offline limiting coefficient before inserting the closed
form for `I(α)`. -/
theorem harmonicLimitDenominator_eq_integral {α : ℝ} (hα : 0 ≤ α) :
    harmonicLimitDenominator α =
      1 / 2 + α + α ^ 2 / 2 + harmonicIntegral α := by
  rw [harmonicIntegral_eq_closedForm hα]
  unfold harmonicLimitDenominator harmonicIntegralClosedForm
  ring

/-- The limiting ratio written directly in terms of the integral `I(α)`. -/
theorem harmonicLimitRatio_eq_integralForm {α : ℝ} (hα : 0 ≤ α) :
    harmonicLimitRatio α =
      1 + (α + α ^ 2 / 2) /
        (1 / 2 + α + α ^ 2 / 2 + harmonicIntegral α) := by
  unfold harmonicLimitRatio
  rw [harmonicLimitDenominator_eq_integral hα]

/-- With `z = (1 + α)²`, the `α`-ratio is exactly the one-variable
`obligatoryRatio` from `Constants`. -/
theorem harmonicLimitRatio_eq_obligatoryRatio {α : ℝ} (hα : 0 < α) :
    harmonicLimitRatio α = obligatoryRatio ((1 + α) ^ 2) := by
  have hden : harmonicLimitDenominator α ≠ 0 :=
    (harmonicLimitDenominator_pos hα).ne'
  have hscaleDen :
      obligatoryDenominator ((1 + α) ^ 2) =
        4 * harmonicLimitDenominator α := by
    unfold obligatoryDenominator harmonicLimitDenominator
    rw [Real.log_pow]
    norm_num
    ring
  have hscaleNum :
      2 * ((1 + α) ^ 2 - 1) =
        4 * (α + α ^ 2 / 2) := by
    ring
  unfold harmonicLimitRatio obligatoryRatio
  rw [hscaleDen, hscaleNum]
  field_simp [hden]

theorem harmonicLimitRatio_le_RStar {α : ℝ} (hα : 0 < α) :
    harmonicLimitRatio α ≤ RStar := by
  rw [harmonicLimitRatio_eq_obligatoryRatio hα]
  apply obligatoryRatio_le_RStar
  nlinarith [sq_pos_of_pos (by linarith : 0 < 1 + α)]

/-- The positive mass ratio corresponding to `zStar`. -/
def alphaStar : ℝ := Real.sqrt zStar - 1

theorem alphaStar_pos : 0 < alphaStar := by
  have hz0 : 0 ≤ zStar := by linarith [zStar_gt_one]
  have hsquare : (Real.sqrt zStar) ^ 2 = zStar := Real.sq_sqrt hz0
  have hsqrt0 : 0 ≤ Real.sqrt zStar := Real.sqrt_nonneg _
  unfold alphaStar
  nlinarith [zStar_gt_one]

theorem one_add_alphaStar_sq : (1 + alphaStar) ^ 2 = zStar := by
  have hz0 : 0 ≤ zStar := by linarith [zStar_gt_one]
  unfold alphaStar
  rw [show 1 + (Real.sqrt zStar - 1) = Real.sqrt zStar by ring,
    Real.sq_sqrt hz0]

theorem harmonicLimitRatio_alphaStar :
    harmonicLimitRatio alphaStar = RStar := by
  rw [harmonicLimitRatio_eq_obligatoryRatio alphaStar_pos,
    one_add_alphaStar_sq, obligatoryRatio_zStar]

/-! ## The admissible span and rational approximation -/

theorem zStar_lt_twentyfive_div_four :
    zStar < (25 : ℝ) / 4 := by
  have hExpOne : (5 : ℝ) / 2 < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hExpTwo : (25 : ℝ) / 4 < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hlog :
      Real.log ((25 : ℝ) / 4) < 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).2 hExpTwo
  have hAt : 0 < zRootFunction ((25 : ℝ) / 4) := by
    unfold zRootFunction
    linarith
  have hAtStar : zRootFunction zStar = 0 := by
    unfold zRootFunction
    linarith [zStar_equation]
  by_contra h
  have hle : (25 : ℝ) / 4 ≤ zStar := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq, hAtStar] at hAt
    linarith
  · have hmono :=
      zRootFunction_strictMonoOn
        (by norm_num : (25 : ℝ) / 4 ∈ Set.Ioi 1)
        zStar_gt_one hlt
    rw [hAtStar] at hmono
    linarith

theorem alphaStar_lt_three_halves :
    alphaStar < (3 : ℝ) / 2 := by
  have hsqrt :
      Real.sqrt zStar < (5 : ℝ) / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 2)]
    nlinarith [zStar_lt_twentyfive_div_four]
  unfold alphaStar
  linarith

/-- The maximizing mass ratio lies strictly inside the span-safe range
`α < exp 1 - 1` used by the harmonic construction. -/
theorem alphaStar_lt_exp_one_sub_one :
    alphaStar < Real.exp 1 - 1 := by
  linarith [alphaStar_lt_three_halves, Real.exp_one_gt_d9]

theorem harmonicLimitRatio_continuousAt {α : ℝ} (hα : 0 < α) :
    ContinuousAt harmonicLimitRatio α := by
  have hlogArg : 1 + α ≠ 0 := by linarith
  have hden : harmonicLimitDenominator α ≠ 0 :=
    (harmonicLimitDenominator_pos hα).ne'
  have honePlus :
      ContinuousAt (fun x : ℝ => 1 + x) α :=
    continuousAt_const.add continuousAt_id
  have hlog :
      ContinuousAt (fun x : ℝ => Real.log (1 + x)) α :=
    (Real.continuousAt_log hlogArg).comp honePlus
  have hnum :
      ContinuousAt (fun x : ℝ => x + x ^ 2 / 2) α :=
    continuousAt_id.add ((continuousAt_id.pow 2).div_const 2)
  have hhalf :
      ContinuousAt (fun _x : ℝ => (1 / 2 : ℝ)) α :=
    continuousAt_const
  have hdenCont : ContinuousAt harmonicLimitDenominator α := by
    unfold harmonicLimitDenominator
    exact
      ((hhalf.add (continuousAt_id.div_const 2)).add
        ((continuousAt_id.pow 2).div_const 4)).add
        ((hhalf.mul (honePlus.pow 2)).mul hlog)
  unfold harmonicLimitRatio
  exact continuousAt_const.add (hnum.div hdenCont hden)

/-- Every strict neighborhood below the optimum contains a rational
span-safe harmonic parameter.  This is the approximation step used before
clearing denominators in the fixed finite instance. -/
theorem exists_rational_harmonic_parameter
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ,
      0 < (q : ℝ) ∧
      (q : ℝ) < Real.exp 1 - 1 ∧
      RStar - ε < harmonicLimitRatio (q : ℝ) := by
  have hvalue :
      RStar - ε < harmonicLimitRatio alphaStar := by
    rw [harmonicLimitRatio_alphaStar]
    linarith
  have htarget :
      Set.Ioi (RStar - ε) ∈
        nhds (harmonicLimitRatio alphaStar) :=
    isOpen_Ioi.mem_nhds hvalue
  have hpre :
      harmonicLimitRatio ⁻¹' Set.Ioi (RStar - ε) ∈ nhds alphaStar :=
    (harmonicLimitRatio_continuousAt alphaStar_pos) htarget
  have hspan :
      Set.Ioo (0 : ℝ) (Real.exp 1 - 1) ∈ nhds alphaStar :=
    isOpen_Ioo.mem_nhds
      ⟨alphaStar_pos, alphaStar_lt_exp_one_sub_one⟩
  obtain ⟨q, hq⟩ :=
    (Rat.denseRange_cast :
      DenseRange ((↑) : ℚ → ℝ)).mem_nhds
        (Filter.inter_mem hpre hspan)
  exact ⟨q, hq.2.1, hq.2.2, hq.1⟩

end

end SchedulingPaper
