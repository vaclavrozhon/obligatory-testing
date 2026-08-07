import Mathlib

/-!
# Announced-multiset randomized obligatory testing: fluid certificates

This file checks the algebraic core of the stationary-threshold analysis for
the randomized announced-multiset model.

It contains:

* the maximum-density threshold certificate in finite dimension;
* the pair inequalities used to reduce an arbitrary distribution to the
  critical binary distribution;
* the sharp `4/3` worst-case bound and its equality witness.

The probability/concentration argument transferring the fluid lower bound to
a finite random permutation is not formalized here.
-/

namespace SchedulingPaper
namespace RandomizedAnnounced

noncomputable section

/-- Work in one unit of the stationary discovery phase. -/
def discoveryWork {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) : ℝ :=
  1 + ∑ i, p i * x i

/-- Job mass completed in one unit of the stationary discovery phase. -/
def discoveryMass {ι : Type*} [Fintype ι]
    (μ0 : ℝ) (x : ι → ℝ) : ℝ :=
  μ0 + ∑ i, x i

/-- Cross-multiplied form of the maximum-density threshold lemma.

`xStar` contains every class strictly below `θ`, no class strictly above
`θ`, and an arbitrary amount at equality.  If its density is `1/θ`, then no
other feasible selection `x` has larger density. -/
theorem threshold_maximizes_discovery_density
    {ι : Type*} [Fintype ι]
    {μ0 θ : ℝ} {μ p xStar x : ι → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_cap : ∀ i, x i ≤ μ i)
    (hstar_low : ∀ i, p i < θ → xStar i = μ i)
    (hstar_high : ∀ i, θ < p i → xStar i = 0)
    (hstar_density :
      θ * discoveryMass μ0 xStar = discoveryWork p xStar) :
    θ * discoveryMass μ0 x ≤ discoveryWork p x := by
  have hcoord : ∀ i, (θ - p i) * x i ≤ (θ - p i) * xStar i := by
    intro i
    rcases lt_trichotomy (p i) θ with hlt | heq | hgt
    · rw [hstar_low i hlt]
      exact mul_le_mul_of_nonneg_left (hx_cap i) (sub_nonneg.mpr hlt.le)
    · simp [heq]
    · rw [hstar_high i hgt]
      have hcoef : θ - p i ≤ 0 := sub_nonpos.mpr hgt.le
      simpa using mul_nonpos_of_nonpos_of_nonneg hcoef (hx_nonneg i)
  have hsum :
      ∑ i, (θ - p i) * x i ≤ ∑ i, (θ - p i) * xStar i :=
    Finset.sum_le_sum fun i _ => hcoord i
  have hrewrite (y : ι → ℝ) :
      θ * discoveryMass μ0 y - discoveryWork p y =
        θ * μ0 - 1 + ∑ i, (θ - p i) * y i := by
    simp only [discoveryMass, discoveryWork, mul_add]
    rw [Finset.mul_sum]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  have hdiff :
      θ * discoveryMass μ0 x - discoveryWork p x ≤
        θ * discoveryMass μ0 xStar - discoveryWork p xStar := by
    rw [hrewrite x, hrewrite xStar]
    linarith
  have hstar_zero :
      θ * discoveryMass μ0 xStar - discoveryWork p xStar = 0 := by
    linarith [hstar_density]
  rw [hstar_zero] at hdiff
  linarith

/-- During the stationary discovery phase, no feasible partial selection can
complete mass faster than the line of slope `1/θ`. -/
theorem discovery_completion_le_density_line
    {ι : Type*} [Fintype ι]
    {μ0 θ T s : ℝ} {μ p xStar x : ι → ℝ}
    (hθ : 0 < θ)
    (hT : 0 ≤ T)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_cap : ∀ i, x i ≤ μ i)
    (hstar_low : ∀ i, p i < θ → xStar i = μ i)
    (hstar_high : ∀ i, θ < p i → xStar i = 0)
    (hstar_density :
      θ * discoveryMass μ0 xStar = discoveryWork p xStar)
    (hwork : T * discoveryWork p x ≤ s) :
    T * discoveryMass μ0 x ≤ s / θ := by
  have hmax := threshold_maximizes_discovery_density
    hx_nonneg hx_cap hstar_low hstar_high hstar_density
  have hscaled := mul_le_mul_of_nonneg_left hmax hT
  rw [le_div_iff₀ hθ]
  nlinarith

/-- A threshold prefix gives a supporting-line inequality for the full-test
fractional knapsack curve. -/
theorem threshold_prefix_supporting
    {ι : Type*} [Fintype ι]
    {μ0 q : ℝ} {μ p y x : ι → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_cap : ∀ i, x i ≤ μ i)
    (hy_low : ∀ i, p i < q → y i = μ i)
    (hy_high : ∀ i, q < p i → y i = 0) :
    q * (discoveryMass μ0 x - discoveryMass μ0 y) ≤
      discoveryWork p x - discoveryWork p y := by
  have hcoord : ∀ i, (q - p i) * (x i - y i) ≤ 0 := by
    intro i
    rcases lt_trichotomy (p i) q with hlt | heq | hgt
    · rw [hy_low i hlt]
      exact mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hlt.le) (sub_nonpos.mpr (hx_cap i))
    · simp [heq]
    · rw [hy_high i hgt]
      apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgt.le)
      simpa using hx_nonneg i
  have hsum : ∑ i, (q - p i) * (x i - y i) ≤ 0 := by
    have := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hcoord i
    simpa using this
  have hidentity :
      q * (discoveryMass μ0 x - discoveryMass μ0 y) -
          (discoveryWork p x - discoveryWork p y) =
        ∑ i, (q - p i) * (x i - y i) := by
    simp only [discoveryMass, discoveryWork]
    have hmassdiff :
        μ0 + ∑ i, x i - (μ0 + ∑ i, y i) =
          ∑ i, (x i - y i) := by
      rw [Finset.sum_sub_distrib]
      ring
    have hworkdiff :
        1 + ∑ i, p i * x i - (1 + ∑ i, p i * y i) =
          ∑ i, p i * (x i - y i) := by
      calc
        1 + ∑ i, p i * x i - (1 + ∑ i, p i * y i) =
            (∑ i, p i * x i) - ∑ i, p i * y i := by ring
        _ = ∑ i, (p i * x i - p i * y i) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ i, p i * (x i - y i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    rw [hmassdiff, hworkdiff, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hidentity] at hsum
  linarith

/-- Extending the maximum-density discovery prefix by processing classes no
longer than `q` preserves average density at least `1/q`. -/
theorem extended_prefix_average_density
    {θ q massStar workStar mass work : ℝ}
    (hθq : θ ≤ q)
    (hmassStar : 0 ≤ massStar)
    (hstar : workStar = θ * massStar)
    (hextend : work - workStar ≤ q * (mass - massStar)) :
    work ≤ q * mass := by
  have hgap : 0 ≤ (q - θ) * massStar :=
    mul_nonneg (sub_nonneg.mpr hθq) hmassStar
  nlinarith

/-- Pointwise tail-phase certificate.

`y` is the full-test SPT prefix chosen at the candidate deadline.  Its
average density is at least the current marginal density `1/q`.  Any partial
testing state `T,x` with no more work has no more completed mass. -/
theorem partial_completion_le_full_threshold_prefix
    {ι : Type*} [Fintype ι]
    {μ0 q T : ℝ} {μ p y x : ι → ℝ}
    (hq : 0 < q)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_cap : ∀ i, x i ≤ μ i)
    (hy_low : ∀ i, p i < q → y i = μ i)
    (hy_high : ∀ i, q < p i → y i = 0)
    (hwork : T * discoveryWork p x ≤ discoveryWork p y)
    (haverage : discoveryWork p y ≤ q * discoveryMass μ0 y) :
    T * discoveryMass μ0 x ≤ discoveryMass μ0 y := by
  have hsupport := threshold_prefix_supporting (μ0 := μ0)
    hx_nonneg hx_cap hy_low hy_high
  have hsupportScaled := mul_le_mul_of_nonneg_left hsupport hT0
  have hremain : 0 ≤ 1 - T := sub_nonneg.mpr hT1
  have haverageScaled := mul_le_mul_of_nonneg_left haverage hremain
  have hqnonneg : 0 ≤ q := hq.le
  by_contra hnot
  have hgreater : discoveryMass μ0 y < T * discoveryMass μ0 x :=
    lt_of_not_ge hnot
  have hqgreater :
      q * discoveryMass μ0 y < q * (T * discoveryMass μ0 x) :=
    mul_lt_mul_of_pos_left hgreater hq
  nlinarith

/-- A processing pair below the threshold has at least the product charge
divided by the threshold, in cross-multiplied form. -/
theorem early_min_pair_mul_le
    {θ x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxθ : x ≤ θ) (hyθ : y ≤ θ) :
    x * y ≤ θ * min x y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hyθ)]
  · rw [min_eq_right hyx]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hxθ)]

/-- A processing pair in the deferred tail has charge at least the threshold. -/
theorem threshold_le_late_min
    {θ x y : ℝ} (hx : θ ≤ x) (hy : θ ≤ y) :
    θ ≤ min x y := by
  exact le_min hx hy

/-- Total mass of a finite weighted processing-time distribution. -/
def weightedMass {ι : Type*} [Fintype ι] (μ : ι → ℝ) : ℝ :=
  ∑ i, μ i

/-- First processing-time moment of a finite weighted distribution. -/
def weightedMoment {ι : Type*} [Fintype ι]
    (μ p : ι → ℝ) : ℝ :=
  ∑ i, μ i * p i

/-- Two-draw minimum moment of a finite weighted distribution. -/
def weightedMinPair {ι : Type*} [Fintype ι]
    (μ p : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, μ i * μ j * min (p i) (p j)

/-- Finite weighted version of `m^2 ≤ θ Kearly`. -/
theorem weightedMoment_sq_le_threshold_mul_minPair
    {ι : Type*} [Fintype ι]
    {θ : ℝ} {μ p : ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpθ : ∀ i, p i ≤ θ) :
    weightedMoment μ p ^ 2 ≤ θ * weightedMinPair μ p := by
  have hpoint : ∀ i j,
      (μ i * p i) * (μ j * p j) ≤
        θ * (μ i * μ j * min (p i) (p j)) := by
    intro i j
    have hmin := early_min_pair_mul_le
      (hp0 i) (hp0 j) (hpθ i) (hpθ j)
    have hweight : 0 ≤ μ i * μ j := mul_nonneg (hμ i) (hμ j)
    have hmul := mul_le_mul_of_nonneg_left hmin hweight
    nlinarith
  have hdouble :
      (∑ i, ∑ j, (μ i * p i) * (μ j * p j)) ≤
        ∑ i, ∑ j, θ * (μ i * μ j * min (p i) (p j)) := by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hpoint i j
  have hleft :
      weightedMoment μ p ^ 2 =
        ∑ i, ∑ j, (μ i * p i) * (μ j * p j) := by
    unfold weightedMoment
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hright :
      (∑ i, ∑ j, θ * (μ i * μ j * min (p i) (p j))) =
        θ * weightedMinPair μ p := by
    unfold weightedMinPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hleft, ← hright]
  exact hdouble

/-- Finite weighted version of `θ h^2 ≤ Klate`. -/
theorem threshold_mul_weightedMass_sq_le_minPair
    {ι : Type*} [Fintype ι]
    {θ : ℝ} {μ p : ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hpθ : ∀ i, θ ≤ p i) :
    θ * weightedMass μ ^ 2 ≤ weightedMinPair μ p := by
  have hpoint : ∀ i j,
      θ * (μ i * μ j) ≤ μ i * μ j * min (p i) (p j) := by
    intro i j
    have hmin := threshold_le_late_min (hpθ i) (hpθ j)
    have hweight : 0 ≤ μ i * μ j := mul_nonneg (hμ i) (hμ j)
    have hmul := mul_le_mul_of_nonneg_left hmin hweight
    nlinarith
  have hdouble :
      (∑ i, ∑ j, θ * (μ i * μ j)) ≤
        ∑ i, ∑ j, μ i * μ j * min (p i) (p j) := by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hpoint i j
  have hleft :
      θ * weightedMass μ ^ 2 =
        ∑ i, ∑ j, θ * (μ i * μ j) := by
    unfold weightedMass
    rw [pow_two, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
  unfold weightedMinPair
  rw [hleft]
  exact hdouble

/-- The normalized stationary-threshold fluid cost, expressed through the
early mass `a`, threshold `θ`, and tail pair moment `Klate`. -/
def stationaryFluidCost (θ a Klate : ℝ) : ℝ :=
  θ * a * (1 - a / 2) + Klate / 2

/-- The normalized offline cost after splitting the pair moment into early,
cross, and late parts. -/
def offlineFluidCost (m h Kearly Klate : ℝ) : ℝ :=
  (1 + Kearly + 2 * h * m + Klate) / 2

/-- Exact sum-of-nonnegative-terms identity behind the sharp ratio. -/
theorem four_thirds_slack_identity
    {θ a m h Kearly Klate : ℝ}
    (hh : h = 1 - a)
    (hm : m = a * θ - 1) :
    2 * θ *
        (4 * offlineFluidCost m h Kearly Klate -
          3 * stationaryFluidCost θ a Klate) =
      (θ - 2) ^ 2 + 4 * (θ * Kearly - m ^ 2) +
        θ * (Klate - θ * h ^ 2) := by
  rw [hh, hm]
  unfold stationaryFluidCost offlineFluidCost
  ring

/-- Robust scaled version of the `4/3` certificate.

The exact threshold inequalities may each lose `s`: early pair mass is
controlled with `θ+s`, while late values are only known to be at least
`θ-s`.  If `Kearly ≤ B`, `θ ≤ B`, and the late mass lies in `[0,1]`, the
entire loss in the scaled slack is at most `5 B s`.  This is the algebraic
core used by a threshold learned from a quantized sample. -/
theorem approximate_four_thirds_scaled_slack
    {θ a m h Kearly Klate B s : ℝ}
    (hθ1 : 1 ≤ θ)
    (hθB : θ ≤ B)
    (hs : 0 ≤ s)
    (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ (θ + s) * Kearly)
    (hEarlyBound : Kearly ≤ B)
    (hLate : (θ - s) * h ^ 2 ≤ Klate) :
    -5 * B * s ≤
      2 * θ *
        (4 * offlineFluidCost m h Kearly Klate -
          3 * stationaryFluidCost θ a Klate) := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) (hθ1.trans hθB)
  have hsEarly : s * Kearly ≤ s * B :=
    mul_le_mul_of_nonneg_left hEarlyBound hs
  have hEarlySlack : -s * B ≤ θ * Kearly - m ^ 2 := by
    nlinarith [hEarly]
  have hhSq : h ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg h]
  have hsLate : s * h ^ 2 ≤ s := by
    nlinarith
  have hLateSlack : -s ≤ Klate - θ * h ^ 2 := by
    nlinarith [hLate]
  have hSquare : 0 ≤ (θ - 2) ^ 2 := sq_nonneg (θ - 2)
  have hIdentity := four_thirds_slack_identity
    (Kearly := Kearly) (Klate := Klate) hh hm
  rw [hIdentity]
  nlinarith

/-- Unscaled robust certificate in the form used by the sampling proof. -/
theorem stationaryFluidCost_le_four_thirds_add_error
    {θ a m h Kearly Klate B s : ℝ}
    (hθ1 : 1 ≤ θ)
    (hθB : θ ≤ B)
    (hs : 0 ≤ s)
    (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ (θ + s) * Kearly)
    (hEarlyBound : Kearly ≤ B)
    (hLate : (θ - s) * h ^ 2 ≤ Klate) :
    stationaryFluidCost θ a Klate ≤
      4 / 3 * offlineFluidCost m h Kearly Klate +
        5 / 6 * B * s := by
  have hscaled := approximate_four_thirds_scaled_slack
    hθ1 hθB hs hh0 hh1 hh hm hEarly hEarlyBound hLate
  have hB0 : 0 ≤ B := le_trans (by norm_num) (hθ1.trans hθB)
  let gap :=
    4 * offlineFluidCost m h Kearly Klate -
      3 * stationaryFluidCost θ a Klate
  by_contra hnot
  have hgap : gap < -(5 / 2 * B * s) := by
    dsimp [gap]
    linarith
  have hgapNonpos : gap ≤ 0 := by
    have herr0 : 0 ≤ 5 / 2 * B * s := by positivity
    linarith
  have hmul : θ * gap ≤ gap := by
    have := mul_le_mul_of_nonpos_right hθ1 hgapNonpos
    simpa using this
  dsimp [gap] at hscaled hgap hmul
  nlinarith

/-- Scale-free robust form of the `4/3` certificate.

Unlike `approximate_four_thirds_scaled_slack`, this version does not lose a
factor equal to an upper cutoff.  The additional premise `Kearly ≤ a * m` is
the elementary subprobability bound obtained from `min x y ≤ x`. -/
theorem approximate_four_thirds_scaled_slack_strong
    {θ a m h Kearly Klate s : ℝ}
    (hθ : 0 < θ)
    (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hs : 0 ≤ s)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ (θ + s) * Kearly)
    (hEarlyMass : Kearly ≤ a * m)
    (hLate : (θ - s) * h ^ 2 ≤ Klate) :
    -4 * θ * s ≤
      2 * θ *
        (4 * offlineFluidCost m h Kearly Klate -
          3 * stationaryFluidCost θ a Klate) := by
  have ham : a * m ≤ a ^ 2 * θ := by
    rw [hm]
    nlinarith
  have hKE : Kearly ≤ a ^ 2 * θ := hEarlyMass.trans ham
  have hsKE : s * Kearly ≤ s * (a ^ 2 * θ) :=
    mul_le_mul_of_nonneg_left hKE hs
  have hEarlySlack : -s * (a ^ 2 * θ) ≤ θ * Kearly - m ^ 2 := by
    nlinarith [hEarly]
  have hLateSlack : -s * h ^ 2 ≤ Klate - θ * h ^ 2 := by
    nlinarith [hLate]
  have haa : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hcoeff : 4 * a ^ 2 + h ^ 2 ≤ 4 := by
    rw [hh]
    nlinarith
  have hθs : 0 ≤ θ * s := mul_nonneg hθ.le hs
  have hscaledCoeff :
      θ * s * (4 * a ^ 2 + h ^ 2) ≤ θ * s * 4 :=
    mul_le_mul_of_nonneg_left hcoeff hθs
  have hSquare : 0 ≤ (θ - 2) ^ 2 := sq_nonneg (θ - 2)
  have hIdentity := four_thirds_slack_identity
    (Kearly := Kearly) (Klate := Klate) hh hm
  rw [hIdentity]
  nlinarith

/-- Unscaled scale-free certificate: an additive threshold error `s` costs
at most `2s/3` in normalized stationary cost. -/
theorem stationaryFluidCost_le_four_thirds_add_slack
    {θ a m h Kearly Klate s : ℝ}
    (hθ : 0 < θ)
    (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hs : 0 ≤ s)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ (θ + s) * Kearly)
    (hEarlyMass : Kearly ≤ a * m)
    (hLate : (θ - s) * h ^ 2 ≤ Klate) :
    stationaryFluidCost θ a Klate ≤
      4 / 3 * offlineFluidCost m h Kearly Klate + 2 / 3 * s := by
  have hscaled := approximate_four_thirds_scaled_slack_strong
    hθ ha0 ha1 hs hh hm hEarly hEarlyMass hLate
  nlinarith

/-- Exact difference between stationary and offline fluid costs. -/
theorem stationaryFluidCost_sub_offlineFluidCost
    {θ a m h Kearly Klate : ℝ}
    (hh : h = 1 - a)
    (hm : m = a * θ - 1) :
    stationaryFluidCost θ a Klate -
        offlineFluidCost m h Kearly Klate =
      (h + a * m - Kearly) / 2 := by
  rw [hh, hm]
  unfold stationaryFluidCost offlineFluidCost
  ring

/-- If every early value is at most a cutoff `B ≥ 1`, even an inaccurately
learned threshold costs at most `B/2` above the offline fluid objective. -/
theorem stationaryFluidCost_le_offline_add_half_cutoff
    {θ a m h Kearly Klate B : ℝ}
    (hB : 1 ≤ B)
    (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1)
    (hK0 : 0 ≤ Kearly)
    (hmB : m ≤ a * B)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1) :
    stationaryFluidCost θ a Klate ≤
      offlineFluidCost m h Kearly Klate + B / 2 := by
  have ham : a * m ≤ a ^ 2 * B :=
    by
      have := mul_le_mul_of_nonneg_left hmB ha0
      simpa [pow_two, mul_assoc] using this
  have haa : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hcorner : 0 ≤ (B - 1) * (1 - a) :=
    mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr ha1)
  have hmass : h + a * m - Kearly ≤ B := by
    rw [hh]
    nlinarith
  have hid := stationaryFluidCost_sub_offlineFluidCost
    (Kearly := Kearly) (Klate := Klate) hh hm
  calc
    stationaryFluidCost θ a Klate =
        offlineFluidCost m h Kearly Klate +
          (h + a * m - Kearly) / 2 := by
      linarith
    _ ≤ offlineFluidCost m h Kearly Klate + B / 2 := by
      linarith

/-- A large maximum-density threshold forces a large total pair moment.

This is the division-free form of
`Ktotal ≥ (θ-1)^2/θ`, used to justify test-all fallback when the learned
density is small. -/
theorem thresholdSplit_totalMinPair_lower
    {θ a m h Kearly Klate : ℝ}
    (hθ : 0 ≤ θ)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ θ * Kearly)
    (hLate : θ * h ^ 2 ≤ Klate) :
    (θ - 1) ^ 2 ≤
      θ * (Kearly + 2 * h * m + Klate) := by
  have hLateScaled : θ ^ 2 * h ^ 2 ≤ θ * Klate := by
    nlinarith [mul_nonneg hθ (sub_nonneg.mpr hLate)]
  have hSquareIdentity :
      (m + θ * h) ^ 2 =
        m ^ 2 + 2 * θ * h * m + θ ^ 2 * h ^ 2 := by
    ring
  have hThresholdIdentity : m + θ * h = θ - 1 := by
    rw [hh, hm]
    ring
  rw [← hThresholdIdentity, hSquareIdentity]
  nlinarith

/-- Ratio-ready form of `thresholdSplit_totalMinPair_lower`: the normalized
offline cost grows linearly with a large maximum-density threshold. -/
theorem offlineFluidCost_lower_of_thresholdSplit
    {θ a m h Kearly Klate : ℝ}
    (hθ : 0 < θ)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ θ * Kearly)
    (hLate : θ * h ^ 2 ≤ Klate) :
    (θ - 1 + 1 / θ) / 2 ≤
      offlineFluidCost m h Kearly Klate := by
  have htotal := thresholdSplit_totalMinPair_lower
    hθ.le hh hm hEarly hLate
  have hdiv :
      (θ - 1) ^ 2 / θ ≤ Kearly + 2 * h * m + Klate := by
    rw [div_le_iff₀ hθ]
    simpa [mul_comm] using htotal
  calc
    (θ - 1 + 1 / θ) / 2 =
        (1 + (θ - 1) ^ 2 / θ) / 2 := by
      field_simp [hθ.ne']
      ring
    _ ≤ (1 + (Kearly + 2 * h * m + Klate)) / 2 := by
      linarith
    _ = offlineFluidCost m h Kearly Klate := by
      unfold offlineFluidCost
      ring

/-- Sharp scalar certificate for the `4/3` upper bound.

The density identity is `1 + m = a θ`; `h=1-a` is the deferred mass.
`Kearly` and `Klate` are bounded below by the two pointwise pair lemmas.
After those substitutions, the slack is `(θ-2)^2/(2θ)`. -/
theorem stationaryFluidCost_le_four_thirds
    {θ a m h Kearly Klate : ℝ}
    (hθ : 0 < θ)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ θ * Kearly)
    (hLate : θ * h ^ 2 ≤ Klate) :
    3 * stationaryFluidCost θ a Klate ≤
      4 * offlineFluidCost m h Kearly Klate := by
  have hLateMul :
      0 ≤ θ * (Klate - θ * h ^ 2) :=
    mul_nonneg hθ.le (sub_nonneg.mpr hLate)
  have hSquare : 0 ≤ (θ - 2) ^ 2 := sq_nonneg (θ - 2)
  have hIdentity := four_thirds_slack_identity
    (Kearly := Kearly) (Klate := Klate) hh hm
  have hScaled :
      0 ≤ 2 * θ *
        (4 * offlineFluidCost m h Kearly Klate -
          3 * stationaryFluidCost θ a Klate) := by
    rw [hIdentity]
    nlinarith
  have hfactor : 0 < 2 * θ := mul_pos (by norm_num) hθ
  have hnonneg :
      0 ≤ 4 * offlineFluidCost m h Kearly Klate -
        3 * stationaryFluidCost θ a Klate := by
    have hScaled' :
        0 ≤ (4 * offlineFluidCost m h Kearly Klate -
          3 * stationaryFluidCost θ a Klate) * (2 * θ) := by
      simpa [mul_comm] using hScaled
    exact nonneg_of_mul_nonneg_left hScaled' hfactor
  linarith

/-- Ratio form of the sharp bound. -/
theorem stationaryFluidRatio_le_four_thirds
    {θ a m h Kearly Klate : ℝ}
    (hθ : 0 < θ)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ θ * Kearly)
    (hLate : θ * h ^ 2 ≤ Klate)
    (hOffline : 0 < offlineFluidCost m h Kearly Klate) :
    stationaryFluidCost θ a Klate /
        offlineFluidCost m h Kearly Klate ≤ 4 / 3 := by
  rw [div_le_iff₀ hOffline]
  have hmain := stationaryFluidCost_le_four_thirds
    hθ hh hm hEarly hLate
  nlinarith

/-- Sharp `4/3` certificate for an arbitrary finite early/tail split.

The assumptions say that the early and late measures form a probability
distribution, the early processing times lie below `θ`, the late times lie
above `θ`, and the selected discovery block has density `1/θ`. -/
theorem finiteSplit_stationaryFluidCost_le_four_thirds
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {θ : ℝ} {μEarly pEarly : ι → ℝ} {μLate pLate : κ → ℝ}
    (hθ : 0 < θ)
    (hμEarly : ∀ i, 0 ≤ μEarly i)
    (hμLate : ∀ i, 0 ≤ μLate i)
    (hpEarly0 : ∀ i, 0 ≤ pEarly i)
    (hpEarlyθ : ∀ i, pEarly i ≤ θ)
    (hpLateθ : ∀ i, θ ≤ pLate i)
    (hmass : weightedMass μLate = 1 - weightedMass μEarly)
    (hdensity :
      weightedMoment μEarly pEarly = weightedMass μEarly * θ - 1) :
    3 * stationaryFluidCost θ (weightedMass μEarly)
          (weightedMinPair μLate pLate) ≤
      4 * offlineFluidCost
          (weightedMoment μEarly pEarly)
          (weightedMass μLate)
          (weightedMinPair μEarly pEarly)
          (weightedMinPair μLate pLate) := by
  apply stationaryFluidCost_le_four_thirds hθ hmass hdensity
  · exact weightedMoment_sq_le_threshold_mul_minPair
      hμEarly hpEarly0 hpEarlyθ
  · exact threshold_mul_weightedMass_sq_le_minPair hμLate hpLateθ

/-- Half zeros and half processing time two have stationary fluid cost one. -/
theorem criticalBinary_stationaryCost :
    stationaryFluidCost 2 (1 / 2) (1 / 2) = 1 := by
  norm_num [stationaryFluidCost]

/-- Half zeros and half processing time two have offline fluid cost `3/4`. -/
theorem criticalBinary_offlineCost :
    offlineFluidCost 0 (1 / 2) 0 (1 / 2) = 3 / 4 := by
  norm_num [offlineFluidCost]

/-- The critical binary distribution attains the sharp ratio `4/3`. -/
theorem criticalBinary_ratio :
    stationaryFluidCost 2 (1 / 2) (1 / 2) /
        offlineFluidCost 0 (1 / 2) 0 (1 / 2) = 4 / 3 := by
  rw [criticalBinary_stationaryCost, criticalBinary_offlineCost]
  norm_num

end

end RandomizedAnnounced
end SchedulingPaper
