import Mathlib.Tactic

/-!
# Scalar certificates for blind optimization

This file checks the algebraic extremal arguments used by the deterministic
and randomized blind-optimization curves.  In particular, the radical in the
deterministic curve is characterized by its tangency equation, and both
one-variable envelopes are bounded by completing a square.  The final two
lemmas check the exact finite arithmetic in the deterministic
instance-optimality counterexample and in the balanced obligatory-testing
counterexample.
-/

namespace SchedulingPaper
namespace BlindOptimization

noncomputable section

/-- The ratio of `OptimizeAll` in the deterministic blind-optimization
envelope. -/
def deterministicOptimizeAllRatio (u : ℝ) : ℝ :=
  (Real.sqrt (4 * u ^ 3 - 4 * u + 1) - 1) / (2 * (u - 1))

/-- The binary survival-function envelope for `OptimizeAll`. -/
def deterministicOptimizeAllEnvelope (u b : ℝ) : ℝ :=
  (1 + 2 * u * b - u * b ^ 2) / (1 + (u - 1) * b ^ 2)

/-- The three-piece deterministic blind-optimization curve displayed in the
paper.  The nontrivial third branch is the exact OptimizeAll envelope. -/
def deterministicCurve (u : ℝ) : ℝ :=
  if u ≤ 1 then 1
  else if u ≤ 2 then u
  else deterministicOptimizeAllRatio u

@[simp] theorem deterministicCurve_of_le_one {u : ℝ} (hu : u ≤ 1) :
    deterministicCurve u = 1 := by simp [deterministicCurve, hu]

theorem deterministicCurve_of_one_lt_le_two {u : ℝ}
    (hu1 : 1 < u) (hu2 : u ≤ 2) :
    deterministicCurve u = u := by
  simp [deterministicCurve, not_le.mpr hu1, hu2]

theorem deterministicCurve_of_two_lt {u : ℝ} (hu : 2 < u) :
    deterministicCurve u = deterministicOptimizeAllRatio u := by
  simp [deterministicCurve, not_le.mpr (by linarith : 1 < u),
    not_le.mpr hu]

theorem deterministicOptimizeAllRatio_at_two :
    deterministicOptimizeAllRatio 2 = 2 := by
  unfold deterministicOptimizeAllRatio
  norm_num

def deterministicStoppingPolynomial (u R y : ℝ) : ℝ :=
  1 - R + 2 * u * y - (u + R * (u - 1)) * y ^ 2

/-- Scalar hidden-stopping certificate for the Raw branch. -/
theorem deterministicStoppingPolynomial_raw
    {u : ℝ} (hu : 1 < u) :
    deterministicStoppingPolynomial u u (1 / u) = 2 - u := by
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans (by norm_num) hu)
  unfold deterministicStoppingPolynomial
  field_simp [hu0]
  ring

theorem deterministic_radicand_pos {u : ℝ} (hu : 2 ≤ u) :
    0 < 4 * u ^ 3 - 4 * u + 1 := by
  nlinarith [sq_nonneg (u - 1), mul_nonneg (by positivity : 0 ≤ u) (sq_nonneg u)]

theorem deterministicOptimizeAllRatio_tangency {u : ℝ} (hu : 2 ≤ u) :
    let R := deterministicOptimizeAllRatio u
    (R - 1) * (u + R * (u - 1)) = u ^ 2 := by
  dsimp [deterministicOptimizeAllRatio]
  have hu1 : u - 1 ≠ 0 := by linarith
  have hrad : 0 ≤ 4 * u ^ 3 - 4 * u + 1 :=
    (deterministic_radicand_pos hu).le
  have hsqrt := Real.sq_sqrt hrad
  field_simp
  ring_nf at hsqrt ⊢
  nlinarith

theorem deterministicOptimizeAllRatio_pos {u : ℝ} (hu : 2 ≤ u) :
    0 < deterministicOptimizeAllRatio u := by
  have hden : 0 < 2 * (u - 1) := by linarith
  have hrad : 1 < 4 * u ^ 3 - 4 * u + 1 := by
    nlinarith [sq_nonneg (u - 1)]
  have hsqrt : 1 < Real.sqrt (4 * u ^ 3 - 4 * u + 1) := by
    nlinarith [Real.sq_sqrt (deterministic_radicand_pos hu).le,
      Real.sqrt_nonneg (4 * u ^ 3 - 4 * u + 1)]
  exact div_pos (by linarith) hden

/-- Scalar hidden-stopping certificate for the OptimizeAll branch: the
chosen stopping line is tangent to zero. -/
theorem deterministicStoppingPolynomial_optimizeAll
    {u : ℝ} (hu : 2 ≤ u) :
    let R := deterministicOptimizeAllRatio u
    let α := u / (u + R * (u - 1))
    deterministicStoppingPolynomial u R α = 0 := by
  dsimp
  let R := deterministicOptimizeAllRatio u
  have htangent := deterministicOptimizeAllRatio_tangency hu
  have hRpos := deterministicOptimizeAllRatio_pos hu
  have hRpos' : 0 < R := by exact hRpos
  have hden : 0 < u + R * (u - 1) := by
    exact add_pos_of_pos_of_nonneg (by linarith)
      (mul_nonneg hRpos'.le (by linarith))
  have htangent' : (R - 1) * (u + R * (u - 1)) = u ^ 2 := by
    exact htangent
  have hquot : u ^ 2 / (u + R * (u - 1)) = R - 1 := by
    rw [div_eq_iff hden.ne']
    nlinarith
  have hrewrite :
      deterministicStoppingPolynomial u R
          (u / (u + R * (u - 1))) =
        1 - R + u ^ 2 / (u + R * (u - 1)) := by
    unfold deterministicStoppingPolynomial
    field_simp [hden.ne']
    ring
  rw [hrewrite, hquot]
  ring

theorem deterministicOptimizeAllRatio_le_u {u : ℝ} (hu : 2 ≤ u) :
    deterministicOptimizeAllRatio u ≤ u := by
  have hden : 0 < 2 * (u - 1) := by linarith
  rw [deterministicOptimizeAllRatio, div_le_iff₀ hden]
  have hrad : 0 ≤ 4 * u ^ 3 - 4 * u + 1 :=
    (deterministic_radicand_pos hu).le
  have hsqrt0 := Real.sqrt_nonneg (4 * u ^ 3 - 4 * u + 1)
  have hsqrtSq := Real.sq_sqrt hrad
  have hcomparison :
      Real.sqrt (4 * u ^ 3 - 4 * u + 1) ≤ 2 * u ^ 2 - 2 * u + 1 := by
    have hright : 0 ≤ 2 * u ^ 2 - 2 * u + 1 := by
      nlinarith [sq_nonneg (u - 1)]
    nlinarith [sq_nonneg
      (Real.sqrt (4 * u ^ 3 - 4 * u + 1) - (2 * u ^ 2 - 2 * u + 1)),
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4 * u ^ 2)
        (by linarith : 0 ≤ u - 2)) (by linarith : 0 ≤ u - 1)]
  nlinarith

/-- A sharp elementary error bound for the deterministic asymptotic:
`G_BO(u)` lies between `√u` and `√u + 1/√u`. -/
theorem deterministicOptimizeAllRatio_sub_sqrt_bounds
    {u : ℝ} (hu : 2 ≤ u) :
    0 ≤ deterministicOptimizeAllRatio u - Real.sqrt u ∧
      deterministicOptimizeAllRatio u - Real.sqrt u ≤ 1 / Real.sqrt u := by
  let R := deterministicOptimizeAllRatio u
  let s := Real.sqrt u
  have hu0 : 0 < u := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg u
  have hsSq : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hs1 : 1 < s := by nlinarith
  have hsPos : 0 < s := by linarith
  have hR0 : 0 < R := deterministicOptimizeAllRatio_pos hu
  have htangent : (R - 1) * (u + R * (u - 1)) = u ^ 2 := by
    simpa [R] using deterministicOptimizeAllRatio_tangency hu
  have hsecond : 0 < u + R * (u - 1) :=
    add_pos_of_pos_of_nonneg hu0 (mul_nonneg hR0.le (by linarith))
  have hR1 : 1 < R := by
    by_contra hnot
    have : R - 1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg this hsecond.le
    rw [htangent] at hnonpos
    nlinarith [sq_pos_of_pos hu0]
  let H : ℝ → ℝ := fun x ↦ (x - 1) * (u + x * (u - 1)) - u ^ 2
  have hHR : H R = 0 := by dsimp [H]; rw [htangent]; ring
  have hHs : H s = -s * (2 * s - 1) := by
    dsimp [H]
    nlinarith
  have hfactorLower : H R - H s =
      (R - s) * (u + (R + s - 1) * (u - 1)) := by
    dsimp [H]
    ring
  have hbracketLower : 0 < u + (R + s - 1) * (u - 1) := by
    apply add_pos_of_pos_of_nonneg hu0
    exact mul_nonneg (by linarith) (by linarith)
  have hprodLower : 0 <
      (R - s) * (u + (R + s - 1) * (u - 1)) := by
    rw [← hfactorLower, hHR, hHs]
    nlinarith
  have hlower : 0 < R - s :=
    pos_of_mul_pos_left hprodLower hbracketLower.le
  let t := s + 1 / s
  have ht1 : 1 < t := by
    dsimp [t]
    have hinv : 0 < 1 / s := one_div_pos.mpr hsPos
    linarith
  have hHt : H t = (s - 1) * (s ^ 2 + 1) / s ^ 2 := by
    dsimp [H, t]
    field_simp [hsPos.ne']
    nlinarith
  have hfactorUpper : H t - H R =
      (t - R) * (u + (t + R - 1) * (u - 1)) := by
    dsimp [H]
    ring
  have hbracketUpper : 0 < u + (t + R - 1) * (u - 1) := by
    apply add_pos_of_pos_of_nonneg hu0
    exact mul_nonneg (by linarith) (by linarith)
  have hprodUpper : 0 <
      (t - R) * (u + (t + R - 1) * (u - 1)) := by
    rw [← hfactorUpper, hHR, hHt]
    simpa only [sub_zero] using
      (div_pos
        (mul_pos (sub_pos.mpr hs1)
          (show 0 < s ^ 2 + 1 by nlinarith [sq_nonneg s]))
        (sq_pos_of_pos hsPos))
  have hupper : 0 < t - R :=
    pos_of_mul_pos_left hprodUpper hbracketUpper.le
  constructor
  · simpa [R, s] using hlower.le
  · dsimp [t] at hupper
    simpa [R, s] using (show R - s ≤ 1 / s by linarith)

/-- Machine-checked form of
`G_BO(u) = √u + o(1)` as `u → ∞`. -/
theorem deterministicOptimizeAllRatio_sub_sqrt_tendsto_zero :
    Filter.Tendsto
      (fun u : ℝ ↦ deterministicOptimizeAllRatio u - Real.sqrt u)
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun u : ℝ ↦ 1 / Real.sqrt u)
      Filter.atTop (nhds 0) := by
    simpa [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Filter.Tendsto (fun _u : ℝ ↦ (0 : ℝ))
        Filter.atTop (nhds 0)) hinv
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with u hu
    exact (deterministicOptimizeAllRatio_sub_sqrt_bounds hu).1
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with u hu
    exact (deterministicOptimizeAllRatio_sub_sqrt_bounds hu).2

/-- The exact completed-square certificate behind the deterministic
`OptimizeAll` upper bound. -/
theorem deterministicOptimizeAll_tangent_square {u b : ℝ} (hu : 2 ≤ u) :
    let R := deterministicOptimizeAllRatio u
    let A := u + R * (u - 1)
    R * (1 + (u - 1) * b ^ 2) - (1 + 2 * u * b - u * b ^ 2) =
      A * (b - u / A) ^ 2 := by
  let R := deterministicOptimizeAllRatio u
  let A := u + R * (u - 1)
  change R * (1 + (u - 1) * b ^ 2) - (1 + 2 * u * b - u * b ^ 2) =
    A * (b - u / A) ^ 2
  have hR : 0 < R := deterministicOptimizeAllRatio_pos hu
  have hA : 0 < A := by
    dsimp [A]
    have : 0 ≤ R * (u - 1) := mul_nonneg hR.le (by linarith)
    linarith
  have htangent : (R - 1) * A = u ^ 2 := by
    dsimp [A]
    simpa [R] using deterministicOptimizeAllRatio_tangency hu
  calc
    R * (1 + (u - 1) * b ^ 2) - (1 + 2 * u * b - u * b ^ 2) =
        A * b ^ 2 - 2 * u * b + (R - 1) := by
          dsimp [A]
          ring
    _ = A * (b - u / A) ^ 2 := by
      field_simp [hA.ne']
      nlinarith

/-- Exact maximization of the deterministic binary envelope. -/
theorem deterministicOptimizeAllEnvelope_le_ratio {u b : ℝ}
    (hu : 2 ≤ u) :
    deterministicOptimizeAllEnvelope u b ≤ deterministicOptimizeAllRatio u := by
  let R := deterministicOptimizeAllRatio u
  let A := u + R * (u - 1)
  have hden : 0 < 1 + (u - 1) * b ^ 2 := by
    have : 0 ≤ (u - 1) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg b)
    linarith
  rw [deterministicOptimizeAllEnvelope, div_le_iff₀ hden]
  have hR : 0 < R := deterministicOptimizeAllRatio_pos hu
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (by linarith) (mul_nonneg hR.le (by linarith))
  have hsquare : 0 ≤ A * (b - u / A) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  have hid := deterministicOptimizeAll_tangent_square (u := u) (b := b) hu
  dsimp only at hid
  exact sub_nonneg.mp (by
    rw [hid]
    exact hsquare)

theorem deterministicOptimizeAllEnvelope_attains_ratio {u : ℝ} (hu : 2 ≤ u) :
    let R := deterministicOptimizeAllRatio u
    let b := u / (u + R * (u - 1))
    deterministicOptimizeAllEnvelope u b = R := by
  dsimp
  let R := deterministicOptimizeAllRatio u
  have hR : 0 < R := deterministicOptimizeAllRatio_pos hu
  have hA : 0 < u + R * (u - 1) := by
    have : 0 ≤ R * (u - 1) := mul_nonneg hR.le (by linarith)
    linarith
  have hid := deterministicOptimizeAll_tangent_square
    (u := u) (b := u / (u + R * (u - 1))) hu
  dsimp only at hid
  have hden : 0 < 1 + (u - 1) * (u / (u + R * (u - 1))) ^ 2 := by
    have : 0 ≤ (u - 1) * (u / (u + R * (u - 1))) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  rw [deterministicOptimizeAllEnvelope, div_eq_iff hden.ne']
  have hzero :
      (u + R * (u - 1)) *
          (u / (u + R * (u - 1)) - u / (u + R * (u - 1))) ^ 2 = 0 := by
    ring
  nlinarith

/-! ## Randomized scalar envelope -/

def randomizedBinaryEnvelope (u b : ℝ) : ℝ :=
  min u (1 + u * b) / (1 + (u - 1) * b ^ 2)

def randomizedBoundaryRatio (u : ℝ) : ℝ :=
  u ^ 3 / (u ^ 2 + (u - 1) ^ 3)

def randomizedInteriorRatio (u : ℝ) : ℝ :=
  (1 + Real.sqrt ((u ^ 2 + u - 1) / (u - 1))) / 2

def randomizedTransitionPolynomial (u : ℝ) : ℝ :=
  u ^ 3 - 2 * u ^ 2 - u + 1

theorem randomizedBoundaryRatio_eq_at_boundary {u : ℝ} (hu : 1 < u) :
    randomizedBinaryEnvelope u ((u - 1) / u) = randomizedBoundaryRatio u := by
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans (by norm_num) hu)
  have hden : u ^ 2 + (u - 1) ^ 3 ≠ 0 := by
    have : 0 < u ^ 2 + (u - 1) ^ 3 := by positivity
    positivity
  rw [randomizedBinaryEnvelope, randomizedBoundaryRatio]
  have hmin : min u (1 + u * ((u - 1) / u)) = u := by
    rw [min_eq_left]
    field_simp
    linarith
  rw [hmin]
  field_simp

/-- Before the transition, the low branch increases up to the switching
point. -/
theorem randomized_low_le_boundary {u b : ℝ}
    (hu : 1 < u) (_hb0 : 0 ≤ b) (hb : b ≤ (u - 1) / u)
    (hpoly : randomizedTransitionPolynomial u ≤ 0) :
    (1 + u * b) / (1 + (u - 1) * b ^ 2) ≤ randomizedBoundaryRatio u := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hdenb : 0 < 1 + (u - 1) * b ^ 2 := by positivity
  have hden0 : 0 < u ^ 2 + (u - 1) ^ 3 := by positivity
  rw [randomizedBoundaryRatio, div_le_div_iff₀ hdenb hden0]
  have hblinear : b * u - u + 1 ≤ 0 := by
    have := mul_le_mul_of_nonneg_right hb hu0.le
    field_simp at this
    linarith
  have hsecond : b * u ^ 3 - b * u ^ 2 - 2 * u + 1 ≤ 0 := by
    have hcoef : 0 ≤ u ^ 2 * (u - 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hb hcoef
    have hpoly' : u ^ 3 - 2 * u ^ 2 - u + 1 ≤ 0 := hpoly
    field_simp at hmul
    nlinarith
  nlinarith [mul_nonneg (neg_nonneg.mpr hblinear) (neg_nonneg.mpr hsecond)]

theorem randomized_high_le_boundary {u b : ℝ}
    (hu : 1 < u) (hb : (u - 1) / u ≤ b) :
    u / (1 + (u - 1) * b ^ 2) ≤ randomizedBoundaryRatio u := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hb0 : 0 ≤ (u - 1) / u := by positivity
  have hbnonneg : 0 ≤ b := hb0.trans hb
  have hsquares : ((u - 1) / u) ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ hb0 hbnonneg).2 hb
  have hdenb : 0 < 1 + (u - 1) * b ^ 2 := by positivity
  have hden0 : 0 < u ^ 2 + (u - 1) ^ 3 := by positivity
  rw [randomizedBoundaryRatio, div_le_div_iff₀ hdenb hden0]
  have hweighted := mul_le_mul_of_nonneg_left hsquares (by linarith : 0 ≤ u - 1)
  field_simp at hweighted
  nlinarith

theorem randomizedBinaryEnvelope_le_boundary {u b : ℝ}
    (hu : 1 < u) (hb0 : 0 ≤ b) (_hb1 : b ≤ 1)
    (hpoly : randomizedTransitionPolynomial u ≤ 0) :
    randomizedBinaryEnvelope u b ≤ randomizedBoundaryRatio u := by
  by_cases hb : b ≤ (u - 1) / u
  · rw [randomizedBinaryEnvelope, min_eq_right]
    · exact randomized_low_le_boundary hu hb0 hb hpoly
    · have hmul := mul_le_mul_of_nonneg_left hb (lt_trans (by norm_num) hu).le
      field_simp at hmul
      linarith
  · have hb' : (u - 1) / u ≤ b := le_of_not_ge hb
    rw [randomizedBinaryEnvelope, min_eq_left]
    · exact randomized_high_le_boundary hu hb'
    · have hmul := mul_le_mul_of_nonneg_left hb' (lt_trans (by norm_num) hu).le
      field_simp at hmul
      linarith

theorem randomizedInteriorRatio_quadratic {u : ℝ} (hu : 1 < u) :
    let R := randomizedInteriorRatio u
    4 * R * (R - 1) * (u - 1) = u ^ 2 := by
  dsimp [randomizedInteriorRatio]
  have hu1 : 0 < u - 1 := by linarith
  have hrad : 0 ≤ (u ^ 2 + u - 1) / (u - 1) := by
    apply div_nonneg
    · nlinarith [sq_nonneg u]
    · linarith
  have hsqrt := Real.sq_sqrt hrad
  field_simp at hsqrt ⊢
  nlinarith

theorem randomizedInteriorRatio_pos {u : ℝ} (_hu : 1 < u) :
    0 < randomizedInteriorRatio u := by
  unfold randomizedInteriorRatio
  have := Real.sqrt_nonneg ((u ^ 2 + u - 1) / (u - 1))
  linarith

/-- The completed-square certificate for the interior randomized branch. -/
theorem randomized_low_tangent_square {u b : ℝ} (hu : 1 < u) :
    let R := randomizedInteriorRatio u
    R * (1 + (u - 1) * b ^ 2) - (1 + u * b) =
      R * (u - 1) * (b - u / (2 * R * (u - 1))) ^ 2 := by
  let R := randomizedInteriorRatio u
  change R * (1 + (u - 1) * b ^ 2) - (1 + u * b) =
    R * (u - 1) * (b - u / (2 * R * (u - 1))) ^ 2
  have hR : 0 < R := randomizedInteriorRatio_pos hu
  have hu1 : 0 < u - 1 := by linarith
  have hquad : 4 * R * (R - 1) * (u - 1) = u ^ 2 := by
    simpa [R] using randomizedInteriorRatio_quadratic hu
  calc
    R * (1 + (u - 1) * b ^ 2) - (1 + u * b) =
        R * (u - 1) * b ^ 2 - u * b + (R - 1) := by ring
    _ = R * (u - 1) * (b - u / (2 * R * (u - 1))) ^ 2 := by
      field_simp [hR.ne', hu1.ne']
      nlinarith

theorem randomized_low_le_interior {u b : ℝ} (hu : 1 < u) :
    (1 + u * b) / (1 + (u - 1) * b ^ 2) ≤ randomizedInteriorRatio u := by
  let R := randomizedInteriorRatio u
  have hR : 0 < R := randomizedInteriorRatio_pos hu
  have hden : 0 < 1 + (u - 1) * b ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hsquare :
      0 ≤ R * (u - 1) * (b - u / (2 * R * (u - 1))) ^ 2 := by
    positivity
  have hid := randomized_low_tangent_square (u := u) (b := b) hu
  dsimp only at hid
  exact sub_nonneg.mp (by
    rw [hid]
    exact hsquare)

theorem randomizedBinaryEnvelope_le_interior {u b : ℝ}
    (hu : 1 < u) (_hb0 : 0 ≤ b) :
    randomizedBinaryEnvelope u b ≤ randomizedInteriorRatio u := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  by_cases hb : b ≤ (u - 1) / u
  · rw [randomizedBinaryEnvelope, min_eq_right]
    · exact randomized_low_le_interior hu
    · have hmul := mul_le_mul_of_nonneg_left hb hu0.le
      field_simp at hmul
      linarith
  · have hb' : (u - 1) / u ≤ b := le_of_not_ge hb
    have hhigh := randomized_high_le_boundary hu hb'
    have hboundary := randomized_low_le_interior
      (u := u) (b := (u - 1) / u) hu
    have heq := randomizedBoundaryRatio_eq_at_boundary hu
    rw [randomizedBinaryEnvelope, min_eq_left]
    · rw [← heq] at hhigh
      rw [randomizedBinaryEnvelope, min_eq_left] at hhigh
      · have hnum : 1 + u * ((u - 1) / u) = u := by
          field_simp
          ring
        rw [hnum] at hboundary
        exact hhigh.trans hboundary
      · field_simp
        linarith
    · have hmul := mul_le_mul_of_nonneg_left hb' hu0.le
      field_simp at hmul
      linarith

/-- On and after the cubic transition, the unconstrained tangent point lies
in the low-numerator region of the binary envelope. -/
theorem randomized_interior_tangent_le_boundary {u : ℝ}
    (hu : 1 < u) (hpoly : 0 ≤ randomizedTransitionPolynomial u) :
    u / (2 * randomizedInteriorRatio u * (u - 1)) ≤ (u - 1) / u := by
  let R := randomizedInteriorRatio u
  let s := Real.sqrt ((u ^ 2 + u - 1) / (u - 1))
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hu1 : 0 < u - 1 := by linarith
  have hR : 0 < R := randomizedInteriorRatio_pos hu
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hrad : 0 ≤ (u ^ 2 + u - 1) / (u - 1) := by
    apply div_nonneg
    · nlinarith [sq_nonneg u]
    · linarith
  have hsSq : s ^ 2 = (u ^ 2 + u - 1) / (u - 1) := by
    exact Real.sq_sqrt hrad
  have halgebra :
      (u ^ 2 + u - 1) * (u - 1) ^ 3 - (2 * u - 1) ^ 2 =
        u ^ 2 * randomizedTransitionPolynomial u := by
    unfold randomizedTransitionPolynomial
    ring
  have hsquares : (2 * u - 1) ^ 2 ≤ (s * (u - 1) ^ 2) ^ 2 := by
    have hproduct : 0 ≤ u ^ 2 * randomizedTransitionPolynomial u :=
      mul_nonneg (sq_nonneg u) hpoly
    have hbase :
        (2 * u - 1) ^ 2 ≤ (u ^ 2 + u - 1) * (u - 1) ^ 3 := by
      nlinarith [halgebra]
    calc
      (2 * u - 1) ^ 2 ≤ (u ^ 2 + u - 1) * (u - 1) ^ 3 := hbase
      _ = (s * (u - 1) ^ 2) ^ 2 := by
        field_simp at hsSq ⊢
        nlinarith
  have hlinear : 2 * u - 1 ≤ s * (u - 1) ^ 2 := by
    exact (sq_le_sq₀ (by linarith) (mul_nonneg hs0 (sq_nonneg _))).mp hsquares
  have hcross : u ^ 2 ≤ 2 * R * (u - 1) ^ 2 := by
    have hRformula : 2 * R = 1 + s := by
      dsimp [R, s, randomizedInteriorRatio]
      ring
    rw [hRformula]
    nlinarith [sq_nonneg (u - 1)]
  change u / (2 * R * (u - 1)) ≤ (u - 1) / u
  rw [div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hR) hu1) hu0]
  nlinarith

theorem randomizedBinaryEnvelope_attains_interior {u : ℝ}
    (hu : 1 < u) (hpoly : 0 ≤ randomizedTransitionPolynomial u) :
    let b := u / (2 * randomizedInteriorRatio u * (u - 1))
    randomizedBinaryEnvelope u b = randomizedInteriorRatio u := by
  dsimp
  let R := randomizedInteriorRatio u
  have hR : 0 < R := randomizedInteriorRatio_pos hu
  have hu1 : 0 < u - 1 := by linarith
  have hb0 : 0 ≤ u / (2 * R * (u - 1)) := by positivity
  have hbRegion : u / (2 * R * (u - 1)) ≤ (u - 1) / u := by
    simpa [R] using randomized_interior_tangent_le_boundary hu hpoly
  have hmin :
      min u (1 + u * (u / (2 * R * (u - 1)))) =
        1 + u * (u / (2 * R * (u - 1))) := by
    rw [min_eq_right]
    have hmul := mul_le_mul_of_nonneg_left hbRegion
      (lt_trans (by norm_num) hu).le
    have hright : u * ((u - 1) / u) = u - 1 := by
      field_simp
    rw [hright] at hmul
    linarith
  rw [randomizedBinaryEnvelope, hmin]
  have hden : 0 < 1 + (u - 1) * (u / (2 * R * (u - 1))) ^ 2 := by
    positivity
  rw [div_eq_iff hden.ne']
  have hid := randomized_low_tangent_square
    (u := u) (b := u / (2 * R * (u - 1))) hu
  dsimp only at hid
  have hzero :
      R * (u - 1) *
        (u / (2 * R * (u - 1)) - u / (2 * R * (u - 1))) ^ 2 = 0 := by
    ring
  nlinarith

/-! ## The blind-optimization transition and exact scalar maximum -/

theorem randomizedTransitionPolynomial_strictMonoOn :
    StrictMonoOn randomizedTransitionPolynomial (Set.Ici (2 : ℝ)) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hxpart : 0 ≤ x ^ 2 - 2 * x := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ x - 2)]
  have hypart : 0 ≤ y ^ 2 - 2 * y := by
    nlinarith [mul_nonneg hy0 (by linarith : 0 ≤ y - 2)]
  have hxyprod : 4 ≤ x * y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 2)
      (by linarith : 0 ≤ y - 2)]
  have hfactor :
      randomizedTransitionPolynomial y - randomizedTransitionPolynomial x =
        (y - x) * (x ^ 2 + x * y + y ^ 2 - 2 * x - 2 * y - 1) := by
    unfold randomizedTransitionPolynomial
    ring
  have hbracket :
      0 < x ^ 2 + x * y + y ^ 2 - 2 * x - 2 * y - 1 := by
    nlinarith
  have hdiff :
      0 < randomizedTransitionPolynomial y - randomizedTransitionPolynomial x := by
    rw [hfactor]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  linarith

theorem randomizedTransitionPolynomial_neg_of_gt_one_le_two {u : ℝ}
    (hu1 : 1 < u) (hu2 : u ≤ 2) :
    randomizedTransitionPolynomial u < 0 := by
  have hterm : u ^ 2 * (u - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) (by linarith)
  unfold randomizedTransitionPolynomial
  nlinarith

theorem existsUnique_randomizedTransition :
    ∃! u : ℝ, 1 < u ∧ randomizedTransitionPolynomial u = 0 := by
  have hcont : Continuous randomizedTransitionPolynomial := by
    unfold randomizedTransitionPolynomial
    fun_prop
  have hmem :
      (0 : ℝ) ∈ Set.Icc
        (randomizedTransitionPolynomial 2) (randomizedTransitionPolynomial 3) := by
    norm_num [randomizedTransitionPolynomial]
  rcases intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3)
      hcont.continuousOn hmem with ⟨u, huIcc, hroot⟩
  have hu2 : 2 < u := by
    refine lt_of_le_of_ne huIcc.1 ?_
    intro heq
    subst u
    norm_num [randomizedTransitionPolynomial] at hroot
  refine ⟨u, ⟨by linarith, hroot⟩, ?_⟩
  intro y hy
  have hy2 : 2 < y := by
    by_contra hnot
    have hneg := randomizedTransitionPolynomial_neg_of_gt_one_le_two
      hy.1 (le_of_not_gt hnot)
    rw [hy.2] at hneg
    linarith
  apply randomizedTransitionPolynomial_strictMonoOn.injOn
  · exact (show (2 : ℝ) ≤ y by linarith)
  · exact (show (2 : ℝ) ≤ u by linarith)
  · exact hy.2.trans hroot.symm

/-- The unique root greater than one of
`u³ - 2u² - u + 1`; this is `u_BO` in the paper. -/
def randomizedTransition : ℝ :=
  Classical.choose existsUnique_randomizedTransition

theorem randomizedTransition_spec :
    1 < randomizedTransition ∧
      randomizedTransitionPolynomial randomizedTransition = 0 :=
  (Classical.choose_spec existsUnique_randomizedTransition).1

theorem randomizedTransition_gt_two : 2 < randomizedTransition := by
  by_contra hnot
  have hneg := randomizedTransitionPolynomial_neg_of_gt_one_le_two
    randomizedTransition_spec.1 (le_of_not_gt hnot)
  rw [randomizedTransition_spec.2] at hneg
  linarith

theorem randomizedTransition_lt_three : randomizedTransition < 3 := by
  by_contra hnot
  have hthree : 3 ≤ randomizedTransition := le_of_not_gt hnot
  by_cases heq : randomizedTransition = 3
  · have hroot := randomizedTransition_spec.2
    rw [heq] at hroot
    norm_num [randomizedTransitionPolynomial] at hroot
  · have hstrict : 3 < randomizedTransition := lt_of_le_of_ne hthree (Ne.symm heq)
    have hmono := randomizedTransitionPolynomial_strictMonoOn
      (show (2 : ℝ) ≤ 3 by norm_num)
      (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ randomizedTransition)
      hstrict
    rw [randomizedTransition_spec.2] at hmono
    norm_num [randomizedTransitionPolynomial] at hmono

theorem randomizedTransitionPolynomial_nonpos_iff {u : ℝ} (hu : 1 < u) :
    randomizedTransitionPolynomial u ≤ 0 ↔ u ≤ randomizedTransition := by
  constructor
  · intro hpoly
    by_contra hnot
    have hmono := randomizedTransitionPolynomial_strictMonoOn
      (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ randomizedTransition)
      (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ u)
      (lt_of_not_ge hnot)
    rw [randomizedTransition_spec.2] at hmono
    linarith
  · intro hle
    by_cases hu2 : u ≤ 2
    · exact (randomizedTransitionPolynomial_neg_of_gt_one_le_two hu hu2).le
    · have hmono := randomizedTransitionPolynomial_strictMonoOn.monotoneOn
        (by linarith : (2 : ℝ) ≤ u)
        (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ randomizedTransition)
        hle
      rwa [randomizedTransition_spec.2] at hmono

def randomizedCurve (u : ℝ) : ℝ :=
  if u ≤ 1 then 1
  else if u ≤ randomizedTransition then randomizedBoundaryRatio u
  else randomizedInteriorRatio u

/-- Exact maximum of the binary envelope from the randomized
blind-optimization proof.  The preceding survival-function reduction in the
paper shows that this is also the maximum over all input distributions. -/
theorem randomizedBinaryEnvelope_le_curve {u b : ℝ}
    (hu : 1 < u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    randomizedBinaryEnvelope u b ≤ randomizedCurve u := by
  unfold randomizedCurve
  rw [if_neg (not_le.mpr hu)]
  by_cases htransition : u ≤ randomizedTransition
  · rw [if_pos htransition]
    exact randomizedBinaryEnvelope_le_boundary hu hb0 hb1
      ((randomizedTransitionPolynomial_nonpos_iff hu).2 htransition)
  · rw [if_neg htransition]
    exact randomizedBinaryEnvelope_le_interior hu hb0

theorem randomizedBinaryEnvelope_attains_curve {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      randomizedBinaryEnvelope u b = randomizedCurve u := by
  unfold randomizedCurve
  rw [if_neg (not_le.mpr hu)]
  by_cases htransition : u ≤ randomizedTransition
  · rw [if_pos htransition]
    refine ⟨(u - 1) / u, ⟨by positivity, by
      have hu0 : 0 < u := lt_trans (by norm_num) hu
      rw [div_le_one hu0]
      linarith⟩, randomizedBoundaryRatio_eq_at_boundary hu⟩
  · rw [if_neg htransition]
    let b := u / (2 * randomizedInteriorRatio u * (u - 1))
    have hpoly : 0 ≤ randomizedTransitionPolynomial u := by
      have hstrict : randomizedTransition < u := lt_of_not_ge htransition
      have hmono := randomizedTransitionPolynomial_strictMonoOn.monotoneOn
        (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ randomizedTransition)
        (by linarith [randomizedTransition_gt_two] : (2 : ℝ) ≤ u)
        hstrict.le
      rwa [randomizedTransition_spec.2] at hmono
    have hbBoundary := randomized_interior_tangent_le_boundary hu hpoly
    have hb0 : 0 ≤ b := by
      dsimp [b]
      apply div_nonneg (lt_trans (by norm_num) hu).le
      exact mul_nonneg
        (mul_nonneg (by norm_num) (randomizedInteriorRatio_pos hu).le)
        (by linarith)
    have hb1 : b ≤ 1 := by
      exact hbBoundary.trans (by
        have hu0 : 0 < u := lt_trans (by norm_num) hu
        rw [div_le_one hu0]
        linarith)
    refine ⟨b, ⟨hb0, hb1⟩, ?_⟩
    simpa [b] using randomizedBinaryEnvelope_attains_interior hu hpoly

/-! ## Asymptotics of the randomized curve -/

/-- Quantitative form of the large-cap expansion of the interior branch. -/
theorem randomizedInteriorRatio_sub_sqrt_bounds
    {u : ℝ} (hu : 3 ≤ u) :
    0 ≤ randomizedInteriorRatio u - (Real.sqrt u / 2 + 1 / 2) ∧
      randomizedInteriorRatio u - (Real.sqrt u / 2 + 1 / 2) ≤
        3 / (4 * Real.sqrt u) := by
  let s := Real.sqrt u
  let q := (u ^ 2 + u - 1) / (u - 1)
  let t := Real.sqrt q
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg u
  have hsPos : 0 < s := Real.sqrt_pos.mpr hu0
  have hsSq : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hqEq : q = u + 2 + 1 / (u - 1) := by
    dsimp [q]
    field_simp [hu1.ne']
    ring
  have hinv0 : 0 ≤ 1 / (u - 1) := by positivity
  have hinv1 : 1 / (u - 1) ≤ 1 := by
    rw [div_le_one hu1]
    linarith
  have hqge : u ≤ q := by rw [hqEq]; linarith
  have hq0 : 0 ≤ q := hu0.le.trans hqge
  have ht0 : 0 ≤ t := Real.sqrt_nonneg q
  have htSq : t ^ 2 = q := Real.sq_sqrt hq0
  have hts : s ≤ t := by
    dsimp [s, t]
    exact Real.sqrt_le_sqrt hqge
  have hdiffIdentity : (t - s) * (t + s) = q - u := by
    nlinarith
  have hqDiff : q - u ≤ 3 := by rw [hqEq]; linarith
  have hmul : (t - s) * (2 * s) ≤ 3 := by
    have hnonneg : 0 ≤ t - s := sub_nonneg.mpr hts
    have hden : 2 * s ≤ t + s := by linarith
    have hcompare := mul_le_mul_of_nonneg_left hden hnonneg
    rw [hdiffIdentity] at hcompare
    exact hcompare.trans hqDiff
  have hdiffUpper : t - s ≤ 3 / (2 * s) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * s)]
    nlinarith
  have hrewrite : randomizedInteriorRatio u - (s / 2 + 1 / 2) =
      (t - s) / 2 := by
    dsimp [randomizedInteriorRatio, q, t]
    ring
  rw [hrewrite]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hts) (by norm_num)
  · have hhalf := div_le_div_of_nonneg_right hdiffUpper (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [s]
    convert hhalf using 1 <;> ring

theorem randomizedCurve_eq_interior_of_three_le {u : ℝ} (hu : 3 ≤ u) :
    randomizedCurve u = randomizedInteriorRatio u := by
  unfold randomizedCurve
  rw [if_neg (by linarith : ¬ u ≤ 1)]
  rw [if_neg (by linarith [randomizedTransition_lt_three] : ¬ u ≤ randomizedTransition)]

/-- Machine-checked form of
`R_rand_BO(u) = √u/2 + 1/2 + o(1)` as `u → ∞`. -/
theorem randomizedCurve_sub_sqrt_tendsto_zero :
    Filter.Tendsto
      (fun u : ℝ ↦ randomizedCurve u - (Real.sqrt u / 2 + 1 / 2))
      Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun u : ℝ ↦ 3 / (4 * Real.sqrt u))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun u : ℝ ↦ 1 / Real.sqrt u)
        Filter.atTop (nhds 0) := by
      simpa [one_div, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
    have hscaled :=
      (tendsto_const_nhds : Filter.Tendsto (fun _u : ℝ ↦ (3 / 4 : ℝ))
        Filter.atTop (nhds (3 / 4 : ℝ))).mul hbase
    convert hscaled using 1
    · funext u
      ring
    · ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Filter.Tendsto (fun _u : ℝ ↦ (0 : ℝ))
        Filter.atTop (nhds 0)) hinv
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with u hu
    rw [randomizedCurve_eq_interior_of_three_le hu]
    exact (randomizedInteriorRatio_sub_sqrt_bounds hu).1
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with u hu
    rw [randomizedCurve_eq_interior_of_three_le hu]
    exact (randomizedInteriorRatio_sub_sqrt_bounds hu).2

/-! ## Finite adversarial-gap arithmetic -/

/-- Exact arithmetic used after the blind-optimization adversary has fixed
`m` optimized jobs. -/
theorem deterministic_instance_gap_algebra
    {n m : ℝ} (hn : 0 ≤ n) (hm0 : 0 ≤ m) (hmn : m ≤ n) :
    let adversarial := n ^ 2 + n + (m ^ 2 + m) / 2
    (m ≤ n / 2 →
      adversarial - (n + 1) * (n + 2 * m) / 2 ≥ n ^ 2 / 8) ∧
    (n / 2 ≤ m →
      adversarial - n * (n + 1) ≥ n ^ 2 / 8) := by
  dsimp
  constructor <;> intro hbranch
  · nlinarith [sq_nonneg (n - m)]
  · nlinarith [sq_nonneg m]

/-- The balanced obligatory-testing lower-bound polynomial from the paper is
at least `9 n² / 8`, independently of the number `h` of early positive
completions. -/
theorem obligatory_balanced_gap_algebra {m h : ℝ}
    (hm : 0 ≤ m) (hh : 0 ≤ h) :
    9 * m ^ 2 / 2 + h ^ 2 / 2 + 3 * m / 2 + h / 2 ≥
      9 * (2 * m) ^ 2 / 8 := by
  nlinarith [sq_nonneg h]

end

end BlindOptimization
end SchedulingPaper
