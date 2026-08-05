import SchedulingPaper.Constants

/-!
# The logarithmic threshold and its bank-potential identities

This file formalizes the one-dimensional analytic core of the upper bound at
the obligatory-testing endpoint.  In particular it proves the root identity
in the paper's `ρ` parametrization, the endpoint values and derivative of the
active threshold, the canonical identities used by the potential, and all
four first-order drift inequalities in both the active and flat regions.

The remaining finite-step argument (uniform Taylor remainder and telescoping)
is deliberately separated from these scalar calculations.
-/

namespace SchedulingPaper

noncomputable section

/-! ## The threshold -/

theorem rhoStar_ne_zero : rhoStar ≠ 0 := ne_of_gt rhoStar_pos

theorem rhoStar_add_two_div :
    (rhoStar + 2) / rhoStar = zStar := by
  unfold rhoStar
  have hz : zStar - 1 ≠ 0 := by linarith [zStar_gt_one]
  field_simp [hz]
  ring

/-- Equation (4.3), written entirely in terms of `rhoStar`. -/
theorem rhoStar_root_identity :
    Real.log ((rhoStar + 2) / rhoStar) = 2 / rhoStar - 2 := by
  rw [rhoStar_add_two_div, ← zStar_equation]
  unfold rhoStar
  have hz : zStar - 1 ≠ 0 := by linarith [zStar_gt_one]
  field_simp [hz]
  ring

/-- The nonsaturated part of the endpoint threshold.  The difference-of-logs
form makes differentiation transparent; `activeThreshold_eq_log_div` below
identifies it with the quotient form displayed in the paper. -/
def activeThreshold (y : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) *
    (Real.log (rhoStar + 2) - Real.log (rhoStar - 2 * y))

/-- The actual saturated threshold used by `AdaptiveThreshold`. -/
def adaptiveThreshold (y : ℝ) : ℝ :=
  if y ≤ -1 then 1 else activeThreshold y

theorem active_denominator_pos {y : ℝ} (hy : y ≤ 0) :
    0 < rhoStar - 2 * y := by
  linarith [rhoStar_pos]

theorem active_numerator_pos : 0 < rhoStar + 2 := by
  linarith [rhoStar_pos]

theorem activeThreshold_eq_log_div {y : ℝ} (hy : y ≤ 0) :
    activeThreshold y =
      1 + (1 / 2 : ℝ) *
        Real.log ((rhoStar + 2) / (rhoStar - 2 * y)) := by
  unfold activeThreshold
  rw [Real.log_div active_numerator_pos.ne'
    (active_denominator_pos hy).ne']

theorem activeThreshold_at_neg_one :
    activeThreshold (-1) = 1 := by
  unfold activeThreshold
  ring_nf

theorem activeThreshold_at_zero :
    activeThreshold 0 = 1 / rhoStar := by
  rw [activeThreshold_eq_log_div (le_refl 0)]
  norm_num
  rw [rhoStar_root_identity]
  field_simp [rhoStar_ne_zero]
  ring

theorem adaptiveThreshold_at_neg_one :
    adaptiveThreshold (-1) = 1 := by
  simp [adaptiveThreshold]

theorem adaptiveThreshold_eq_active {y : ℝ} (hy : -1 < y) :
    adaptiveThreshold y = activeThreshold y := by
  simp [adaptiveThreshold, not_le.mpr hy]

theorem activeThreshold_hasDerivAt {y : ℝ} (hy : y ≤ 0) :
    HasDerivAt activeThreshold (1 / (rhoStar - 2 * y)) y := by
  have hinner :
      HasDerivAt (fun t : ℝ => rhoStar - 2 * t) (-2) y := by
    convert (hasDerivAt_const y rhoStar).sub
      ((hasDerivAt_const y 2).mul (hasDerivAt_id y)) using 1
    ring
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (rhoStar - 2 * t))
        ((rhoStar - 2 * y)⁻¹ * (-2)) y :=
    by
      convert
        (Real.hasDerivAt_log (active_denominator_pos hy).ne').comp y hinner
        using 1
  unfold activeThreshold
  convert (hasDerivAt_const y 1).add
    ((hasDerivAt_const y (1 / 2 : ℝ)).mul
      ((hasDerivAt_const y (Real.log (rhoStar + 2))).sub hlog)) using 1
  field_simp [rhoStar_ne_zero, (active_denominator_pos hy).ne']
  ring

theorem activeThreshold_deriv {y : ℝ} (hy : y ≤ 0) :
    deriv activeThreshold y = 1 / (rhoStar - 2 * y) :=
  (activeThreshold_hasDerivAt hy).deriv

theorem activeThreshold_ge_one {y : ℝ} (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 0) :
    1 ≤ activeThreshold y := by
  have hden := active_denominator_pos hyUpper
  have hratio :
      1 ≤ (rhoStar + 2) / (rhoStar - 2 * y) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [activeThreshold_eq_log_div hyUpper]
  have hlog := Real.log_nonneg hratio
  linarith

theorem activeThreshold_mul_le_RStar {y : ℝ}
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    activeThreshold y * (rhoStar - y) ≤ RStar := by
  let q := (rhoStar + 2) / (rhoStar - 2 * y)
  have hden := active_denominator_pos hyUpper
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos active_numerator_pos hden
  have hlog : Real.log q ≤ q - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  have hqsub :
      q - 1 = 2 * (1 + y) / (rhoStar - 2 * y) := by
    dsimp [q]
    field_simp [hden.ne']
    ring
  rw [hqsub] at hlog
  have hleft : 0 ≤ (1 / 2 : ℝ) * (rhoStar - y) := by
    exact mul_nonneg (by norm_num) (by linarith [rhoStar_pos])
  have hscaled := mul_le_mul_of_nonneg_left hlog hleft
  have hfrac :
      (rhoStar - y) / (rhoStar - 2 * y) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hone : 0 ≤ 1 + y := by linarith
  have hlast :
      ((rhoStar - y) / (rhoStar - 2 * y)) * (1 + y) ≤ 1 + y := by
    nlinarith [mul_le_mul_of_nonneg_right hfrac hone]
  have hmain :
      (1 / 2 : ℝ) * (rhoStar - y) * Real.log q ≤ 1 + y := by
    calc
      (1 / 2 : ℝ) * (rhoStar - y) * Real.log q
          ≤ (1 / 2 : ℝ) * (rhoStar - y) *
              (2 * (1 + y) / (rhoStar - 2 * y)) := by
                simpa [mul_assoc] using hscaled
      _ = ((rhoStar - y) / (rhoStar - 2 * y)) * (1 + y) := by
            ring
      _ ≤ 1 + y := hlast
  rw [activeThreshold_eq_log_div hyUpper]
  change
    (1 + (1 / 2 : ℝ) * Real.log q) * (rhoStar - y) ≤ RStar
  unfold RStar
  nlinarith

/-! ## The active potential and canonical identities -/

/-- The primitive `f` in an algebraic form forced by the immediate-boundary
balance equation.  Its derivative and endpoint values are proved below. -/
def bankF (y : ℝ) : ℝ :=
  ((y - RStar) * (activeThreshold y - 1) +
    activeThreshold y * (1 + y)) / 2

def bankH (y : ℝ) : ℝ := activeThreshold y * (1 + y)

/-- The derivative of `h=A(1+y)` on the active interval. -/
def bankHPrime (y : ℝ) : ℝ :=
  activeThreshold y + (1 + y) / (rhoStar - 2 * y)

theorem bankF_at_neg_one : bankF (-1) = 0 := by
  simp [bankF, activeThreshold_at_neg_one]

theorem bankF_at_zero : bankF 0 = rhoStar / 2 := by
  rw [bankF, activeThreshold_at_zero]
  unfold RStar
  field_simp [rhoStar_ne_zero]
  ring

theorem bankF_twice_alt (y : ℝ) :
    2 * bankF y =
      1 + y - (rhoStar - 2 * y) * (activeThreshold y - 1) := by
  unfold bankF RStar
  ring

theorem bankF_nonneg {y : ℝ} (_hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    0 ≤ bankF y := by
  let q := (rhoStar + 2) / (rhoStar - 2 * y)
  have hden := active_denominator_pos hyUpper
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos active_numerator_pos hden
  have hlog : Real.log q ≤ q - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  have hqsub :
      q - 1 = 2 * (1 + y) / (rhoStar - 2 * y) := by
    dsimp [q]
    field_simp [hden.ne']
    ring
  rw [hqsub] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (show
    0 ≤ (rhoStar - 2 * y) / 2 by
      exact div_nonneg hden.le (by norm_num))
  have hbound :
      (rhoStar - 2 * y) * (activeThreshold y - 1) ≤ 1 + y := by
    have hAminus :
        activeThreshold y - 1 = (1 / 2 : ℝ) * Real.log q := by
      rw [activeThreshold_eq_log_div hyUpper]
      ring
    rw [hAminus]
    calc
      (rhoStar - 2 * y) * ((1 / 2 : ℝ) * Real.log q) =
          ((rhoStar - 2 * y) / 2) * Real.log q := by ring
      _ ≤ ((rhoStar - 2 * y) / 2) *
          (2 * (1 + y) / (rhoStar - 2 * y)) := hmul
      _ = 1 + y := by field_simp [hden.ne']
  have hF := bankF_twice_alt y
  nlinarith

theorem bankF_hasDerivAt {y : ℝ} (hy : y ≤ 0) :
    HasDerivAt bankF (activeThreshold y - 1) y := by
  have hA := activeThreshold_hasDerivAt hy
  unfold bankF
  have hraw :=
    ((((hasDerivAt_id y).sub_const RStar).mul
        (hA.sub_const 1)).add
      (hA.mul ((hasDerivAt_const y 1).add (hasDerivAt_id y)))).div_const 2
  convert hraw using 1
  simp only [id_eq, Pi.add_apply]
  have hden := (active_denominator_pos hy).ne'
  have hfrac :
      (y - RStar) * (1 / (rhoStar - 2 * y)) +
          (1 / (rhoStar - 2 * y)) * (1 + y) = -1 := by
    unfold RStar
    rw [one_div]
    calc
      (y - (1 + rhoStar)) * (rhoStar - 2 * y)⁻¹ +
          (rhoStar - 2 * y)⁻¹ * (1 + y) =
          -((rhoStar - 2 * y) * (rhoStar - 2 * y)⁻¹) := by ring
      _ = -1 := by rw [mul_inv_cancel₀ hden]
  nlinarith

theorem bankF_deriv {y : ℝ} (hy : y ≤ 0) :
    deriv bankF y = activeThreshold y - 1 :=
  (bankF_hasDerivAt hy).deriv

theorem bankH_hasDerivAt {y : ℝ} (hy : y ≤ 0) :
    HasDerivAt bankH (bankHPrime y) y := by
  unfold bankH bankHPrime
  convert (activeThreshold_hasDerivAt hy).mul
    ((hasDerivAt_const y 1).add (hasDerivAt_id y)) using 1
  simp only [id_eq, Pi.add_apply]
  ring

theorem bankH_nonneg {y : ℝ} (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    0 ≤ bankH y := by
  unfold bankH
  exact mul_nonneg (by linarith [activeThreshold_ge_one hyLower hyUpper])
    (by linarith)

theorem bankHPrime_nonneg {y : ℝ} (hyLower : -1 ≤ y)
    (hyUpper : y ≤ 0) :
    0 ≤ bankHPrime y := by
  unfold bankHPrime
  have hA := activeThreshold_ge_one hyLower hyUpper
  have hfrac : 0 ≤ (1 + y) / (rhoStar - 2 * y) :=
    div_nonneg (by linarith) (active_denominator_pos hyUpper).le
  linarith

theorem canonical_immediate (y : ℝ) :
    -2 * bankF y + (y - RStar) * (activeThreshold y - 1) +
      activeThreshold y * (1 + y) = 0 := by
  unfold bankF
  ring

theorem canonical_deferred (y : ℝ) :
    1 - 2 * bankF y + (y - rhoStar) * (activeThreshold y - 1) +
      activeThreshold y * y = 0 := by
  have hI := canonical_immediate y
  unfold RStar at hI
  linarith

theorem canonical_zero (y : ℝ) :
    -2 * bankF y + y * (activeThreshold y - 1) =
      activeThreshold y * (rhoStar - y) - RStar := by
  have hI := canonical_immediate y
  unfold RStar at hI ⊢
  linarith

theorem canonical_zero_nonpos {y : ℝ}
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    -2 * bankF y + y * (activeThreshold y - 1) ≤ 0 := by
  rw [canonical_zero]
  exact sub_nonpos.mpr (activeThreshold_mul_le_RStar hyLower hyUpper)

theorem canonical_h (y : ℝ) :
    bankH y + (rhoStar - y) * bankHPrime y =
      activeThreshold y * RStar +
        (rhoStar - y) * (1 + y) / (rhoStar - 2 * y) := by
  unfold bankH bankHPrime RStar
  ring

theorem canonical_h_lower {y : ℝ}
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    activeThreshold y * RStar ≤
      bankH y + (rhoStar - y) * bankHPrime y := by
  rw [canonical_h]
  have : 0 ≤ (rhoStar - y) * (1 + y) / (rhoStar - 2 * y) :=
    div_nonneg
      (mul_nonneg (by linarith [rhoStar_pos]) (by linarith))
      (active_denominator_pos hyUpper).le
  linarith

/-! ## Active-region first-order drifts -/

def activeG (y b : ℝ) : ℝ :=
  bankF y + b * bankH y + RStar * b ^ 2 / 2

def activeGy (y b : ℝ) : ℝ :=
  activeThreshold y - 1 + b * bankHPrime y

def activeGb (y b : ℝ) : ℝ :=
  bankH y + RStar * b

def driftZ (G Gy Gb y b : ℝ) : ℝ := -2 * G + y * Gy + b * Gb

def driftE (G Gy Gb y b : ℝ) : ℝ :=
  -2 * G + (y - RStar) * Gy + (b + 1) * Gb

def driftI (G Gy Gb y b A : ℝ) : ℝ :=
  -2 * G + (y - RStar) * Gy + b * Gb + A * (1 + y + RStar * b)

def driftQ (G Gy Gb y b A : ℝ) : ℝ :=
  1 - 2 * G + (y - rhoStar) * Gy + b * Gb + A * (y + RStar * b)

theorem active_driftZ_identity (y b : ℝ) :
    driftZ (activeG y b) (activeGy y b) (activeGb y b) y b =
      (-2 * bankF y + y * (activeThreshold y - 1)) +
        b * (-bankH y + y * bankHPrime y) := by
  unfold driftZ activeG activeGy activeGb
  ring

theorem active_driftE_identity (y b : ℝ) :
    driftE (activeG y b) (activeGy y b) (activeGb y b) y b =
      b * (-bankH y + (y - RStar) * bankHPrime y + RStar) := by
  unfold driftE activeG activeGy activeGb
  have hI := canonical_immediate y
  unfold bankH at *
  ring_nf at hI ⊢
  linarith

theorem active_driftI_identity (y b : ℝ) :
    driftI (activeG y b) (activeGy y b) (activeGb y b) y b
        (activeThreshold y) =
      b * (-bankH y + (y - RStar) * bankHPrime y +
        activeThreshold y * RStar) := by
  unfold driftI activeG activeGy activeGb
  have hI := canonical_immediate y
  ring_nf at hI ⊢
  linarith

theorem active_driftQ_identity (y b : ℝ) :
    driftQ (activeG y b) (activeGy y b) (activeGb y b) y b
        (activeThreshold y) =
      b * (-bankH y + (y - rhoStar) * bankHPrime y +
        activeThreshold y * RStar) := by
  unfold driftQ activeG activeGy activeGb
  have hQ := canonical_deferred y
  ring_nf at hQ ⊢
  linarith

/-- All four infinitesimal bank checks in the changing-threshold region. -/
theorem active_all_drifts_nonpos {y b : ℝ}
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) (hb : 0 ≤ b) :
    driftZ (activeG y b) (activeGy y b) (activeGb y b) y b ≤ 0 ∧
    driftE (activeG y b) (activeGy y b) (activeGb y b) y b ≤ 0 ∧
    driftI (activeG y b) (activeGy y b) (activeGb y b) y b
        (activeThreshold y) ≤ 0 ∧
    driftQ (activeG y b) (activeGy y b) (activeGb y b) y b
        (activeThreshold y) ≤ 0 := by
  have hH := bankH_nonneg hyLower hyUpper
  have hHp := bankHPrime_nonneg hyLower hyUpper
  have hA := activeThreshold_ge_one hyLower hyUpper
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  have hZbase := canonical_zero_nonpos hyLower hyUpper
  have hZcoef : -bankH y + y * bankHPrime y ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hyUpper hHp]
  have hQcoef :
      -bankH y + (y - rhoStar) * bankHPrime y +
          activeThreshold y * RStar ≤ 0 := by
    have hh := canonical_h_lower hyLower hyUpper
    nlinarith
  have hIcoef :
      -bankH y + (y - RStar) * bankHPrime y +
          activeThreshold y * RStar ≤ 0 := by
    unfold RStar at hQcoef ⊢
    nlinarith
  have hEcoef :
      -bankH y + (y - RStar) * bankHPrime y + RStar ≤ 0 := by
    have hAR : RStar ≤ activeThreshold y * RStar := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) hR.le]
    linarith
  constructor
  · rw [active_driftZ_identity]
    exact add_nonpos hZbase (mul_nonpos_of_nonneg_of_nonpos hb hZcoef)
  constructor
  · rw [active_driftE_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hEcoef
  constructor
  · rw [active_driftI_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hIcoef
  · rw [active_driftQ_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hQcoef

theorem activeG_nonneg {y b : ℝ}
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) (hb : 0 ≤ b) :
    0 ≤ activeG y b := by
  unfold activeG
  have hf := bankF_nonneg hyLower hyUpper
  have hh := bankH_nonneg hyLower hyUpper
  have hR : 0 ≤ RStar := (lt_trans zero_lt_one one_lt_RStar).le
  positivity

/-! ## Saturated (flat) region -/

def positivePart (t : ℝ) : ℝ := max t 0

def flatG (η : ℝ) : ℝ := positivePart (1 + η) ^ 2 / (2 * RStar)

/-- A convenient explicit representative of `g'`; it is also the derivative
at the join because the positive-part square is `C¹`. -/
def flatGPrime (η : ℝ) : ℝ := positivePart (1 + η) / RStar

def flatDriftZ (η : ℝ) : ℝ := -2 * flatG η + η * flatGPrime η

def flatDriftI (η : ℝ) : ℝ :=
  -2 * flatG η + (η - RStar) * flatGPrime η + 1 + η

def flatDriftQ (η : ℝ) : ℝ :=
  1 - 2 * flatG η + (η - rhoStar) * flatGPrime η + η

theorem flatG_nonneg (η : ℝ) : 0 ≤ flatG η := by
  unfold flatG
  exact div_nonneg (sq_nonneg _) (by
    nlinarith [lt_trans zero_lt_one one_lt_RStar])

theorem flat_all_drifts_nonpos {η : ℝ} :
    flatDriftZ η ≤ 0 ∧ flatDriftI η ≤ 0 ∧ flatDriftQ η ≤ 0 := by
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  by_cases hlow : η ≤ -1
  · have hpart : positivePart (1 + η) = 0 := by
      unfold positivePart
      rw [max_eq_right]
      linarith
    simp [flatDriftZ, flatDriftI, flatDriftQ, flatG, flatGPrime, hpart]; linarith
  · have hηlower : -1 ≤ η := le_of_not_ge hlow
    have hpart : positivePart (1 + η) = 1 + η := by
      unfold positivePart
      rw [max_eq_left]
      linarith
    rw [flatDriftZ, flatDriftI, flatDriftQ, flatG, flatGPrime,
      hpart]
    constructor
    · field_simp [hR.ne']
      nlinarith
    constructor
    · field_simp [hR.ne']
      nlinarith
    · unfold RStar at hR ⊢
      field_simp [hR.ne']
      ring_nf
      norm_num

/-! ## The glued normalized potential -/

def bankG (y b : ℝ) : ℝ :=
  if -1 ≤ y then activeG y b else flatG (y + RStar * b)

/-- At the regional interface, feasible active and flat formulas have the
same value. -/
theorem bankG_interface {b : ℝ} (hb0 : 0 ≤ b)
    : activeG (-1) b = flatG (-1 + RStar * b) := by
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  have hpart : positivePart (RStar * b) = RStar * b := by
    unfold positivePart
    rw [max_eq_left]
    positivity
  rw [activeG, bankF_at_neg_one]
  have hh : bankH (-1) = 0 := by
    simp [bankH, activeThreshold_at_neg_one]
  rw [hh]
  unfold flatG
  rw [show 1 + (-1 + RStar * b) = RStar * b by ring, hpart]
  field_simp [hR.ne']
  ring

theorem bankG_nonneg {y b : ℝ} (hy : y ≤ 0) (hb : 0 ≤ b) :
    0 ≤ bankG y b := by
  unfold bankG
  split_ifs with hactive
  · exact activeG_nonneg hactive hy hb
  · exact flatG_nonneg _

/-- Homogeneous raw-coordinate bank balance.  Defining the `x=0` value
separately makes terminal telescoping statements total. -/
def bankW (x S e d : ℝ) : ℝ :=
  if x = 0 then 0
  else
    let η := (d - RStar * S) / x
    let b := e / x
    let y := η - RStar * b
    x * d + x ^ 2 * bankG y b

theorem bankW_at_terminal (S e d : ℝ) :
    bankW 0 S e d = 0 := by
  simp [bankW]

theorem bankW_initial {n : ℝ} (hn : n ≠ 0) :
    bankW n 0 0 0 = rhoStar * n ^ 2 / 2 := by
  simp [bankW, hn, bankG, activeG, bankF_at_zero]
  ring

end

end SchedulingPaper
