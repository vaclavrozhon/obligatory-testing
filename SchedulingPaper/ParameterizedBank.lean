import SchedulingPaper.BankPotential

/-!
# The parameterized four-endpoint bank

This file is the scalar certificate used on the finite-cap mixed branch.
The parameter `c` is the excess competitive ratio and `C = 1 + c` is the
target coefficient.  At `c = rhoStar` all formulas specialize to the
obligatory-testing bank in `BankPotential`.
-/

namespace SchedulingPaper

noncomputable section

/-! ## The parameterized threshold -/

/-- The varying part of the threshold with excess ratio `c`. -/
def parameterizedThreshold (c y : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) *
    (Real.log (c + 2) - Real.log (c - 2 * y))

/-- The actual threshold, saturated at one below `y = -1`. -/
def parameterizedAdaptiveThreshold (c y : ℝ) : ℝ :=
  if y ≤ -1 then 1 else parameterizedThreshold c y

theorem parameterized_denominator_pos {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    0 < c - 2 * y := by
  linarith

theorem parameterized_numerator_pos {c : ℝ} (hc : 0 < c) :
    0 < c + 2 := by
  linarith

theorem parameterizedThreshold_eq_log_div {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    parameterizedThreshold c y =
      1 + (1 / 2 : ℝ) * Real.log ((c + 2) / (c - 2 * y)) := by
  unfold parameterizedThreshold
  rw [Real.log_div (parameterized_numerator_pos hc).ne'
    (parameterized_denominator_pos hc hy).ne']

@[simp]
theorem parameterizedThreshold_at_neg_one (c : ℝ) :
    parameterizedThreshold c (-1) = 1 := by
  unfold parameterizedThreshold
  ring_nf

@[simp]
theorem parameterizedAdaptiveThreshold_at_neg_one (c : ℝ) :
    parameterizedAdaptiveThreshold c (-1) = 1 := by
  simp [parameterizedAdaptiveThreshold]

theorem parameterizedAdaptiveThreshold_eq_active {c y : ℝ}
    (hy : -1 < y) :
    parameterizedAdaptiveThreshold c y = parameterizedThreshold c y := by
  simp [parameterizedAdaptiveThreshold, not_le.mpr hy]

theorem parameterizedThreshold_hasDerivAt {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    HasDerivAt (parameterizedThreshold c)
      (1 / (c - 2 * y)) y := by
  have hinner :
      HasDerivAt (fun t : ℝ => c - 2 * t) (-2) y := by
    convert (hasDerivAt_const y c).sub
      ((hasDerivAt_const y 2).mul (hasDerivAt_id y)) using 1
    ring
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (c - 2 * t))
        ((c - 2 * y)⁻¹ * (-2)) y := by
    convert
      (Real.hasDerivAt_log
        (parameterized_denominator_pos hc hy).ne').comp y hinner using 1
  unfold parameterizedThreshold
  convert (hasDerivAt_const y 1).add
    ((hasDerivAt_const y (1 / 2 : ℝ)).mul
      ((hasDerivAt_const y (Real.log (c + 2))).sub hlog)) using 1
  field_simp [(parameterized_denominator_pos hc hy).ne']
  ring

theorem parameterizedThreshold_deriv {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    deriv (parameterizedThreshold c) y = 1 / (c - 2 * y) :=
  (parameterizedThreshold_hasDerivAt hc hy).deriv

theorem parameterizedThreshold_continuousOn_Iic {c : ℝ} (hc : 0 < c) :
    ContinuousOn (parameterizedThreshold c) (Set.Iic 0) := by
  intro y hy
  exact (parameterizedThreshold_hasDerivAt hc hy).continuousAt.continuousWithinAt

theorem parameterizedThreshold_strictMonoOn_Iic {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (parameterizedThreshold c) (Set.Iic 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic (0 : ℝ))
    (parameterizedThreshold_continuousOn_Iic hc) ?_
  intro y hy
  simp only [interior_Iic, Set.mem_Iio] at hy
  rw [(parameterizedThreshold_hasDerivAt hc hy.le).deriv]
  exact one_div_pos.mpr (parameterized_denominator_pos hc hy.le)

theorem parameterizedThreshold_monoOn_Iic {c : ℝ} (hc : 0 < c) :
    MonotoneOn (parameterizedThreshold c) (Set.Iic 0) :=
  (parameterizedThreshold_strictMonoOn_Iic hc).monotoneOn

theorem parameterizedThreshold_ge_one {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    1 ≤ parameterizedThreshold c y := by
  have hden := parameterized_denominator_pos hc hyUpper
  have hratio : 1 ≤ (c + 2) / (c - 2 * y) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [parameterizedThreshold_eq_log_div hc hyUpper]
  linarith [Real.log_nonneg hratio]

/-- The sign inequality needed by the zero endpoint. -/
theorem parameterizedThreshold_mul_le_target {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    parameterizedThreshold c y * (c - y) ≤ 1 + c := by
  let q := (c + 2) / (c - 2 * y)
  have hden := parameterized_denominator_pos hc hyUpper
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (parameterized_numerator_pos hc) hden
  have hlog : Real.log q ≤ q - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  have hqsub :
      q - 1 = 2 * (1 + y) / (c - 2 * y) := by
    dsimp [q]
    field_simp [hden.ne']
    ring
  rw [hqsub] at hlog
  have hleft : 0 ≤ (1 / 2 : ℝ) * (c - y) := by
    exact mul_nonneg (by norm_num) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hlog hleft
  have hfrac : (c - y) / (c - 2 * y) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hone : 0 ≤ 1 + y := by linarith
  have hlast :
      ((c - y) / (c - 2 * y)) * (1 + y) ≤ 1 + y := by
    nlinarith [mul_le_mul_of_nonneg_right hfrac hone]
  have hmain :
      (1 / 2 : ℝ) * (c - y) * Real.log q ≤ 1 + y := by
    calc
      (1 / 2 : ℝ) * (c - y) * Real.log q
          ≤ (1 / 2 : ℝ) * (c - y) *
              (2 * (1 + y) / (c - 2 * y)) := by
                simpa [mul_assoc] using hscaled
      _ = ((c - y) / (c - 2 * y)) * (1 + y) := by ring
      _ ≤ 1 + y := hlast
  rw [parameterizedThreshold_eq_log_div hc hyUpper]
  change (1 + (1 / 2 : ℝ) * Real.log q) * (c - y) ≤ 1 + c
  nlinarith

/-! ## The active potential -/

/-- The primitive forced by the immediate-endpoint balance equation. -/
def parameterizedBankF (c y : ℝ) : ℝ :=
  ((y - (1 + c)) * (parameterizedThreshold c y - 1) +
    parameterizedThreshold c y * (1 + y)) / 2

def parameterizedBankH (c y : ℝ) : ℝ :=
  parameterizedThreshold c y * (1 + y)

def parameterizedBankHPrime (c y : ℝ) : ℝ :=
  parameterizedThreshold c y + (1 + y) / (c - 2 * y)

theorem parameterizedBankF_log_formula {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    parameterizedBankF c y =
      (1 + y) / 2 -
        (c - 2 * y) / 4 *
          Real.log ((c + 2) / (c - 2 * y)) := by
  rw [parameterizedBankF, parameterizedThreshold_eq_log_div hc hy]
  ring

theorem parameterizedBankF_at_zero_formula {c : ℝ} (hc : 0 < c) :
    parameterizedBankF c 0 =
      1 / 2 - c / 4 * Real.log (1 + 2 / c) := by
  rw [parameterizedBankF_log_formula hc le_rfl]
  have hratio : (c + 2) / (c - 2 * 0) = 1 + 2 / c := by
    field_simp [hc.ne']
    ring
  rw [hratio]
  ring

@[simp]
theorem parameterizedBankF_at_neg_one (c : ℝ) :
    parameterizedBankF c (-1) = 0 := by
  simp [parameterizedBankF]

theorem parameterizedBankF_twice_alt (c y : ℝ) :
    2 * parameterizedBankF c y =
      1 + y - (c - 2 * y) * (parameterizedThreshold c y - 1) := by
  unfold parameterizedBankF
  ring

theorem parameterizedBankF_nonneg {c y : ℝ}
    (hc : 0 < c) (_hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    0 ≤ parameterizedBankF c y := by
  let q := (c + 2) / (c - 2 * y)
  have hden := parameterized_denominator_pos hc hyUpper
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (parameterized_numerator_pos hc) hden
  have hlog : Real.log q ≤ q - 1 :=
    Real.log_le_sub_one_of_pos hqpos
  have hqsub :
      q - 1 = 2 * (1 + y) / (c - 2 * y) := by
    dsimp [q]
    field_simp [hden.ne']
    ring
  rw [hqsub] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (c - 2 * y) / 2 by positivity)
  have hbound :
      (c - 2 * y) * (parameterizedThreshold c y - 1) ≤ 1 + y := by
    have hAminus :
        parameterizedThreshold c y - 1 =
          (1 / 2 : ℝ) * Real.log q := by
      rw [parameterizedThreshold_eq_log_div hc hyUpper]
      ring
    rw [hAminus]
    calc
      (c - 2 * y) * ((1 / 2 : ℝ) * Real.log q) =
          ((c - 2 * y) / 2) * Real.log q := by ring
      _ ≤ ((c - 2 * y) / 2) *
          (2 * (1 + y) / (c - 2 * y)) := hmul
      _ = 1 + y := by field_simp [hden.ne']
  nlinarith [parameterizedBankF_twice_alt c y]

theorem parameterizedBankF_hasDerivAt {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    HasDerivAt (parameterizedBankF c)
      (parameterizedThreshold c y - 1) y := by
  have hA := parameterizedThreshold_hasDerivAt hc hy
  unfold parameterizedBankF
  have hraw :=
    ((((hasDerivAt_id y).sub_const (1 + c)).mul
        (hA.sub_const 1)).add
      (hA.mul ((hasDerivAt_const y 1).add
        (hasDerivAt_id y)))).div_const 2
  convert hraw using 1
  simp only [id_eq, Pi.add_apply]
  have hden := (parameterized_denominator_pos hc hy).ne'
  have hfrac :
      (y - (1 + c)) * (1 / (c - 2 * y)) +
          (1 / (c - 2 * y)) * (1 + y) = -1 := by
    rw [one_div]
    calc
      (y - (1 + c)) * (c - 2 * y)⁻¹ +
          (c - 2 * y)⁻¹ * (1 + y) =
          -((c - 2 * y) * (c - 2 * y)⁻¹) := by ring
      _ = -1 := by rw [mul_inv_cancel₀ hden]
  nlinarith

theorem parameterizedBankF_deriv {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    deriv (parameterizedBankF c) y =
      parameterizedThreshold c y - 1 :=
  (parameterizedBankF_hasDerivAt hc hy).deriv

theorem parameterizedBankH_hasDerivAt {c y : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) :
    HasDerivAt (parameterizedBankH c)
      (parameterizedBankHPrime c y) y := by
  unfold parameterizedBankH parameterizedBankHPrime
  convert (parameterizedThreshold_hasDerivAt hc hy).mul
    ((hasDerivAt_const y 1).add (hasDerivAt_id y)) using 1
  simp only [id_eq, Pi.add_apply]
  ring

theorem parameterizedBankH_nonneg {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    0 ≤ parameterizedBankH c y := by
  unfold parameterizedBankH
  exact mul_nonneg
    (by linarith [parameterizedThreshold_ge_one hc hyLower hyUpper])
    (by linarith)

theorem parameterizedBankHPrime_nonneg {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    0 ≤ parameterizedBankHPrime c y := by
  unfold parameterizedBankHPrime
  have hA := parameterizedThreshold_ge_one hc hyLower hyUpper
  have hfrac : 0 ≤ (1 + y) / (c - 2 * y) :=
    div_nonneg (by linarith) (parameterized_denominator_pos hc hyUpper).le
  linarith

theorem parameterized_canonical_immediate (c y : ℝ) :
    -2 * parameterizedBankF c y +
        (y - (1 + c)) * (parameterizedThreshold c y - 1) +
        parameterizedThreshold c y * (1 + y) = 0 := by
  unfold parameterizedBankF
  ring

theorem parameterized_canonical_deferred (c y : ℝ) :
    1 - 2 * parameterizedBankF c y +
        (y - c) * (parameterizedThreshold c y - 1) +
        parameterizedThreshold c y * y = 0 := by
  linarith [parameterized_canonical_immediate c y]

theorem parameterized_canonical_zero (c y : ℝ) :
    -2 * parameterizedBankF c y +
        y * (parameterizedThreshold c y - 1) =
      parameterizedThreshold c y * (c - y) - (1 + c) := by
  linarith [parameterized_canonical_immediate c y]

theorem parameterized_canonical_zero_nonpos {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    -2 * parameterizedBankF c y +
        y * (parameterizedThreshold c y - 1) ≤ 0 := by
  rw [parameterized_canonical_zero]
  exact sub_nonpos.mpr
    (parameterizedThreshold_mul_le_target hc hyLower hyUpper)

theorem parameterized_canonical_h (c y : ℝ) :
    parameterizedBankH c y +
        (c - y) * parameterizedBankHPrime c y =
      parameterizedThreshold c y * (1 + c) +
        (c - y) * (1 + y) / (c - 2 * y) := by
  unfold parameterizedBankH parameterizedBankHPrime
  ring

theorem parameterized_canonical_h_lower {c y : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0) :
    parameterizedThreshold c y * (1 + c) ≤
      parameterizedBankH c y +
        (c - y) * parameterizedBankHPrime c y := by
  rw [parameterized_canonical_h]
  have hnonneg :
      0 ≤ (c - y) * (1 + y) / (c - 2 * y) :=
    div_nonneg
      (mul_nonneg (by linarith) (by linarith))
      (parameterized_denominator_pos hc hyUpper).le
  linarith

/-! ## The four active-region Hamiltonians -/

def parameterizedActiveG (c y b : ℝ) : ℝ :=
  parameterizedBankF c y + b * parameterizedBankH c y +
    (1 + c) * b ^ 2 / 2

def parameterizedActiveGy (c y b : ℝ) : ℝ :=
  parameterizedThreshold c y - 1 +
    b * parameterizedBankHPrime c y

def parameterizedActiveGb (c y b : ℝ) : ℝ :=
  parameterizedBankH c y + (1 + c) * b

def parameterizedDriftZ (G Gy Gb y b : ℝ) : ℝ :=
  -2 * G + y * Gy + b * Gb

def parameterizedDriftE (c G Gy Gb y b : ℝ) : ℝ :=
  -2 * G + (y - (1 + c)) * Gy + (b + 1) * Gb

def parameterizedDriftI (c G Gy Gb y b A : ℝ) : ℝ :=
  -2 * G + (y - (1 + c)) * Gy + b * Gb +
    A * (1 + y + (1 + c) * b)

def parameterizedDriftQ (c G Gy Gb y b A : ℝ) : ℝ :=
  1 - 2 * G + (y - c) * Gy + b * Gb +
    A * (y + (1 + c) * b)

theorem parameterized_active_driftZ_identity (c y b : ℝ) :
    parameterizedDriftZ
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b =
      (-2 * parameterizedBankF c y +
        y * (parameterizedThreshold c y - 1)) +
      b * (-parameterizedBankH c y +
        y * parameterizedBankHPrime c y) := by
  unfold parameterizedDriftZ parameterizedActiveG
    parameterizedActiveGy parameterizedActiveGb
  ring

theorem parameterized_active_driftE_identity (c y b : ℝ) :
    parameterizedDriftE c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b =
      b * (-parameterizedBankH c y +
        (y - (1 + c)) * parameterizedBankHPrime c y + (1 + c)) := by
  unfold parameterizedDriftE parameterizedActiveG
    parameterizedActiveGy parameterizedActiveGb
  have hI := parameterized_canonical_immediate c y
  unfold parameterizedBankH at *
  ring_nf at hI ⊢
  linarith

theorem parameterized_active_driftI_identity (c y b : ℝ) :
    parameterizedDriftI c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b
        (parameterizedThreshold c y) =
      b * (-parameterizedBankH c y +
        (y - (1 + c)) * parameterizedBankHPrime c y +
        parameterizedThreshold c y * (1 + c)) := by
  unfold parameterizedDriftI parameterizedActiveG
    parameterizedActiveGy parameterizedActiveGb
  have hI := parameterized_canonical_immediate c y
  ring_nf at hI ⊢
  linarith

theorem parameterized_active_driftQ_identity (c y b : ℝ) :
    parameterizedDriftQ c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b
        (parameterizedThreshold c y) =
      b * (-parameterizedBankH c y +
        (y - c) * parameterizedBankHPrime c y +
        parameterizedThreshold c y * (1 + c)) := by
  unfold parameterizedDriftQ parameterizedActiveG
    parameterizedActiveGy parameterizedActiveGb
  have hQ := parameterized_canonical_deferred c y
  ring_nf at hQ ⊢
  linarith

theorem parameterized_active_all_drifts_nonpos {c y b : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0)
    (hb : 0 ≤ b) :
    parameterizedDriftZ
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b ≤ 0 ∧
    parameterizedDriftE c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b ≤ 0 ∧
    parameterizedDriftI c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b
        (parameterizedThreshold c y) ≤ 0 ∧
    parameterizedDriftQ c
        (parameterizedActiveG c y b)
        (parameterizedActiveGy c y b)
        (parameterizedActiveGb c y b) y b
        (parameterizedThreshold c y) ≤ 0 := by
  have hH :=
    parameterizedBankH_nonneg hc hyLower hyUpper
  have hHp :=
    parameterizedBankHPrime_nonneg hc hyLower hyUpper
  have hA :=
    parameterizedThreshold_ge_one hc hyLower hyUpper
  have hC : 0 < 1 + c := by linarith
  have hZbase :=
    parameterized_canonical_zero_nonpos hc hyLower hyUpper
  have hZcoef :
      -parameterizedBankH c y +
          y * parameterizedBankHPrime c y ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hyUpper hHp]
  have hQcoef :
      -parameterizedBankH c y +
          (y - c) * parameterizedBankHPrime c y +
          parameterizedThreshold c y * (1 + c) ≤ 0 := by
    have hh := parameterized_canonical_h_lower hc hyLower hyUpper
    nlinarith
  have hIcoef :
      -parameterizedBankH c y +
          (y - (1 + c)) * parameterizedBankHPrime c y +
          parameterizedThreshold c y * (1 + c) ≤ 0 := by
    nlinarith
  have hEcoef :
      -parameterizedBankH c y +
          (y - (1 + c)) * parameterizedBankHPrime c y +
          (1 + c) ≤ 0 := by
    have hAC :
        1 + c ≤ parameterizedThreshold c y * (1 + c) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) hC.le]
    linarith
  constructor
  · rw [parameterized_active_driftZ_identity]
    exact add_nonpos hZbase
      (mul_nonpos_of_nonneg_of_nonpos hb hZcoef)
  constructor
  · rw [parameterized_active_driftE_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hEcoef
  constructor
  · rw [parameterized_active_driftI_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hIcoef
  · rw [parameterized_active_driftQ_identity]
    exact mul_nonpos_of_nonneg_of_nonpos hb hQcoef

theorem parameterizedActiveG_nonneg {c y b : ℝ}
    (hc : 0 < c) (hyLower : -1 ≤ y) (hyUpper : y ≤ 0)
    (hb : 0 ≤ b) :
    0 ≤ parameterizedActiveG c y b := by
  unfold parameterizedActiveG
  have hf := parameterizedBankF_nonneg hc hyLower hyUpper
  have hh := parameterizedBankH_nonneg hc hyLower hyUpper
  have hC : 0 ≤ 1 + c := by linarith
  positivity

/-! ## The saturated region and the glued formula -/

def parameterizedFlatG (c η : ℝ) : ℝ :=
  positivePart (1 + η) ^ 2 / (2 * (1 + c))

def parameterizedFlatGPrime (c η : ℝ) : ℝ :=
  positivePart (1 + η) / (1 + c)

def parameterizedFlatDriftZ (c η : ℝ) : ℝ :=
  -2 * parameterizedFlatG c η + η * parameterizedFlatGPrime c η

def parameterizedFlatDriftI (c η : ℝ) : ℝ :=
  -2 * parameterizedFlatG c η +
    (η - (1 + c)) * parameterizedFlatGPrime c η + 1 + η

def parameterizedFlatDriftQ (c η : ℝ) : ℝ :=
  1 - 2 * parameterizedFlatG c η +
    (η - c) * parameterizedFlatGPrime c η + η

theorem parameterizedFlatG_nonneg {c : ℝ} (hc : 0 < c) (η : ℝ) :
    0 ≤ parameterizedFlatG c η := by
  unfold parameterizedFlatG
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem parameterized_flat_all_drifts_nonpos {c η : ℝ}
    (hc : 0 < c) :
    parameterizedFlatDriftZ c η ≤ 0 ∧
    parameterizedFlatDriftI c η ≤ 0 ∧
    parameterizedFlatDriftQ c η ≤ 0 := by
  have hC : 0 < 1 + c := by linarith
  by_cases hlow : η ≤ -1
  · have hpart : positivePart (1 + η) = 0 := by
      unfold positivePart
      rw [max_eq_right]
      linarith
    simp [parameterizedFlatDriftZ, parameterizedFlatDriftI,
      parameterizedFlatDriftQ, parameterizedFlatG,
      parameterizedFlatGPrime, hpart]
    linarith
  · have hηlower : -1 ≤ η := le_of_not_ge hlow
    have hpart : positivePart (1 + η) = 1 + η := by
      unfold positivePart
      rw [max_eq_left]
      linarith
    rw [parameterizedFlatDriftZ, parameterizedFlatDriftI,
      parameterizedFlatDriftQ, parameterizedFlatG,
      parameterizedFlatGPrime, hpart]
    constructor
    · field_simp [hC.ne']
      nlinarith
    constructor
    · field_simp [hC.ne']
      linarith
    · field_simp [hC.ne']
      ring_nf
      norm_num

def parameterizedBankG (c y b : ℝ) : ℝ :=
  if -1 ≤ y then parameterizedActiveG c y b
  else parameterizedFlatG c (y + (1 + c) * b)

theorem parameterizedBankG_interface {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) :
    parameterizedActiveG c (-1) b =
      parameterizedFlatG c (-1 + (1 + c) * b) := by
  have hC : 0 < 1 + c := by linarith
  have hpart :
      positivePart ((1 + c) * b) = (1 + c) * b := by
    unfold positivePart
    rw [max_eq_left]
    positivity
  rw [parameterizedActiveG, parameterizedBankF_at_neg_one]
  have hh : parameterizedBankH c (-1) = 0 := by
    simp [parameterizedBankH]
  rw [hh]
  unfold parameterizedFlatG
  rw [show 1 + (-1 + (1 + c) * b) = (1 + c) * b by ring,
    hpart]
  field_simp [hC.ne']
  ring

theorem parameterizedBankG_nonneg {c y b : ℝ}
    (hc : 0 < c) (hy : y ≤ 0) (hb : 0 ≤ b) :
    0 ≤ parameterizedBankG c y b := by
  unfold parameterizedBankG
  split_ifs with hactive
  · exact parameterizedActiveG_nonneg hc hactive hy hb
  · exact parameterizedFlatG_nonneg hc _

/-- Homogeneous raw-coordinate form of the reusable base bank. -/
def parameterizedBankW (c x P E D : ℝ) : ℝ :=
  if x = 0 then 0
  else
    let η := (D - (1 + c) * P) / x
    let b := E / x
    let y := η - (1 + c) * b
    x * D + x ^ 2 * parameterizedBankG c y b

@[simp]
theorem parameterizedBankW_terminal (c P E D : ℝ) :
    parameterizedBankW c 0 P E D = 0 := by
  simp [parameterizedBankW]

theorem parameterizedBankW_initial {c n : ℝ} (hn : n ≠ 0) :
    parameterizedBankW c n 0 0 0 =
      n ^ 2 * parameterizedBankF c 0 := by
  simp [parameterizedBankW, hn, parameterizedBankG,
    parameterizedActiveG]

/-! ## Exact specialization at the obligatory endpoint -/

theorem parameterizedThreshold_rhoStar (y : ℝ) :
    parameterizedThreshold rhoStar y = activeThreshold y := rfl

theorem parameterizedBankF_rhoStar (y : ℝ) :
    parameterizedBankF rhoStar y = bankF y := by
  rfl

theorem parameterizedBankH_rhoStar (y : ℝ) :
    parameterizedBankH rhoStar y = bankH y := rfl

theorem parameterizedActiveG_rhoStar (y b : ℝ) :
    parameterizedActiveG rhoStar y b = activeG y b := by
  unfold parameterizedActiveG activeG
  rw [parameterizedBankF_rhoStar, parameterizedBankH_rhoStar]
  rfl

theorem parameterizedFlatG_rhoStar (η : ℝ) :
    parameterizedFlatG rhoStar η = flatG η := rfl

theorem parameterizedBankG_rhoStar (y b : ℝ) :
    parameterizedBankG rhoStar y b = bankG y b := by
  unfold parameterizedBankG bankG
  split_ifs
  · exact parameterizedActiveG_rhoStar y b
  · exact parameterizedFlatG_rhoStar (y + RStar * b)

theorem parameterizedBankW_rhoStar (x P E D : ℝ) :
    parameterizedBankW rhoStar x P E D = bankW x P E D := by
  unfold parameterizedBankW bankW
  split_ifs
  · rfl
  · dsimp only
    rw [parameterizedBankG_rhoStar]
    rfl

end

end SchedulingPaper
