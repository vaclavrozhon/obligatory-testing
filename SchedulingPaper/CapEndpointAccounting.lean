import SchedulingPaper.CappedBankAccounting

/-!
# Exact accounting of the capped endpoint

Before the cap reserve can be applied, the exact fifth local charge has to be
compared with the hypothetical ordinary deferred (`Q`) charge.  This file
formalizes that comparison, the state inequality `y ≤ -cq`, and the
logarithmic residual bound used by the reserve.
-/

namespace SchedulingPaper

noncomputable section

/-- The ordinary deferred local charge at counts `(I,d,K)`. -/
def ordinaryDeferredCharge (c a I d K : ℝ) : ℝ :=
  let P := I + d + K
  let D := d + K
  D + a * (D - (1 + c) * P)

/-- The self-interaction coefficient of one capped endpoint. -/
def cappedSelfCoefficient (c u : ℝ) : ℝ :=
  1 + u - (1 + c) * (u - 1)

/-- The exact fifth-endpoint charge from the pair allocation. -/
def exactCappedCharge
    (c u _I d K immediateSum deferredSum : ℝ) : ℝ :=
  d - (1 + c) * immediateSum - c * deferredSum +
    K * cappedSelfCoefficient c u

/-- Exact identity (cap charge minus the hypothetical `Q` charge). -/
theorem exactCappedCharge_sub_ordinaryDeferredCharge
    (c u a I d K immediateSum deferredSum : ℝ) :
    exactCappedCharge c u I d K immediateSum deferredSum -
        ordinaryDeferredCharge c a I d K =
      (1 + c) * (a * I - immediateSum) +
        c * (a * d - deferredSum) +
        K * (1 - c * (u - 1 - a)) := by
  unfold exactCappedCharge ordinaryDeferredCharge
    cappedSelfCoefficient
  dsimp only
  ring

/-- Threshold monotonicity removes the two historic-sum errors. -/
theorem exactCappedCharge_sub_ordinary_le
    {c u a I d K immediateSum deferredSum : ℝ}
    (hc : 0 ≤ c)
    (hImmediate : a * I ≤ immediateSum)
    (hDeferred : a * d ≤ deferredSum) :
    exactCappedCharge c u I d K immediateSum deferredSum -
        ordinaryDeferredCharge c a I d K ≤
      K * (1 - c * (u - 1 - a)) := by
  rw [exactCappedCharge_sub_ordinaryDeferredCharge]
  have hC : 0 ≤ 1 + c := by linarith
  have hfirst :
      (1 + c) * (a * I - immediateSum) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hC (sub_nonpos.mpr hImmediate)
  have hsecond :
      c * (a * d - deferredSum) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hDeferred)
  linarith

/-! ## The logarithmic cap residual -/

theorem cap_bound_threshold_identity {c u q : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) :
    1 - c * (u - 1 - parameterizedThreshold c (-c * q)) =
      c * (capGap c u - (1 / 2) * Real.log (1 + 2 * q)) := by
  have hy : -c * q ≤ 0 := by
    nlinarith [mul_nonneg hc.le hq]
  rw [parameterizedThreshold_eq_log_div hc hy]
  have hqden : 0 < 1 + 2 * q := by linarith
  have hcarg : 0 < 1 + 2 / c := by positivity
  have hratio :
      (c + 2) / (c - 2 * (-c * q)) =
        (1 + 2 / c) / (1 + 2 * q) := by
    field_simp [hc.ne', hqden.ne']
    ring
  rw [hratio, Real.log_div hcarg.ne' hqden.ne']
  unfold capGap capReference
  field_simp [hc.ne']
  ring

/-- On the active cap cone, the saturated threshold at an arbitrary feasible
state is no larger than the analytic threshold at `-cq`. -/
theorem parameterizedAdaptiveThreshold_le_cap_bound
    {c q y : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (hcq : c * q ≤ 1) (hy : y ≤ 0) (hyCap : y ≤ -c * q) :
    parameterizedAdaptiveThreshold c y ≤
      parameterizedThreshold c (-c * q) := by
  unfold parameterizedAdaptiveThreshold
  split_ifs with hflat
  · have hLower : -1 ≤ -c * q := by linarith
    exact parameterizedThreshold_ge_one hc hLower
      (by nlinarith [mul_nonneg hc.le hq])
  · have hbound0 : -c * q ≤ 0 := by
      nlinarith [mul_nonneg hc.le hq]
    exact (parameterizedThreshold_monoOn_Iic hc)
      (show y ∈ Set.Iic 0 from hy)
      (show -c * q ∈ Set.Iic 0 from hbound0)
      hyCap

theorem cap_actual_bracket_le_residual
    {c u q y : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (hcq : c * q ≤ 1) (hy : y ≤ 0) (hyCap : y ≤ -c * q) :
    1 - c *
        (u - 1 - parameterizedAdaptiveThreshold c y) ≤
      c * (capGap c u - (1 / 2) * Real.log (1 + 2 * q)) := by
  have hthreshold :=
    parameterizedAdaptiveThreshold_le_cap_bound hc hq hcq hy hyCap
  have hscaled :=
    mul_le_mul_of_nonneg_left hthreshold hc.le
  rw [← cap_bound_threshold_identity hc hq]
  linarith

/-- Feasibility alone gives the state inequality `y ≤ -cq`. -/
theorem parameterized_state_y_le_neg_cq
    {c : ℝ} (hc : 0 ≤ c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    s.y c ≤ -c * s.q := by
  have hx : 0 < s.x := hs.1
  have hC : 0 ≤ 1 + c := by linarith
  have hDP : s.deferred ≤ s.substantive :=
    hs.2.2.2.2.2.1
  have hKP : s.capped ≤ s.substantive :=
    hs.2.2.2.2.2.2
  have hEP : 0 ≤ s.epsilon := hs.2.2.1
  have hcK :
      c * s.capped ≤ c * s.substantive :=
    mul_le_mul_of_nonneg_left hKP hc
  have hraw :
      s.deferred - (1 + c) *
          (s.substantive + s.epsilon) ≤
        -c * s.capped := by
    nlinarith [mul_nonneg hC hEP]
  have hyFormula :
      s.y c =
        (s.deferred - (1 + c) *
          (s.substantive + s.epsilon)) / s.x := by
    unfold ParameterizedAnalysisState.y
      ParameterizedAnalysisState.eta
      ParameterizedAnalysisState.b
    field_simp [hx.ne']
    ring
  rw [hyFormula]
  unfold ParameterizedAnalysisState.q
  rw [show -c * (s.capped / s.x) =
    (-c * s.capped) / s.x by ring]
  rw [div_le_div_iff_of_pos_right hx]
  exact hraw

theorem parameterized_state_threshold_eq_adaptive
    (c : ℝ) (s : ParameterizedAnalysisState) :
    s.threshold c =
      parameterizedAdaptiveThreshold c (s.y c) := by
  unfold ParameterizedAnalysisState.threshold
    parameterizedAdaptiveThreshold
  by_cases hlow : s.y c ≤ -1
  · by_cases hupp : -1 ≤ s.y c
    · have heq : s.y c = -1 := le_antisymm hlow hupp
      simp [heq]
    · simp [hlow, hupp]
  · have hstrict : -1 < s.y c := lt_of_not_ge hlow
    simp [not_le.mpr hstrict, hstrict.le]

theorem ordinaryDeferredCharge_eq_stateReward
    {c I d K : ℝ} {s : ParameterizedAnalysisState}
    (hx : 0 < s.x)
    (hP : s.substantive = I + d + K)
    (hD : s.deferred = d + K) :
    ordinaryDeferredCharge c
        (parameterizedAdaptiveThreshold c (s.y c)) I d K =
      parameterizedOrdinaryReward c s .cap := by
  rw [parameterizedOrdinaryReward]
  rw [parameterized_state_threshold_eq_adaptive]
  unfold ordinaryDeferredCharge ParameterizedAnalysisState.eta
  dsimp only
  rw [hP, hD]
  field_simp [hx.ne']

/-- The exact capped local charge is bounded by the envelope used in
`CappedBankAccounting`. -/
theorem exactCappedCharge_le_reserveEnvelope
    {c u x y I d K immediateSum deferredSum : ℝ}
    (hc : 0 < c) (hx : 0 < x) (hK : 0 ≤ K)
    (hcq : c * (K / x) ≤ 1)
    (hy : y ≤ 0) (hyCap : y ≤ -c * (K / x))
    (hImmediate :
      parameterizedAdaptiveThreshold c y * I ≤ immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold c y * d ≤ deferredSum) :
    exactCappedCharge c u I d K immediateSum deferredSum ≤
      ordinaryDeferredCharge c
          (parameterizedAdaptiveThreshold c y) I d K +
        x * capResidual c (capGap c u) (K / x) := by
  have hcharge :=
    exactCappedCharge_sub_ordinary_le
      (c := c) (u := u)
      (a := parameterizedAdaptiveThreshold c y)
      (I := I) (d := d) (K := K)
      (immediateSum := immediateSum)
      (deferredSum := deferredSum) hc.le
      hImmediate hDeferred
  have hbracket :=
    cap_actual_bracket_le_residual
      (c := c) (u := u) (q := K / x) (y := y) hc
      (div_nonneg hK hx.le) hcq hy hyCap
  have hscaled :=
    mul_le_mul_of_nonneg_left hbracket hK
  have hresidual :
      x * capResidual c (capGap c u) (K / x) =
        K * (c * (capGap c u -
          (1 / 2) * Real.log (1 + 2 * (K / x)))) := by
    unfold capResidual
    field_simp [hx.ne']
  rw [hresidual]
  linarith

/-! ## Mixed-branch specialization -/

theorem mixed_state_active_cap_bracket
    (c : MixedRatioDomain) {s : ParameterizedAnalysisState}
    (hs : s.Feasible)
    (hactive : reserveMu s.q ≤ (mixedMass c : ℝ)) :
    1 - (c : ℝ) *
        (mixedUpperCurve c - 1 -
          parameterizedAdaptiveThreshold c (s.y c)) ≤
      (c : ℝ) * (mixedReserveDelta c -
        (1 / 2) * Real.log (1 + 2 * s.q)) := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  exact cap_actual_bracket_le_residual hc
    (s.q_nonneg hs)
    (mixed_active_cq_le_one c (s.q_nonneg hs) hactive)
    (s.y_nonpos hc.le hs)
    (parameterized_state_y_le_neg_cq hc.le hs)

theorem mixed_exactCappedCharge_le_reserveEnvelope
    (c : MixedRatioDomain)
    {x y I d K immediateSum deferredSum : ℝ}
    (hx : 0 < x) (hK : 0 ≤ K)
    (hactive :
      reserveMu (K / x) ≤ (mixedMass c : ℝ))
    (hy : y ≤ 0) (hyCap : y ≤ -(c : ℝ) * (K / x))
    (hImmediate :
      parameterizedAdaptiveThreshold c y * I ≤ immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold c y * d ≤ deferredSum) :
    exactCappedCharge c (mixedUpperCurve c)
        I d K immediateSum deferredSum ≤
      ordinaryDeferredCharge c
          (parameterizedAdaptiveThreshold c y) I d K +
        x * capResidual c (mixedReserveDelta c) (K / x) := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  rw [mixedReserveDelta]
  exact exactCappedCharge_le_reserveEnvelope hc hx hK
    (mixed_active_cq_le_one c (div_nonneg hK hx.le) hactive)
    hy hyCap hImmediate hDeferred

theorem mixed_c_mul_one_add_mass_le_one (c : MixedRatioDomain) :
    (c : ℝ) * (1 + (mixedMass c : ℝ)) ≤ 1 := by
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hfirst :
      (c : ℝ) * (1 + (mixedMass c : ℝ)) ≤
        (1 / goldenRatio) * (1 + (mixedMass c : ℝ)) :=
    mul_le_mul_of_nonneg_right c.property.2 (by linarith)
  have hsecond :
      (1 / goldenRatio) * (1 + (mixedMass c : ℝ)) ≤
        (1 / goldenRatio) * (1 + 1 / goldenRatio) :=
    mul_le_mul_of_nonneg_left
      (by linarith [(mixedMass c).property.2])
      inv_goldenRatio_pos.le
  have heq :
      (1 / goldenRatio) * (1 + 1 / goldenRatio) = 1 := by
    rw [inv_goldenRatio_eq_sub_one]
    nlinarith [goldenRatio_sq]
  linarith

theorem mixed_flat_cap_bracket_nonpos (c : MixedRatioDomain) :
    1 - (c : ℝ) * (mixedUpperCurve c - 1 - 1) ≤ 0 := by
  have hc : (c : ℝ) ≠ 0 :=
    (rhoStar_pos.trans_le c.property.1).ne'
  have hcm := mixed_c_mul_one_add_mass_le_one c
  unfold mixedUpperCurve mixedUpperParameter
  have hid :
      1 - (c : ℝ) *
          (1 + 2 / (c : ℝ) - (mixedMass c : ℝ) - 1 - 1) =
        (c : ℝ) * (1 + (mixedMass c : ℝ)) - 1 := by
    field_simp [hc]
    ring
  rw [hid]
  linarith

/-- Once the reserve has switched off, the exact fifth charge is already no
larger than the ordinary deferred charge. -/
theorem mixed_inactive_cap_bracket_nonpos
    (c : MixedRatioDomain) {q y : ℝ}
    (hq : 0 ≤ q)
    (hcut : (mixedMass c : ℝ) ≤ reserveMu q)
    (hy : y ≤ 0) (hyCap : y ≤ -(c : ℝ) * q) :
    1 - (c : ℝ) *
        (mixedUpperCurve c - 1 -
          parameterizedAdaptiveThreshold c y) ≤ 0 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  by_cases hcq : (c : ℝ) * q ≤ 1
  · have hbound :=
      cap_actual_bracket_le_residual
        (c := (c : ℝ)) (u := mixedUpperCurve c)
        (q := q) (y := y) hc hq hcq hy hyCap
    have hmu1 : reserveMu q < 1 := reserveMu_lt_one hq
    have hartanh :
        Real.artanh (mixedMass c) ≤ Real.artanh (reserveMu q) :=
      Real.artanh_le_artanh
        (by linarith [(mixedMass c).property.1]) hmu1 hcut
    have hrhs :
        (c : ℝ) * (capGap c (mixedUpperCurve c) -
          (1 / 2) * Real.log (1 + 2 * q)) ≤ 0 := by
      rw [mixed_capGap_eq_artanh,
        ← artanh_reserveMu_eq_half_log hq]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le
        (sub_nonpos.mpr hartanh)
    linarith
  · have hcq' : 1 < (c : ℝ) * q := lt_of_not_ge hcq
    have hyFlat : y ≤ -1 := by linarith
    have hthreshold :
        parameterizedAdaptiveThreshold c y = 1 := by
      simp [parameterizedAdaptiveThreshold, hyFlat]
    rw [hthreshold]
    exact mixed_flat_cap_bracket_nonpos c

theorem mixed_exactCappedCharge_le_ordinary_of_inactive
    (c : MixedRatioDomain)
    {q y I d K immediateSum deferredSum : ℝ}
    (hK : 0 ≤ K)
    (hq : 0 ≤ q)
    (hcut : (mixedMass c : ℝ) ≤ reserveMu q)
    (hy : y ≤ 0) (hyCap : y ≤ -(c : ℝ) * q)
    (hImmediate :
      parameterizedAdaptiveThreshold c y * I ≤ immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold c y * d ≤ deferredSum) :
    exactCappedCharge c (mixedUpperCurve c)
        I d K immediateSum deferredSum ≤
      ordinaryDeferredCharge c
        (parameterizedAdaptiveThreshold c y) I d K := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hcharge :=
    exactCappedCharge_sub_ordinary_le
      (c := (c : ℝ)) (u := mixedUpperCurve c)
      (a := parameterizedAdaptiveThreshold c y)
      (I := I) (d := d) (K := K)
      (immediateSum := immediateSum)
      (deferredSum := deferredSum)
      hc.le hImmediate hDeferred
  have hbracket :=
    mixed_inactive_cap_bracket_nonpos c hq hcut hy hyCap
  have hscaled :=
    mul_nonpos_of_nonneg_of_nonpos hK hbracket
  linarith

/-- State-level form used by the five-endpoint bank: the exact cap charge is
bounded by the piecewise mixed envelope on both sides of the reserve cutoff. -/
theorem mixed_exactCappedCharge_le_stateEnvelope
    (c : MixedRatioDomain)
    {s : ParameterizedAnalysisState}
    {I d immediateSum deferredSum : ℝ}
    (hs : s.Feasible)
    (hP : s.substantive = I + d + s.capped)
    (hD : s.deferred = d + s.capped)
    (hImmediate :
      parameterizedAdaptiveThreshold c (s.y c) * I ≤ immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold c (s.y c) * d ≤ deferredSum) :
    exactCappedCharge c (mixedUpperCurve c)
        I d s.capped immediateSum deferredSum ≤
      mixedCappedEnvelopeReward c s .cap := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hq : 0 ≤ s.q := s.q_nonneg hs
  have hK : 0 ≤ s.capped := hs.2.2.2.2.1
  have hy : s.y c ≤ 0 := s.y_nonpos hc.le hs
  have hyCap :
      s.y c ≤ -(c : ℝ) * s.q :=
    parameterized_state_y_le_neg_cq hc.le hs
  have hordinary :=
    ordinaryDeferredCharge_eq_stateReward
      (c := (c : ℝ)) (I := I) (d := d)
      (K := s.capped) (s := s) hs.1 hP hD
  by_cases hactive :
      reserveMu s.q ≤ (mixedMass c : ℝ)
  · have hcap :=
      mixed_exactCappedCharge_le_reserveEnvelope
        c hs.1 hK hactive hy hyCap hImmediate hDeferred
    rw [hordinary] at hcap
    simpa [mixedCappedEnvelopeReward, hactive] using hcap
  · have hcut :
        (mixedMass c : ℝ) ≤ reserveMu s.q :=
      le_of_not_ge hactive
    have hcap :=
      mixed_exactCappedCharge_le_ordinary_of_inactive
        c hK hq hcut hy hyCap hImmediate hDeferred
    rw [hordinary] at hcap
    simpa [mixedCappedEnvelopeReward, hactive] using hcap

end

end SchedulingPaper
