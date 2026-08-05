import SchedulingPaper.ParameterizedBank
import SchedulingPaper.MixedCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fifth-endpoint cap reserve

The ordinary four-endpoint bank is not sufficient when an outcome equals the
common upper cap.  This file formalizes the reserve used to pay that fifth
Hamiltonian.  It includes the mixed-curve gap identity, the integral reserve,
its active derivative, the logarithmic change of variables, exact
cancellation, nonnegativity, and the `C¹` cutoff identities.
-/

namespace SchedulingPaper

noncomputable section

open Set
open Filter
open scoped Interval

/-! ## The mixed-curve gap -/

/-- The reference cap `Z(c)` from the optional-upper proof. -/
def capReference (c : ℝ) : ℝ :=
  2 + 1 / c + (1 / 2) * Real.log (1 + 2 / c)

/-- The distance between the reference cap and a supplied cap. -/
def capGap (c u : ℝ) : ℝ := capReference c - u

/-- On the implicit mixed curve the cap gap is exactly `artanh m`. -/
theorem mixed_capGap_eq_artanh (c : MixedRatioDomain) :
    capGap c (mixedUpperCurve c) = Real.artanh (mixedMass c) := by
  have heq := mixedMass_equation c
  unfold mixedMassSide mixedRatioSide at heq
  unfold capGap capReference mixedUpperCurve mixedUpperParameter
  ring_nf at heq ⊢
  linarith

/-! ## The reserve integrand -/

/-- The reserve density `β(t)=ct(δ-artanh t)`. -/
def capReserveBeta (c δ t : ℝ) : ℝ :=
  c * t * (δ - Real.artanh t)

/-- Local differentiability of `artanh` on its natural open interval. -/
theorem artanh_hasDerivAt_of_mem_Ioo {t : ℝ}
    (htLower : -1 < t) (htUpper : t < 1) :
    HasDerivAt Real.artanh (1 / (1 - t ^ 2)) t := by
  have hlog :=
    Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      (y := t) 0 htLower htUpper
  have hlog' :
      HasDerivAt
        (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x)))
        (1 / (1 - t ^ 2)) t := by
    simpa using hlog
  apply hlog'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htLower htUpper] with x hx
  exact Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩

theorem capReserveBeta_continuousAt {c δ t : ℝ}
    (htLower : -1 < t) (htUpper : t < 1) :
    ContinuousAt (capReserveBeta c δ) t := by
  unfold capReserveBeta
  exact (continuousAt_const.mul continuousAt_id).mul
    (continuousAt_const.sub
      (artanh_hasDerivAt_of_mem_Ioo htLower htUpper).continuousAt)

theorem capReserveBeta_nonneg {c m t : ℝ}
    (hc : 0 ≤ c) (_hmLower : 0 ≤ m) (hmUpper : m < 1)
    (htLower : 0 ≤ t) (htUpper : t ≤ m) :
    0 ≤ capReserveBeta c (Real.artanh m) t := by
  unfold capReserveBeta
  have hartanh :
      Real.artanh t ≤ Real.artanh m :=
    Real.artanh_le_artanh (by linarith) hmUpper htUpper
  positivity

@[simp]
theorem capReserveBeta_at_endpoint (c m : ℝ) :
    capReserveBeta c (Real.artanh m) m = 0 := by
  simp [capReserveBeta]

/-! ## The integral reserve -/

/-- The untruncated integral appearing in the reserve. -/
def capReserveVCore (c δ m t : ℝ) : ℝ :=
  ∫ s in t..m, capReserveBeta c δ s

/-- The paper's extension by zero after the cutoff `m`. -/
def capReserveV (c δ m t : ℝ) : ℝ :=
  if t ≤ m then capReserveVCore c δ m t else 0

@[simp]
theorem capReserveV_at_endpoint (c δ m : ℝ) :
    capReserveV c δ m m = 0 := by
  simp [capReserveV, capReserveVCore]

theorem capReserveVCore_hasDerivAt {c δ m t : ℝ}
    (htLower : 0 ≤ t) (htUpper : t ≤ m) (hmUpper : m < 1) :
    HasDerivAt (capReserveVCore c δ m)
      (-capReserveBeta c δ t) t := by
  have hcont :
      ContinuousOn (capReserveBeta c δ) (Icc t m) := by
    intro s hs
    exact (capReserveBeta_continuousAt
      (by linarith [hs.1]) (hs.2.trans_lt hmUpper)).continuousWithinAt
  have hint :
      IntervalIntegrable (capReserveBeta c δ) MeasureTheory.volume t m :=
    hcont.intervalIntegrable_of_Icc htUpper
  have hcontAt :
      ContinuousAt (capReserveBeta c δ) t :=
    capReserveBeta_continuousAt (by linarith) (htUpper.trans_lt hmUpper)
  have hmeas :
      StronglyMeasurableAtFilter (capReserveBeta c δ) (nhds t)
        MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter (μ := MeasureTheory.volume)
      isOpen_Ioo
      (fun s hs => capReserveBeta_continuousAt hs.1 hs.2)
      t ⟨by linarith, htUpper.trans_lt hmUpper⟩
  exact intervalIntegral.integral_hasDerivAt_left hint
    hmeas hcontAt

theorem capReserveV_hasDerivAt {c δ m t : ℝ}
    (htLower : 0 ≤ t) (htUpper : t < m) (hmUpper : m < 1) :
    HasDerivAt (capReserveV c δ m)
      (-capReserveBeta c δ t) t := by
  have hcore :=
    capReserveVCore_hasDerivAt (c := c) (δ := δ)
      htLower htUpper.le hmUpper
  apply hcore.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds htUpper] with s hs
  have hslt : s < m := hs
  simp [capReserveV, hslt.le]

theorem capReserveV_nonneg {c m t : ℝ}
    (hc : 0 ≤ c) (hmLower : 0 ≤ m) (hmUpper : m < 1)
    (htLower : 0 ≤ t) (htUpper : t ≤ m) :
    0 ≤ capReserveV c (Real.artanh m) m t := by
  rw [capReserveV, if_pos htUpper]
  unfold capReserveVCore
  exact intervalIntegral.integral_nonneg htUpper fun s hs =>
    capReserveBeta_nonneg hc hmLower hmUpper
      (htLower.trans hs.1) hs.2

/-! ## Exact evaluation at the initial state -/

/-- An antiderivative of `t ↦ t * artanh t`. -/
def artanhMomentPrimitive (t : ℝ) : ℝ :=
  ((t ^ 2 - 1) * Real.artanh t + t) / 2

theorem artanhMomentPrimitive_hasDerivAt {t : ℝ}
    (htLower : -1 < t) (htUpper : t < 1) :
    HasDerivAt artanhMomentPrimitive (t * Real.artanh t) t := by
  have ha := artanh_hasDerivAt_of_mem_Ioo htLower htUpper
  have hpoly := ((hasDerivAt_id t).pow 2).sub_const 1
  have hsum := (hpoly.mul ha).add (hasDerivAt_id t)
  have hraw := hsum.div_const 2
  unfold artanhMomentPrimitive
  convert hraw using 1
  simp only [id_eq, Pi.pow_apply]
  have hden : 1 - t ^ 2 ≠ 0 := by
    nlinarith
  field_simp [hden]
  ring

/-- A closed antiderivative for the reserve density. -/
def capReserveBetaPrimitive (c δ t : ℝ) : ℝ :=
  c * (δ * t ^ 2 / 2 - artanhMomentPrimitive t)

theorem capReserveBetaPrimitive_hasDerivAt {c δ t : ℝ}
    (htLower : -1 < t) (htUpper : t < 1) :
    HasDerivAt (capReserveBetaPrimitive c δ)
      (capReserveBeta c δ t) t := by
  have hmoment :=
    artanhMomentPrimitive_hasDerivAt htLower htUpper
  have hsquare :
      HasDerivAt (fun s : ℝ => δ * s ^ 2 / 2) (δ * t) t := by
    convert
      (((hasDerivAt_const t δ).mul ((hasDerivAt_id t).pow 2)).div_const 2)
      using 1
    simp only [id_eq]
    ring
  unfold capReserveBetaPrimitive capReserveBeta
  convert (hasDerivAt_const t c).mul (hsquare.sub hmoment) using 1
  simp only [Pi.sub_apply]
  ring

theorem capReserveVCore_eq_primitive {c δ m : ℝ}
    (hmLower : 0 ≤ m) (hmUpper : m < 1) :
    capReserveVCore c δ m 0 =
      capReserveBetaPrimitive c δ m -
        capReserveBetaPrimitive c δ 0 := by
  have hprimCont :
      ContinuousOn (capReserveBetaPrimitive c δ) (Icc 0 m) := by
    intro t ht
    exact (capReserveBetaPrimitive_hasDerivAt
      (by linarith [ht.1]) (ht.2.trans_lt hmUpper)).continuousAt.continuousWithinAt
  have hbetaCont :
      ContinuousOn (capReserveBeta c δ) (Icc 0 m) := by
    intro t ht
    exact (capReserveBeta_continuousAt
      (by linarith [ht.1]) (ht.2.trans_lt hmUpper)).continuousWithinAt
  have hint :
      IntervalIntegrable (capReserveBeta c δ) MeasureTheory.volume 0 m :=
    hbetaCont.intervalIntegrable_of_Icc hmLower
  unfold capReserveVCore
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hmLower hprimCont
    (fun t ht => capReserveBetaPrimitive_hasDerivAt
      (by linarith [ht.1]) (ht.2.trans hmUpper))
    hint

/-- Formula (the reserve part of the initial calibration). -/
theorem capReserveV_at_zero_formula {c m : ℝ}
    (hmLower : 0 ≤ m) (hmUpper : m < 1) :
    capReserveV c (Real.artanh m) m 0 =
      c / 2 * (Real.artanh m - m) := by
  rw [capReserveV, if_pos hmLower,
    capReserveVCore_eq_primitive hmLower hmUpper]
  simp [capReserveBetaPrimitive, artanhMomentPrimitive,
    Real.artanh_zero]
  ring

/-! ## Perspective change of variables -/

/-- The cap fraction among jobs not yet assigned to the ordinary suffix. -/
def reserveMu (q : ℝ) : ℝ := q / (1 + q)

theorem reserveMu_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ reserveMu q := by
  unfold reserveMu
  positivity

theorem reserveMu_lt_one {q : ℝ} (hq : 0 ≤ q) :
    reserveMu q < 1 := by
  unfold reserveMu
  rw [div_lt_one (by linarith : 0 < 1 + q)]
  linarith

theorem reserveMu_hasDerivAt {q : ℝ} (hq : -1 < q) :
    HasDerivAt reserveMu (1 / (1 + q) ^ 2) q := by
  have hden : 1 + q ≠ 0 := by linarith
  change HasDerivAt (fun z : ℝ => z / (1 + z))
    (1 / (1 + q) ^ 2) q
  convert (hasDerivAt_id q).div
    ((hasDerivAt_const q 1).add (hasDerivAt_id q)) hden using 1
  simp only [Pi.add_apply, id_eq]
  field_simp [hden]
  ring_nf

/-- The logarithmic identity used to recognize the cap residual. -/
theorem artanh_reserveMu_eq_half_log {q : ℝ} (hq : 0 ≤ q) :
    Real.artanh (reserveMu q) =
      (1 / 2) * Real.log (1 + 2 * q) := by
  have hden : 0 < 1 + q := by linarith
  have hmu0 := reserveMu_nonneg hq
  have hmu1 := reserveMu_lt_one hq
  rw [Real.artanh_eq_half_log ⟨by linarith, hmu1.le⟩]
  congr 2
  unfold reserveMu
  field_simp [hden.ne']
  ring

/-- The residual left by treating a cap relative to an ordinary `Q` point. -/
def capResidual (c δ q : ℝ) : ℝ :=
  c * q * (δ - (1 / 2) * Real.log (1 + 2 * q))

theorem capResidual_eq_scaled_beta {c δ q : ℝ} (hq : 0 ≤ q) :
    capResidual c δ q =
      (1 + q) * capReserveBeta c δ (reserveMu q) := by
  rw [capResidual, capReserveBeta, artanh_reserveMu_eq_half_log hq]
  unfold reserveMu
  have hden : 1 + q ≠ 0 := by linarith
  field_simp [hden]

/-! ## The perspective reserve and exact cancellation -/

def capReserveH (c δ m q : ℝ) : ℝ :=
  (1 + q) ^ 2 * capReserveV c δ m (reserveMu q)

/-- The derivative formula on the active side of the cutoff. -/
def capReserveHPrime (c δ m q : ℝ) : ℝ :=
  2 * (1 + q) * capReserveV c δ m (reserveMu q) -
    capReserveBeta c δ (reserveMu q)

/-- Contribution of the reserve to an ordinary endpoint. -/
def capReserveL0 (c δ m q : ℝ) : ℝ :=
  -2 * capReserveH c δ m q + q * capReserveHPrime c δ m q

/-- The actual derivative of the zero-extended reserve.  The active formula
is used through the cutoff; afterwards both the reserve and its derivative
are zero. -/
def capReserveHPrimeFull (c δ m q : ℝ) : ℝ :=
  if reserveMu q ≤ m then capReserveHPrime c δ m q else 0

def capReserveL0Full (c δ m q : ℝ) : ℝ :=
  -2 * capReserveH c δ m q + q * capReserveHPrimeFull c δ m q

theorem capReserveHPrimeFull_eq_active {c δ m q : ℝ}
    (hactive : reserveMu q ≤ m) :
    capReserveHPrimeFull c δ m q = capReserveHPrime c δ m q := by
  simp [capReserveHPrimeFull, hactive]

theorem capReserveL0Full_eq_active {c δ m q : ℝ}
    (hactive : reserveMu q ≤ m) :
    capReserveL0Full c δ m q = capReserveL0 c δ m q := by
  rw [capReserveL0Full, capReserveL0,
    capReserveHPrimeFull_eq_active hactive]

theorem capReserveH_hasDerivAt {c δ m q : ℝ}
    (hq : 0 ≤ q) (hactive : reserveMu q < m) (hmUpper : m < 1) :
    HasDerivAt (capReserveH c δ m)
      (capReserveHPrime c δ m q) q := by
  have hmu0 : 0 ≤ reserveMu q := reserveMu_nonneg hq
  have hv :
      HasDerivAt (capReserveV c δ m)
        (-capReserveBeta c δ (reserveMu q)) (reserveMu q) :=
    capReserveV_hasDerivAt hmu0 hactive hmUpper
  have hmu := reserveMu_hasDerivAt (q := q) (by linarith)
  have hcomp := hv.comp q hmu
  have hpow :
      HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + q)) q := by
    convert
      (((hasDerivAt_const q 1).add (hasDerivAt_id q)).pow 2) using 1
    simp only [Pi.add_apply, id_eq]
    ring
  unfold capReserveH capReserveHPrime
  convert hpow.mul hcomp using 1
  simp only [Function.comp_apply]
  field_simp [show 1 + q ≠ 0 by linarith]
  ring_nf

theorem capReserveL0_identity (c δ m q : ℝ) :
    capReserveL0 c δ m q =
      -2 * (1 + q) * capReserveV c δ m (reserveMu q) -
        q * capReserveBeta c δ (reserveMu q) := by
  unfold capReserveL0 capReserveH capReserveHPrime
  ring

theorem capReserveL0_nonpos {c m q : ℝ}
    (hc : 0 ≤ c) (hmLower : 0 ≤ m) (hmUpper : m < 1)
    (hq : 0 ≤ q) (hactive : reserveMu q ≤ m) :
    capReserveL0 c (Real.artanh m) m q ≤ 0 := by
  rw [capReserveL0_identity]
  have hV :=
    capReserveV_nonneg hc hmLower hmUpper
      (reserveMu_nonneg hq) hactive
  have hβ :=
    capReserveBeta_nonneg hc hmLower hmUpper
      (reserveMu_nonneg hq) hactive
  have hq1 : 0 ≤ 1 + q := by linarith
  nlinarith [mul_nonneg hq1 hV, mul_nonneg hq hβ]

/-- The cap Hamiltonian residual is cancelled identically on the active
reserve cone. -/
theorem capReserve_exact_cancellation {c δ m q : ℝ} (hq : 0 ≤ q) :
    capReserveL0 c δ m q +
        capReserveHPrime c δ m q +
        capResidual c δ q = 0 := by
  rw [capReserveL0_identity, capResidual_eq_scaled_beta hq]
  unfold capReserveHPrime
  ring

theorem capReserveFull_exact_cancellation
    {c δ m q : ℝ} (hq : 0 ≤ q)
    (hactive : reserveMu q ≤ m) :
    capReserveL0Full c δ m q +
        capReserveHPrimeFull c δ m q +
        capResidual c δ q = 0 := by
  rw [capReserveL0Full_eq_active hactive,
    capReserveHPrimeFull_eq_active hactive]
  exact capReserve_exact_cancellation hq

/-! ## Cutoff and `C¹` join -/

def reserveQStar (m : ℝ) : ℝ := m / (1 - m)

theorem reserveMu_le_iff_le_qStar {q m : ℝ}
    (hq : 0 ≤ q) (hmUpper : m < 1) :
    reserveMu q ≤ m ↔ q ≤ reserveQStar m := by
  have hqden : 0 < 1 + q := by linarith
  have hmden : 0 < 1 - m := by linarith
  unfold reserveMu reserveQStar
  rw [div_le_iff₀ hqden, le_div_iff₀ hmden]
  constructor <;> intro h <;> nlinarith

theorem reserveQStar_le_goldenRatio {m : ℝ}
    (_hmLower : 0 ≤ m) (hmUpper : m ≤ 1 / goldenRatio) :
    reserveQStar m ≤ goldenRatio := by
  have hφ : 0 < goldenRatio := goldenRatio_pos
  have hm1 : m < 1 :=
    hmUpper.trans_lt inv_goldenRatio_lt_one
  have hfactor : 0 ≤ 1 + goldenRatio := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hmUpper hfactor
  rw [inv_goldenRatio_eq_sub_one] at hscaled
  have hendpoint :
      (goldenRatio - 1) * (1 + goldenRatio) = goldenRatio := by
    nlinarith [goldenRatio_sq]
  rw [hendpoint] at hscaled
  unfold reserveQStar
  rw [div_le_iff₀ (by linarith : 0 < 1 - m)]
  nlinarith

theorem mixed_active_cq_le_one (c : MixedRatioDomain) {q : ℝ}
    (hq : 0 ≤ q) (hactive : reserveMu q ≤ (mixedMass c : ℝ)) :
    (c : ℝ) * q ≤ 1 := by
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hm1 : (mixedMass c : ℝ) < 1 :=
    (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one
  have hqstar :
      q ≤ reserveQStar (mixedMass c) :=
    (reserveMu_le_iff_le_qStar hq hm1).mp hactive
  have hqφ : q ≤ goldenRatio :=
    hqstar.trans (reserveQStar_le_goldenRatio hm0
      (mixedMass c).property.2)
  calc
    (c : ℝ) * q ≤ (1 / goldenRatio) * q :=
      mul_le_mul_of_nonneg_right c.property.2 hq
    _ ≤ (1 / goldenRatio) * goldenRatio :=
      mul_le_mul_of_nonneg_left hqφ inv_goldenRatio_pos.le
    _ = 1 := by field_simp [goldenRatio_pos.ne']

theorem reserveMu_qStar {m : ℝ} (hmUpper : m < 1) :
    reserveMu (reserveQStar m) = m := by
  unfold reserveMu reserveQStar
  have hden : 1 - m ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem capReserveH_at_qStar {c m : ℝ} (hmUpper : m < 1) :
    capReserveH c (Real.artanh m) m (reserveQStar m) = 0 := by
  rw [capReserveH, reserveMu_qStar hmUpper,
    capReserveV_at_endpoint]
  ring

theorem capReserveHPrime_at_qStar {c m : ℝ} (hmUpper : m < 1) :
    capReserveHPrime c (Real.artanh m) m (reserveQStar m) = 0 := by
  rw [capReserveHPrime, reserveMu_qStar hmUpper,
    capReserveV_at_endpoint, capReserveBeta_at_endpoint]
  ring

theorem capReserveHPrimeFull_eq_zero_of_cutoff
    {c m q : ℝ} (hcut : m ≤ reserveMu q) :
    capReserveHPrimeFull c (Real.artanh m) m q = 0 := by
  unfold capReserveHPrimeFull
  split_ifs with hactive
  · have heq : reserveMu q = m := le_antisymm hactive hcut
    simp [capReserveHPrime, heq]
  · rfl

theorem capReserveV_eq_zero_of_cutoff {c δ m t : ℝ} (hmt : m ≤ t) :
    capReserveV c δ m t = 0 := by
  by_cases hEq : t = m
  · subst t
    exact capReserveV_at_endpoint _ _ _
  · have hnot : ¬t ≤ m :=
      not_le.mpr (lt_of_le_of_ne hmt (Ne.symm hEq))
    simp [capReserveV, hnot]

theorem capReserveH_eq_zero_of_cutoff {c δ m q : ℝ}
    (hcut : m ≤ reserveMu q) :
    capReserveH c δ m q = 0 := by
  rw [capReserveH, capReserveV_eq_zero_of_cutoff hcut]
  ring

theorem capReserveL0Full_eq_zero_of_cutoff
    {c m q : ℝ} (hcut : m ≤ reserveMu q) :
    capReserveL0Full c (Real.artanh m) m q = 0 := by
  rw [capReserveL0Full,
    capReserveH_eq_zero_of_cutoff hcut,
    capReserveHPrimeFull_eq_zero_of_cutoff hcut]
  ring

/-! ## Specialization to the mixed branch -/

def mixedReserveDelta (c : MixedRatioDomain) : ℝ :=
  capGap c (mixedUpperCurve c)

theorem mixedReserveDelta_eq_artanh (c : MixedRatioDomain) :
    mixedReserveDelta c = Real.artanh (mixedMass c) :=
  mixed_capGap_eq_artanh c

theorem mixedReserve_nonnegative (c : MixedRatioDomain) {q : ℝ}
    (hq : 0 ≤ q) (hactive : reserveMu q ≤ mixedMass c) :
    0 ≤ capReserveH c (mixedReserveDelta c) (mixedMass c) q := by
  rw [mixedReserveDelta_eq_artanh]
  unfold capReserveH
  have hm0 : 0 ≤ (mixedMass c : ℝ) := (mixedMass c).property.1
  have hm1 : (mixedMass c : ℝ) < 1 :=
    (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one
  have hV :=
    capReserveV_nonneg
      (rhoStar_pos.le.trans c.property.1) hm0 hm1
      (reserveMu_nonneg hq) hactive
  positivity

/-- The base bank and the cap reserve calibrate to exactly `c/2` at the
initial normalized state. -/
theorem mixedReserve_initial_calibration (c : MixedRatioDomain) :
    parameterizedBankF c 0 +
        capReserveH c (mixedReserveDelta c) (mixedMass c) 0 =
      (c : ℝ) / 2 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hm1 : (mixedMass c : ℝ) < 1 :=
    (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one
  have heq := mixedMass_equation c
  unfold mixedMassSide mixedRatioSide at heq
  rw [parameterizedBankF_at_zero_formula hc,
    mixedReserveDelta_eq_artanh]
  simp only [capReserveH, reserveMu, zero_div, add_zero, pow_two,
    one_mul]
  rw [capReserveV_at_zero_formula hm0 hm1]
  field_simp [hc.ne'] at heq
  have hratio :
      ((c : ℝ) + 2) / (c : ℝ) = 1 + 2 / (c : ℝ) := by
    field_simp [hc.ne']
  rw [hratio] at heq
  ring_nf at heq ⊢
  linarith

theorem mixedReserve_exact_cancellation (c : MixedRatioDomain) {q : ℝ}
    (hq : 0 ≤ q) :
    capReserveL0 c (mixedReserveDelta c) (mixedMass c) q +
        capReserveHPrime c (mixedReserveDelta c) (mixedMass c) q +
        capResidual c (mixedReserveDelta c) q = 0 :=
  capReserve_exact_cancellation hq

theorem mixedReserveFull_exact_cancellation
    (c : MixedRatioDomain) {q : ℝ}
    (hq : 0 ≤ q) (hactive : reserveMu q ≤ (mixedMass c : ℝ)) :
    capReserveL0Full c (mixedReserveDelta c) (mixedMass c) q +
        capReserveHPrimeFull c (mixedReserveDelta c) (mixedMass c) q +
        capResidual c (mixedReserveDelta c) q = 0 := by
  exact capReserveFull_exact_cancellation hq hactive

theorem mixed_capResidual_nonpos_of_cutoff
    (c : MixedRatioDomain) {q : ℝ}
    (hq : 0 ≤ q) (hcut : (mixedMass c : ℝ) ≤ reserveMu q) :
    capResidual c (mixedReserveDelta c) q ≤ 0 := by
  have hc : 0 ≤ (c : ℝ) :=
    (rhoStar_pos.trans_le c.property.1).le
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hmu1 : reserveMu q < 1 := reserveMu_lt_one hq
  have hartanh :
      Real.artanh (mixedMass c) ≤ Real.artanh (reserveMu q) :=
    Real.artanh_le_artanh (by linarith) hmu1 hcut
  rw [mixedReserveDelta_eq_artanh]
  unfold capResidual
  rw [← artanh_reserveMu_eq_half_log hq]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hc hq) (sub_nonpos.mpr hartanh)

end

end SchedulingPaper
