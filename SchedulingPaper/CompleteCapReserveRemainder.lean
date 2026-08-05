import SchedulingPaper.ReachableCappedBankRemainder
import Mathlib.Tactic

/-!
# Analytic core for the complete cap-reserve remainder

This module gives a closed active-side formula for the reserve, verifies its
first two derivatives, differentiates the associated perspective path twice,
and obtains the uniform curvature bound on the mixed compact active region.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Closed active-side representative of the truncated integral. -/
def capReserveVActive (c δ m t : ℝ) : ℝ :=
  capReserveBetaPrimitive c δ m -
    capReserveBetaPrimitive c δ t

theorem capReserveVCore_eq_active
    {c δ m t : ℝ} (htLower : -1 < t)
    (htm : t ≤ m) (hmUpper : m < 1) :
    capReserveVCore c δ m t =
      capReserveVActive c δ m t := by
  have hprimCont :
      ContinuousOn (capReserveBetaPrimitive c δ) (Set.Icc t m) := by
    intro u hu
    exact (capReserveBetaPrimitive_hasDerivAt
      (by linarith [htLower, hu.1])
      (hu.2.trans_lt hmUpper)).continuousAt.continuousWithinAt
  have hbetaCont :
      ContinuousOn (capReserveBeta c δ) (Set.Icc t m) := by
    intro u hu
    exact (capReserveBeta_continuousAt
      (by linarith [htLower, hu.1])
      (hu.2.trans_lt hmUpper)).continuousWithinAt
  have hint :
      IntervalIntegrable (capReserveBeta c δ)
        MeasureTheory.volume t m :=
    hbetaCont.intervalIntegrable_of_Icc htm
  unfold capReserveVCore capReserveVActive
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    htm hprimCont
    (fun u hu => capReserveBetaPrimitive_hasDerivAt
      (by linarith [htLower, hu.1])
      (hu.2.trans hmUpper))
    hint

theorem capReserveV_eq_active
    {c δ m t : ℝ} (htLower : -1 < t)
    (htm : t ≤ m) (hmUpper : m < 1) :
    capReserveV c δ m t =
      capReserveVActive c δ m t := by
  rw [capReserveV, if_pos htm]
  exact capReserveVCore_eq_active htLower htm hmUpper

def capReserveHActive (c δ m q : ℝ) : ℝ :=
  (1 + q) ^ 2 *
    capReserveVActive c δ m (reserveMu q)

def capReserveHPrimeActive (c δ m q : ℝ) : ℝ :=
  2 * (1 + q) *
      capReserveVActive c δ m (reserveMu q) -
    capReserveBeta c δ (reserveMu q)

theorem capReserveH_eq_active
    {c δ m q : ℝ} (hq : 0 ≤ q)
    (hactive : reserveMu q ≤ m) (hmUpper : m < 1) :
    capReserveH c δ m q = capReserveHActive c δ m q := by
  unfold capReserveH capReserveHActive
  rw [capReserveV_eq_active (by
    linarith [reserveMu_nonneg hq]) hactive hmUpper]

theorem capReserveHPrime_eq_activeFormula
    {c δ m q : ℝ} (hq : 0 ≤ q)
    (hactive : reserveMu q ≤ m) (hmUpper : m < 1) :
    capReserveHPrime c δ m q =
      capReserveHPrimeActive c δ m q := by
  unfold capReserveHPrime capReserveHPrimeActive
  rw [capReserveV_eq_active (by
    linarith [reserveMu_nonneg hq]) hactive hmUpper]

def capReserveBetaPrime (c δ t : ℝ) : ℝ :=
  c * (δ - Real.artanh t - t / (1 - t ^ 2))

theorem capReserveBeta_hasDerivAt
    {c δ t : ℝ} (htLower : -1 < t) (htUpper : t < 1) :
    HasDerivAt (capReserveBeta c δ)
      (capReserveBetaPrime c δ t) t := by
  have ha := artanh_hasDerivAt_of_mem_Ioo htLower htUpper
  have hleft :
      HasDerivAt (fun u : ℝ => c * u) c t := by
    convert (hasDerivAt_const t c).mul (hasDerivAt_id t) using 1
    simp
  have hright :
      HasDerivAt (fun u : ℝ => δ - Real.artanh u)
        (-(1 / (1 - t ^ 2))) t := by
    convert (hasDerivAt_const t δ).sub ha using 1
    ring
  unfold capReserveBeta capReserveBetaPrime
  convert hleft.mul hright using 1
  field_simp [show 1 - t ^ 2 ≠ 0 by nlinarith]
  ring

theorem capReserveVActive_hasDerivAt
    {c δ m t : ℝ} (htLower : -1 < t) (htUpper : t < 1) :
    HasDerivAt (capReserveVActive c δ m)
      (-capReserveBeta c δ t) t := by
  unfold capReserveVActive
  convert (hasDerivAt_const t
    (capReserveBetaPrimitive c δ m)).sub
      (capReserveBetaPrimitive_hasDerivAt htLower htUpper) using 1
  ring

theorem capReserveHActive_hasDerivAt
    {c δ m q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (capReserveHActive c δ m)
      (capReserveHPrimeActive c δ m q) q := by
  have hmu0 := reserveMu_nonneg hq
  have hmu1 := reserveMu_lt_one hq
  have hv :=
    (capReserveVActive_hasDerivAt
      (c := c) (δ := δ) (m := m)
      (by linarith) hmu1).comp q
      (reserveMu_hasDerivAt (by linarith : -1 < q))
  have hpow :
      HasDerivAt (fun z : ℝ => (1 + z) ^ 2)
        (2 * (1 + q)) q := by
    convert (((hasDerivAt_const q 1).add
      (hasDerivAt_id q)).pow 2) using 1
    simp
  unfold capReserveHActive capReserveHPrimeActive
  convert hpow.mul hv using 1
  simp only [Function.comp_apply]
  field_simp [show 1 + q ≠ 0 by linarith]
  ring

def capReserveHSecondActive (c δ m q : ℝ) : ℝ :=
  2 * capReserveVActive c δ m (reserveMu q) -
    2 * capReserveBeta c δ (reserveMu q) / (1 + q) -
    capReserveBetaPrime c δ (reserveMu q) / (1 + q) ^ 2

theorem capReserveHPrimeActive_hasDerivAt
    {c δ m q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (capReserveHPrimeActive c δ m)
      (capReserveHSecondActive c δ m q) q := by
  have hmu0 := reserveMu_nonneg hq
  have hmu1 := reserveMu_lt_one hq
  have hmu := reserveMu_hasDerivAt (by linarith : -1 < q)
  have hv :=
    (capReserveVActive_hasDerivAt
      (c := c) (δ := δ) (m := m)
      (by linarith) hmu1).comp q hmu
  have hbeta :=
    (capReserveBeta_hasDerivAt
      (c := c) (δ := δ) (by linarith) hmu1).comp q hmu
  have hone :
      HasDerivAt (fun z : ℝ => 1 + z) 1 q := by
    convert (hasDerivAt_const q 1).add (hasDerivAt_id q) using 1
    simp
  unfold capReserveHPrimeActive capReserveHSecondActive
  have hraw :=
    (((hasDerivAt_const q 2).mul hone).mul hv).sub hbeta
  convert hraw using 1
  simp only [Function.comp_apply, Pi.mul_apply]
  field_simp [show 1 + q ≠ 0 by linarith]
  ring

def capReservePerspectivePathActive
    (c δ m x q κ t : ℝ) : ℝ :=
  (x - t) ^ 2 *
    capReserveHActive c δ m
      (normalizedAffinePath x q κ t)

def capReservePerspectiveSlopeActive
    (c δ m x q κ t : ℝ) : ℝ :=
  (x - t) *
    (-2 * capReserveHActive c δ m
        (normalizedAffinePath x q κ t) +
      (normalizedAffinePath x q κ t + κ) *
        capReserveHPrimeActive c δ m
          (normalizedAffinePath x q κ t))

def capReservePerspectiveCurvatureActive
    (c δ m q κ : ℝ) : ℝ :=
  2 * capReserveHActive c δ m q -
    2 * (q + κ) * capReserveHPrimeActive c δ m q +
    (q + κ) ^ 2 * capReserveHSecondActive c δ m q

theorem capReservePerspectivePathActive_hasDerivAt
    {c δ m x q κ t : ℝ}
    (hxt : x - t ≠ 0)
    (hQ : 0 ≤ normalizedAffinePath x q κ t) :
    HasDerivAt
      (capReservePerspectivePathActive c δ m x q κ)
      (capReservePerspectiveSlopeActive c δ m x q κ t) t := by
  let X : ℝ → ℝ := fun u => x - u
  let Q : ℝ → ℝ := normalizedAffinePath x q κ
  have hX : HasDerivAt X (-1) t := by
    dsimp [X]
    convert (hasDerivAt_const t x).sub (hasDerivAt_id t) using 1
    ring
  have hQ' :
      HasDerivAt Q (x * (q + κ) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hH :=
    (capReserveHActive_hasDerivAt
      (c := c) (δ := δ) (m := m) hQ).comp t hQ'
  unfold capReservePerspectivePathActive
    capReservePerspectiveSlopeActive
  dsimp [X, Q] at hX hQ' hH ⊢
  have hraw := (hX.pow 2).mul hH
  simp only [Pi.pow_apply] at hraw
  convert hraw using 1
  simp only [Function.comp_apply]
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

theorem capReservePerspectiveSlopeActive_hasDerivAt
    {c δ m x q κ t : ℝ}
    (hxt : x - t ≠ 0)
    (hQ : 0 ≤ normalizedAffinePath x q κ t) :
    HasDerivAt
      (capReservePerspectiveSlopeActive c δ m x q κ)
      (capReservePerspectiveCurvatureActive c δ m
        (normalizedAffinePath x q κ t) κ) t := by
  let X : ℝ → ℝ := fun u => x - u
  let Q : ℝ → ℝ := normalizedAffinePath x q κ
  let U : ℝ → ℝ := fun u => Q u + κ
  have hX : HasDerivAt X (-1) t := by
    dsimp [X]
    convert (hasDerivAt_const t x).sub (hasDerivAt_id t) using 1
    ring
  have hQ' :
      HasDerivAt Q (x * (q + κ) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hU :
      HasDerivAt U (x * (q + κ) / (x - t) ^ 2) t :=
    hQ'.add_const κ
  have hH :=
    (capReserveHActive_hasDerivAt
      (c := c) (δ := δ) (m := m) hQ).comp t hQ'
  have hHp :=
    (capReserveHPrimeActive_hasDerivAt
      (c := c) (δ := δ) (m := m) hQ).comp t hQ'
  have hinner :=
    ((hasDerivAt_const t (-2)).mul hH).add (hU.mul hHp)
  have hraw := hX.mul hinner
  unfold capReservePerspectiveSlopeActive
    capReservePerspectiveCurvatureActive
  dsimp [X, Q, U] at hX hQ' hU hH hHp hinner hraw ⊢
  convert hraw using 1
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

def capReserveCurvatureFor
    (c δ m κ : ℝ) (q : ℝ) : ℝ :=
  capReservePerspectiveCurvatureActive c δ m q κ

theorem capReserveCurvatureFor_continuousOn
    {c δ m κ qmax : ℝ} :
    ContinuousOn (capReserveCurvatureFor c δ m κ)
      (Set.Icc (0 : ℝ) qmax) := by
  intro q hq
  have hqden : 1 + q ≠ 0 := by linarith [hq.1]
  have hmuLower : -1 < reserveMu q := by
    linarith [reserveMu_nonneg hq.1]
  have hmuUpper : reserveMu q < 1 :=
    reserveMu_lt_one hq.1
  have hmuCont :
      ContinuousAt reserveMu q :=
    (reserveMu_hasDerivAt (by linarith [hq.1])).continuousAt
  have hVBase :
      ContinuousAt (capReserveVActive c δ m) (reserveMu q) :=
    (capReserveVActive_hasDerivAt
      hmuLower hmuUpper).continuousAt
  have hV :
      ContinuousAt
        (fun z => capReserveVActive c δ m (reserveMu z)) q := by
    simpa [Function.comp_def] using hVBase.comp hmuCont
  have hBetaBase :
      ContinuousAt (capReserveBeta c δ) (reserveMu q) :=
    (capReserveBeta_hasDerivAt
      hmuLower hmuUpper).continuousAt
  have hBeta :
      ContinuousAt
        (fun z => capReserveBeta c δ (reserveMu z)) q := by
    simpa [Function.comp_def] using hBetaBase.comp hmuCont
  have hmuSq : (reserveMu q) ^ 2 < 1 := by
    nlinarith
  have hsqden : 1 - (reserveMu q) ^ 2 ≠ 0 := by
    nlinarith
  have hArtanh :
      ContinuousAt Real.artanh (reserveMu q) :=
    (artanh_hasDerivAt_of_mem_Ioo
      hmuLower hmuUpper).continuousAt
  have hBetaPrimeBase :
      ContinuousAt (capReserveBetaPrime c δ) (reserveMu q) := by
    unfold capReserveBetaPrime
    fun_prop
  have hBetaPrime :
      ContinuousAt
        (fun z => capReserveBetaPrime c δ (reserveMu z)) q := by
    simpa [Function.comp_def] using
      hBetaPrimeBase.comp hmuCont
  have hH :
      ContinuousAt (capReserveHActive c δ m) q :=
    (capReserveHActive_hasDerivAt hq.1).continuousAt
  have hHp :
      ContinuousAt (capReserveHPrimeActive c δ m) q :=
    (capReserveHPrimeActive_hasDerivAt hq.1).continuousAt
  have hHpp :
      ContinuousAt (capReserveHSecondActive c δ m) q := by
    unfold capReserveHSecondActive
    fun_prop (disch := simp [hqden])
  unfold capReserveCurvatureFor
    capReservePerspectiveCurvatureActive
  apply ContinuousAt.continuousWithinAt
  fun_prop

theorem exists_capReserveUniformCurvature
    (c : MixedRatioDomain) :
    ∃ C : ℝ, ∀ κ ∈ ({0, 1} : Set ℝ),
      ∀ q ∈ Set.Icc (0 : ℝ) (reserveQStar (mixedMass c)),
        capReservePerspectiveCurvatureActive
          c (mixedReserveDelta c) (mixedMass c) q κ ≤ C := by
  let qmax : ℝ := reserveQStar (mixedMass c)
  have hcompact : IsCompact (Set.Icc (0 : ℝ) qmax) :=
    isCompact_Icc
  have hbound (κ : ℝ) :
      ∃ C : ℝ, ∀ q ∈ Set.Icc (0 : ℝ) qmax,
        capReserveCurvatureFor c (mixedReserveDelta c)
          (mixedMass c) κ q ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (capReserveCurvatureFor_continuousOn
          (c := (c : ℝ)) (δ := mixedReserveDelta c)
          (m := (mixedMass c : ℝ)) (κ := κ) (qmax := qmax))
    refine ⟨C, ?_⟩
    intro q hq
    simpa [Real.norm_eq_abs] using
      (le_abs_self
        (capReserveCurvatureFor c (mixedReserveDelta c)
          (mixedMass c) κ q)).trans (by
          simpa [Real.norm_eq_abs] using hC q hq)
  obtain ⟨C0, hC0⟩ := hbound 0
  obtain ⟨C1, hC1⟩ := hbound 1
  refine ⟨max C0 C1, ?_⟩
  intro κ hκ q hq
  rcases hκ with (rfl | rfl)
  · exact (hC0 q hq).trans (le_max_left _ _)
  · exact (hC1 q hq).trans (le_max_right _ _)

end

end SchedulingPaper
