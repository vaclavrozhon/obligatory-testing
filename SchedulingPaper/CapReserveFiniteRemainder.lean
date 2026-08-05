import SchedulingPaper.CompleteCapReserveRemainder
import SchedulingPaper.CapReservePathGeometry
import Mathlib.Tactic

/-!
# Finite reachable remainder for the complete cap reserve

This module closes the one-dimensional premise left by
`ReachableCappedBankRemainder`.  It combines the uniform active curvature
bound with the explicit cutoff-crossing geometry, treats inactive states
exactly, and bounds the terminal `x = 1` residual on the compact active
interval.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Set

theorem mixedMass_nonneg (c : MixedRatioDomain) :
    0 ≤ (mixedMass c : ℝ) :=
  (mixedMass c).property.1

theorem mixedMass_lt_one (c : MixedRatioDomain) :
    (mixedMass c : ℝ) < 1 :=
  (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one

theorem mixed_reserveQStar_nonneg (c : MixedRatioDomain) :
    0 ≤ reserveQStar (mixedMass c) := by
  unfold reserveQStar
  exact div_nonneg (mixedMass_nonneg c)
    (sub_nonneg.mpr (mixedMass_lt_one c).le)

theorem capReservePerspectivePathActive_eq_rawW_interpolated
    {c δ m : ℝ} {s : ParameterizedAnalysisState}
    (outcome : CappedBoundaryOutcome) {t : ℝ}
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0)
    (hq : 0 ≤ (s.interpolatedStep outcome t).q)
    (hactive : reserveMu (s.interpolatedStep outcome t).q ≤ m)
    (hmUpper : m < 1) :
    capReservePerspectivePathActive c δ m s.x s.q
        (ParameterizedAnalysisState.cappedStepRate outcome) t =
      capReserveRawW c δ m
        (s.interpolatedStep outcome t).x
        (s.interpolatedStep outcome t).capped := by
  have hxcoord :=
    parameterizedInterpolatedStep_x_formula s outcome t
  have hqcoord :=
    ParameterizedAnalysisState.interpolatedStep_q_formula
      outcome t hx hxt
  unfold capReserveRawW capReservePerspectivePathActive
  rw [if_neg]
  · change
      (s.x - t) ^ 2 *
          capReserveHActive c δ m
            (normalizedAffinePath s.x s.q
              (ParameterizedAnalysisState.cappedStepRate outcome) t) =
        (s.interpolatedStep outcome t).x ^ 2 *
          capReserveH c δ m (s.interpolatedStep outcome t).q
    rw [capReserveH_eq_active hq hactive hmUpper,
      hxcoord, hqcoord]
    rfl
  · rw [hxcoord]
    exact hxt

theorem capReservePerspectiveSlopeActive_zero_eq_completeGradient
    {c δ m : ℝ} {s : ParameterizedAnalysisState}
    (outcome : CappedBoundaryOutcome)
    (hx : s.x ≠ 0)
    (hq : 0 ≤ s.q)
    (hactive : reserveMu s.q ≤ m)
    (hmUpper : m < 1) :
    capReservePerspectiveSlopeActive c δ m s.x s.q
        (ParameterizedAnalysisState.cappedStepRate outcome) 0 =
      (capReserveCompleteRawGradient c δ m s).dotDirection outcome := by
  have hH :=
    capReserveH_eq_active
      (c := c) (δ := δ) (m := m) hq hactive hmUpper
  have hHp :=
    capReserveHPrime_eq_activeFormula
      (c := c) (δ := δ) (m := m) hq hactive hmUpper
  have hHpFull :=
    capReserveHPrimeFull_eq_active
      (c := c) (δ := δ) (m := m) hactive
  cases outcome <;>
    simp only [ParameterizedAnalysisState.cappedStepRate,
      capReservePerspectiveSlopeActive,
      capReserveCompleteRawGradient, CappedRawGradient.dotDirection,
      hH, hHp, hHpFull] <;>
    simp [normalizedAffinePath, hx] <;> ring

theorem capReservePerspectiveActive_unit_remainder
    {c δ m x q κ qmax C : ℝ}
    (hx : 2 ≤ x) (hC : 0 ≤ C)
    (hregion : ∀ t ∈ Icc (0 : ℝ) 1,
      normalizedAffinePath x q κ t ∈ Icc (0 : ℝ) qmax)
    (hcurvature : ∀ z ∈ Icc (0 : ℝ) qmax,
      capReservePerspectiveCurvatureActive c δ m z κ ≤ C) :
    capReservePerspectivePathActive c δ m x q κ 1 -
        capReservePerspectivePathActive c δ m x q κ 0 ≤
      capReservePerspectiveSlopeActive c δ m x q κ 0 + C := by
  let φ := capReservePerspectivePathActive c δ m x q κ
  let slope := capReservePerspectiveSlopeActive c δ m x q κ
  let curvature := fun t =>
    capReservePerspectiveCurvatureActive c δ m
      (normalizedAffinePath x q κ t) κ
  have hxt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      x - t ≠ 0 :=
    ne_of_gt (by linarith [ht.2])
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact capReservePerspectivePathActive_hasDerivAt
      (hxt t ht) (hregion t ht).1
  have hslope : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact capReservePerspectiveSlopeActive_hasDerivAt
      (hxt t ht) (hregion t ht).1
  exact unit_taylor_upper_of_second_deriv_le hC hφ hslope
    (fun t ht => hcurvature _ (hregion t ht))

theorem exists_capReserve_active_to_active_remainder
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ outcome : CappedBoundaryOutcome,
        reserveMu s.q ≤ (mixedMass c : ℝ) →
        reserveMu (s.step outcome).q ≤ (mixedMass c : ℝ) →
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              (s.step outcome).x (s.step outcome).capped -
            capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              s.x s.capped ≤
          (capReserveCompleteRawGradient c
            (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome + C := by
  obtain ⟨C₀, hC₀⟩ := exists_capReserveUniformCurvature c
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro s hs hx outcome hactiveStart hactiveEnd
  let κ := ParameterizedAnalysisState.cappedStepRate outcome
  let qstar := reserveQStar (mixedMass c)
  have hκ : κ ∈ ({0, 1} : Set ℝ) := by
    dsimp [κ]
    exact cappedStepRate_mem_zero_one outcome
  have hq := ParameterizedAnalysisState.q_nonneg hs
  have hm1 := mixedMass_lt_one c
  have hqstar0 : 0 ≤ qstar := by
    dsimp [qstar]
    exact mixed_reserveQStar_nonneg c
  have hxt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      s.x - t ≠ 0 :=
    ne_of_gt (by linarith [ht.2])
  have hpathState (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      normalizedAffinePath s.x s.q κ t =
        (s.interpolatedStep outcome t).q := by
    rw [ParameterizedAnalysisState.interpolatedStep_q_formula
      outcome t hs.1.ne' (hxt t ht)]
    rfl
  have hqEnd :
      normalizedAffinePath s.x s.q κ 1 =
        (s.step outcome).q := by
    simpa using hpathState 1 (by simp)
  have hqEndStar :
      normalizedAffinePath s.x s.q κ 1 ≤ qstar := by
    rw [hqEnd]
    have hnextFeas : (s.step outcome).Feasible := by
      have h :=
        ParameterizedAnalysisState.interpolatedStep_feasible
          hs hx outcome (t := 1) (by simp)
      simpa using h
    exact (reserveMu_le_iff_le_qStar
      (ParameterizedAnalysisState.q_nonneg hnextFeas)
      hm1).mp hactiveEnd
  have hmono :=
    normalizedAffinePath_monotoneOn_of_capRate hx hq hκ
  have hregion (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      normalizedAffinePath s.x s.q κ t ∈
        Icc (0 : ℝ) qstar := by
    constructor
    · exact normalizedAffinePath_nonneg_of_capRate hx hq hκ ht
    · exact (hmono ht (by simp) ht.2).trans hqEndStar
  have htaylor :=
    capReservePerspectiveActive_unit_remainder
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (x := s.x) (q := s.q)
      (κ := κ) (qmax := qstar) (C := C)
      hx hC hregion (by
        intro z hz
        exact (hC₀ κ hκ z hz).trans (le_max_left _ _))
  have hpath0 :=
    capReservePerspectivePathActive_eq_rawW_interpolated
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hq) (by simpa using hactiveStart) hm1
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpath0
  have hnextFeas :=
    ParameterizedAnalysisState.interpolatedStep_feasible
      hs hx outcome (t := 1) (by simp)
  have hnextFeas' : (s.step outcome).Feasible := by
    simpa using hnextFeas
  have hpath1 :=
    capReservePerspectivePathActive_eq_rawW_interpolated
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome (t := 1) hs.1.ne'
      (ne_of_gt (by linarith : 0 < s.x - 1))
      (ParameterizedAnalysisState.q_nonneg hnextFeas')
      hactiveEnd hm1
  simp only [ParameterizedAnalysisState.interpolatedStep_one] at hpath1
  have hslope0 :=
    capReservePerspectiveSlopeActive_zero_eq_completeGradient
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome hs.1.ne' hq hactiveStart hm1
  rw [hpath1, hpath0, hslope0] at htaylor
  exact htaylor

theorem capReserveRawW_eq_zero_of_cutoff
    {c δ m x K : ℝ}
    (hcut : m ≤ reserveMu (K / x)) :
    capReserveRawW c δ m x K = 0 := by
  by_cases hx : x = 0
  · simp [capReserveRawW, hx]
  · unfold capReserveRawW
    rw [if_neg hx, capReserveH_eq_zero_of_cutoff hcut]
    ring

theorem exists_capReserve_active_to_cutoff_remainder
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ outcome : CappedBoundaryOutcome,
        reserveMu s.q ≤ (mixedMass c : ℝ) →
        ¬ reserveMu (s.step outcome).q ≤ (mixedMass c : ℝ) →
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              (s.step outcome).x (s.step outcome).capped -
            capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              s.x s.capped ≤
          (capReserveCompleteRawGradient c
            (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome + C := by
  obtain ⟨C₀, hC₀⟩ := exists_capReserveUniformCurvature c
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro s hs hx outcome hactiveStart hnotActiveEnd
  let κ := ParameterizedAnalysisState.cappedStepRate outcome
  let qstar := reserveQStar (mixedMass c)
  let τ := capReserveCutoffCrossingTime s.x s.q κ qstar
  have hκ : κ ∈ ({0, 1} : Set ℝ) := by
    dsimp [κ]
    exact cappedStepRate_mem_zero_one outcome
  have hq := ParameterizedAnalysisState.q_nonneg hs
  have hm1 := mixedMass_lt_one c
  have hqstar0 : 0 ≤ qstar := by
    dsimp [qstar]
    exact mixed_reserveQStar_nonneg c
  have hqStartStar : s.q ≤ qstar := by
    exact (reserveMu_le_iff_le_qStar hq hm1).mp hactiveStart
  have hnextFeas : (s.step outcome).Feasible := by
    have h :=
      ParameterizedAnalysisState.interpolatedStep_feasible
        hs hx outcome (t := 1) (by simp)
    simpa using h
  have hqEnd := ParameterizedAnalysisState.q_nonneg hnextFeas
  have hxtOne : s.x - 1 ≠ 0 :=
    ne_of_gt (by linarith : 0 < s.x - 1)
  have hqPathOne :
      normalizedAffinePath s.x s.q κ 1 =
        (s.step outcome).q := by
    rw [← ParameterizedAnalysisState.interpolatedStep_one s outcome,
      ParameterizedAnalysisState.interpolatedStep_q_formula
        outcome 1 hs.1.ne' hxtOne]
    rfl
  have hqStarEnd :
      qstar < normalizedAffinePath s.x s.q κ 1 := by
    rw [hqPathOne]
    have hiff := reserveMu_le_iff_le_qStar hqEnd hm1
    exact lt_of_not_ge (fun h => hnotActiveEnd (hiff.mpr h))
  have hτraw :=
    capReserveCutoffCrossingTime_mem_and_eq
      hx hq hκ hqstar0 hqStartStar hqStarEnd
  have hτ : τ ∈ Icc (0 : ℝ) 1 :=
    ⟨hτraw.1.1, hτraw.1.2.le⟩
  have hQτ :
      normalizedAffinePath s.x s.q κ τ = qstar :=
    hτraw.2
  let φ :=
    capReservePerspectivePathActive
      (c : ℝ) (mixedReserveDelta c) (mixedMass c)
        s.x s.q κ
  let slope :=
    capReservePerspectiveSlopeActive
      (c : ℝ) (mixedReserveDelta c) (mixedMass c)
        s.x s.q κ
  let curvature := fun t =>
    capReservePerspectiveCurvatureActive
      (c : ℝ) (mixedReserveDelta c) (mixedMass c)
        (normalizedAffinePath s.x s.q κ t) κ
  have hxt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :
      s.x - t ≠ 0 :=
    ne_of_gt (by linarith [ht.2, hτ.2])
  have hregion (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :
      normalizedAffinePath s.x s.q κ t ∈
        Icc (0 : ℝ) qstar := by
    have htUnit : t ∈ Icc (0 : ℝ) 1 :=
      ⟨ht.1, ht.2.trans hτ.2⟩
    constructor
    · exact normalizedAffinePath_nonneg_of_capRate
        hx hq hκ htUnit
    · exact normalizedAffinePath_le_cutoff_before_crossing
        hx hq hκ hqstar0 hqStartStar hqStarEnd ht.1 ht.2
  have hφ : ∀ t ∈ Icc (0 : ℝ) τ,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact capReservePerspectivePathActive_hasDerivAt
      (hxt t ht) (hregion t ht).1
  have hslope : ∀ t ∈ Icc (0 : ℝ) τ,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact capReservePerspectiveSlopeActive_hasDerivAt
      (hxt t ht) (hregion t ht).1
  have hcurv : ∀ t ∈ Icc (0 : ℝ) τ,
      curvature t ≤ C := by
    intro t ht
    exact (hC₀ κ hκ _ (hregion t ht)).trans (le_max_left _ _)
  have hprefix :=
    segment_taylor_of_second_deriv_le
      hC hτ hφ hslope hcurv
  have hactiveStar :
      reserveMu qstar ≤ (mixedMass c : ℝ) := by
    dsimp [qstar]
    rw [reserveMu_qStar hm1]
  have hHStar :
      capReserveHActive (c : ℝ) (mixedReserveDelta c)
          (mixedMass c) qstar = 0 := by
    rw [← capReserveH_eq_active hqstar0 hactiveStar hm1,
      mixedReserveDelta_eq_artanh,
      capReserveH_at_qStar hm1]
  have hHpStar :
      capReserveHPrimeActive (c : ℝ) (mixedReserveDelta c)
          (mixedMass c) qstar = 0 := by
    rw [← capReserveHPrime_eq_activeFormula
        hqstar0 hactiveStar hm1,
      mixedReserveDelta_eq_artanh,
      capReserveHPrime_at_qStar hm1]
  have hφτ : φ τ = 0 := by
    dsimp [φ]
    unfold capReservePerspectivePathActive
    rw [hQτ]
    simp [hHStar]
  have hslopeτ : slope τ = 0 := by
    dsimp [slope]
    unfold capReservePerspectiveSlopeActive
    rw [hQτ]
    simp [hHStar, hHpStar]
  have hpath0 :=
    capReservePerspectivePathActive_eq_rawW_interpolated
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hq) (by simpa using hactiveStart) hm1
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpath0
  have hslope0 :=
    capReservePerspectiveSlopeActive_zero_eq_completeGradient
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome hs.1.ne' hq hactiveStart hm1
  have hnextZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped = 0 := by
    apply capReserveRawW_eq_zero_of_cutoff
    exact le_of_not_ge hnotActiveEnd
  have hnonnegSlope :
      0 ≤ slope 0 + C * τ := by
    rw [hslopeτ] at hprefix
    exact hprefix.2
  have hprod :
      0 ≤ (slope 0 + C * τ) * (1 - τ) :=
    mul_nonneg hnonnegSlope (sub_nonneg.mpr hτ.2)
  have hCτ : C * τ ≤ C :=
    by simpa using mul_le_mul_of_nonneg_left hτ.2 hC
  rw [hφτ] at hprefix
  rw [hnextZero, ← hpath0, ← hslope0]
  nlinarith

theorem capReserve_inactive_remainder_above_two
    (c : MixedRatioDomain)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (outcome : CappedBoundaryOutcome)
    (hnotActive : ¬ reserveMu s.q ≤ (mixedMass c : ℝ)) :
    capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped -
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          s.x s.capped ≤
      (capReserveCompleteRawGradient c
        (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome := by
  let κ := ParameterizedAnalysisState.cappedStepRate outcome
  let qstar := reserveQStar (mixedMass c)
  have hκ : κ ∈ ({0, 1} : Set ℝ) := by
    dsimp [κ]
    exact cappedStepRate_mem_zero_one outcome
  have hq := ParameterizedAnalysisState.q_nonneg hs
  have hm1 := mixedMass_lt_one c
  have hcutStart :
      (mixedMass c : ℝ) ≤ reserveMu s.q :=
    le_of_not_ge hnotActive
  have hqStarStart : qstar < s.q := by
    exact lt_of_not_ge (fun h =>
      hnotActive ((reserveMu_le_iff_le_qStar hq hm1).mpr h))
  have hnextFeas : (s.step outcome).Feasible := by
    have h :=
      ParameterizedAnalysisState.interpolatedStep_feasible
        hs hx outcome (t := 1) (by simp)
    simpa using h
  have hqEnd := ParameterizedAnalysisState.q_nonneg hnextFeas
  have hxtOne : s.x - 1 ≠ 0 :=
    ne_of_gt (by linarith : 0 < s.x - 1)
  have hpathZero :
      normalizedAffinePath s.x s.q κ 0 = s.q := by
    exact normalizedAffinePath_zero_of_pos hs.1
  have hpathOne :
      normalizedAffinePath s.x s.q κ 1 =
        (s.step outcome).q := by
    rw [← ParameterizedAnalysisState.interpolatedStep_one s outcome,
      ParameterizedAnalysisState.interpolatedStep_q_formula
        outcome 1 hs.1.ne' hxtOne]
    rfl
  have hqMono :=
    normalizedAffinePath_monotoneOn_of_capRate hx hq hκ
      (by simp : (0 : ℝ) ∈ Icc 0 1)
      (by simp : (1 : ℝ) ∈ Icc 0 1) (by norm_num)
  have hqStarEnd : qstar < (s.step outcome).q := by
    rw [← hpathOne]
    exact hqStarStart.trans_le (by simpa [hpathZero] using hqMono)
  have hnotActiveEnd :
      ¬ reserveMu (s.step outcome).q ≤ (mixedMass c : ℝ) := by
    intro h
    have :=
      (reserveMu_le_iff_le_qStar hqEnd hm1).mp h
    linarith
  have hcutEnd :
      (mixedMass c : ℝ) ≤ reserveMu (s.step outcome).q :=
    le_of_not_ge hnotActiveEnd
  have hstartZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          s.x s.capped = 0 := by
    apply capReserveRawW_eq_zero_of_cutoff
    simpa [ParameterizedAnalysisState.q] using hcutStart
  have hendZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped = 0 := by
    apply capReserveRawW_eq_zero_of_cutoff
    simpa [ParameterizedAnalysisState.q] using hcutEnd
  have hH :
      capReserveH c (mixedReserveDelta c) (mixedMass c) s.q = 0 :=
    capReserveH_eq_zero_of_cutoff hcutStart
  have hHp :
      capReserveHPrimeFull c (mixedReserveDelta c)
          (mixedMass c) s.q = 0 := by
    rw [mixedReserveDelta_eq_artanh]
    exact capReserveHPrimeFull_eq_zero_of_cutoff hcutStart
  cases outcome <;>
    simp [hstartZero, hendZero, capReserveCompleteRawGradient,
      CappedRawGradient.dotDirection, hH, hHp]

theorem exists_capReserve_remainder_above_two
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ outcome : CappedBoundaryOutcome,
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              (s.step outcome).x (s.step outcome).capped -
            capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              s.x s.capped ≤
          (capReserveCompleteRawGradient c
            (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome + C := by
  obtain ⟨Caa, hCaa, haa⟩ :=
    exists_capReserve_active_to_active_remainder c
  obtain ⟨Cac, hCac, hac⟩ :=
    exists_capReserve_active_to_cutoff_remainder c
  let C := max Caa Cac
  have hC : 0 ≤ C := hCaa.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs hx outcome
  by_cases hstart :
      reserveMu s.q ≤ (mixedMass c : ℝ)
  · by_cases hend :
        reserveMu (s.step outcome).q ≤ (mixedMass c : ℝ)
    · have h := haa s hs hx outcome hstart hend
      have hle : Caa ≤ C := le_max_left _ _
      linarith
    · have h := hac s hs hx outcome hstart hend
      have hle : Cac ≤ C := le_max_right _ _
      linarith
  · have h :=
      capReserve_inactive_remainder_above_two
        c hs hx outcome hstart
    linarith

def capReserveActiveTerminalRemainder
    (c δ m q κ : ℝ) : ℝ :=
  capReserveHActive c δ m q -
    (q + κ) * capReserveHPrimeActive c δ m q

theorem capReserveActiveTerminalRemainder_continuousOn
    {c δ m κ qmax : ℝ} :
    ContinuousOn
      (fun q => capReserveActiveTerminalRemainder c δ m q κ)
      (Icc (0 : ℝ) qmax) := by
  intro q hq
  have hH :
      ContinuousAt (capReserveHActive c δ m) q :=
    (capReserveHActive_hasDerivAt hq.1).continuousAt
  have hHp :
      ContinuousAt (capReserveHPrimeActive c δ m) q :=
    (capReserveHPrimeActive_hasDerivAt hq.1).continuousAt
  unfold capReserveActiveTerminalRemainder
  exact (by fun_prop : ContinuousAt
    (fun z => capReserveHActive c δ m z -
      (z + κ) * capReserveHPrimeActive c δ m z) q
    ).continuousWithinAt

theorem exists_capReserveActiveTerminalUniformBound
    (c : MixedRatioDomain) :
    ∃ C : ℝ, ∀ κ ∈ ({0, 1} : Set ℝ),
      ∀ q ∈ Icc (0 : ℝ) (reserveQStar (mixedMass c)),
        capReserveActiveTerminalRemainder
          c (mixedReserveDelta c) (mixedMass c) q κ ≤ C := by
  let qmax : ℝ := reserveQStar (mixedMass c)
  have hcompact : IsCompact (Icc (0 : ℝ) qmax) :=
    isCompact_Icc
  have hbound (κ : ℝ) :
      ∃ C : ℝ, ∀ q ∈ Icc (0 : ℝ) qmax,
        capReserveActiveTerminalRemainder
          c (mixedReserveDelta c) (mixedMass c) q κ ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (capReserveActiveTerminalRemainder_continuousOn
          (c := (c : ℝ)) (δ := mixedReserveDelta c)
          (m := (mixedMass c : ℝ)) (κ := κ) (qmax := qmax))
    refine ⟨C, ?_⟩
    intro q hq
    exact (le_abs_self
      (capReserveActiveTerminalRemainder
        c (mixedReserveDelta c) (mixedMass c) q κ)).trans (by
          simpa [Real.norm_eq_abs] using hC q hq)
  obtain ⟨C0, hC0⟩ := hbound 0
  obtain ⟨C1, hC1⟩ := hbound 1
  refine ⟨max C0 C1, ?_⟩
  intro κ hκ q hq
  rcases hκ with (rfl | rfl)
  · exact (hC0 q hq).trans (le_max_left _ _)
  · exact (hC1 q hq).trans (le_max_right _ _)

theorem capReserveActiveTerminal_residual_eq
    (c δ m : ℝ) (s : ParameterizedAnalysisState)
    (outcome : CappedBoundaryOutcome) (hx : s.x = 1) :
    -capReservePerspectivePathActive c δ m s.x s.q
        (ParameterizedAnalysisState.cappedStepRate outcome) 0 -
      capReservePerspectiveSlopeActive c δ m s.x s.q
        (ParameterizedAnalysisState.cappedStepRate outcome) 0 =
      capReserveActiveTerminalRemainder c δ m s.q
        (ParameterizedAnalysisState.cappedStepRate outcome) := by
  rw [hx]
  unfold capReserveActiveTerminalRemainder
    capReservePerspectivePathActive
    capReservePerspectiveSlopeActive normalizedAffinePath
  ring_nf

theorem exists_capReserve_active_terminal_remainder
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → s.x = 1 →
      ∀ outcome : CappedBoundaryOutcome,
        reserveMu s.q ≤ (mixedMass c : ℝ) →
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              (s.step outcome).x (s.step outcome).capped -
            capReserveRawW c (mixedReserveDelta c) (mixedMass c)
              s.x s.capped ≤
          (capReserveCompleteRawGradient c
            (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome + C := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_capReserveActiveTerminalUniformBound c
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro s hs hx outcome hactive
  have hq := ParameterizedAnalysisState.q_nonneg hs
  have hm1 := mixedMass_lt_one c
  have hqstar :
      s.q ≤ reserveQStar (mixedMass c) :=
    (reserveMu_le_iff_le_qStar hq hm1).mp hactive
  have hbound :=
    hC₀ (ParameterizedAnalysisState.cappedStepRate outcome)
      (cappedStepRate_mem_zero_one outcome) s.q ⟨hq, hqstar⟩
  have hbound' :
      capReserveActiveTerminalRemainder
          c (mixedReserveDelta c) (mixedMass c) s.q
            (ParameterizedAnalysisState.cappedStepRate outcome) ≤ C :=
    hbound.trans (le_max_left _ _)
  have hnextX : (s.step outcome).x = 0 := by
    cases outcome <;>
      simp [ParameterizedAnalysisState.step, hx]
  have hnextZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped = 0 := by
    rw [hnextX]
    simp [capReserveRawW]
  have hpath0 :=
    capReservePerspectivePathActive_eq_rawW_interpolated
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hq) (by simpa using hactive) hm1
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpath0
  have hslope0 :=
    capReservePerspectiveSlopeActive_zero_eq_completeGradient
      (c := (c : ℝ)) (δ := mixedReserveDelta c)
      (m := (mixedMass c : ℝ)) (s := s)
      outcome hs.1.ne' hq hactive hm1
  have hresidual :=
    capReserveActiveTerminal_residual_eq
      (c : ℝ) (mixedReserveDelta c) (mixedMass c)
        s outcome hx
  rw [hnextZero, ← hpath0, ← hslope0]
  linarith

theorem capReserve_inactive_terminal_remainder
    (c : MixedRatioDomain)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : s.x = 1) (outcome : CappedBoundaryOutcome)
    (hnotActive : ¬ reserveMu s.q ≤ (mixedMass c : ℝ)) :
    capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped -
        capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          s.x s.capped ≤
      (capReserveCompleteRawGradient c
        (mixedReserveDelta c) (mixedMass c) s).dotDirection outcome := by
  have hcut :
      (mixedMass c : ℝ) ≤ reserveMu s.q :=
    le_of_not_ge hnotActive
  have hstartZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          s.x s.capped = 0 := by
    apply capReserveRawW_eq_zero_of_cutoff
    simpa [ParameterizedAnalysisState.q] using hcut
  have hnextX : (s.step outcome).x = 0 := by
    cases outcome <;>
      simp [ParameterizedAnalysisState.step, hx]
  have hnextZero :
      capReserveRawW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x (s.step outcome).capped = 0 := by
    rw [hnextX]
    simp [capReserveRawW]
  have hH :
      capReserveH c (mixedReserveDelta c) (mixedMass c) s.q = 0 :=
    capReserveH_eq_zero_of_cutoff hcut
  have hHp :
      capReserveHPrimeFull c (mixedReserveDelta c)
          (mixedMass c) s.q = 0 := by
    rw [mixedReserveDelta_eq_artanh]
    exact capReserveHPrimeFull_eq_zero_of_cutoff hcut
  cases outcome <;>
    simp [hstartZero, hnextZero, capReserveCompleteRawGradient,
      CappedRawGradient.dotDirection, hH, hHp]

/-- The missing one-dimensional mixed reserve premise is finite on every
reachable unit-countdown pre-state. -/
theorem exists_reachableCompleteCapReserveRemainder
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasReachableCompleteCapReserveRemainder
        c (mixedReserveDelta c) (mixedMass c) C := by
  obtain ⟨Cabove, hCabove, habove⟩ :=
    exists_capReserve_remainder_above_two c
  obtain ⟨Cterminal, hCterminal, hterminal⟩ :=
    exists_capReserve_active_terminal_remainder c
  let C := max Cabove Cterminal
  have hC : 0 ≤ C :=
    hCabove.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs outcome
  rcases hs.2 with hx | hx
  · by_cases hactive :
        reserveMu s.q ≤ (mixedMass c : ℝ)
    · have h :=
        hterminal s hs.1 hx outcome hactive
      have hle : Cterminal ≤ C := le_max_right _ _
      linarith
    · have h :=
        capReserve_inactive_terminal_remainder
          c hs.1 hx outcome hactive
      linarith
  · have h := habove s hs.1 hx outcome
    have hle : Cabove ≤ C := le_max_left _ _
    linarith

/-- Consequently the complete five-endpoint mixed bank has a reachable
uniform one-step remainder with no remaining analytic premise. -/
theorem exists_reachableCompleteCappedBankRemainder
    (c : MixedRatioDomain) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasReachableCompleteCappedBankRemainder
        c (mixedReserveDelta c) (mixedMass c) C :=
  exists_reachableCompleteCappedBankRemainder_of_capReserve c
    (exists_reachableCompleteCapReserveRemainder c)

end

end SchedulingPaper
