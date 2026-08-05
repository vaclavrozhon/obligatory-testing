import SchedulingPaper.CapReserve
import SchedulingPaper.BankAccounting

/-!
# Raw-coordinate accounting for the five-endpoint mixed bank

This module combines the parameterized four-endpoint base bank with the cap
reserve.  The fifth endpoint is charged by the ordinary `Q` envelope plus
the residual `B(q)`.  In raw coordinates the perspective reserve contributes
`x L₀` to an ordinary step and `x(L₀+H')` to a cap step, so the cancellation
proved in `CapReserve` applies literally.
-/

namespace SchedulingPaper

noncomputable section

inductive CappedBoundaryOutcome
  | zero
  | epsilon
  | immediate
  | deferred
  | cap
  deriving DecidableEq, Repr

structure ParameterizedAnalysisState where
  x : ℝ
  substantive : ℝ
  epsilon : ℝ
  deferred : ℝ
  capped : ℝ

namespace ParameterizedAnalysisState

def eta (c : ℝ) (s : ParameterizedAnalysisState) : ℝ :=
  (s.deferred - (1 + c) * s.substantive) / s.x

def b (s : ParameterizedAnalysisState) : ℝ := s.epsilon / s.x

def y (c : ℝ) (s : ParameterizedAnalysisState) : ℝ :=
  s.eta c - (1 + c) * s.b

def q (s : ParameterizedAnalysisState) : ℝ := s.capped / s.x

def threshold (c : ℝ) (s : ParameterizedAnalysisState) : ℝ :=
  if -1 ≤ s.y c then parameterizedThreshold c (s.y c) else 1

def Feasible (s : ParameterizedAnalysisState) : Prop :=
  0 < s.x ∧
  0 ≤ s.substantive ∧
  0 ≤ s.epsilon ∧
  0 ≤ s.deferred ∧
  0 ≤ s.capped ∧
  s.deferred ≤ s.substantive ∧
  s.capped ≤ s.substantive

theorem eta_nonpos {c : ℝ} (hc : 0 ≤ c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    s.eta c ≤ 0 := by
  have hscale :
      s.substantive ≤ (1 + c) * s.substantive := by
    nlinarith [mul_nonneg hc hs.2.1]
  have hnum :
      s.deferred - (1 + c) * s.substantive ≤ 0 := by
    linarith [hs.2.2.2.2.2.1]
  exact div_nonpos_of_nonpos_of_nonneg hnum hs.1.le

theorem b_nonneg {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    0 ≤ s.b :=
  div_nonneg hs.2.2.1 hs.1.le

theorem q_nonneg {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    0 ≤ s.q :=
  div_nonneg hs.2.2.2.2.1 hs.1.le

theorem y_nonpos {c : ℝ} (hc : 0 ≤ c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    s.y c ≤ 0 := by
  have hC : 0 ≤ 1 + c := by linarith
  have hb := b_nonneg hs
  unfold y
  nlinarith [eta_nonpos hc hs, mul_nonneg hC hb]

theorem eta_eq_y_add (c : ℝ) (s : ParameterizedAnalysisState) :
    s.eta c = s.y c + (1 + c) * s.b := by
  unfold y
  ring

def step (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ParameterizedAnalysisState
  | .zero =>
      { s with x := s.x - 1 }
  | .epsilon =>
      { s with x := s.x - 1, epsilon := s.epsilon + 1 }
  | .immediate =>
      { s with
        x := s.x - 1
        substantive := s.substantive + 1 }
  | .deferred =>
      { s with
        x := s.x - 1
        substantive := s.substantive + 1
        deferred := s.deferred + 1 }
  | .cap =>
      { s with
        x := s.x - 1
        substantive := s.substantive + 1
        deferred := s.deferred + 1
        capped := s.capped + 1 }

end ParameterizedAnalysisState

structure CappedRawGradient where
  x : ℝ
  substantive : ℝ
  epsilon : ℝ
  deferred : ℝ
  capped : ℝ

def CappedRawGradient.dotDirection (g : CappedRawGradient) :
    CappedBoundaryOutcome → ℝ
  | .zero => -g.x
  | .epsilon => -g.x + g.epsilon
  | .immediate => -g.x + g.substantive
  | .deferred => -g.x + g.substantive + g.deferred
  | .cap => -g.x + g.substantive + g.deferred + g.capped

def CappedRawGradient.add
    (left right : CappedRawGradient) : CappedRawGradient :=
  {
    x := left.x + right.x
    substantive := left.substantive + right.substantive
    epsilon := left.epsilon + right.epsilon
    deferred := left.deferred + right.deferred
    capped := left.capped + right.capped
  }

theorem CappedRawGradient.dotDirection_add
    (left right : CappedRawGradient) (outcome : CappedBoundaryOutcome) :
    (left.add right).dotDirection outcome =
      left.dotDirection outcome + right.dotDirection outcome := by
  cases outcome <;>
    simp [CappedRawGradient.add, CappedRawGradient.dotDirection] <;> ring

/-! ## The parameterized base bank in raw coordinates -/

def parameterizedOrdinaryReward (c : ℝ)
    (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ℝ
  | .zero | .epsilon => s.deferred
  | .immediate =>
      s.deferred + s.threshold c * s.x * (1 + s.eta c)
  | .deferred | .cap =>
      s.deferred + s.threshold c * s.x * s.eta c

def parameterizedActiveRawGradient (c : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  let G := parameterizedActiveG c (s.y c) s.b
  let Gy := parameterizedActiveGy c (s.y c) s.b
  let Gb := parameterizedActiveGb c (s.y c) s.b
  {
    x := s.deferred + s.x *
      (2 * G - s.y c * Gy - s.b * Gb)
    substantive := -(1 + c) * s.x * Gy
    epsilon := s.x * (-(1 + c) * Gy + Gb)
    deferred := s.x * (1 + Gy)
    capped := 0
  }

def parameterizedFlatRawGradient (c : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  let G := parameterizedFlatG c (s.eta c)
  let Gη := parameterizedFlatGPrime c (s.eta c)
  {
    x := s.deferred + s.x * (2 * G - s.eta c * Gη)
    substantive := -(1 + c) * s.x * Gη
    epsilon := 0
    deferred := s.x * (1 + Gη)
    capped := 0
  }

def parameterizedBaseRawGradient (c : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  if -1 ≤ s.y c then parameterizedActiveRawGradient c s
  else parameterizedFlatRawGradient c s

theorem parameterized_active_reward_add_dot
    (c : ℝ) (s : ParameterizedAnalysisState)
    (outcome : CappedBoundaryOutcome) (hy : -1 ≤ s.y c) :
    parameterizedOrdinaryReward c s outcome +
        (parameterizedActiveRawGradient c s).dotDirection outcome =
      s.x *
        match outcome with
        | .zero =>
            parameterizedDriftZ
              (parameterizedActiveG c (s.y c) s.b)
              (parameterizedActiveGy c (s.y c) s.b)
              (parameterizedActiveGb c (s.y c) s.b)
              (s.y c) s.b
        | .epsilon =>
            parameterizedDriftE c
              (parameterizedActiveG c (s.y c) s.b)
              (parameterizedActiveGy c (s.y c) s.b)
              (parameterizedActiveGb c (s.y c) s.b)
              (s.y c) s.b
        | .immediate =>
            parameterizedDriftI c
              (parameterizedActiveG c (s.y c) s.b)
              (parameterizedActiveGy c (s.y c) s.b)
              (parameterizedActiveGb c (s.y c) s.b)
              (s.y c) s.b (parameterizedThreshold c (s.y c))
        | .deferred | .cap =>
            parameterizedDriftQ c
              (parameterizedActiveG c (s.y c) s.b)
              (parameterizedActiveGy c (s.y c) s.b)
              (parameterizedActiveGb c (s.y c) s.b)
              (s.y c) s.b (parameterizedThreshold c (s.y c)) := by
  have hthreshold :
      s.threshold c = parameterizedThreshold c (s.y c) := by
    simp [ParameterizedAnalysisState.threshold, hy]
  have heta := s.eta_eq_y_add c
  cases outcome with
  | zero =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection,
        parameterizedActiveRawGradient, parameterizedDriftZ]
      ring
  | epsilon =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection,
        parameterizedActiveRawGradient, parameterizedDriftE]
      ring
  | immediate =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection,
        parameterizedActiveRawGradient, parameterizedDriftI, hthreshold]
      rw [heta]
      ring
  | deferred =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection,
        parameterizedActiveRawGradient, parameterizedDriftQ, hthreshold]
      rw [heta]
      ring
  | cap =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection,
        parameterizedActiveRawGradient, parameterizedDriftQ, hthreshold]
      rw [heta]
      ring

theorem parameterized_flat_reward_add_dot
    (c : ℝ) (s : ParameterizedAnalysisState)
    (outcome : CappedBoundaryOutcome) (hy : s.y c < -1) :
    parameterizedOrdinaryReward c s outcome +
        (parameterizedFlatRawGradient c s).dotDirection outcome =
      s.x *
        match outcome with
        | .zero | .epsilon =>
            parameterizedFlatDriftZ c (s.eta c)
        | .immediate =>
            parameterizedFlatDriftI c (s.eta c)
        | .deferred | .cap =>
            parameterizedFlatDriftQ c (s.eta c) := by
  have hthreshold : s.threshold c = 1 := by
    simp [ParameterizedAnalysisState.threshold, not_le.mpr hy]
  cases outcome with
  | zero =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection, parameterizedFlatRawGradient,
        parameterizedFlatDriftZ]
      ring
  | epsilon =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection, parameterizedFlatRawGradient,
        parameterizedFlatDriftZ]
      ring
  | immediate =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection, parameterizedFlatRawGradient,
        parameterizedFlatDriftI, hthreshold]
      ring
  | deferred =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection, parameterizedFlatRawGradient,
        parameterizedFlatDriftQ, hthreshold]
      ring
  | cap =>
      simp only [parameterizedOrdinaryReward,
        CappedRawGradient.dotDirection, parameterizedFlatRawGradient,
        parameterizedFlatDriftQ, hthreshold]
      ring

theorem parameterizedOrdinaryReward_add_baseGradient_nonpos
    {c : ℝ} (hc : 0 < c) {s : ParameterizedAnalysisState}
    (hs : s.Feasible) (outcome : CappedBoundaryOutcome) :
    parameterizedOrdinaryReward c s outcome +
      (parameterizedBaseRawGradient c s).dotDirection outcome ≤ 0 := by
  have hx : 0 ≤ s.x := hs.1.le
  have hy0 := s.y_nonpos hc.le hs
  have hb := s.b_nonneg hs
  unfold parameterizedBaseRawGradient
  split_ifs with hy
  · rw [parameterized_active_reward_add_dot c s outcome hy]
    rcases parameterized_active_all_drifts_nonpos hc hy hy0 hb with
      ⟨hZ, hE, hI, hQ⟩
    cases outcome
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hE
    · exact mul_nonpos_of_nonneg_of_nonpos hx hI
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ
  · have hy' : s.y c < -1 := lt_of_not_ge hy
    rw [parameterized_flat_reward_add_dot c s outcome hy']
    rcases parameterized_flat_all_drifts_nonpos hc with
      ⟨hZ, hI, hQ⟩
    cases outcome
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hI
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ

/-! ## The cap reserve in raw coordinates -/

def capReserveRawGradient (c δ m : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  {
    x := s.x * (2 * capReserveH c δ m s.q -
      s.q * capReserveHPrime c δ m s.q)
    substantive := 0
    epsilon := 0
    deferred := 0
    capped := s.x * capReserveHPrime c δ m s.q
  }

theorem capReserveRawGradient_dot_ordinary
    (c δ m : ℝ) (s : ParameterizedAnalysisState)
    {outcome : CappedBoundaryOutcome} (hcap : outcome ≠ .cap) :
    (capReserveRawGradient c δ m s).dotDirection outcome =
      s.x * capReserveL0 c δ m s.q := by
  cases outcome <;>
    simp_all [capReserveRawGradient, CappedRawGradient.dotDirection,
      capReserveL0] <;> ring

theorem capReserveRawGradient_dot_cap
    (c δ m : ℝ) (s : ParameterizedAnalysisState) :
    (capReserveRawGradient c δ m s).dotDirection .cap =
      s.x * (capReserveL0 c δ m s.q +
        capReserveHPrime c δ m s.q) := by
  simp [capReserveRawGradient, CappedRawGradient.dotDirection,
    capReserveL0]
  ring

/-- Raw gradient of the genuinely zero-extended reserve. -/
def capReserveCompleteRawGradient (c δ m : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  {
    x := s.x * (2 * capReserveH c δ m s.q -
      s.q * capReserveHPrimeFull c δ m s.q)
    substantive := 0
    epsilon := 0
    deferred := 0
    capped := s.x * capReserveHPrimeFull c δ m s.q
  }

theorem capReserveCompleteRawGradient_dot_ordinary
    (c δ m : ℝ) (s : ParameterizedAnalysisState)
    {outcome : CappedBoundaryOutcome} (hcap : outcome ≠ .cap) :
    (capReserveCompleteRawGradient c δ m s).dotDirection outcome =
      s.x * capReserveL0Full c δ m s.q := by
  cases outcome <;>
    simp_all [capReserveCompleteRawGradient,
      CappedRawGradient.dotDirection, capReserveL0Full] <;> ring

theorem capReserveCompleteRawGradient_dot_cap
    (c δ m : ℝ) (s : ParameterizedAnalysisState) :
    (capReserveCompleteRawGradient c δ m s).dotDirection .cap =
      s.x * (capReserveL0Full c δ m s.q +
        capReserveHPrimeFull c δ m s.q) := by
  simp [capReserveCompleteRawGradient,
    CappedRawGradient.dotDirection, capReserveL0Full]
  ring

def cappedFullRawGradient (c δ m : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  (parameterizedBaseRawGradient c s).add
    (capReserveRawGradient c δ m s)

def cappedCompleteRawGradient (c δ m : ℝ)
    (s : ParameterizedAnalysisState) : CappedRawGradient :=
  (parameterizedBaseRawGradient c s).add
    (capReserveCompleteRawGradient c δ m s)

/-- The fifth reward is the ordinary deferred envelope plus `x B(q)`. -/
def cappedEnvelopeReward (c δ : ℝ)
    (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ℝ
  | .zero => parameterizedOrdinaryReward c s .zero
  | .epsilon => parameterizedOrdinaryReward c s .epsilon
  | .immediate => parameterizedOrdinaryReward c s .immediate
  | .deferred => parameterizedOrdinaryReward c s .deferred
  | .cap =>
      parameterizedOrdinaryReward c s .cap +
        s.x * capResidual c δ s.q

/-- The actual mixed-branch envelope: the residual is present only while the
reserve is active.  After the cutoff the exact cap charge is bounded directly
by the ordinary `Q` charge. -/
def mixedCappedEnvelopeReward (c : MixedRatioDomain)
    (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ℝ
  | .zero => parameterizedOrdinaryReward c s .zero
  | .epsilon => parameterizedOrdinaryReward c s .epsilon
  | .immediate => parameterizedOrdinaryReward c s .immediate
  | .deferred => parameterizedOrdinaryReward c s .deferred
  | .cap =>
      if reserveMu s.q ≤ (mixedMass c : ℝ) then
        parameterizedOrdinaryReward c s .cap +
          s.x * capResidual c (mixedReserveDelta c) s.q
      else
        parameterizedOrdinaryReward c s .cap

/-- The complete five-Hamiltonian certificate on the active reserve cone. -/
theorem mixed_cappedEnvelopeReward_add_fullGradient_nonpos
    (c : MixedRatioDomain) {s : ParameterizedAnalysisState}
    (hs : s.Feasible)
    (hreserve : reserveMu s.q ≤ (mixedMass c : ℝ))
    (outcome : CappedBoundaryOutcome) :
    cappedEnvelopeReward c (mixedReserveDelta c) s outcome +
      (cappedFullRawGradient c (mixedReserveDelta c)
        (mixedMass c) s).dotDirection outcome ≤ 0 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hbase :=
    parameterizedOrdinaryReward_add_baseGradient_nonpos
      hc hs outcome
  rw [cappedFullRawGradient,
    CappedRawGradient.dotDirection_add]
  have hq : 0 ≤ s.q := s.q_nonneg hs
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hm1 : (mixedMass c : ℝ) < 1 :=
    (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one
  cases outcome with
  | zero =>
      rw [capReserveRawGradient_dot_ordinary _ _ _ _ (by simp)]
      have hL := capReserveL0_nonpos
        hc.le hm0 hm1 hq hreserve
      rw [← mixedReserveDelta_eq_artanh c] at hL
      simp only [cappedEnvelopeReward] at *
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
  | epsilon =>
      rw [capReserveRawGradient_dot_ordinary _ _ _ _ (by simp)]
      have hL := capReserveL0_nonpos
        hc.le hm0 hm1 hq hreserve
      rw [← mixedReserveDelta_eq_artanh c] at hL
      simp only [cappedEnvelopeReward] at *
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
  | immediate =>
      rw [capReserveRawGradient_dot_ordinary _ _ _ _ (by simp)]
      have hL := capReserveL0_nonpos
        hc.le hm0 hm1 hq hreserve
      rw [← mixedReserveDelta_eq_artanh c] at hL
      simp only [cappedEnvelopeReward] at *
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
  | deferred =>
      rw [capReserveRawGradient_dot_ordinary _ _ _ _ (by simp)]
      have hL := capReserveL0_nonpos
        hc.le hm0 hm1 hq hreserve
      rw [← mixedReserveDelta_eq_artanh c] at hL
      simp only [cappedEnvelopeReward] at *
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
  | cap =>
      rw [capReserveRawGradient_dot_cap]
      have hcancel :=
        mixedReserve_exact_cancellation c hq
      have hcancelScaled :=
        congrArg (fun z : ℝ => s.x * z) hcancel
      simp only [cappedEnvelopeReward] at *
      ring_nf at hcancelScaled
      linarith

/-- The five-Hamiltonian certificate on the entire feasible cone, including
the region after the reserve has switched off. -/
theorem mixed_cappedEnvelopeReward_add_completeGradient_nonpos
    (c : MixedRatioDomain) {s : ParameterizedAnalysisState}
    (hs : s.Feasible) (outcome : CappedBoundaryOutcome) :
    cappedEnvelopeReward c (mixedReserveDelta c) s outcome +
      (cappedCompleteRawGradient c (mixedReserveDelta c)
        (mixedMass c) s).dotDirection outcome ≤ 0 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hbase :=
    parameterizedOrdinaryReward_add_baseGradient_nonpos
      hc hs outcome
  rw [cappedCompleteRawGradient,
    CappedRawGradient.dotDirection_add]
  have hq : 0 ≤ s.q := s.q_nonneg hs
  have hm0 : 0 ≤ (mixedMass c : ℝ) :=
    (mixedMass c).property.1
  have hm1 : (mixedMass c : ℝ) < 1 :=
    (mixedMass c).property.2.trans_lt inv_goldenRatio_lt_one
  by_cases hactive : reserveMu s.q ≤ (mixedMass c : ℝ)
  · have hL :
        capReserveL0Full c (mixedReserveDelta c)
            (mixedMass c) s.q ≤ 0 := by
      rw [capReserveL0Full_eq_active hactive,
        mixedReserveDelta_eq_artanh]
      exact capReserveL0_nonpos hc.le hm0 hm1 hq hactive
    cases outcome with
    | zero =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp)]
        simp only [cappedEnvelopeReward] at *
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
    | epsilon =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp)]
        simp only [cappedEnvelopeReward] at *
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
    | immediate =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp)]
        simp only [cappedEnvelopeReward] at *
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
    | deferred =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp)]
        simp only [cappedEnvelopeReward] at *
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.1.le hL]
    | cap =>
        rw [capReserveCompleteRawGradient_dot_cap]
        have hcancel :=
          mixedReserveFull_exact_cancellation c hq hactive
        have hcancelScaled :=
          congrArg (fun z : ℝ => s.x * z) hcancel
        simp only [cappedEnvelopeReward] at *
        ring_nf at hcancelScaled
        linarith
  · have hcut :
        (mixedMass c : ℝ) ≤ reserveMu s.q :=
      le_of_not_ge hactive
    have hLzero :
        capReserveL0Full c (mixedReserveDelta c)
            (mixedMass c) s.q = 0 := by
      rw [mixedReserveDelta_eq_artanh]
      exact capReserveL0Full_eq_zero_of_cutoff hcut
    have hHpzero :
        capReserveHPrimeFull c (mixedReserveDelta c)
            (mixedMass c) s.q = 0 := by
      rw [mixedReserveDelta_eq_artanh]
      exact capReserveHPrimeFull_eq_zero_of_cutoff hcut
    cases outcome with
    | zero =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp),
          hLzero]
        simpa [cappedEnvelopeReward] using hbase
    | epsilon =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp),
          hLzero]
        simpa [cappedEnvelopeReward] using hbase
    | immediate =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp),
          hLzero]
        simpa [cappedEnvelopeReward] using hbase
    | deferred =>
        rw [capReserveCompleteRawGradient_dot_ordinary _ _ _ _ (by simp),
          hLzero]
        simpa [cappedEnvelopeReward] using hbase
    | cap =>
        rw [capReserveCompleteRawGradient_dot_cap, hLzero, hHpzero]
        have hB :=
          mixed_capResidual_nonpos_of_cutoff c hq hcut
        have hxB :=
          mul_nonpos_of_nonneg_of_nonpos hs.1.le hB
        simp only [cappedEnvelopeReward] at *
        linarith

theorem mixed_actualEnvelopeReward_add_completeGradient_nonpos
    (c : MixedRatioDomain) {s : ParameterizedAnalysisState}
    (hs : s.Feasible) (outcome : CappedBoundaryOutcome) :
    mixedCappedEnvelopeReward c s outcome +
      (cappedCompleteRawGradient c (mixedReserveDelta c)
        (mixedMass c) s).dotDirection outcome ≤ 0 := by
  cases outcome with
  | zero =>
      simpa [mixedCappedEnvelopeReward, cappedEnvelopeReward] using
        mixed_cappedEnvelopeReward_add_completeGradient_nonpos
          c hs .zero
  | epsilon =>
      simpa [mixedCappedEnvelopeReward, cappedEnvelopeReward] using
        mixed_cappedEnvelopeReward_add_completeGradient_nonpos
          c hs .epsilon
  | immediate =>
      simpa [mixedCappedEnvelopeReward, cappedEnvelopeReward] using
        mixed_cappedEnvelopeReward_add_completeGradient_nonpos
          c hs .immediate
  | deferred =>
      simpa [mixedCappedEnvelopeReward, cappedEnvelopeReward] using
        mixed_cappedEnvelopeReward_add_completeGradient_nonpos
          c hs .deferred
  | cap =>
      by_cases hactive :
          reserveMu s.q ≤ (mixedMass c : ℝ)
      · simpa [mixedCappedEnvelopeReward, cappedEnvelopeReward,
          hactive] using
          mixed_cappedEnvelopeReward_add_completeGradient_nonpos
            c hs .cap
      · have hcut :
            (mixedMass c : ℝ) ≤ reserveMu s.q :=
          le_of_not_ge hactive
        have hLzero :
            capReserveL0Full c (mixedReserveDelta c)
                (mixedMass c) s.q = 0 := by
          rw [mixedReserveDelta_eq_artanh]
          exact capReserveL0Full_eq_zero_of_cutoff hcut
        have hHpzero :
            capReserveHPrimeFull c (mixedReserveDelta c)
                (mixedMass c) s.q = 0 := by
          rw [mixedReserveDelta_eq_artanh]
          exact capReserveHPrimeFull_eq_zero_of_cutoff hcut
        have hbase :=
          parameterizedOrdinaryReward_add_baseGradient_nonpos
            (rhoStar_pos.trans_le c.property.1) hs .cap
        rw [cappedCompleteRawGradient,
          CappedRawGradient.dotDirection_add,
          capReserveCompleteRawGradient_dot_cap,
          hLzero, hHpzero]
        simpa [mixedCappedEnvelopeReward, hactive] using hbase

/-! ## The full homogeneous bank and finite-step interface -/

def capReserveRawW (c δ m x K : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 * capReserveH c δ m (K / x)

def cappedFullBankW (c δ m x P E D K : ℝ) : ℝ :=
  parameterizedBankW c x P E D + capReserveRawW c δ m x K

@[simp]
theorem cappedFullBankW_terminal (c δ m P E D K : ℝ) :
    cappedFullBankW c δ m 0 P E D K = 0 := by
  simp [cappedFullBankW, capReserveRawW]

theorem mixed_cappedFullBankW_initial
    (c : MixedRatioDomain) {n : ℝ} (hn : n ≠ 0) :
    cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
      n 0 0 0 0 = (c : ℝ) * n ^ 2 / 2 := by
  rw [cappedFullBankW, parameterizedBankW_initial hn]
  simp [capReserveRawW, hn, capReserveH, reserveMu]
  have hcal :
      parameterizedBankF c 0 +
          capReserveV c (mixedReserveDelta c) (mixedMass c) 0 =
        (c : ℝ) / 2 := by
    simpa [capReserveH, reserveMu] using
      mixedReserve_initial_calibration c
  have hscaled :=
    congrArg (fun z : ℝ => n ^ 2 * z) hcal
  ring_nf at hscaled ⊢
  exact hscaled

/-- The finite Taylor estimate needed to turn the exact first-order mixed
certificate into unit transitions. -/
def HasUniformCappedBankRemainder
    (c δ m C₀ : ℝ) : Prop :=
  ∀ s : ParameterizedAnalysisState, s.Feasible →
    ∀ outcome : CappedBoundaryOutcome,
      cappedFullBankW c δ m
          (s.step outcome).x
          (s.step outcome).substantive
          (s.step outcome).epsilon
          (s.step outcome).deferred
          (s.step outcome).capped -
        cappedFullBankW c δ m
          s.x s.substantive s.epsilon s.deferred s.capped ≤
        (cappedFullRawGradient c δ m s).dotDirection outcome + C₀

def HasUniformCompleteCappedBankRemainder
    (c δ m C₀ : ℝ) : Prop :=
  ∀ s : ParameterizedAnalysisState, s.Feasible →
    ∀ outcome : CappedBoundaryOutcome,
      cappedFullBankW c δ m
          (s.step outcome).x
          (s.step outcome).substantive
          (s.step outcome).epsilon
          (s.step outcome).deferred
          (s.step outcome).capped -
        cappedFullBankW c δ m
          s.x s.substantive s.epsilon s.deferred s.capped ≤
        (cappedCompleteRawGradient c δ m s).dotDirection outcome + C₀

theorem mixed_capped_boundary_one_step
    (c : MixedRatioDomain) {C₀ : ℝ}
    (hTaylor : HasUniformCappedBankRemainder
      c (mixedReserveDelta c) (mixedMass c) C₀)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hreserve : reserveMu s.q ≤ (mixedMass c : ℝ))
    (outcome : CappedBoundaryOutcome) :
    cappedEnvelopeReward c (mixedReserveDelta c) s outcome +
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x
          (s.step outcome).substantive
          (s.step outcome).epsilon
          (s.step outcome).deferred
          (s.step outcome).capped -
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          s.x s.substantive s.epsilon s.deferred s.capped ≤ C₀ := by
  have hlocal :=
    mixed_cappedEnvelopeReward_add_fullGradient_nonpos
      c hs hreserve outcome
  have hrem := hTaylor s hs outcome
  linarith

theorem mixed_capped_boundary_one_step_global
    (c : MixedRatioDomain) {C₀ : ℝ}
    (hTaylor : HasUniformCompleteCappedBankRemainder
      c (mixedReserveDelta c) (mixedMass c) C₀)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (outcome : CappedBoundaryOutcome) :
    cappedEnvelopeReward c (mixedReserveDelta c) s outcome +
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x
          (s.step outcome).substantive
          (s.step outcome).epsilon
          (s.step outcome).deferred
          (s.step outcome).capped -
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          s.x s.substantive s.epsilon s.deferred s.capped ≤ C₀ := by
  have hlocal :=
    mixed_cappedEnvelopeReward_add_completeGradient_nonpos
      c hs outcome
  have hrem := hTaylor s hs outcome
  linarith

theorem mixed_actual_boundary_one_step_global
    (c : MixedRatioDomain) {C₀ : ℝ}
    (hTaylor : HasUniformCompleteCappedBankRemainder
      c (mixedReserveDelta c) (mixedMass c) C₀)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (outcome : CappedBoundaryOutcome) :
    mixedCappedEnvelopeReward c s outcome +
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          (s.step outcome).x
          (s.step outcome).substantive
          (s.step outcome).epsilon
          (s.step outcome).deferred
          (s.step outcome).capped -
        cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
          s.x s.substantive s.epsilon s.deferred s.capped ≤ C₀ := by
  have hlocal :=
    mixed_actualEnvelopeReward_add_completeGradient_nonpos
      c hs outcome
  have hrem := hTaylor s hs outcome
  linarith

end

end SchedulingPaper
