import SchedulingPaper.BoundaryRelaxation

/-!
# Reusing the obligatory bank on the finite plateau

For `u ≥ zStar`, the algorithm uses `c = rhoStar`.  A capped endpoint is
already cheaper than the hypothetical ordinary deferred endpoint, so no cap
reserve is needed.  This file proves that fact and then erases the fifth
endpoint to the obligatory four-endpoint word, allowing the already proved
uniform bank remainder to be reused verbatim.
-/

namespace SchedulingPaper

noncomputable section

/-- At the endpoint coefficient, every saturated threshold is at most its
value at state zero. -/
theorem parameterizedAdaptiveThreshold_rhoStar_le_inv
    {y : ℝ} (hy : y ≤ 0) :
    parameterizedAdaptiveThreshold rhoStar y ≤ 1 / rhoStar := by
  by_cases hflat : y ≤ -1
  · rw [show parameterizedAdaptiveThreshold rhoStar y = 1 by
      simp [parameterizedAdaptiveThreshold, hflat]]
    have hr : rhoStar ≤ 1 := rhoStar_lt_one.le
    exact (le_div_iff₀ rhoStar_pos).2 (by simpa using hr)
  · have hyLower : -1 ≤ y := (lt_of_not_ge hflat).le
    rw [parameterizedAdaptiveThreshold]
    simp only [if_neg (not_le.mpr (lt_of_not_ge hflat))]
    have hmono :=
      (parameterizedThreshold_monoOn_Iic rhoStar_pos)
        (show y ∈ Set.Iic 0 from hy)
        (show (0 : ℝ) ∈ Set.Iic 0 by simp)
        hy
    simpa [parameterizedThreshold_rhoStar,
      activeThreshold_at_zero] using hmono

/-- On the whole plateau, the fifth-endpoint bracket is nonpositive. -/
theorem plateau_cap_bracket_nonpos
    {u y : ℝ} (hu : zStar ≤ u) (hy : y ≤ 0) :
    1 - rhoStar *
        (u - 1 - parameterizedAdaptiveThreshold rhoStar y) ≤ 0 := by
  have ha := parameterizedAdaptiveThreshold_rhoStar_le_inv hy
  have htwo := two_div_rhoStar
  have hr0 := rhoStar_pos
  have huDistance : 2 / rhoStar ≤ u - 1 := by
    rw [htwo]
    linarith
  have hsplit :
      2 / rhoStar = 1 / rhoStar + 1 / rhoStar := by ring
  rw [hsplit] at huDistance
  have hdistance :
      1 / rhoStar ≤
        u - 1 - parameterizedAdaptiveThreshold rhoStar y := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hdistance hr0.le
  have hcancel : rhoStar * (1 / rhoStar) = 1 := by
    field_simp [rhoStar_pos.ne']
  nlinarith

/-- Exact cap charge is no larger than the ordinary deferred charge for
every `u ≥ zStar`. -/
theorem plateau_exactCappedCharge_le_ordinary
    {u y I d K immediateSum deferredSum : ℝ}
    (hu : zStar ≤ u) (hK : 0 ≤ K) (hy : y ≤ 0)
    (hImmediate :
      parameterizedAdaptiveThreshold rhoStar y * I ≤ immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold rhoStar y * d ≤ deferredSum) :
    exactCappedCharge rhoStar u I d K immediateSum deferredSum ≤
      ordinaryDeferredCharge rhoStar
        (parameterizedAdaptiveThreshold rhoStar y) I d K := by
  have hcharge :=
    exactCappedCharge_sub_ordinary_le
      (c := rhoStar) (u := u)
      (a := parameterizedAdaptiveThreshold rhoStar y)
      (I := I) (d := d) (K := K)
      (immediateSum := immediateSum)
      (deferredSum := deferredSum)
      rhoStar_pos.le hImmediate hDeferred
  have hbracket := plateau_cap_bracket_nonpos hu hy
  have hscaled :=
    mul_nonpos_of_nonneg_of_nonpos hK hbracket
  linarith

/-- State form of the plateau cap comparison. -/
theorem plateau_exactCappedCharge_le_stateReward
    {u : ℝ} (hu : zStar ≤ u)
    {s : ParameterizedAnalysisState}
    {I d immediateSum deferredSum : ℝ}
    (hs : s.Feasible)
    (hP : s.substantive = I + d + s.capped)
    (hD : s.deferred = d + s.capped)
    (hImmediate :
      parameterizedAdaptiveThreshold rhoStar (s.y rhoStar) * I ≤
        immediateSum)
    (hDeferred :
      parameterizedAdaptiveThreshold rhoStar (s.y rhoStar) * d ≤
        deferredSum) :
    exactCappedCharge rhoStar u I d s.capped
        immediateSum deferredSum ≤
      parameterizedOrdinaryReward rhoStar s .cap := by
  have hordinary :=
    ordinaryDeferredCharge_eq_stateReward
      (c := rhoStar) (I := I) (d := d) (K := s.capped)
      (s := s) hs.1 hP hD
  rw [← hordinary]
  exact plateau_exactCappedCharge_le_ordinary hu
    hs.2.2.2.2.1
    (s.y_nonpos rhoStar_pos.le hs)
    hImmediate hDeferred

/-! ## Erasing the fifth endpoint -/

def eraseCapOutcome : CappedBoundaryOutcome → BoundaryOutcome
  | .zero => .zero
  | .epsilon => .epsilon
  | .immediate => .immediate
  | .deferred | .cap => .deferred

def ParameterizedAnalysisState.toObligatory
    (s : ParameterizedAnalysisState) : AnalysisState where
  x := s.x
  substantive := s.substantive
  epsilon := s.epsilon
  deferred := s.deferred

@[simp]
theorem ParameterizedAnalysisState.toObligatory_step
    (s : ParameterizedAnalysisState) (outcome : CappedBoundaryOutcome) :
    (s.step outcome).toObligatory =
      s.toObligatory.step (eraseCapOutcome outcome) := by
  cases outcome <;>
    rfl

theorem ParameterizedAnalysisState.toObligatory_feasible
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    s.toObligatory.Feasible :=
  ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    hs.2.2.2.2.2.1⟩

theorem ParameterizedAnalysisState.y_rhoStar
    (s : ParameterizedAnalysisState) :
    s.y rhoStar = s.toObligatory.y := by
  unfold ParameterizedAnalysisState.y
    ParameterizedAnalysisState.eta ParameterizedAnalysisState.b
    AnalysisState.y AnalysisState.eta AnalysisState.b
    ParameterizedAnalysisState.toObligatory RStar
  ring

theorem ParameterizedAnalysisState.threshold_rhoStar
    (s : ParameterizedAnalysisState) :
    s.threshold rhoStar = s.toObligatory.threshold := by
  unfold ParameterizedAnalysisState.threshold AnalysisState.threshold
  rw [s.y_rhoStar]
  split_ifs
  · exact parameterizedThreshold_rhoStar _
  · rfl

theorem parameterizedOrdinaryReward_rhoStar
    (s : ParameterizedAnalysisState)
    (outcome : CappedBoundaryOutcome) :
    parameterizedOrdinaryReward rhoStar s outcome =
      boundaryReward s.toObligatory (eraseCapOutcome outcome) := by
  have heta :
      s.eta rhoStar = s.toObligatory.eta := by
    unfold ParameterizedAnalysisState.eta AnalysisState.eta
      ParameterizedAnalysisState.toObligatory RStar
    rfl
  have hthreshold := s.threshold_rhoStar
  cases outcome <;>
    simp only [parameterizedOrdinaryReward, boundaryReward,
      eraseCapOutcome, hthreshold, heta] <;>
    rfl

theorem plateau_trajectoryReward_erasure
    (s : ParameterizedAnalysisState)
    (outcomes : List CappedBoundaryOutcome) :
    trajectoryReward ParameterizedAnalysisState.step
        (parameterizedOrdinaryReward rhoStar) s outcomes =
      trajectoryReward AnalysisState.step boundaryReward
        s.toObligatory (outcomes.map eraseCapOutcome) := by
  induction outcomes generalizing s with
  | nil =>
      simp [trajectoryReward]
  | cons outcome outcomes ih =>
      simp only [trajectoryReward, List.map_cons]
      rw [parameterizedOrdinaryReward_rhoStar,
        ih (s.step outcome),
        ParameterizedAnalysisState.toObligatory_step]

theorem initialParameterized_toObligatory (n : ℕ) :
    (initialParameterizedAnalysisState n).toObligatory =
      initialAnalysisState n := by
  rfl

/-- Every five-letter plateau word is paid by the already proved obligatory
bank, with the same absolute uniform constant. -/
theorem plateau_boundary_rewards_uniform
    (outcomes : List CappedBoundaryOutcome) :
    trajectoryReward ParameterizedAnalysisState.step
        (parameterizedOrdinaryReward rhoStar)
        (initialParameterizedAnalysisState outcomes.length) outcomes ≤
      rhoStar * outcomes.length ^ 2 / 2 +
        outcomes.length *
          uniformBankRemainderOnUnitCountdownConstant := by
  have h :=
    obligatory_boundary_rewards_uniform
      (outcomes.map eraseCapOutcome)
  simp only [List.length_map] at h
  rw [← initialParameterized_toObligatory outcomes.length] at h
  rw [← plateau_trajectoryReward_erasure] at h
  exact h

end

end SchedulingPaper
