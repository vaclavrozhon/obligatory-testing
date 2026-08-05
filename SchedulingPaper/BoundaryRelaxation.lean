import SchedulingPaper.BankTelescope

/-!
# Exact endpoint charges versus the bank envelopes

The pair decomposition in the manuscript first produces exact local charges.
The bank uses slightly larger charges obtained by deleting favorable diagonal
terms.  This file checks that relaxation explicitly for both the obligatory
four-endpoint account and the parameterized finite-cap account.
-/

namespace SchedulingPaper

noncomputable section

/-! ## Obligatory four-endpoint relaxation -/

/-- Exact local charges (before deleting the favorable own-job terms). -/
def exactBoundaryReward (s : AnalysisState) : BoundaryOutcome → ℝ
  | .zero | .epsilon => s.deferred
  | .immediate =>
      s.deferred + s.threshold *
        (s.x + s.deferred - RStar * s.substantive - RStar)
  | .deferred =>
      s.deferred + s.threshold *
        (s.deferred - RStar * s.substantive - rhoStar)

theorem AnalysisState.threshold_ge_one
    {s : AnalysisState} (hs : s.Feasible) :
    1 ≤ s.threshold := by
  unfold AnalysisState.threshold
  split_ifs with hy
  · exact activeThreshold_ge_one hy (s.y_nonpos hs)
  · exact le_rfl

theorem boundaryReward_immediate_raw
    {s : AnalysisState} (hx : s.x ≠ 0) :
    boundaryReward s .immediate =
      s.deferred + s.threshold *
        (s.x + s.deferred - RStar * s.substantive) := by
  simp only [boundaryReward]
  unfold AnalysisState.eta
  field_simp [hx]
  ring

theorem boundaryReward_deferred_raw
    {s : AnalysisState} (hx : s.x ≠ 0) :
    boundaryReward s .deferred =
      s.deferred + s.threshold *
        (s.deferred - RStar * s.substantive) := by
  simp only [boundaryReward]
  unfold AnalysisState.eta
  field_simp [hx]

/-- Every exact endpoint charge is no larger than the relaxed reward paid by
the bank. -/
theorem exactBoundaryReward_le_boundaryReward
    {s : AnalysisState} (hs : s.Feasible) (outcome : BoundaryOutcome) :
    exactBoundaryReward s outcome ≤ boundaryReward s outcome := by
  have ha : 0 ≤ s.threshold := (s.threshold_ge_one hs).trans' zero_le_one
  have hR : 0 ≤ RStar :=
    (lt_trans zero_lt_one one_lt_RStar).le
  have hρ : 0 ≤ rhoStar := rhoStar_pos.le
  cases outcome with
  | zero =>
      simp [exactBoundaryReward, boundaryReward]
  | epsilon =>
      simp [exactBoundaryReward, boundaryReward]
  | immediate =>
      rw [boundaryReward_immediate_raw hs.1.ne']
      simp only [exactBoundaryReward]
      nlinarith [mul_nonneg ha hR]
  | deferred =>
      rw [boundaryReward_deferred_raw hs.1.ne']
      simp only [exactBoundaryReward]
      nlinarith [mul_nonneg ha hρ]

/-- Pointwise relaxation lifts to every reachable endpoint word. -/
theorem exact_trajectoryReward_le_relaxed
    (s : AnalysisState) (outcomes : List BoundaryOutcome)
    (hgood :
      TrajectoryGood AnalysisState.step AnalysisState.Feasible s outcomes) :
    trajectoryReward AnalysisState.step exactBoundaryReward s outcomes ≤
      trajectoryReward AnalysisState.step boundaryReward s outcomes := by
  induction outcomes generalizing s with
  | nil =>
      simp [trajectoryReward]
  | cons outcome outcomes ih =>
      rcases hgood with ⟨hs, htail⟩
      simp only [trajectoryReward]
      exact add_le_add
        (exactBoundaryReward_le_boundaryReward hs outcome)
        (ih (s.step outcome) htail)

/-- Exact four-endpoint rewards inherit the unconditional finite bank
bound. -/
theorem exact_obligatory_boundary_rewards_uniform
    (outcomes : List BoundaryOutcome) :
    trajectoryReward AnalysisState.step exactBoundaryReward
        (initialAnalysisState outcomes.length) outcomes ≤
      rhoStar * outcomes.length ^ 2 / 2 +
        outcomes.length * uniformBankRemainderOnUnitCountdownConstant := by
  have hreachable :=
    initialAnalysisState_trajectory_good outcomes
  have hfeasible :
      TrajectoryGood AnalysisState.step AnalysisState.Feasible
        (initialAnalysisState outcomes.length) outcomes :=
    hreachable.mono AnalysisState.step (fun _ hs => hs.1)
  exact
    (exact_trajectoryReward_le_relaxed _ _ hfeasible).trans
      (obligatory_boundary_rewards_uniform outcomes)

/-- The complete boundary-word excess after restoring the universal
`-ρ n(n+1)/2` term from the exact pair decomposition. -/
def obligatoryBoundaryExcess (outcomes : List BoundaryOutcome) : ℝ :=
  -rhoStar * outcomes.length * (outcomes.length + 1) / 2 +
    trajectoryReward AnalysisState.step exactBoundaryReward
      (initialAnalysisState outcomes.length) outcomes

theorem obligatoryBoundaryExcess_linear
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryExcess outcomes ≤
      (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2) *
        outcomes.length := by
  have hreward := exact_obligatory_boundary_rewards_uniform outcomes
  unfold obligatoryBoundaryExcess
  nlinarith

/-! ## Parameterized finite-cap relaxation -/

/-- Exact ordinary endpoint charge.  The fifth (`cap`) endpoint has a
different exact formula and is treated by `exactCappedCharge`; here it shares
the ordinary deferred diagonal term only as a comparison value. -/
def parameterizedExactOrdinaryReward (c : ℝ)
    (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ℝ
  | .zero | .epsilon => s.deferred
  | .immediate =>
      s.deferred + s.threshold c *
        (s.x + s.deferred - (1 + c) * s.substantive - (1 + c))
  | .deferred | .cap =>
      s.deferred + s.threshold c *
        (s.deferred - (1 + c) * s.substantive - c)

theorem ParameterizedAnalysisState.threshold_ge_one
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    1 ≤ s.threshold c := by
  unfold ParameterizedAnalysisState.threshold
  split_ifs with hy
  · exact parameterizedThreshold_ge_one hc hy (s.y_nonpos hc.le hs)
  · exact le_rfl

theorem parameterizedOrdinaryReward_immediate_raw
    (c : ℝ) {s : ParameterizedAnalysisState} (hx : s.x ≠ 0) :
    parameterizedOrdinaryReward c s .immediate =
      s.deferred + s.threshold c *
        (s.x + s.deferred - (1 + c) * s.substantive) := by
  simp only [parameterizedOrdinaryReward]
  unfold ParameterizedAnalysisState.eta
  field_simp [hx]
  ring

theorem parameterizedOrdinaryReward_deferred_raw
    (c : ℝ) {s : ParameterizedAnalysisState} (hx : s.x ≠ 0) :
    parameterizedOrdinaryReward c s .deferred =
      s.deferred + s.threshold c *
        (s.deferred - (1 + c) * s.substantive) := by
  simp only [parameterizedOrdinaryReward]
  unfold ParameterizedAnalysisState.eta
  field_simp [hx]

theorem parameterizedOrdinaryReward_cap_raw
    (c : ℝ) {s : ParameterizedAnalysisState} (hx : s.x ≠ 0) :
    parameterizedOrdinaryReward c s .cap =
      s.deferred + s.threshold c *
        (s.deferred - (1 + c) * s.substantive) := by
  simp only [parameterizedOrdinaryReward]
  unfold ParameterizedAnalysisState.eta
  field_simp [hx]

/-- Deleting the two favorable diagonal terms enlarges every ordinary local
charge. -/
theorem parameterizedExactOrdinaryReward_le
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (outcome : CappedBoundaryOutcome) :
    parameterizedExactOrdinaryReward c s outcome ≤
      parameterizedOrdinaryReward c s outcome := by
  have ha : 0 ≤ s.threshold c :=
    (s.threshold_ge_one hc hs).trans' zero_le_one
  have hC : 0 ≤ 1 + c := by linarith
  have hc0 : 0 ≤ c := hc.le
  cases outcome with
  | zero =>
      simp [parameterizedExactOrdinaryReward,
        parameterizedOrdinaryReward]
  | epsilon =>
      simp [parameterizedExactOrdinaryReward,
        parameterizedOrdinaryReward]
  | immediate =>
      rw [parameterizedOrdinaryReward_immediate_raw c hs.1.ne']
      simp only [parameterizedExactOrdinaryReward]
      nlinarith [mul_nonneg ha hC]
  | deferred =>
      rw [parameterizedOrdinaryReward_deferred_raw c hs.1.ne']
      simp only [parameterizedExactOrdinaryReward]
      nlinarith [mul_nonneg ha hc0]
  | cap =>
      rw [parameterizedOrdinaryReward_cap_raw c hs.1.ne']
      simp only [parameterizedExactOrdinaryReward]
      nlinarith [mul_nonneg ha hc0]

end

end SchedulingPaper
