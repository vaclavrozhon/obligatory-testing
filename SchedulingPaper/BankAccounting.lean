import SchedulingPaper.BankPotential

/-!
# Raw-coordinate bank accounting and telescoping

`BankPotential` proves the scalar inequalities.  This file puts them back
into the four raw coordinates `(x,S,e,d)` from the paper, checks that reward
plus the directional derivative proxy is nonpositive for every boundary
outcome, and isolates the only remaining analytic input: a uniform
finite-step Taylor remainder.
-/

namespace SchedulingPaper

noncomputable section

inductive BoundaryOutcome
  | zero
  | epsilon
  | immediate
  | deferred
  deriving DecidableEq, Repr

structure AnalysisState where
  x : ℝ
  substantive : ℝ
  epsilon : ℝ
  deferred : ℝ

namespace AnalysisState

def eta (s : AnalysisState) : ℝ :=
  (s.deferred - RStar * s.substantive) / s.x

def b (s : AnalysisState) : ℝ := s.epsilon / s.x

def y (s : AnalysisState) : ℝ := s.eta - RStar * s.b

def threshold (s : AnalysisState) : ℝ :=
  if -1 ≤ s.y then activeThreshold s.y else 1

def Feasible (s : AnalysisState) : Prop :=
  0 < s.x ∧
  0 ≤ s.substantive ∧
  0 ≤ s.epsilon ∧
  0 ≤ s.deferred ∧
  s.deferred ≤ s.substantive

theorem eta_nonpos {s : AnalysisState} (hs : s.Feasible) :
    s.eta ≤ 0 := by
  have hRS : s.substantive ≤ RStar * s.substantive := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr (one_lt_RStar.le)) hs.2.1]
  have hnum : s.deferred - RStar * s.substantive ≤ 0 := by
    linarith [hs.2.2.2.2, hRS]
  exact div_nonpos_of_nonpos_of_nonneg hnum hs.1.le

theorem b_nonneg {s : AnalysisState} (hs : s.Feasible) :
    0 ≤ s.b := by
  exact div_nonneg hs.2.2.1 hs.1.le

theorem y_nonpos {s : AnalysisState} (hs : s.Feasible) :
    s.y ≤ 0 := by
  unfold y
  have hb := b_nonneg hs
  have hR : 0 ≤ RStar := (lt_trans zero_lt_one one_lt_RStar).le
  nlinarith [mul_nonneg hR hb, eta_nonpos hs]

theorem eta_eq_y_add (s : AnalysisState) :
    s.eta = s.y + RStar * s.b := by
  unfold y
  ring

end AnalysisState

/-- The four counter updates in equation (4.31). -/
def AnalysisState.step (s : AnalysisState) :
    BoundaryOutcome → AnalysisState
  | .zero =>
      { s with x := s.x - 1 }
  | .epsilon =>
      { s with x := s.x - 1, epsilon := s.epsilon + 1 }
  | .immediate =>
      { s with x := s.x - 1, substantive := s.substantive + 1 }
  | .deferred =>
      { s with
        x := s.x - 1
        substantive := s.substantive + 1
        deferred := s.deferred + 1 }

/-- Relaxed local rewards (4.27)--(4.29). -/
def boundaryReward (s : AnalysisState) : BoundaryOutcome → ℝ
  | .zero | .epsilon => s.deferred
  | .immediate =>
      s.deferred + s.threshold * s.x * (1 + s.eta)
  | .deferred =>
      s.deferred + s.threshold * s.x * s.eta

structure RawGradient where
  x : ℝ
  substantive : ℝ
  epsilon : ℝ
  deferred : ℝ

def RawGradient.dotDirection (g : RawGradient) :
    BoundaryOutcome → ℝ
  | .zero => -g.x
  | .epsilon => -g.x + g.epsilon
  | .immediate => -g.x + g.substantive
  | .deferred => -g.x + g.substantive + g.deferred

/-- Chain-rule gradient of `x*d + x² G(y,b)` in the active region. -/
def activeRawGradient (s : AnalysisState) : RawGradient :=
  let G := activeG s.y s.b
  let Gy := activeGy s.y s.b
  let Gb := activeGb s.y s.b
  {
    x := s.deferred + s.x * (2 * G - s.y * Gy - s.b * Gb)
    substantive := -RStar * s.x * Gy
    epsilon := s.x * (-RStar * Gy + Gb)
    deferred := s.x * (1 + Gy)
  }

/-- Chain-rule gradient of `x*d + x² g(η)` in the flat region. -/
def flatRawGradient (s : AnalysisState) : RawGradient :=
  let G := flatG s.eta
  let Gη := flatGPrime s.eta
  {
    x := s.deferred + s.x * (2 * G - s.eta * Gη)
    substantive := -RStar * s.x * Gη
    epsilon := 0
    deferred := s.x * (1 + Gη)
  }

def bankRawGradient (s : AnalysisState) : RawGradient :=
  if -1 ≤ s.y then activeRawGradient s else flatRawGradient s

theorem active_reward_add_dot (s : AnalysisState) (q : BoundaryOutcome)
    (hy : -1 ≤ s.y) :
    boundaryReward s q + (activeRawGradient s).dotDirection q =
      s.x *
        match q with
        | .zero =>
            driftZ (activeG s.y s.b) (activeGy s.y s.b)
              (activeGb s.y s.b) s.y s.b
        | .epsilon =>
            driftE (activeG s.y s.b) (activeGy s.y s.b)
              (activeGb s.y s.b) s.y s.b
        | .immediate =>
            driftI (activeG s.y s.b) (activeGy s.y s.b)
              (activeGb s.y s.b) s.y s.b (activeThreshold s.y)
        | .deferred =>
            driftQ (activeG s.y s.b) (activeGy s.y s.b)
              (activeGb s.y s.b) s.y s.b (activeThreshold s.y) := by
  have hthreshold : s.threshold = activeThreshold s.y := by
    simp [AnalysisState.threshold, hy]
  have heta := s.eta_eq_y_add
  cases q with
  | zero =>
      simp only [boundaryReward, RawGradient.dotDirection,
        activeRawGradient, driftZ]
      ring
  | epsilon =>
      simp only [boundaryReward, RawGradient.dotDirection,
        activeRawGradient, driftE]
      ring
  | immediate =>
      simp only [boundaryReward, RawGradient.dotDirection,
        activeRawGradient, driftI, hthreshold]
      rw [heta]
      ring
  | deferred =>
      simp only [boundaryReward, RawGradient.dotDirection,
        activeRawGradient, driftQ, hthreshold]
      rw [heta]
      unfold RStar
      ring

theorem flat_reward_add_dot (s : AnalysisState) (q : BoundaryOutcome)
    (hy : s.y < -1) :
    boundaryReward s q + (flatRawGradient s).dotDirection q =
      s.x *
        match q with
        | .zero | .epsilon => flatDriftZ s.eta
        | .immediate => flatDriftI s.eta
        | .deferred => flatDriftQ s.eta := by
  have hthreshold : s.threshold = 1 := by
    simp [AnalysisState.threshold, not_le.mpr hy]
  cases q with
  | zero =>
      simp only [boundaryReward, RawGradient.dotDirection,
        flatRawGradient, flatDriftZ]
      ring
  | epsilon =>
      simp only [boundaryReward, RawGradient.dotDirection,
        flatRawGradient, flatDriftZ]
      ring
  | immediate =>
      simp only [boundaryReward, RawGradient.dotDirection,
        flatRawGradient, flatDriftI, hthreshold]
      ring
  | deferred =>
      simp only [boundaryReward, RawGradient.dotDirection,
        flatRawGradient, flatDriftQ, hthreshold]
      unfold RStar
      ring

/-- Equation (4.45): every endpoint reward is paid by the first-order
decrease of the bank. -/
theorem boundaryReward_add_bankRawGradient_nonpos
    {s : AnalysisState} (hs : s.Feasible) (q : BoundaryOutcome) :
    boundaryReward s q + (bankRawGradient s).dotDirection q ≤ 0 := by
  have hx : 0 ≤ s.x := hs.1.le
  have hy0 := s.y_nonpos hs
  have hb := s.b_nonneg hs
  unfold bankRawGradient
  split_ifs with hy
  · rw [active_reward_add_dot s q hy]
    rcases active_all_drifts_nonpos hy hy0 hb with
      ⟨hZ, hE, hI, hQ⟩
    cases q
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hE
    · exact mul_nonpos_of_nonneg_of_nonpos hx hI
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ
  · have hy' : s.y < -1 := lt_of_not_ge hy
    rw [flat_reward_add_dot s q hy']
    rcases flat_all_drifts_nonpos with ⟨hZ, hI, hQ⟩
    cases q
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hZ
    · exact mul_nonpos_of_nonneg_of_nonpos hx hI
    · exact mul_nonpos_of_nonneg_of_nonpos hx hQ

/-! ## From a uniform Taylor remainder to actual unit steps -/

/-- The precise finite-step estimate still needed from bounded curvature. -/
def HasUniformBankRemainder (C₀ : ℝ) : Prop :=
  ∀ s : AnalysisState, s.Feasible → ∀ q : BoundaryOutcome,
    bankW (s.step q).x (s.step q).substantive
        (s.step q).epsilon (s.step q).deferred -
      bankW s.x s.substantive s.epsilon s.deferred ≤
        (bankRawGradient s).dotDirection q + C₀

theorem boundary_one_step
    {C₀ : ℝ} (hTaylor : HasUniformBankRemainder C₀)
    {s : AnalysisState} (hs : s.Feasible) (q : BoundaryOutcome) :
    boundaryReward s q +
        bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        bankW s.x s.substantive s.epsilon s.deferred ≤ C₀ := by
  have hlocal := boundaryReward_add_bankRawGradient_nonpos hs q
  have hrem := hTaylor s hs q
  linarith

/-! ## A generic checked telescoping lemma -/

section Telescope

variable {State Move : Type*}

def trajectoryFinal (step : State → Move → State) :
    State → List Move → State
  | s, [] => s
  | s, q :: qs => trajectoryFinal step (step s q) qs

def trajectoryReward (step : State → Move → State)
    (reward : State → Move → ℝ) :
    State → List Move → ℝ
  | _, [] => 0
  | s, q :: qs =>
      reward s q + trajectoryReward step reward (step s q) qs

theorem trajectory_telescope
    (step : State → Move → State) (reward : State → Move → ℝ)
    (W : State → ℝ) (C₀ : ℝ)
    (hstep : ∀ s q, reward s q + W (step s q) - W s ≤ C₀)
    (s : State) (qs : List Move) :
    trajectoryReward step reward s qs +
        W (trajectoryFinal step s qs) - W s ≤ qs.length * C₀ := by
  induction qs generalizing s with
  | nil =>
      simp [trajectoryReward, trajectoryFinal]
  | cons q qs ih =>
      have hnow := hstep s q
      have htail := ih (step s q)
      simp only [trajectoryReward, trajectoryFinal, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      linarith

end Telescope

/-- Final arithmetic of the obligatory upper proof.  All scheduling and
analytic content is exposed in the two hypotheses rather than hidden. -/
theorem obligatory_excess_from_bank
    {n : ℕ} {F totalReward C₀ : ℝ}
    (hreward : totalReward ≤ rhoStar * n ^ 2 / 2 + n * C₀)
    (hdecomp :
      F ≤ -rhoStar * (n : ℝ) * (n + 1) / 2 + totalReward) :
    F ≤ (C₀ - rhoStar / 2) * n := by
  nlinarith

end

end SchedulingPaper
