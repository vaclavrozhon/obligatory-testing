import SchedulingPaper.ReachableBankRemainder
import SchedulingPaper.CapEndpointAccounting

/-!
# Reachable bank trajectories and telescoping

The raw bank interfaces deliberately allow real-valued states.  A genuine
word of `n` boundary outcomes, however, visits only the states with
`x = n, n-1, ..., 1` before its transitions.  This module records that
reachability invariant and performs the finite telescoping step for both the
four-endpoint and five-endpoint banks.

This distinction matters: a unit step from an arbitrary real state
`0 < x < 1` leaves the physical cone and need not have a uniform Taylor
remainder.
-/

namespace SchedulingPaper

noncomputable section

section Generic

variable {State Move : Type*}

/-- Every pre-state along a finite word satisfies `Good`. -/
def TrajectoryGood (step : State → Move → State) (Good : State → Prop) :
    State → List Move → Prop
  | _, [] => True
  | state, move :: moves =>
      Good state ∧ TrajectoryGood step Good (step state move) moves

theorem TrajectoryGood.mono
    (step : State → Move → State) {Strong Good : State → Prop}
    (hmono : ∀ state, Strong state → Good state)
    {state : State} {moves : List Move}
    (hgood : TrajectoryGood step Strong state moves) :
    TrajectoryGood step Good state moves := by
  induction moves generalizing state with
  | nil =>
      simp [TrajectoryGood]
  | cons move moves ih =>
      rcases hgood with ⟨hstate, htail⟩
      exact ⟨hmono state hstate, ih htail⟩

/-- Telescoping when the one-step inequality is known only on reachable
pre-states. -/
theorem trajectory_telescope_of_good
    (step : State → Move → State) (reward : State → Move → ℝ)
    (W : State → ℝ) (C₀ : ℝ) (Good : State → Prop)
    (hstep :
      ∀ state, Good state → ∀ move,
        reward state move + W (step state move) - W state ≤ C₀)
    (state : State) (moves : List Move)
    (hgood : TrajectoryGood step Good state moves) :
    trajectoryReward step reward state moves +
        W (trajectoryFinal step state moves) - W state ≤
      moves.length * C₀ := by
  induction moves generalizing state with
  | nil =>
      simp [trajectoryReward, trajectoryFinal]
  | cons move moves ih =>
      rcases hgood with ⟨hstate, htail⟩
      have hnow := hstep state hstate move
      have hlater := ih (step state move) htail
      simp only [trajectoryReward, trajectoryFinal, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      linarith

end Generic

/-! ## Four-endpoint trajectories -/

def AnalysisState.Reachable (s : AnalysisState) : Prop :=
  s.Feasible ∧ s.IsUnitCountdownPreState

def initialAnalysisState (n : ℕ) : AnalysisState where
  x := n
  substantive := 0
  epsilon := 0
  deferred := 0

/-- A remainder interface with exactly the physical domain needed by a word
of unit boundary transitions. -/
def HasReachableBankRemainder (C₀ : ℝ) : Prop :=
  HasUniformBankRemainderOnUnitCountdown C₀

theorem analysis_trajectory_good_of_remaining
    (s : AnalysisState) (outcomes : List BoundaryOutcome)
    (hx : s.x = outcomes.length)
    (hS : 0 ≤ s.substantive) (he : 0 ≤ s.epsilon)
    (hd : 0 ≤ s.deferred) (hdS : s.deferred ≤ s.substantive) :
    TrajectoryGood AnalysisState.step AnalysisState.Reachable s outcomes := by
  induction outcomes generalizing s with
  | nil =>
      simp [TrajectoryGood]
  | cons outcome outcomes ih =>
      have hxpos : 0 < s.x := by
        rw [hx]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        positivity
      have hreach : s.Reachable :=
        ⟨⟨hxpos, hS, he, hd, hdS⟩, by
          unfold AnalysisState.IsUnitCountdownPreState
          by_cases hnil : outcomes = []
          · subst outcomes
            left
            simpa using hx
          · right
            have hlen : 1 ≤ outcomes.length := by
              exact List.length_pos_iff.mpr hnil
            rw [hx]
            norm_num only [List.length_cons, Nat.cast_add, Nat.cast_one]
            exact_mod_cast Nat.succ_le_succ hlen⟩
      refine ⟨hreach, ih (s.step outcome) ?_ ?_ ?_ ?_ ?_⟩
      · cases outcome <;>
          simp [AnalysisState.step, hx]
      · cases outcome <;>
          simp [AnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [AnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [AnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [AnalysisState.step] <;> linarith

theorem initialAnalysisState_trajectory_good
    (outcomes : List BoundaryOutcome) :
    TrajectoryGood AnalysisState.step AnalysisState.Reachable
      (initialAnalysisState outcomes.length) outcomes := by
  apply analysis_trajectory_good_of_remaining
  · rfl
  · simp [initialAnalysisState]
  · simp [initialAnalysisState]
  · simp [initialAnalysisState]
  · simp [initialAnalysisState]

theorem trajectoryFinal_analysis_x
    (s : AnalysisState) (outcomes : List BoundaryOutcome) :
    (trajectoryFinal AnalysisState.step s outcomes).x =
      s.x - outcomes.length := by
  induction outcomes generalizing s with
  | nil =>
      simp [trajectoryFinal]
  | cons outcome outcomes ih =>
      rw [trajectoryFinal, ih]
      cases outcome <;>
        simp [AnalysisState.step] <;> ring

theorem trajectoryFinal_initialAnalysisState_x
    (outcomes : List BoundaryOutcome) :
    (trajectoryFinal AnalysisState.step
      (initialAnalysisState outcomes.length) outcomes).x = 0 := by
  rw [trajectoryFinal_analysis_x]
  simp [initialAnalysisState]

/-- The complete finite telescope for an arbitrary four-endpoint word. -/
theorem obligatory_boundary_rewards_le
    {C₀ : ℝ} (hTaylor : HasReachableBankRemainder C₀)
    (outcomes : List BoundaryOutcome) :
    trajectoryReward AnalysisState.step boundaryReward
        (initialAnalysisState outcomes.length) outcomes ≤
      rhoStar * outcomes.length ^ 2 / 2 + outcomes.length * C₀ := by
  let W : AnalysisState → ℝ :=
    fun s => bankW s.x s.substantive s.epsilon s.deferred
  have hstep :
      ∀ s, s.Reachable → ∀ q,
        boundaryReward s q + W (s.step q) - W s ≤ C₀ := by
    intro s hs q
    have hlocal := boundaryReward_add_bankRawGradient_nonpos hs.1 q
    have hrem := hTaylor s hs.1 hs.2 q
    dsimp [W] at *
    linarith
  have htelescope :=
    trajectory_telescope_of_good AnalysisState.step boundaryReward
      W C₀ AnalysisState.Reachable hstep
      (initialAnalysisState outcomes.length) outcomes
      (initialAnalysisState_trajectory_good outcomes)
  have hfinal :
      W (trajectoryFinal AnalysisState.step
        (initialAnalysisState outcomes.length) outcomes) = 0 := by
    dsimp [W]
    rw [show
      (trajectoryFinal AnalysisState.step
        (initialAnalysisState outcomes.length) outcomes).x = 0 from
          trajectoryFinal_initialAnalysisState_x outcomes]
    exact bankW_at_terminal _ _ _
  by_cases hn : outcomes.length = 0
  · have houtcomes : outcomes = [] := by simpa using hn
    subst outcomes
    simp [trajectoryReward]
  · have hinitial :
        W (initialAnalysisState outcomes.length) =
          rhoStar * outcomes.length ^ 2 / 2 := by
      dsimp [W, initialAnalysisState]
      exact bankW_initial (by exact_mod_cast hn)
    rw [hfinal, hinitial] at htelescope
    linarith

/-- Unconditional finite four-endpoint bank bound, using the proved uniform
remainder on the integral unit countdown. -/
theorem obligatory_boundary_rewards_uniform
    (outcomes : List BoundaryOutcome) :
    trajectoryReward AnalysisState.step boundaryReward
        (initialAnalysisState outcomes.length) outcomes ≤
      rhoStar * outcomes.length ^ 2 / 2 +
        outcomes.length * uniformBankRemainderOnUnitCountdownConstant :=
  obligatory_boundary_rewards_le
    uniformBankRemainderOnUnitCountdown outcomes

/-! ## Five-endpoint trajectories -/

def ParameterizedAnalysisState.Reachable
    (s : ParameterizedAnalysisState) : Prop :=
  s.Feasible ∧ (s.x = 1 ∨ 2 ≤ s.x)

def initialParameterizedAnalysisState (n : ℕ) :
    ParameterizedAnalysisState where
  x := n
  substantive := 0
  epsilon := 0
  deferred := 0
  capped := 0

def HasReachableCompleteCappedBankRemainder
    (c δ m C₀ : ℝ) : Prop :=
  ∀ s : ParameterizedAnalysisState, s.Reachable →
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

theorem parameterized_trajectory_good_of_remaining
    (s : ParameterizedAnalysisState)
    (outcomes : List CappedBoundaryOutcome)
    (hx : s.x = outcomes.length)
    (hP : 0 ≤ s.substantive) (hE : 0 ≤ s.epsilon)
    (hD : 0 ≤ s.deferred) (hK : 0 ≤ s.capped)
    (hDP : s.deferred ≤ s.substantive)
    (hKP : s.capped ≤ s.substantive) :
    TrajectoryGood ParameterizedAnalysisState.step
      ParameterizedAnalysisState.Reachable s outcomes := by
  induction outcomes generalizing s with
  | nil =>
      simp [TrajectoryGood]
  | cons outcome outcomes ih =>
      have hxpos : 0 < s.x := by
        rw [hx]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        positivity
      have hreach : s.Reachable :=
        ⟨⟨hxpos, hP, hE, hD, hK, hDP, hKP⟩, by
          by_cases hnil : outcomes = []
          · subst outcomes
            left
            simpa using hx
          · right
            have hlen : 1 ≤ outcomes.length := by
              exact List.length_pos_iff.mpr hnil
            rw [hx]
            norm_num only [List.length_cons, Nat.cast_add, Nat.cast_one]
            exact_mod_cast Nat.succ_le_succ hlen⟩
      refine ⟨hreach, ih (s.step outcome) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step, hx]
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith
      · cases outcome <;>
          simp [ParameterizedAnalysisState.step] <;> linarith

theorem initialParameterizedAnalysisState_trajectory_good
    (outcomes : List CappedBoundaryOutcome) :
    TrajectoryGood ParameterizedAnalysisState.step
      ParameterizedAnalysisState.Reachable
      (initialParameterizedAnalysisState outcomes.length) outcomes := by
  apply parameterized_trajectory_good_of_remaining
  all_goals simp [initialParameterizedAnalysisState]

theorem trajectoryFinal_parameterized_x
    (s : ParameterizedAnalysisState)
    (outcomes : List CappedBoundaryOutcome) :
    (trajectoryFinal ParameterizedAnalysisState.step s outcomes).x =
      s.x - outcomes.length := by
  induction outcomes generalizing s with
  | nil =>
      simp [trajectoryFinal]
  | cons outcome outcomes ih =>
      rw [trajectoryFinal, ih]
      cases outcome <;>
        simp [ParameterizedAnalysisState.step] <;> ring

theorem trajectoryFinal_initialParameterizedAnalysisState_x
    (outcomes : List CappedBoundaryOutcome) :
    (trajectoryFinal ParameterizedAnalysisState.step
      (initialParameterizedAnalysisState outcomes.length) outcomes).x = 0 := by
  rw [trajectoryFinal_parameterized_x]
  simp [initialParameterizedAnalysisState]

/-- Conditional finite telescope for every five-endpoint mixed word.  Its
only analytic hypothesis is now the reachable (rather than all-real-state)
Taylor estimate. -/
theorem mixed_boundary_rewards_le
    (c : MixedRatioDomain) {C₀ : ℝ}
    (hTaylor : HasReachableCompleteCappedBankRemainder
      c (mixedReserveDelta c) (mixedMass c) C₀)
    (outcomes : List CappedBoundaryOutcome) :
    trajectoryReward ParameterizedAnalysisState.step
        (mixedCappedEnvelopeReward c)
        (initialParameterizedAnalysisState outcomes.length) outcomes ≤
      (c : ℝ) * outcomes.length ^ 2 / 2 +
        outcomes.length * C₀ := by
  let W : ParameterizedAnalysisState → ℝ :=
    fun s => cappedFullBankW c (mixedReserveDelta c) (mixedMass c)
      s.x s.substantive s.epsilon s.deferred s.capped
  have hstep :
      ∀ s, s.Reachable → ∀ q,
        mixedCappedEnvelopeReward c s q +
          W (s.step q) - W s ≤ C₀ := by
    intro s hs q
    have hlocal :=
      mixed_actualEnvelopeReward_add_completeGradient_nonpos c hs.1 q
    have hrem := hTaylor s hs q
    dsimp [W] at *
    linarith
  have htelescope :=
    trajectory_telescope_of_good ParameterizedAnalysisState.step
      (mixedCappedEnvelopeReward c) W C₀
      ParameterizedAnalysisState.Reachable hstep
      (initialParameterizedAnalysisState outcomes.length) outcomes
      (initialParameterizedAnalysisState_trajectory_good outcomes)
  have hfinal :
      W (trajectoryFinal ParameterizedAnalysisState.step
        (initialParameterizedAnalysisState outcomes.length) outcomes) = 0 := by
    dsimp [W]
    rw [show
      (trajectoryFinal ParameterizedAnalysisState.step
        (initialParameterizedAnalysisState outcomes.length) outcomes).x = 0
        from trajectoryFinal_initialParameterizedAnalysisState_x outcomes]
    exact cappedFullBankW_terminal _ _ _ _ _ _ _
  by_cases hn : outcomes.length = 0
  · have houtcomes : outcomes = [] := by simpa using hn
    subst outcomes
    simp [trajectoryReward]
  · have hinitial :
        W (initialParameterizedAnalysisState outcomes.length) =
          (c : ℝ) * outcomes.length ^ 2 / 2 := by
      dsimp [W, initialParameterizedAnalysisState]
      exact mixed_cappedFullBankW_initial c (by exact_mod_cast hn)
    rw [hfinal, hinitial] at htelescope
    linarith

end

end SchedulingPaper
