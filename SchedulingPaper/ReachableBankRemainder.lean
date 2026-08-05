import SchedulingPaper.UniformBankRemainder

/-!
# Uniform bank remainder on reachable countdown states

This module adds the terminal layer `x = 1 → 0` to the uniform remainder
proved for `2 ≤ x`.  Since raw states use real-valued coordinates, the
reachable countdown domain is stated explicitly as `x = 1 ∨ 2 ≤ x`; this
does not accidentally include the artificial interval `1 < x < 2`.
-/

namespace SchedulingPaper

noncomputable section

def activeTerminalRemainder
    (q : BoundaryOutcome) (y b : ℝ) : ℝ :=
  activeG y b - deferredStepRate q -
    (y + AnalysisState.yStepRate q) * activeGy y b -
    (b + bStepRate q) * activeGb y b

def activeTerminalRemainderFor
    (q : BoundaryOutcome) (p : ℝ × ℝ) : ℝ :=
  activeTerminalRemainder q p.1 p.2

theorem activeTerminalRemainderFor_continuousOn
    (q : BoundaryOutcome) :
    ContinuousOn (activeTerminalRemainderFor q)
      (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (0 : ℝ) (1 / RStar)) := by
  intro p hp
  have hy0 : p.1 ≤ 0 := hp.1.2
  have hden : rhoStar - 2 * p.1 ≠ 0 :=
    (active_denominator_pos hy0).ne'
  have hA : ContinuousAt activeThreshold p.1 :=
    (activeThreshold_hasDerivAt hy0).continuousAt
  have hAcomp :
      ContinuousAt (fun z : ℝ × ℝ => activeThreshold z.1) p := by
    change ContinuousAt (activeThreshold ∘ Prod.fst) p
    exact hA.comp continuousAt_fst
  unfold activeTerminalRemainderFor activeTerminalRemainder
    activeG activeGy activeGb bankHPrime bankF bankH
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp)

theorem exists_activeTerminalUniformRemainder :
    ∃ C : ℝ, ∀ q : BoundaryOutcome,
      ∀ y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ b ∈ Set.Icc (0 : ℝ) (1 / RStar),
        activeTerminalRemainder q y b ≤ C := by
  have hcompact :
      IsCompact (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / RStar)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound (q : BoundaryOutcome) :
      ∃ C : ℝ, ∀ p ∈
          (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (0 : ℝ) (1 / RStar)),
        activeTerminalRemainderFor q p ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (activeTerminalRemainderFor_continuousOn q)
    refine ⟨C, ?_⟩
    intro p hp
    simpa [Real.norm_eq_abs] using
      (le_abs_self (activeTerminalRemainderFor q p)).trans (by
        simpa [Real.norm_eq_abs] using hC p hp)
  obtain ⟨Cz, hz⟩ := hbound .zero
  obtain ⟨Ce, he⟩ := hbound .epsilon
  obtain ⟨Ci, hi⟩ := hbound .immediate
  obtain ⟨Cd, hd⟩ := hbound .deferred
  refine ⟨max (max Cz Ce) (max Ci Cd), ?_⟩
  intro q y hy b hb
  have hp : (y, b) ∈
      (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (0 : ℝ) (1 / RStar)) :=
    ⟨hy, hb⟩
  cases q with
  | zero =>
      exact (hz (y, b) hp).trans
        (le_max_of_le_left (le_max_left _ _))
  | epsilon =>
      exact (he (y, b) hp).trans
        (le_max_of_le_left (le_max_right _ _))
  | immediate =>
      exact (hi (y, b) hp).trans
        (le_max_of_le_right (le_max_left _ _))
  | deferred =>
      exact (hd (y, b) hp).trans
        (le_max_of_le_right (le_max_right _ _))

theorem activeTerminal_residual_eq
    (s : AnalysisState) (q : BoundaryOutcome) (hx : s.x = 1) :
    -activePerspectivePath s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q) 0 -
      activePerspectiveSlope s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q) 0 =
      activeTerminalRemainder q s.y s.b := by
  rw [hx]
  unfold activeTerminalRemainder activePerspectivePath
    activePerspectiveSlope normalizedAffinePath
  ring_nf

theorem exists_active_terminal_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : AnalysisState), s.Feasible → s.x = 1 →
      ∀ q : BoundaryOutcome, -1 ≤ s.y →
        bankW (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            bankW s.x s.substantive s.epsilon s.deferred ≤
          (bankRawGradient s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ := exists_activeTerminalUniformRemainder
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro s hs hx q hy
  have hy0 : s.y ≤ 0 := AnalysisState.y_nonpos hs
  have hb := AnalysisState.active_eta_b_bounds hs hy
  have hbound :=
    hC₀ q s.y ⟨hy, hy0⟩ s.b ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hbound' :
      activeTerminalRemainder q s.y s.b ≤ max C₀ 0 :=
    hbound.trans (le_max_left _ _)
  have hnext0 : (s.step q).x = 0 := by
    cases q <;> simp [AnalysisState.step, hx]
  have hbankNext :
      bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred = 0 := by
    rw [hnext0]
    exact bankW_at_terminal _ _ _
  have hpathZero :=
    activePerspectivePath_eq_bankW_interpolated
      (s := s) q (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hy)
  simp only [AnalysisState.interpolatedStep_zero] at hpathZero
  have hresidual := activeTerminal_residual_eq s q hx
  have hgrad :
      (bankRawGradient s).dotDirection q =
        activePerspectiveSlope s.x s.deferred s.y s.b
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) 0 := by
    unfold bankRawGradient
    rw [if_pos hy]
    exact (activePerspectiveSlope_zero_eq_dotDirection
      s q hs.1.ne').symm
  rw [hbankNext, ← hpathZero, hgrad]
  linarith

/-- A pre-state on an integral unit countdown is either the terminal
`x = 1` layer or has at least two units remaining.  Stating the real-valued
disjunction explicitly avoids accidentally including `1 < x < 2`. -/
def AnalysisState.IsUnitCountdownPreState (s : AnalysisState) : Prop :=
  s.x = 1 ∨ 2 ≤ s.x

theorem AnalysisState.IsUnitCountdownPreState.one_le
    {s : AnalysisState} (hs : s.IsUnitCountdownPreState) :
    1 ≤ s.x := by
  rcases hs with h | h
  · rw [h]
  · linarith

def HasUniformBankRemainderOnUnitCountdown (C : ℝ) : Prop :=
  ∀ (s : AnalysisState), s.Feasible → s.IsUnitCountdownPreState →
    ∀ q : BoundaryOutcome,
      bankW (s.step q).x (s.step q).substantive
            (s.step q).epsilon (s.step q).deferred -
          bankW s.x s.substantive s.epsilon s.deferred ≤
        (bankRawGradient s).dotDirection q + C

theorem exists_terminal_uniformBankRemainder :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : AnalysisState), s.Feasible → s.x = 1 →
      ∀ q : BoundaryOutcome,
        bankW (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            bankW s.x s.substantive s.epsilon s.deferred ≤
          (bankRawGradient s).dotDirection q + C := by
  obtain ⟨Cactive, hCactive, hactive⟩ :=
    exists_active_terminal_uniform_remainder
  let C := max Cactive saturatedUniformRemainder
  have hCflat : 0 ≤ saturatedUniformRemainder := by
    unfold saturatedUniformRemainder
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num)
        (lt_trans zero_lt_one one_lt_RStar).le)
  have hC : 0 ≤ C :=
    hCactive.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs hx q
  by_cases hy : -1 ≤ s.y
  · have h := hactive s hs hx q hy
    have hle : Cactive ≤ C := le_max_left _ _
    linarith
  · have h := flat_terminal_uniform_remainder
      hs hx (lt_of_not_ge hy) q
    have hle : saturatedUniformRemainder ≤ C := le_max_right _ _
    linarith

theorem exists_uniformBankRemainderOnUnitCountdown :
    ∃ C : ℝ, 0 ≤ C ∧
      HasUniformBankRemainderOnUnitCountdown C := by
  obtain ⟨Cterminal, hCterminal, hterminal⟩ :=
    exists_terminal_uniformBankRemainder
  let C := max uniformBankRemainderAboveTwoConstant Cterminal
  have hC : 0 ≤ C :=
    uniformBankRemainderAboveTwoConstant_nonneg.trans
      (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs hreach q
  rcases hreach with hx | hx
  · have h := hterminal s hs hx q
    have hle : Cterminal ≤ C := le_max_right _ _
    linarith
  · have h := uniformBankRemainderAboveTwo s hs hx q
    have hle : uniformBankRemainderAboveTwoConstant ≤ C :=
      le_max_left _ _
    linarith

noncomputable def uniformBankRemainderOnUnitCountdownConstant : ℝ :=
  exists_uniformBankRemainderOnUnitCountdown.choose

theorem uniformBankRemainderOnUnitCountdownConstant_nonneg :
    0 ≤ uniformBankRemainderOnUnitCountdownConstant :=
  exists_uniformBankRemainderOnUnitCountdown.choose_spec.1

theorem uniformBankRemainderOnUnitCountdown :
    HasUniformBankRemainderOnUnitCountdown
      uniformBankRemainderOnUnitCountdownConstant :=
  exists_uniformBankRemainderOnUnitCountdown.choose_spec.2

/-- One-step accounting in the exact domain used by an integral countdown. -/
theorem boundary_one_step_onUnitCountdown
    {C : ℝ} (hTaylor : HasUniformBankRemainderOnUnitCountdown C)
    {s : AnalysisState} (hs : s.Feasible)
    (hreach : s.IsUnitCountdownPreState) (q : BoundaryOutcome) :
    boundaryReward s q +
        bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        bankW s.x s.substantive s.epsilon s.deferred ≤ C := by
  have hlocal := boundaryReward_add_bankRawGradient_nonpos hs q
  have hrem := hTaylor s hs hreach q
  linarith

end

end SchedulingPaper
