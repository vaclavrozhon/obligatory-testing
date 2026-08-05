import SchedulingPaper.BankTelescope
import Mathlib.Tactic

/-!
# Reachable finite remainder for the complete capped bank

This module proves the full reachable remainder for the parameterized
four-endpoint base bank, including active/flat crossings and `x = 1`.
It also separates addition of the one-dimensional cap reserve, leaving no
unbounded raw-state premise in the five-endpoint interface.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ParameterizedAnalysisState

/-- Affine interpolation of one capped boundary update. -/
def interpolatedStep (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (t : ℝ) : ParameterizedAnalysisState :=
  match q with
  | .zero => { s with x := s.x - t }
  | .epsilon =>
      { s with x := s.x - t, epsilon := s.epsilon + t }
  | .immediate =>
      { s with x := s.x - t, substantive := s.substantive + t }
  | .deferred =>
      { s with
        x := s.x - t
        substantive := s.substantive + t
        deferred := s.deferred + t }
  | .cap =>
      { s with
        x := s.x - t
        substantive := s.substantive + t
        deferred := s.deferred + t
        capped := s.capped + t }

@[simp] theorem interpolatedStep_zero
    (s : ParameterizedAnalysisState) (q : CappedBoundaryOutcome) :
    s.interpolatedStep q 0 = s := by
  cases s
  cases q <;> simp [interpolatedStep]

@[simp] theorem interpolatedStep_one
    (s : ParameterizedAnalysisState) (q : CappedBoundaryOutcome) :
    s.interpolatedStep q 1 = s.step q := by
  cases q <;> rfl

theorem interpolatedStep_feasible
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s.interpolatedStep q t).Feasible := by
  rcases hs with ⟨hx0, hP, hE, hD, hK, hDP, hKP⟩
  cases q <;>
    simp only [interpolatedStep, Feasible] <;>
    constructor
  · linarith [ht.2]
  · exact ⟨hP, hE, hD, hK, hDP, hKP⟩
  · linarith [ht.2]
  · exact ⟨hP, by linarith [ht.1], hD, hK, hDP, hKP⟩
  · linarith [ht.2]
  · exact ⟨by linarith [ht.1], hE, hD, hK,
      by linarith [ht.1], by linarith [ht.1]⟩
  · linarith [ht.2]
  · exact ⟨by linarith [ht.1], hE, by linarith [ht.1],
      hK, by linarith, by linarith [ht.1]⟩
  · linarith [ht.2]
  · exact ⟨by linarith [ht.1], hE, by linarith [ht.1],
      by linarith [ht.1], by linarith, by linarith⟩

def etaStepRate (c : ℝ) : CappedBoundaryOutcome → ℝ
  | .zero | .epsilon => 0
  | .immediate => -(1 + c)
  | .deferred | .cap => -c

def yStepRate (c : ℝ) : CappedBoundaryOutcome → ℝ
  | .zero => 0
  | .epsilon | .immediate => -(1 + c)
  | .deferred | .cap => -c

def bStepRate : CappedBoundaryOutcome → ℝ
  | .epsilon => 1
  | _ => 0

def deferredStepRate : CappedBoundaryOutcome → ℝ
  | .deferred | .cap => 1
  | _ => 0

def cappedStepRate : CappedBoundaryOutcome → ℝ
  | .cap => 1
  | _ => 0

theorem interpolatedStep_eta_formula
    {s : ParameterizedAnalysisState} (c : ℝ)
    (q : CappedBoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).eta c =
      (s.x * s.eta c + etaStepRate c q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, etaStepRate, eta] <;>
    field_simp [hx, hxt] <;> ring

theorem interpolatedStep_y_formula
    {s : ParameterizedAnalysisState} (c : ℝ)
    (q : CappedBoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).y c =
      (s.x * s.y c + yStepRate c q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, yStepRate, y, eta, b] <;>
    field_simp [hx, hxt] <;> ring

theorem interpolatedStep_b_formula
    {s : ParameterizedAnalysisState}
    (q : CappedBoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).b =
      (s.x * s.b + bStepRate q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, bStepRate, b] <;>
    field_simp [hx, hxt] <;> ring

theorem interpolatedStep_q_formula
    {s : ParameterizedAnalysisState}
    (q : CappedBoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).q =
      (s.x * s.q + cappedStepRate q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, cappedStepRate,
      ParameterizedAnalysisState.q] <;>
    field_simp [hx, hxt] <;> ring

private theorem linearFraction_antitone
    {x z δ t u : ℝ}
    (hx : 1 < x) (hzδ : z + δ ≤ 0)
    (htu : t ≤ u) (hu : u ≤ 1) :
    (x * z + δ * u) / (x - u) ≤
      (x * z + δ * t) / (x - t) := by
  have hxu : 0 < x - u := by linarith
  have hxt : 0 < x - t := by linarith
  apply (div_le_div_iff₀ hxu hxt).2
  have hprod :
      0 ≤ x * (u - t) * (-(z + δ)) :=
    mul_nonneg
      (mul_nonneg (by linarith) (sub_nonneg.mpr htu))
      (neg_nonneg.mpr hzδ)
  nlinarith

theorem y_interpolatedStep_antitone
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    {t u : ℝ} (htu : t ≤ u) (hu : u ≤ 1) :
    (s.interpolatedStep q u).y c ≤
      (s.interpolatedStep q t).y c := by
  have hx1 : 1 < s.x := lt_of_lt_of_le (by norm_num) hx
  have hxu : s.x - u ≠ 0 := ne_of_gt (by linarith)
  have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith)
  rw [interpolatedStep_y_formula c q u hs.1.ne' hxu,
    interpolatedStep_y_formula c q t hs.1.ne' hxt]
  apply linearFraction_antitone hx1
  · have hy := y_nonpos hc.le hs
    cases q <;> simp only [yStepRate] <;> linarith
  · exact htu
  · exact hu

theorem eta_interpolatedStep_antitone
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    {t u : ℝ} (htu : t ≤ u) (hu : u ≤ 1) :
    (s.interpolatedStep q u).eta c ≤
      (s.interpolatedStep q t).eta c := by
  have hx1 : 1 < s.x := lt_of_lt_of_le (by norm_num) hx
  have hxu : s.x - u ≠ 0 := ne_of_gt (by linarith)
  have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith)
  rw [interpolatedStep_eta_formula c q u hs.1.ne' hxu,
    interpolatedStep_eta_formula c q t hs.1.ne' hxt]
  apply linearFraction_antitone hx1
  · have hη := eta_nonpos hc.le hs
    cases q <;> simp only [etaStepRate] <;> linarith
  · exact htu
  · exact hu

theorem y_interpolatedStep_le
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s.interpolatedStep q t).y c ≤ s.y c := by
  have h := y_interpolatedStep_antitone hc hs hx q
    (t := 0) (u := t) ht.1 ht.2
  simpa using h

theorem flat_persists_interpolated
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : s.y c < -1) :
    (s.interpolatedStep q t).y c < -1 :=
  lt_of_le_of_lt (y_interpolatedStep_le hc hs hx q ht) hy

theorem active_eta_b_bounds
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hy : -1 ≤ s.y c) :
    -1 ≤ s.y c ∧ s.y c ≤ s.eta c ∧ s.eta c ≤ 0 ∧
      0 ≤ s.b ∧ s.b ≤ 1 / (1 + c) := by
  have hscale : 0 < 1 + c := by linarith
  have hyη : s.y c ≤ s.eta c := by
    rw [eta_eq_y_add c s]
    exact le_add_of_nonneg_right
      (mul_nonneg hscale.le (b_nonneg hs))
  have hη := eta_nonpos hc.le hs
  have hb := b_nonneg hs
  have hetaEq := eta_eq_y_add c s
  have hscaled : (1 + c) * s.b ≤ -s.y c := by linarith
  have hbUpper : s.b ≤ 1 / (1 + c) := by
    apply (le_div_iff₀ hscale).2
    nlinarith
  exact ⟨hy, hyη, hη, hb, hbUpper⟩

end ParameterizedAnalysisState

/-- Chain rule for the parameterized active normalized potential. -/
theorem parameterizedActiveG_hasDerivAt_comp
    {c : ℝ} (hc : 0 < c)
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => parameterizedActiveG c (Y u) (B u))
      (parameterizedActiveGy c y b * y' +
        parameterizedActiveGb c y b * b') t := by
  have hF : HasDerivAt (fun u => parameterizedBankF c (Y u))
      ((parameterizedThreshold c y - 1) * y') t := by
    convert (parameterizedBankF_hasDerivAt hc
      (by simpa [hy] using hy0)).comp t hY using 1 <;> simp [hy]
  have hH : HasDerivAt (fun u => parameterizedBankH c (Y u))
      (parameterizedBankHPrime c y * y') t := by
    convert (parameterizedBankH_hasDerivAt hc
      (by simpa [hy] using hy0)).comp t hY using 1 <;> simp [hy]
  have hquad :
      HasDerivAt (fun u => (1 + c) * B u ^ 2 / 2)
        ((1 + c) * b * b') t := by
    convert
      (((hasDerivAt_const t (1 + c)).mul (hB.pow 2)).div_const 2)
        using 1 <;> simp [hb] <;> ring
  unfold parameterizedActiveG parameterizedActiveGy
    parameterizedActiveGb
  convert hF.add (hB.mul hH) |>.add hquad using 1 <;>
    simp [hy, hb] <;> ring

def parameterizedActivePerspectivePath
    (c x d y b δd δy δb t : ℝ) : ℝ :=
  (x - t) * (d + δd * t) +
    (x - t) ^ 2 *
      parameterizedActiveG c
        (normalizedAffinePath x y δy t)
        (normalizedAffinePath x b δb t)

def parameterizedActivePerspectiveSlope
    (c x d y b δd δy δb t : ℝ) : ℝ :=
  -(d + δd * t) + (x - t) * δd +
    (x - t) *
      (-2 * parameterizedActiveG c
          (normalizedAffinePath x y δy t)
          (normalizedAffinePath x b δb t) +
        (normalizedAffinePath x y δy t + δy) *
          parameterizedActiveGy c
            (normalizedAffinePath x y δy t)
            (normalizedAffinePath x b δb t) +
        (normalizedAffinePath x b δb t + δb) *
          parameterizedActiveGb c
            (normalizedAffinePath x y δy t)
            (normalizedAffinePath x b δb t))

theorem parameterizedActivePerspectivePath_hasDerivAt
    {c x d y b δd δy δb t : ℝ} (hc : 0 < c)
    (hxt : x - t ≠ 0)
    (hy0 : normalizedAffinePath x y δy t ≤ 0) :
    HasDerivAt
      (parameterizedActivePerspectivePath c x d y b δd δy δb)
      (parameterizedActivePerspectiveSlope c x d y b δd δy δb t) t := by
  let X : ℝ → ℝ := fun u => x - u
  let D : ℝ → ℝ := fun u => d + δd * u
  let Y : ℝ → ℝ := normalizedAffinePath x y δy
  let B : ℝ → ℝ := normalizedAffinePath x b δb
  have hX : HasDerivAt X (-1) t := by
    dsimp [X]
    convert (hasDerivAt_const t x).sub (hasDerivAt_id t) using 1 <;> ring
  have hD : HasDerivAt D δd t := by
    dsimp [D]
    convert (hasDerivAt_const t d).add
      ((hasDerivAt_const t δd).mul (hasDerivAt_id t)) using 1 <;> ring
  have hY : HasDerivAt Y
      (x * (y + δy) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hB : HasDerivAt B
      (x * (b + δb) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hG :=
    parameterizedActiveG_hasDerivAt_comp hc hY rfl hB rfl hy0
  unfold parameterizedActivePerspectivePath
    parameterizedActivePerspectiveSlope
  dsimp [X, D, Y, B] at hX hD hY hB hG ⊢
  have hraw := (hX.mul hD).add ((hX.pow 2).mul hG)
  simp only [Pi.pow_apply] at hraw
  convert hraw using 1
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

theorem parameterizedActivePerspectiveSlope_zero_eq_dotDirection
    (c : ℝ) (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (hx : s.x ≠ 0) :
    parameterizedActivePerspectiveSlope c s.x s.deferred (s.y c) s.b
        (ParameterizedAnalysisState.deferredStepRate q)
        (ParameterizedAnalysisState.yStepRate c q)
        (ParameterizedAnalysisState.bStepRate q) 0 =
      (parameterizedActiveRawGradient c s).dotDirection q := by
  cases q <;>
    simp only [parameterizedActivePerspectiveSlope,
      normalizedAffinePath,
      ParameterizedAnalysisState.deferredStepRate,
      ParameterizedAnalysisState.yStepRate,
      ParameterizedAnalysisState.bStepRate,
      CappedRawGradient.dotDirection,
      parameterizedActiveRawGradient] <;>
    simp [hx] <;> ring

def parameterizedBankHSecond (c y : ℝ) : ℝ :=
  2 / (c - 2 * y) +
    2 * (1 + y) / (c - 2 * y) ^ 2

theorem parameterizedBankHPrime_hasDerivAt
    {c y : ℝ} (hc : 0 < c) (hy : y ≤ 0) :
    HasDerivAt (parameterizedBankHPrime c)
      (parameterizedBankHSecond c y) y := by
  have hA := parameterizedThreshold_hasDerivAt hc hy
  have hnum : HasDerivAt (fun u : ℝ => 1 + u) 1 y := by
    convert (hasDerivAt_const y 1).add (hasDerivAt_id y) using 1 <;> ring
  have hden : HasDerivAt (fun u : ℝ => c - 2 * u) (-2) y := by
    convert (hasDerivAt_const y c).sub
      ((hasDerivAt_const y 2).mul (hasDerivAt_id y)) using 1 <;> ring
  have hden0 : c - 2 * y ≠ 0 :=
    (parameterized_denominator_pos hc hy).ne'
  unfold parameterizedBankHPrime parameterizedBankHSecond
  convert hA.add (hnum.div hden hden0) using 1
  field_simp [hden0]
  ring

def parameterizedActiveGyy (c y b : ℝ) : ℝ :=
  1 / (c - 2 * y) + b * parameterizedBankHSecond c y

theorem parameterizedActiveGy_hasDerivAt_comp
    {c : ℝ} (hc : 0 < c)
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => parameterizedActiveGy c (Y u) (B u))
      (parameterizedActiveGyy c y b * y' +
        parameterizedBankHPrime c y * b') t := by
  have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
  have hA := (parameterizedThreshold_hasDerivAt hc hy0').comp t hY
  have hHp :=
    (parameterizedBankHPrime_hasDerivAt hc hy0').comp t hY
  unfold parameterizedActiveGy parameterizedActiveGyy
  convert (hA.sub_const 1).add (hB.mul hHp) using 1 <;>
    simp [hy, hb] <;> ring

theorem parameterizedActiveGb_hasDerivAt_comp
    {c : ℝ} (hc : 0 < c)
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => parameterizedActiveGb c (Y u) (B u))
      (parameterizedBankHPrime c y * y' + (1 + c) * b') t := by
  have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
  have hH := (parameterizedBankH_hasDerivAt hc hy0').comp t hY
  unfold parameterizedActiveGb
  convert hH.add ((hasDerivAt_const t (1 + c)).mul hB) using 1 <;>
    simp [hy, hb] <;> ring

def parameterizedActivePerspectiveCurvature
    (c y b δd δy δb : ℝ) : ℝ :=
  -2 * δd + 2 * parameterizedActiveG c y b -
    2 * (y + δy) * parameterizedActiveGy c y b -
    2 * (b + δb) * parameterizedActiveGb c y b +
    parameterizedActiveGyy c y b * (y + δy) ^ 2 +
    2 * parameterizedBankHPrime c y *
      (y + δy) * (b + δb) +
    (1 + c) * (b + δb) ^ 2

theorem parameterizedActivePerspectiveSlope_hasDerivAt
    {c x d y b δd δy δb t : ℝ} (hc : 0 < c)
    (hxt : x - t ≠ 0)
    (hy0 : normalizedAffinePath x y δy t ≤ 0) :
    HasDerivAt
      (parameterizedActivePerspectiveSlope c x d y b δd δy δb)
      (parameterizedActivePerspectiveCurvature c
        (normalizedAffinePath x y δy t)
        (normalizedAffinePath x b δb t) δd δy δb) t := by
  let X : ℝ → ℝ := fun u => x - u
  let D : ℝ → ℝ := fun u => d + δd * u
  let Y : ℝ → ℝ := normalizedAffinePath x y δy
  let B : ℝ → ℝ := normalizedAffinePath x b δb
  let U : ℝ → ℝ := fun u => Y u + δy
  let V : ℝ → ℝ := fun u => B u + δb
  have hX : HasDerivAt X (-1) t := by
    dsimp [X]
    convert (hasDerivAt_const t x).sub (hasDerivAt_id t) using 1 <;> ring
  have hD : HasDerivAt D δd t := by
    dsimp [D]
    convert (hasDerivAt_const t d).add
      ((hasDerivAt_const t δd).mul (hasDerivAt_id t)) using 1 <;> ring
  have hY : HasDerivAt Y
      (x * (y + δy) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hB : HasDerivAt B
      (x * (b + δb) / (x - t) ^ 2) t :=
    normalizedAffinePath_hasDerivAt hxt
  have hU : HasDerivAt U
      (x * (y + δy) / (x - t) ^ 2) t := hY.add_const δy
  have hV : HasDerivAt V
      (x * (b + δb) / (x - t) ^ 2) t := hB.add_const δb
  have hG :=
    parameterizedActiveG_hasDerivAt_comp hc hY rfl hB rfl hy0
  have hGy :=
    parameterizedActiveGy_hasDerivAt_comp hc hY rfl hB rfl hy0
  have hGb :=
    parameterizedActiveGb_hasDerivAt_comp hc hY rfl hB rfl hy0
  have hQ :=
    (((hasDerivAt_const t (-2)).mul hG).add (hU.mul hGy)).add
      (hV.mul hGb)
  have hSlope :=
    ((hD.neg).add (hX.mul_const δd)).add (hX.mul hQ)
  unfold parameterizedActivePerspectiveSlope
    parameterizedActivePerspectiveCurvature
  dsimp [X, D, Y, B, U, V] at hX hD hY hB hU hV hG hGy hGb hQ hSlope ⊢
  convert hSlope using 1
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

def parameterizedActiveCurvatureFor
    (c : ℝ) (q : CappedBoundaryOutcome) (p : ℝ × ℝ) : ℝ :=
  parameterizedActivePerspectiveCurvature c p.1 p.2
    (ParameterizedAnalysisState.deferredStepRate q)
    (ParameterizedAnalysisState.yStepRate c q)
    (ParameterizedAnalysisState.bStepRate q)

theorem parameterizedActiveCurvatureFor_continuousOn
    {c : ℝ} (hc : 0 < c) (q : CappedBoundaryOutcome) :
    ContinuousOn (parameterizedActiveCurvatureFor c q)
      (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) := by
  intro p hp
  have hy0 : p.1 ≤ 0 := hp.1.2
  have hden : c - 2 * p.1 ≠ 0 :=
    (parameterized_denominator_pos hc hy0).ne'
  have hA : ContinuousAt (parameterizedThreshold c) p.1 :=
    (parameterizedThreshold_hasDerivAt hc hy0).continuousAt
  have hAcomp :
      ContinuousAt (fun z : ℝ × ℝ => parameterizedThreshold c z.1) p := by
    change ContinuousAt (parameterizedThreshold c ∘ Prod.fst) p
    exact hA.comp continuousAt_fst
  unfold parameterizedActiveCurvatureFor
    parameterizedActivePerspectiveCurvature
    parameterizedActiveGyy parameterizedBankHSecond
    parameterizedActiveG parameterizedActiveGy
    parameterizedActiveGb parameterizedBankHPrime
    parameterizedBankF parameterizedBankH
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp [hden])

theorem exists_parameterizedActiveUniformCurvature
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ q : CappedBoundaryOutcome,
      ∀ y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ b ∈ Set.Icc (0 : ℝ) (1 / (1 + c)),
        parameterizedActivePerspectiveCurvature c y b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) ≤ C := by
  have hcompact :
      IsCompact (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound (q : CappedBoundaryOutcome) :
      ∃ C : ℝ, ∀ p ∈
          (Set.Icc (-1 : ℝ) 0 ×ˢ
            Set.Icc (0 : ℝ) (1 / (1 + c))),
        parameterizedActiveCurvatureFor c q p ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (parameterizedActiveCurvatureFor_continuousOn hc q)
    refine ⟨C, ?_⟩
    intro p hp
    simpa [Real.norm_eq_abs] using
      (le_abs_self (parameterizedActiveCurvatureFor c q p)).trans (by
        simpa [Real.norm_eq_abs] using hC p hp)
  obtain ⟨Cz, hz⟩ := hbound .zero
  obtain ⟨Ce, he⟩ := hbound .epsilon
  obtain ⟨Ci, hi⟩ := hbound .immediate
  obtain ⟨Cd, hd⟩ := hbound .deferred
  obtain ⟨Ck, hk⟩ := hbound .cap
  refine ⟨max (max (max Cz Ce) (max Ci Cd)) Ck, ?_⟩
  intro q y hy b hb
  have hp : (y, b) ∈
      (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) := ⟨hy, hb⟩
  cases q with
  | zero =>
      exact (hz (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_left (le_max_left _ _)))
  | epsilon =>
      exact (he (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_left (le_max_right _ _)))
  | immediate =>
      exact (hi (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_right (le_max_left _ _)))
  | deferred =>
      exact (hd (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_right (le_max_right _ _)))
  | cap =>
      exact (hk (y, b) hp).trans (le_max_right _ _)

/-- Taylor remainder for a parameterized active path that stays active. -/
theorem parameterizedActivePerspective_unit_remainder
    {c x d y b C : ℝ} (hc : 0 < c) (hx : 2 ≤ x)
    (hC : 0 ≤ C) (q : CappedBoundaryOutcome)
    (hregion : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      normalizedAffinePath x y
          (ParameterizedAnalysisState.yStepRate c q) t ∈
        Set.Icc (-1 : ℝ) 0 ∧
      normalizedAffinePath x b
          (ParameterizedAnalysisState.bStepRate q) t ∈
        Set.Icc (0 : ℝ) (1 / (1 + c)))
    (hcurvature : ∀ Y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ B ∈ Set.Icc (0 : ℝ) (1 / (1 + c)),
        parameterizedActivePerspectiveCurvature c Y B
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) ≤ C) :
    parameterizedActivePerspectivePath c x d y b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) 1 -
        parameterizedActivePerspectivePath c x d y b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) 0 ≤
      parameterizedActivePerspectiveSlope c x d y b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) 0 + C := by
  let φ := parameterizedActivePerspectivePath c x d y b
    (ParameterizedAnalysisState.deferredStepRate q)
    (ParameterizedAnalysisState.yStepRate c q)
    (ParameterizedAnalysisState.bStepRate q)
  let slope := parameterizedActivePerspectiveSlope c x d y b
    (ParameterizedAnalysisState.deferredStepRate q)
    (ParameterizedAnalysisState.yStepRate c q)
    (ParameterizedAnalysisState.bStepRate q)
  let curvature := fun t =>
    parameterizedActivePerspectiveCurvature c
      (normalizedAffinePath x y
        (ParameterizedAnalysisState.yStepRate c q) t)
      (normalizedAffinePath x b
        (ParameterizedAnalysisState.bStepRate q) t)
      (ParameterizedAnalysisState.deferredStepRate q)
      (ParameterizedAnalysisState.yStepRate c q)
      (ParameterizedAnalysisState.bStepRate q)
  have hxt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      x - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact parameterizedActivePerspectivePath_hasDerivAt hc
      (hxt t ht) (hregion t ht).1.2
  have hslope : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact parameterizedActivePerspectiveSlope_hasDerivAt hc
      (hxt t ht) (hregion t ht).1.2
  exact unit_taylor_upper_of_second_deriv_le hC hφ hslope
    (fun t ht => hcurvature _ (hregion t ht).1 _ (hregion t ht).2)

theorem parameterizedInterpolatedStep_x_formula
    (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (t : ℝ) :
    (s.interpolatedStep q t).x = s.x - t := by
  cases q <;> rfl

theorem parameterizedInterpolatedStep_deferred_formula
    (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (t : ℝ) :
    (s.interpolatedStep q t).deferred =
      s.deferred +
        ParameterizedAnalysisState.deferredStepRate q * t := by
  cases q <;>
    simp [ParameterizedAnalysisState.interpolatedStep,
      ParameterizedAnalysisState.deferredStepRate]

theorem parameterizedActivePerspectivePath_eq_bankW_interpolated
    {c : ℝ} {s : ParameterizedAnalysisState}
    (q : CappedBoundaryOutcome) {t : ℝ}
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0)
    (hy : -1 ≤ (s.interpolatedStep q t).y c) :
    parameterizedActivePerspectivePath c s.x s.deferred
        (s.y c) s.b
        (ParameterizedAnalysisState.deferredStepRate q)
        (ParameterizedAnalysisState.yStepRate c q)
        (ParameterizedAnalysisState.bStepRate q) t =
      parameterizedBankW c
        (s.interpolatedStep q t).x
        (s.interpolatedStep q t).substantive
        (s.interpolatedStep q t).epsilon
        (s.interpolatedStep q t).deferred := by
  have hxcoord := parameterizedInterpolatedStep_x_formula s q t
  have hdcoord :=
    parameterizedInterpolatedStep_deferred_formula s q t
  have hycoord :=
    ParameterizedAnalysisState.interpolatedStep_y_formula
      c q t hx hxt
  have hbcoord :=
    ParameterizedAnalysisState.interpolatedStep_b_formula
      q t hx hxt
  unfold parameterizedBankW
  rw [if_neg]
  · dsimp only
    change
      parameterizedActivePerspectivePath c s.x s.deferred
          (s.y c) s.b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) t =
        (s.interpolatedStep q t).x *
            (s.interpolatedStep q t).deferred +
          (s.interpolatedStep q t).x ^ 2 *
            parameterizedBankG c
              ((s.interpolatedStep q t).y c)
              (s.interpolatedStep q t).b
    rw [parameterizedBankG, if_pos hy,
      parameterizedActivePerspectivePath, hxcoord, hdcoord,
      hycoord, hbcoord]
    rfl
  · rw [hxcoord]
    exact hxt

theorem exists_parameterized_active_to_active_remainder
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ q : CappedBoundaryOutcome,
        -1 ≤ s.y c → -1 ≤ (s.step q).y c →
        parameterizedBankW c
              (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            parameterizedBankW c
              s.x s.substantive s.epsilon s.deferred ≤
          (parameterizedBaseRawGradient c s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_parameterizedActiveUniformCurvature hc
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro s hs hx q hyStart hyEnd
  have hregion : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      normalizedAffinePath s.x (s.y c)
          (ParameterizedAnalysisState.yStepRate c q) t ∈
        Set.Icc (-1 : ℝ) 0 ∧
      normalizedAffinePath s.x s.b
          (ParameterizedAnalysisState.bStepRate q) t ∈
        Set.Icc (0 : ℝ) (1 / (1 + c)) := by
    intro t ht
    have hfeas :=
      ParameterizedAnalysisState.interpolatedStep_feasible hs hx q ht
    have hylower :
        -1 ≤ (s.interpolatedStep q t).y c := by
      have hmono :=
        ParameterizedAnalysisState.y_interpolatedStep_antitone
          hc hs hx q (t := t) (u := 1) ht.2 le_rfl
      simpa using hyEnd.trans hmono
    have hyupper :
        (s.interpolatedStep q t).y c ≤ 0 :=
      ParameterizedAnalysisState.y_nonpos hc.le hfeas
    have hb :=
      ParameterizedAnalysisState.active_eta_b_bounds
        hc hfeas hylower
    have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith [ht.2])
    have hyformula :=
      ParameterizedAnalysisState.interpolatedStep_y_formula
        c q t hs.1.ne' hxt
    have hbformula :=
      ParameterizedAnalysisState.interpolatedStep_b_formula
        q t hs.1.ne' hxt
    constructor
    · unfold normalizedAffinePath
      rw [← hyformula]
      exact ⟨hylower, hyupper⟩
    · unfold normalizedAffinePath
      rw [← hbformula]
      exact ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hrem :=
    parameterizedActivePerspective_unit_remainder
      (c := c) (x := s.x) (d := s.deferred)
      (y := s.y c) (b := s.b) (C := max C₀ 0)
      hc hx
      (le_max_right C₀ 0) q hregion (by
        intro Y hY B hB
        exact (hC₀ q Y hY B hB).trans (le_max_left _ _))
  have hxOne : s.x - 1 ≠ 0 := ne_of_gt (by linarith)
  have hpathOne :=
    parameterizedActivePerspectivePath_eq_bankW_interpolated
      (c := c) (s := s) q (t := 1) hs.1.ne' hxOne
      (by simpa using hyEnd)
  have hpathZero :=
    parameterizedActivePerspectivePath_eq_bankW_interpolated
      (c := c) (s := s) q (t := 0) hs.1.ne'
      (by simpa using hs.1.ne') (by simpa using hyStart)
  simp only [ParameterizedAnalysisState.interpolatedStep_one] at hpathOne
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpathZero
  rw [hpathOne, hpathZero,
    parameterizedActivePerspectiveSlope_zero_eq_dotDirection
      c s q hs.1.ne'] at hrem
  unfold parameterizedBaseRawGradient
  rw [if_pos hyStart]
  exact hrem

/-! ## The parameterized flat branch -/

def parameterizedSaturatedBank (c x P D : ℝ) : ℝ :=
  x * D +
    positivePart (x + D - (1 + c) * P) ^ 2 /
      (2 * (1 + c))

def parameterizedSaturatedGradient
    (c x P D : ℝ) : CappedRawGradient :=
  let p := positivePart (x + D - (1 + c) * P)
  {
    x := D + p / (1 + c)
    substantive := -p
    epsilon := 0
    deferred := x + p / (1 + c)
    capped := 0
  }

theorem parameterizedSaturatedBank_eq_flat_normalized
    {c x P D : ℝ} (hc : 0 < c) (hx : 0 < x) :
    parameterizedSaturatedBank c x P D =
      x * D + x ^ 2 *
        parameterizedFlatG c ((D - (1 + c) * P) / x) := by
  have harg :
      x + D - (1 + c) * P =
        x * (1 + (D - (1 + c) * P) / x) := by
    field_simp [hx.ne']
    ring
  unfold parameterizedSaturatedBank parameterizedFlatG
  rw [harg, positivePart_mul_of_nonneg hx.le]
  ring

theorem parameterizedFlatG_radial_identity
    {c : ℝ} (hc : 0 < c) (η : ℝ) :
    2 * parameterizedFlatG c η -
        η * parameterizedFlatGPrime c η =
      positivePart (1 + η) / (1 + c) := by
  have hscale : 1 + c ≠ 0 := by linarith
  by_cases hη : 0 ≤ 1 + η
  · have hpart : positivePart (1 + η) = 1 + η := by
      unfold positivePart
      exact max_eq_left hη
    rw [parameterizedFlatG, parameterizedFlatGPrime, hpart]
    field_simp [hscale]
    ring
  · have hpart : positivePart (1 + η) = 0 := by
      unfold positivePart
      exact max_eq_right (le_of_not_ge hη)
    simp [parameterizedFlatG, parameterizedFlatGPrime, hpart]

theorem parameterizedSaturatedGradient_eq_flatRawGradient
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState) (hx : 0 < s.x) :
    parameterizedSaturatedGradient c s.x s.substantive s.deferred =
      parameterizedFlatRawGradient c s := by
  have harg :
      s.x + s.deferred - (1 + c) * s.substantive =
        s.x * (1 + s.eta c) := by
    unfold ParameterizedAnalysisState.eta
    field_simp [hx.ne']
    ring
  have hpart :
      positivePart
          (s.x + s.deferred - (1 + c) * s.substantive) =
        s.x * positivePart (1 + s.eta c) := by
    rw [harg, positivePart_mul_of_nonneg hx.le]
  unfold parameterizedSaturatedGradient parameterizedFlatRawGradient
  dsimp only
  rw [CappedRawGradient.mk.injEq]
  constructor
  · rw [hpart, parameterizedFlatG_radial_identity hc]
    ring
  constructor
  · rw [hpart]
    unfold parameterizedFlatGPrime
    have hscale : 1 + c ≠ 0 := by linarith
    field_simp [hscale]
  constructor
  · rfl
  constructor
  · rw [hpart]
    unfold parameterizedFlatGPrime
    ring
  · rfl

theorem parameterizedBankW_eq_saturated_of_flat
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState) (hx : 0 < s.x)
    (hy : s.y c < -1) :
    parameterizedBankW c s.x s.substantive
        s.epsilon s.deferred =
      parameterizedSaturatedBank c s.x
        s.substantive s.deferred := by
  have hyRaw :
      (s.deferred - (1 + c) * s.substantive) / s.x -
          (1 + c) * (s.epsilon / s.x) < -1 := by
    simpa [ParameterizedAnalysisState.y,
      ParameterizedAnalysisState.eta,
      ParameterizedAnalysisState.b] using hy
  unfold parameterizedBankW
  rw [if_neg hx.ne']
  dsimp only
  unfold parameterizedBankG
  rw [if_neg (not_le.mpr hyRaw)]
  rw [show
      (s.deferred - (1 + c) * s.substantive) / s.x -
            (1 + c) * (s.epsilon / s.x) +
          (1 + c) * (s.epsilon / s.x) =
        (s.deferred - (1 + c) * s.substantive) / s.x by ring]
  exact (parameterizedSaturatedBank_eq_flat_normalized
    hc hx).symm

theorem parameterizedBaseGradient_eq_saturated_of_flat
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState) (hx : 0 < s.x)
    (hy : s.y c < -1) :
    parameterizedBaseRawGradient c s =
      parameterizedSaturatedGradient c s.x
        s.substantive s.deferred := by
  unfold parameterizedBaseRawGradient
  rw [if_neg (not_le.mpr hy)]
  exact (parameterizedSaturatedGradient_eq_flatRawGradient
    hc s hx).symm

theorem parameterizedSaturatedBank_increment_le
    {c : ℝ} (hc : 0 < c)
    (x P D Δx ΔP ΔD : ℝ) :
    parameterizedSaturatedBank c
          (x + Δx) (P + ΔP) (D + ΔD) -
        parameterizedSaturatedBank c x P D ≤
      (D + positivePart (x + D - (1 + c) * P) / (1 + c)) * Δx -
        positivePart (x + D - (1 + c) * P) * ΔP +
        (x + positivePart (x + D - (1 + c) * P) / (1 + c)) * ΔD +
        Δx * ΔD +
        (Δx + ΔD - (1 + c) * ΔP) ^ 2 /
          (2 * (1 + c)) := by
  have hscale : 0 < 1 + c := by linarith
  have hden : 0 < 2 * (1 + c) := mul_pos (by norm_num) hscale
  have hscalar :=
    positivePart_sq_remainder
      (x + D - (1 + c) * P)
      (Δx + ΔD - (1 + c) * ΔP)
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hscalar
  have hscale0 : 1 + c ≠ 0 := hscale.ne'
  have hexact :
      parameterizedSaturatedBank c
            (x + Δx) (P + ΔP) (D + ΔD) -
          parameterizedSaturatedBank c x P D =
        (D + positivePart (x + D - (1 + c) * P) / (1 + c)) * Δx -
          positivePart (x + D - (1 + c) * P) * ΔP +
          (x + positivePart (x + D - (1 + c) * P) / (1 + c)) * ΔD +
          Δx * ΔD +
          (positivePart
                ((x + D - (1 + c) * P) +
                  (Δx + ΔD - (1 + c) * ΔP)) ^ 2 -
              positivePart (x + D - (1 + c) * P) ^ 2 -
              2 * positivePart (x + D - (1 + c) * P) *
                (Δx + ΔD - (1 + c) * ΔP)) /
            (2 * (1 + c)) := by
    unfold parameterizedSaturatedBank
    rw [show
        x + Δx + (D + ΔD) - (1 + c) * (P + ΔP) =
          (x + D - (1 + c) * P) +
            (Δx + ΔD - (1 + c) * ΔP) by ring]
    field_simp [hscale0]
    ring
  rw [hexact]
  linarith

def parameterizedFlatUniformRemainder (c : ℝ) : ℝ :=
  1 + (2 + c) ^ 2 / (2 * (1 + c))

theorem parameterizedFlatUniformRemainder_nonneg
    {c : ℝ} (hc : 0 < c) :
    0 ≤ parameterizedFlatUniformRemainder c := by
  unfold parameterizedFlatUniformRemainder
  positivity

theorem parameterizedSaturatedBank_step_le
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState) (q : CappedBoundaryOutcome) :
    parameterizedSaturatedBank c
          (s.step q).x (s.step q).substantive
          (s.step q).deferred -
        parameterizedSaturatedBank c
          s.x s.substantive s.deferred ≤
      (parameterizedSaturatedGradient c s.x
        s.substantive s.deferred).dotDirection q +
        parameterizedFlatUniformRemainder c := by
  have hden : 0 < 2 * (1 + c) := by positivity
  have hmain :
      1 / (2 * (1 + c)) ≤
        parameterizedFlatUniformRemainder c := by
    unfold parameterizedFlatUniformRemainder
    have hsmall : 1 / (2 * (1 + c)) ≤ 1 := by
      exact (div_le_one hden).2 (by linarith)
    have hquot :
        0 ≤ (2 + c) ^ 2 / (2 * (1 + c)) :=
      div_nonneg (sq_nonneg _) hden.le
    linarith
  have himmediate :
      (2 + c) ^ 2 / (2 * (1 + c)) ≤
        parameterizedFlatUniformRemainder c := by
    unfold parameterizedFlatUniformRemainder
    linarith
  have hdeferred :
      -1 + (1 + c) ^ 2 / (2 * (1 + c)) ≤
        parameterizedFlatUniformRemainder c := by
    unfold parameterizedFlatUniformRemainder
    have hscale : 1 + c ≠ 0 := by linarith
    field_simp [hscale]
    nlinarith [sq_nonneg (2 + c)]
  cases q with
  | zero =>
      have h := parameterizedSaturatedBank_increment_le hc
        s.x s.substantive s.deferred (-1) 0 0
      simp only [ParameterizedAnalysisState.step]
      simp [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection] at *
      rw [show s.x - 1 = s.x + (-1) by ring]
      linarith
  | epsilon =>
      have h := parameterizedSaturatedBank_increment_le hc
        s.x s.substantive s.deferred (-1) 0 0
      simp only [ParameterizedAnalysisState.step]
      simp [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection] at *
      rw [show s.x - 1 = s.x + (-1) by ring]
      linarith
  | immediate =>
      have h := parameterizedSaturatedBank_increment_le hc
        s.x s.substantive s.deferred (-1) 1 0
      simp only [ParameterizedAnalysisState.step]
      simp [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection] at *
      have hr :
          (-1 - (1 + c)) ^ 2 / (2 * (1 + c)) ≤
            parameterizedFlatUniformRemainder c := by
        convert himmediate using 1 <;> ring
      rw [show s.x - 1 = s.x + (-1) by ring]
      linarith
  | deferred =>
      have h := parameterizedSaturatedBank_increment_le hc
        s.x s.substantive s.deferred (-1) 1 1
      simp only [ParameterizedAnalysisState.step]
      simp [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection] at *
      have hr :
          -1 + (-c - 1) ^ 2 / (2 * (1 + c)) ≤
            parameterizedFlatUniformRemainder c := by
        have heq : (-c - 1) ^ 2 = (1 + c) ^ 2 := by ring
        rw [heq]
        linarith
      have hremainder :
          (-c + -1) ^ 2 = (-c - 1) ^ 2 := by ring
      rw [hremainder] at h
      rw [show s.x - 1 = s.x + (-1) by ring]
      linarith
  | cap =>
      have h := parameterizedSaturatedBank_increment_le hc
        s.x s.substantive s.deferred (-1) 1 1
      simp only [ParameterizedAnalysisState.step]
      simp [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection] at *
      have hr :
          -1 + (-c - 1) ^ 2 / (2 * (1 + c)) ≤
            parameterizedFlatUniformRemainder c := by
        have heq : (-c - 1) ^ 2 = (1 + c) ^ 2 := by ring
        rw [heq]
        linarith
      have hremainder :
          (-c + -1) ^ 2 = (-c - 1) ^ 2 := by ring
      rw [hremainder] at h
      rw [show s.x - 1 = s.x + (-1) by ring]
      linarith

theorem parameterized_flat_remainder_above_two
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (hy : s.y c < -1)
    (q : CappedBoundaryOutcome) :
    parameterizedBankW c
          (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        parameterizedBankW c
          s.x s.substantive s.epsilon s.deferred ≤
      (parameterizedBaseRawGradient c s).dotDirection q +
        parameterizedFlatUniformRemainder c := by
  have hxNext : 0 < (s.step q).x := by
    cases q <;> simp [ParameterizedAnalysisState.step] <;> linarith
  have hyNext : (s.step q).y c < -1 := by
    rw [← ParameterizedAnalysisState.interpolatedStep_one s q]
    exact ParameterizedAnalysisState.flat_persists_interpolated
      hc hs hx q (by simp) hy
  rw [parameterizedBankW_eq_saturated_of_flat hc (s.step q)
      hxNext hyNext,
    parameterizedBankW_eq_saturated_of_flat hc s hs.1 hy,
    parameterizedBaseGradient_eq_saturated_of_flat hc s hs.1 hy]
  exact parameterizedSaturatedBank_step_le hc s q

def parameterizedFlatDirectionRemainder
    (c : ℝ) : CappedBoundaryOutcome → ℝ
  | .zero | .epsilon => 1 / (2 * (1 + c))
  | .immediate => (2 + c) ^ 2 / (2 * (1 + c))
  | .deferred | .cap => -1 + (1 + c) ^ 2 / (2 * (1 + c))

theorem parameterizedFlatDirectionRemainder_le_uniform
    {c : ℝ} (hc : 0 < c) (q : CappedBoundaryOutcome) :
    parameterizedFlatDirectionRemainder c q ≤
      parameterizedFlatUniformRemainder c := by
  have hden : 0 < 2 * (1 + c) := by positivity
  cases q with
  | zero =>
      unfold parameterizedFlatDirectionRemainder
        parameterizedFlatUniformRemainder
      have hsmall : 1 / (2 * (1 + c)) ≤ 1 :=
        (div_le_one hden).2 (by linarith)
      have hq : 0 ≤ (2 + c) ^ 2 / (2 * (1 + c)) :=
        div_nonneg (sq_nonneg _) hden.le
      linarith
  | epsilon =>
      unfold parameterizedFlatDirectionRemainder
        parameterizedFlatUniformRemainder
      have hsmall : 1 / (2 * (1 + c)) ≤ 1 :=
        (div_le_one hden).2 (by linarith)
      have hq : 0 ≤ (2 + c) ^ 2 / (2 * (1 + c)) :=
        div_nonneg (sq_nonneg _) hden.le
      linarith
  | immediate =>
      unfold parameterizedFlatDirectionRemainder
        parameterizedFlatUniformRemainder
      linarith
  | deferred =>
      unfold parameterizedFlatDirectionRemainder
        parameterizedFlatUniformRemainder
      have hscale : 1 + c ≠ 0 := by linarith
      field_simp [hscale]
      nlinarith [sq_nonneg (2 + c)]
  | cap =>
      unfold parameterizedFlatDirectionRemainder
        parameterizedFlatUniformRemainder
      have hscale : 1 + c ≠ 0 := by linarith
      field_simp [hscale]
      nlinarith [sq_nonneg (2 + c)]

theorem parameterizedSaturatedBank_interpolated_subsegment
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (t u : ℝ) :
    parameterizedSaturatedBank c
          (s.interpolatedStep q u).x
          (s.interpolatedStep q u).substantive
          (s.interpolatedStep q u).deferred -
        parameterizedSaturatedBank c
          (s.interpolatedStep q t).x
          (s.interpolatedStep q t).substantive
          (s.interpolatedStep q t).deferred ≤
      (parameterizedSaturatedGradient c
          (s.interpolatedStep q t).x
          (s.interpolatedStep q t).substantive
          (s.interpolatedStep q t).deferred).dotDirection q *
          (u - t) +
        parameterizedFlatDirectionRemainder c q * (u - t) ^ 2 := by
  have hscale : 1 + c ≠ 0 := by linarith
  cases q with
  | zero =>
      simp only [ParameterizedAnalysisState.interpolatedStep]
      have h := parameterizedSaturatedBank_increment_le hc
        (s.x - t) s.substantive s.deferred (-(u - t)) 0 0
      convert h using 1
      all_goals try simp only [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection,
        parameterizedFlatDirectionRemainder]
      all_goals field_simp [hscale]
      all_goals ring_nf
  | epsilon =>
      simp only [ParameterizedAnalysisState.interpolatedStep]
      have h := parameterizedSaturatedBank_increment_le hc
        (s.x - t) s.substantive s.deferred (-(u - t)) 0 0
      convert h using 1
      all_goals try simp only [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection,
        parameterizedFlatDirectionRemainder]
      all_goals field_simp [hscale]
      all_goals ring_nf
  | immediate =>
      simp only [ParameterizedAnalysisState.interpolatedStep]
      have h := parameterizedSaturatedBank_increment_le hc
        (s.x - t) (s.substantive + t) s.deferred
          (-(u - t)) (u - t) 0
      convert h using 1
      all_goals try simp only [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection,
        parameterizedFlatDirectionRemainder]
      all_goals field_simp [hscale]
      all_goals ring_nf
  | deferred =>
      simp only [ParameterizedAnalysisState.interpolatedStep]
      have h := parameterizedSaturatedBank_increment_le hc
        (s.x - t) (s.substantive + t) (s.deferred + t)
          (-(u - t)) (u - t) (u - t)
      convert h using 1
      all_goals try simp only [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection,
        parameterizedFlatDirectionRemainder]
      all_goals field_simp [hscale]
      all_goals ring_nf
  | cap =>
      simp only [ParameterizedAnalysisState.interpolatedStep]
      have h := parameterizedSaturatedBank_increment_le hc
        (s.x - t) (s.substantive + t) (s.deferred + t)
          (-(u - t)) (u - t) (u - t)
      convert h using 1
      all_goals try simp only [parameterizedSaturatedGradient,
        CappedRawGradient.dotDirection,
        parameterizedFlatDirectionRemainder]
      all_goals field_simp [hscale]
      all_goals ring_nf

theorem parameterizedActiveRawGradient_eq_flat_of_interface
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState)
    (hy : s.y c = -1) (hb : 0 ≤ s.b) :
    parameterizedActiveRawGradient c s =
      parameterizedFlatRawGradient c s := by
  have hA : parameterizedThreshold c (s.y c) = 1 := by
    rw [hy]
    exact parameterizedThreshold_at_neg_one c
  have hH : parameterizedBankH c (s.y c) = 0 := by
    rw [hy]
    simp [parameterizedBankH]
  have hHp : parameterizedBankHPrime c (s.y c) = 1 := by
    rw [hy]
    simp [parameterizedBankHPrime,
      parameterizedThreshold_at_neg_one]
  have hpart :
      positivePart (1 + s.eta c) = (1 + c) * s.b := by
    have heta : s.eta c = -1 + (1 + c) * s.b := by
      rw [s.eta_eq_y_add c, hy]
    rw [heta]
    simp only [show
      1 + (-1 + (1 + c) * s.b) = (1 + c) * s.b by ring]
    unfold positivePart
    rw [max_eq_left]
    exact mul_nonneg (by linarith) hb
  have hG :
      parameterizedActiveG c (s.y c) s.b =
        (1 + c) * s.b ^ 2 / 2 := by
    rw [parameterizedActiveG, hy,
      parameterizedBankF_at_neg_one]
    simp [parameterizedBankH]
  have hGy :
      parameterizedActiveGy c (s.y c) s.b = s.b := by
    simp [parameterizedActiveGy, hA, hHp]
  have hGb :
      parameterizedActiveGb c (s.y c) s.b =
        (1 + c) * s.b := by
    simp [parameterizedActiveGb, hH]
  have hflatG :
      parameterizedFlatG c (s.eta c) =
        (1 + c) * s.b ^ 2 / 2 := by
    unfold parameterizedFlatG
    rw [hpart]
    have hscale : 1 + c ≠ 0 := by linarith
    field_simp [hscale]
  have hflatGp :
      parameterizedFlatGPrime c (s.eta c) = s.b := by
    unfold parameterizedFlatGPrime
    rw [hpart]
    have hscale : 1 + c ≠ 0 := by linarith
    field_simp [hscale]
  unfold parameterizedActiveRawGradient
    parameterizedFlatRawGradient
  dsimp only
  rw [hG, hGy, hGb, hflatG, hflatGp,
    CappedRawGradient.mk.injEq]
  rw [s.eta_eq_y_add c, hy]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem parameterizedActiveSlope_eq_interpolated_gradient
    {c : ℝ} {s : ParameterizedAnalysisState}
    (q : CappedBoundaryOutcome) {t : ℝ}
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    parameterizedActivePerspectiveSlope c s.x s.deferred
        (s.y c) s.b
        (ParameterizedAnalysisState.deferredStepRate q)
        (ParameterizedAnalysisState.yStepRate c q)
        (ParameterizedAnalysisState.bStepRate q) t =
      (parameterizedActiveRawGradient c
        (s.interpolatedStep q t)).dotDirection q := by
  have hxcoord := parameterizedInterpolatedStep_x_formula s q t
  have hdcoord :=
    parameterizedInterpolatedStep_deferred_formula s q t
  have hycoord :=
    ParameterizedAnalysisState.interpolatedStep_y_formula
      c q t hx hxt
  have hbcoord :=
    ParameterizedAnalysisState.interpolatedStep_b_formula
      q t hx hxt
  have hY :
      normalizedAffinePath s.x (s.y c)
          (ParameterizedAnalysisState.yStepRate c q) t =
        (s.interpolatedStep q t).y c := by
    unfold normalizedAffinePath
    exact hycoord.symm
  have hB :
      normalizedAffinePath s.x s.b
          (ParameterizedAnalysisState.bStepRate q) t =
        (s.interpolatedStep q t).b := by
    unfold normalizedAffinePath
    exact hbcoord.symm
  have hcX : (s.interpolatedStep q t).x ≠ 0 := by
    rw [hxcoord]
    exact hxt
  rw [← parameterizedActivePerspectiveSlope_zero_eq_dotDirection
    c (s.interpolatedStep q t) q hcX]
  unfold parameterizedActivePerspectiveSlope
  rw [hY, hB, ← hxcoord, ← hdcoord]
  simp [normalizedAffinePath, hcX]

theorem parameterizedBankW_eq_saturated_of_interface
    {c : ℝ} (hc : 0 < c)
    (s : ParameterizedAnalysisState) (hx : 0 < s.x)
    (hy : s.y c = -1) (hb : 0 ≤ s.b) :
    parameterizedBankW c s.x s.substantive
        s.epsilon s.deferred =
      parameterizedSaturatedBank c s.x
        s.substantive s.deferred := by
  have hactive : -1 ≤ s.y c := by linarith
  have hbank :
      parameterizedBankW c s.x s.substantive
          s.epsilon s.deferred =
        s.x * s.deferred +
          s.x ^ 2 * parameterizedActiveG c (s.y c) s.b := by
    unfold parameterizedBankW
    rw [if_neg hx.ne']
    dsimp only
    change
      s.x * s.deferred +
          s.x ^ 2 * parameterizedBankG c (s.y c) s.b =
        s.x * s.deferred +
          s.x ^ 2 * parameterizedActiveG c (s.y c) s.b
    unfold parameterizedBankG
    rw [if_pos hactive]
  rw [hbank, hy, parameterizedBankG_interface hc hb]
  rw [← hy, ← s.eta_eq_y_add c]
  exact (parameterizedSaturatedBank_eq_flat_normalized hc hx).symm

def parameterizedInterfaceCrossingTime
    (c : ℝ) (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) : ℝ :=
  s.x * (1 + s.y c) /
    (1 - ParameterizedAnalysisState.yStepRate c q)

theorem one_sub_parameterizedYStepRate_pos
    {c : ℝ} (hc : 0 < c) (q : CappedBoundaryOutcome) :
    0 < 1 - ParameterizedAnalysisState.yStepRate c q := by
  cases q <;>
    simp only [ParameterizedAnalysisState.yStepRate] <;> linarith

theorem parameterizedInterfaceCrossingTime_mem_and_y
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    (hy0 : -1 ≤ s.y c) (hy1 : (s.step q).y c < -1) :
    parameterizedInterfaceCrossingTime c s q ∈ Set.Ico (0 : ℝ) 1 ∧
      (s.interpolatedStep q
        (parameterizedInterfaceCrossingTime c s q)).y c = -1 := by
  let δ := ParameterizedAnalysisState.yStepRate c q
  have hden : 0 < 1 - δ := by
    dsimp [δ]
    exact one_sub_parameterizedYStepRate_pos hc q
  have hx1 : 0 < s.x - 1 := by linarith
  have hyAtOne :
      (s.step q).y c =
        (s.x * s.y c + δ) / (s.x - 1) := by
    rw [← ParameterizedAnalysisState.interpolatedStep_one s q,
      ParameterizedAnalysisState.interpolatedStep_y_formula
        c q 1 hs.1.ne']
    · simp [δ]
    · exact ne_of_gt hx1
  have hcrossRaw : s.x * (1 + s.y c) < 1 - δ := by
    rw [hyAtOne] at hy1
    have hmul := (div_lt_iff₀ hx1).1 hy1
    nlinarith
  have ht0 :
      0 ≤ parameterizedInterfaceCrossingTime c s q := by
    unfold parameterizedInterfaceCrossingTime
    exact div_nonneg
      (mul_nonneg hs.1.le (by linarith)) hden.le
  have ht1 :
      parameterizedInterfaceCrossingTime c s q < 1 := by
    unfold parameterizedInterfaceCrossingTime
    exact (div_lt_one hden).2 hcrossRaw
  constructor
  · exact ⟨ht0, ht1⟩
  · have hxt :
        s.x - parameterizedInterfaceCrossingTime c s q ≠ 0 :=
      ne_of_gt (by linarith)
    rw [ParameterizedAnalysisState.interpolatedStep_y_formula
      c q (parameterizedInterfaceCrossingTime c s q)
      hs.1.ne' hxt]
    apply (div_eq_iff hxt).2
    unfold parameterizedInterfaceCrossingTime
    dsimp [δ] at hden hcrossRaw ⊢
    have hδ :
        1 - ParameterizedAnalysisState.yStepRate c q ≠ 0 :=
      hden.ne'
    field_simp [hδ]
    ring

theorem parameterized_active_before_crossing
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome)
    (hy0 : -1 ≤ s.y c) (hy1 : (s.step q).y c < -1)
    {t : ℝ} (_ht0 : 0 ≤ t)
    (ht : t ≤ parameterizedInterfaceCrossingTime c s q) :
    -1 ≤ (s.interpolatedStep q t).y c := by
  have hcross :=
    (parameterizedInterfaceCrossingTime_mem_and_y
      hc hs hx q hy0 hy1).2
  rw [← hcross]
  exact ParameterizedAnalysisState.y_interpolatedStep_antitone
    hc hs hx q ht
      (parameterizedInterfaceCrossingTime_mem_and_y
        hc hs hx q hy0 hy1).1.2.le

theorem exists_parameterized_active_to_flat_remainder
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ q : CappedBoundaryOutcome,
        -1 ≤ s.y c → (s.step q).y c < -1 →
        parameterizedBankW c
              (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            parameterizedBankW c
              s.x s.substantive s.epsilon s.deferred ≤
          (parameterizedBaseRawGradient c s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_parameterizedActiveUniformCurvature hc
  let Cactive := max C₀ 0
  let Cflat := parameterizedFlatUniformRemainder c
  let C := Cactive + Cflat
  have hCactive : 0 ≤ Cactive := le_max_right _ _
  have hCflat : 0 ≤ Cflat :=
    parameterizedFlatUniformRemainder_nonneg hc
  refine ⟨C, add_nonneg hCactive hCflat, ?_⟩
  intro s hs hx q hyStart hyEnd
  let τ := parameterizedInterfaceCrossingTime c s q
  have hτraw :=
    parameterizedInterfaceCrossingTime_mem_and_y
      hc hs hx q hyStart hyEnd
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hτraw.1.1, hτraw.1.2.le⟩
  have hyτ : (s.interpolatedStep q τ).y c = -1 := hτraw.2
  have hxt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
      s.x - t ≠ 0 :=
    ne_of_gt (by linarith [ht.2, hτ.2])
  let φ := parameterizedActivePerspectivePath c
    s.x s.deferred (s.y c) s.b
    (ParameterizedAnalysisState.deferredStepRate q)
    (ParameterizedAnalysisState.yStepRate c q)
    (ParameterizedAnalysisState.bStepRate q)
  let slope := parameterizedActivePerspectiveSlope c
    s.x s.deferred (s.y c) s.b
    (ParameterizedAnalysisState.deferredStepRate q)
    (ParameterizedAnalysisState.yStepRate c q)
    (ParameterizedAnalysisState.bStepRate q)
  let curvature := fun t =>
    parameterizedActivePerspectiveCurvature c
      (normalizedAffinePath s.x (s.y c)
        (ParameterizedAnalysisState.yStepRate c q) t)
      (normalizedAffinePath s.x s.b
        (ParameterizedAnalysisState.bStepRate q) t)
      (ParameterizedAnalysisState.deferredStepRate q)
      (ParameterizedAnalysisState.yStepRate c q)
      (ParameterizedAnalysisState.bStepRate q)
  have hregion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
      normalizedAffinePath s.x (s.y c)
          (ParameterizedAnalysisState.yStepRate c q) t ∈
        Set.Icc (-1 : ℝ) 0 ∧
      normalizedAffinePath s.x s.b
          (ParameterizedAnalysisState.bStepRate q) t ∈
        Set.Icc (0 : ℝ) (1 / (1 + c)) := by
    have htUnit : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ht.1, ht.2.trans hτ.2⟩
    have hfeas :=
      ParameterizedAnalysisState.interpolatedStep_feasible
        hs hx q htUnit
    have hylower :=
      parameterized_active_before_crossing
        hc hs hx q hyStart hyEnd ht.1 ht.2
    have hyupper :=
      ParameterizedAnalysisState.y_nonpos hc.le hfeas
    have hb :=
      ParameterizedAnalysisState.active_eta_b_bounds
        hc hfeas hylower
    have hyformula :=
      ParameterizedAnalysisState.interpolatedStep_y_formula
        c q t hs.1.ne' (hxt t ht)
    have hbformula :=
      ParameterizedAnalysisState.interpolatedStep_b_formula
        q t hs.1.ne' (hxt t ht)
    constructor
    · unfold normalizedAffinePath
      rw [← hyformula]
      exact ⟨hylower, hyupper⟩
    · unfold normalizedAffinePath
      rw [← hbformula]
      exact ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact parameterizedActivePerspectivePath_hasDerivAt
      hc (hxt t ht) (hregion t ht).1.2
  have hslope : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact parameterizedActivePerspectiveSlope_hasDerivAt
      hc (hxt t ht) (hregion t ht).1.2
  have hcurv : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      curvature t ≤ Cactive := by
    intro t ht
    exact (hC₀ q _ (hregion t ht).1 _
      (hregion t ht).2).trans (le_max_left _ _)
  have hprefix :=
    segment_taylor_of_second_deriv_le
      hCactive hτ hφ hslope hcurv
  have hpathτ :=
    parameterizedActivePerspectivePath_eq_bankW_interpolated
      (c := c) (s := s) q (t := τ) hs.1.ne'
      (hxt τ ⟨hτ.1, le_rfl⟩) (by rw [hyτ])
  have hpath0 :=
    parameterizedActivePerspectivePath_eq_bankW_interpolated
      (c := c) (s := s) q (t := 0) hs.1.ne'
      (by simpa using hs.1.ne') (by simpa using hyStart)
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpath0
  have hslope0 :
      slope 0 =
        (parameterizedBaseRawGradient c s).dotDirection q := by
    dsimp [slope]
    rw [parameterizedActivePerspectiveSlope_zero_eq_dotDirection
      c s q hs.1.ne']
    unfold parameterizedBaseRawGradient
    rw [if_pos hyStart]
  have hslopeτ :
      slope τ =
        (parameterizedSaturatedGradient c
          (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).deferred).dotDirection q := by
    have hcFeas :=
      ParameterizedAnalysisState.interpolatedStep_feasible
        hs hx q hτ
    have hactiveFlat :=
      parameterizedActiveRawGradient_eq_flat_of_interface
        hc (s.interpolatedStep q τ) hyτ
        (ParameterizedAnalysisState.b_nonneg hcFeas)
    have hsatFlat :=
      parameterizedSaturatedGradient_eq_flatRawGradient
        hc (s.interpolatedStep q τ) hcFeas.1
    dsimp [slope]
    rw [parameterizedActiveSlope_eq_interpolated_gradient
      q hs.1.ne' (hxt τ ⟨hτ.1, le_rfl⟩)]
    rw [hsatFlat, ← hactiveFlat]
  have hprefixValue :
      parameterizedBankW c
          (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).epsilon
          (s.interpolatedStep q τ).deferred -
        parameterizedBankW c
          s.x s.substantive s.epsilon s.deferred ≤
      (parameterizedBaseRawGradient c s).dotDirection q * τ +
        Cactive * τ ^ 2 := by
    rw [← hpathτ, ← hpath0, ← hslope0]
    exact hprefix.1
  have hslopeVar :
      (parameterizedSaturatedGradient c
          (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).deferred).dotDirection q ≤
        (parameterizedBaseRawGradient c s).dotDirection q +
          Cactive * τ := by
    rw [← hslopeτ, ← hslope0]
    exact hprefix.2
  have hflatRaw :=
    parameterizedSaturatedBank_interpolated_subsegment
      hc s q τ 1
  have hxNext : 0 < (s.step q).x := by
    cases q <;>
      simp only [ParameterizedAnalysisState.step] <;> linarith
  have hbankNext :=
    parameterizedBankW_eq_saturated_of_flat
      hc (s.step q) hxNext hyEnd
  have hcFeas :=
    ParameterizedAnalysisState.interpolatedStep_feasible
      hs hx q hτ
  have hbankτ :=
    parameterizedBankW_eq_saturated_of_interface
      hc (s.interpolatedStep q τ) hcFeas.1 hyτ
      (ParameterizedAnalysisState.b_nonneg hcFeas)
  simp only [ParameterizedAnalysisState.interpolatedStep_one] at hflatRaw
  rw [← hbankNext, ← hbankτ] at hflatRaw
  have hDirection :=
    parameterizedFlatDirectionRemainder_le_uniform hc q
  have hr0 : 0 ≤ 1 - τ := by linarith [hτ.2]
  have hr2 : (1 - τ) ^ 2 ≤ 1 := by
    nlinarith [hτ.1, hτ.2, sq_nonneg (1 - τ)]
  have hflatConst :
      parameterizedFlatDirectionRemainder c q * (1 - τ) ^ 2 ≤
        Cflat := by
    calc
      parameterizedFlatDirectionRemainder c q * (1 - τ) ^ 2 ≤
          Cflat * (1 - τ) ^ 2 :=
        mul_le_mul_of_nonneg_right hDirection (sq_nonneg _)
      _ ≤ Cflat := mul_le_of_le_one_right hCflat hr2
  have hslopeScaled :=
    mul_le_mul_of_nonneg_right hslopeVar hr0
  have hactiveConst :
      Cactive * τ ^ 2 + Cactive * τ * (1 - τ) ≤ Cactive := by
    nlinarith [hCactive, hτ.1, hτ.2]
  have hgradSplit :
      (parameterizedBaseRawGradient c s).dotDirection q * τ +
          (parameterizedBaseRawGradient c s).dotDirection q * (1 - τ) =
        (parameterizedBaseRawGradient c s).dotDirection q := by ring
  dsimp [C]
  linarith

def HasParameterizedBaseRemainderAboveTwo
    (c C : ℝ) : Prop :=
  ∀ (s : ParameterizedAnalysisState), s.Feasible → 2 ≤ s.x →
    ∀ q : CappedBoundaryOutcome,
      parameterizedBankW c
            (s.step q).x (s.step q).substantive
            (s.step q).epsilon (s.step q).deferred -
          parameterizedBankW c
            s.x s.substantive s.epsilon s.deferred ≤
        (parameterizedBaseRawGradient c s).dotDirection q + C

theorem exists_parameterizedBaseRemainderAboveTwo
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasParameterizedBaseRemainderAboveTwo c C := by
  obtain ⟨Caa, hCaa, haa⟩ :=
    exists_parameterized_active_to_active_remainder hc
  obtain ⟨Caf, hCaf, haf⟩ :=
    exists_parameterized_active_to_flat_remainder hc
  let C := max (max Caa Caf) (parameterizedFlatUniformRemainder c)
  have hC : 0 ≤ C :=
    hCaa.trans (le_max_of_le_left (le_max_left _ _))
  refine ⟨C, hC, ?_⟩
  intro s hs hx q
  by_cases hyStart : -1 ≤ s.y c
  · by_cases hyEnd : -1 ≤ (s.step q).y c
    · have h := haa s hs hx q hyStart hyEnd
      have hle : Caa ≤ C :=
        le_max_of_le_left (le_max_left _ _)
      linarith
    · have h := haf s hs hx q hyStart (lt_of_not_ge hyEnd)
      have hle : Caf ≤ C :=
        le_max_of_le_left (le_max_right _ _)
      linarith
  · have h := parameterized_flat_remainder_above_two
      hc hs hx (lt_of_not_ge hyStart) q
    have hle : parameterizedFlatUniformRemainder c ≤ C :=
      le_max_right _ _
    linarith

def parameterizedActiveTerminalRemainder
    (c : ℝ) (q : CappedBoundaryOutcome) (y b : ℝ) : ℝ :=
  parameterizedActiveG c y b -
    ParameterizedAnalysisState.deferredStepRate q -
    (y + ParameterizedAnalysisState.yStepRate c q) *
      parameterizedActiveGy c y b -
    (b + ParameterizedAnalysisState.bStepRate q) *
      parameterizedActiveGb c y b

def parameterizedActiveTerminalRemainderFor
    (c : ℝ) (q : CappedBoundaryOutcome) (p : ℝ × ℝ) : ℝ :=
  parameterizedActiveTerminalRemainder c q p.1 p.2

theorem parameterizedActiveTerminalRemainderFor_continuousOn
    {c : ℝ} (hc : 0 < c) (q : CappedBoundaryOutcome) :
    ContinuousOn (parameterizedActiveTerminalRemainderFor c q)
      (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) := by
  intro p hp
  have hy0 : p.1 ≤ 0 := hp.1.2
  have hden : c - 2 * p.1 ≠ 0 :=
    (parameterized_denominator_pos hc hy0).ne'
  have hA : ContinuousAt (parameterizedThreshold c) p.1 :=
    (parameterizedThreshold_hasDerivAt hc hy0).continuousAt
  have hAcomp :
      ContinuousAt
        (fun z : ℝ × ℝ => parameterizedThreshold c z.1) p := by
    change ContinuousAt (parameterizedThreshold c ∘ Prod.fst) p
    exact hA.comp continuousAt_fst
  unfold parameterizedActiveTerminalRemainderFor
    parameterizedActiveTerminalRemainder
    parameterizedActiveG parameterizedActiveGy
    parameterizedActiveGb parameterizedBankHPrime
    parameterizedBankF parameterizedBankH
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp)

theorem exists_parameterizedActiveTerminalUniformBound
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ q : CappedBoundaryOutcome,
      ∀ y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ b ∈ Set.Icc (0 : ℝ) (1 / (1 + c)),
        parameterizedActiveTerminalRemainder c q y b ≤ C := by
  have hcompact :
      IsCompact (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound (q : CappedBoundaryOutcome) :
      ∃ C : ℝ, ∀ p ∈
          (Set.Icc (-1 : ℝ) 0 ×ˢ
            Set.Icc (0 : ℝ) (1 / (1 + c))),
        parameterizedActiveTerminalRemainderFor c q p ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (parameterizedActiveTerminalRemainderFor_continuousOn hc q)
    refine ⟨C, ?_⟩
    intro p hp
    simpa [Real.norm_eq_abs] using
      (le_abs_self
        (parameterizedActiveTerminalRemainderFor c q p)).trans (by
          simpa [Real.norm_eq_abs] using hC p hp)
  obtain ⟨Cz, hz⟩ := hbound .zero
  obtain ⟨Ce, he⟩ := hbound .epsilon
  obtain ⟨Ci, hi⟩ := hbound .immediate
  obtain ⟨Cd, hd⟩ := hbound .deferred
  obtain ⟨Ck, hk⟩ := hbound .cap
  refine ⟨max (max (max Cz Ce) (max Ci Cd)) Ck, ?_⟩
  intro q y hy b hb
  have hp : (y, b) ∈
      (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / (1 + c))) := ⟨hy, hb⟩
  cases q with
  | zero =>
      exact (hz (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_left (le_max_left _ _)))
  | epsilon =>
      exact (he (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_left (le_max_right _ _)))
  | immediate =>
      exact (hi (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_right (le_max_left _ _)))
  | deferred =>
      exact (hd (y, b) hp).trans
        (le_max_of_le_left
          (le_max_of_le_right (le_max_right _ _)))
  | cap =>
      exact (hk (y, b) hp).trans (le_max_right _ _)

theorem parameterizedActiveTerminal_residual_eq
    (c : ℝ) (s : ParameterizedAnalysisState)
    (q : CappedBoundaryOutcome) (hx : s.x = 1) :
    -parameterizedActivePerspectivePath c s.x s.deferred
        (s.y c) s.b
        (ParameterizedAnalysisState.deferredStepRate q)
        (ParameterizedAnalysisState.yStepRate c q)
        (ParameterizedAnalysisState.bStepRate q) 0 -
      parameterizedActivePerspectiveSlope c s.x s.deferred
        (s.y c) s.b
        (ParameterizedAnalysisState.deferredStepRate q)
        (ParameterizedAnalysisState.yStepRate c q)
        (ParameterizedAnalysisState.bStepRate q) 0 =
      parameterizedActiveTerminalRemainder c q (s.y c) s.b := by
  rw [hx]
  unfold parameterizedActiveTerminalRemainder
    parameterizedActivePerspectivePath
    parameterizedActivePerspectiveSlope normalizedAffinePath
  ring_nf

theorem exists_parameterized_active_terminal_remainder
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ParameterizedAnalysisState), s.Feasible → s.x = 1 →
      ∀ q : CappedBoundaryOutcome, -1 ≤ s.y c →
        parameterizedBankW c
              (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            parameterizedBankW c
              s.x s.substantive s.epsilon s.deferred ≤
          (parameterizedBaseRawGradient c s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_parameterizedActiveTerminalUniformBound hc
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro s hs hx q hy
  have hy0 := ParameterizedAnalysisState.y_nonpos hc.le hs
  have hb :=
    ParameterizedAnalysisState.active_eta_b_bounds hc hs hy
  have hbound :=
    hC₀ q (s.y c) ⟨hy, hy0⟩ s.b
      ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hbound' :
      parameterizedActiveTerminalRemainder c q (s.y c) s.b ≤
        max C₀ 0 :=
    hbound.trans (le_max_left _ _)
  have hnext0 : (s.step q).x = 0 := by
    cases q <;> simp [ParameterizedAnalysisState.step, hx]
  have hbankNext :
      parameterizedBankW c
          (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred = 0 := by
    rw [hnext0]
    exact parameterizedBankW_terminal _ _ _ _
  have hpathZero :=
    parameterizedActivePerspectivePath_eq_bankW_interpolated
      (c := c) (s := s) q (t := 0) hs.1.ne'
      (by simpa using hs.1.ne') (by simpa using hy)
  simp only [ParameterizedAnalysisState.interpolatedStep_zero] at hpathZero
  have hresidual :=
    parameterizedActiveTerminal_residual_eq c s q hx
  have hgrad :
      (parameterizedBaseRawGradient c s).dotDirection q =
        parameterizedActivePerspectiveSlope c s.x s.deferred
          (s.y c) s.b
          (ParameterizedAnalysisState.deferredStepRate q)
          (ParameterizedAnalysisState.yStepRate c q)
          (ParameterizedAnalysisState.bStepRate q) 0 := by
    unfold parameterizedBaseRawGradient
    rw [if_pos hy]
    exact (parameterizedActivePerspectiveSlope_zero_eq_dotDirection
      c s q hs.1.ne').symm
  rw [hbankNext, ← hpathZero, hgrad]
  linarith

theorem parameterized_flat_terminal_remainder
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : s.x = 1) (hy : s.y c < -1)
    (q : CappedBoundaryOutcome) :
    parameterizedBankW c
          (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        parameterizedBankW c
          s.x s.substantive s.epsilon s.deferred ≤
      (parameterizedBaseRawGradient c s).dotDirection q +
        parameterizedFlatUniformRemainder c := by
  have hsat := parameterizedSaturatedBank_step_le hc s q
  have hnext0 : (s.step q).x = 0 := by
    cases q <;> simp [ParameterizedAnalysisState.step, hx]
  have hbankNext :
      parameterizedBankW c
          (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred = 0 := by
    rw [hnext0]
    exact parameterizedBankW_terminal _ _ _ _
  have hsatNext :
      0 ≤ parameterizedSaturatedBank c
          (s.step q).x (s.step q).substantive
          (s.step q).deferred := by
    rw [hnext0]
    unfold parameterizedSaturatedBank
    simp only [zero_mul, zero_add]
    exact div_nonneg (sq_nonneg _) (by positivity)
  rw [hbankNext,
    parameterizedBankW_eq_saturated_of_flat hc s hs.1 hy,
    parameterizedBaseGradient_eq_saturated_of_flat hc s hs.1 hy]
  linarith

def HasReachableParameterizedBaseRemainder
    (c C : ℝ) : Prop :=
  ∀ s : ParameterizedAnalysisState, s.Reachable →
    ∀ q : CappedBoundaryOutcome,
      parameterizedBankW c
            (s.step q).x (s.step q).substantive
            (s.step q).epsilon (s.step q).deferred -
          parameterizedBankW c
            s.x s.substantive s.epsilon s.deferred ≤
        (parameterizedBaseRawGradient c s).dotDirection q + C

theorem exists_reachableParameterizedBaseRemainder
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasReachableParameterizedBaseRemainder c C := by
  obtain ⟨Cabove, hCabove, habove⟩ :=
    exists_parameterizedBaseRemainderAboveTwo hc
  obtain ⟨Cactive, hCactive, hactive⟩ :=
    exists_parameterized_active_terminal_remainder hc
  let Cterminal :=
    max Cactive (parameterizedFlatUniformRemainder c)
  let C := max Cabove Cterminal
  have hC : 0 ≤ C := hCabove.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hs q
  rcases hs.2 with hx | hx
  · by_cases hy : -1 ≤ s.y c
    · have h := hactive s hs.1 hx q hy
      have hle : Cactive ≤ C :=
        le_trans (le_max_left _ _ ) (le_max_right _ _)
      linarith
    · have h := parameterized_flat_terminal_remainder
        hc hs.1 hx (lt_of_not_ge hy) q
      have hle : parameterizedFlatUniformRemainder c ≤ C :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
  · have h := habove s hs.1 hx q
    have hle : Cabove ≤ C := le_max_left _ _
    linarith

/-! ## Separation of the remaining one-dimensional cap reserve -/

def HasReachableCompleteCapReserveRemainder
    (c δ m C : ℝ) : Prop :=
  ∀ s : ParameterizedAnalysisState, s.Reachable →
    ∀ q : CappedBoundaryOutcome,
      capReserveRawW c δ m
            (s.step q).x (s.step q).capped -
          capReserveRawW c δ m s.x s.capped ≤
        (capReserveCompleteRawGradient c δ m s).dotDirection q + C

theorem hasReachableCompleteCappedBankRemainder_of_components
    {c δ m Cbase Creserve : ℝ}
    (hbase : HasReachableParameterizedBaseRemainder c Cbase)
    (hreserve :
      HasReachableCompleteCapReserveRemainder
        c δ m Creserve) :
    HasReachableCompleteCappedBankRemainder
      c δ m (Cbase + Creserve) := by
  intro s hs q
  have hb := hbase s hs q
  have hr := hreserve s hs q
  unfold cappedFullBankW cappedCompleteRawGradient
  rw [CappedRawGradient.dotDirection_add]
  linarith

/-- The complete parameterized base bank is now discharged.  Thus the only
remaining analytic input for the full five-endpoint theorem is the
one-dimensional perspective reserve in `(x,K)`. -/
theorem exists_reachableCompleteCappedBankRemainder_of_capReserve
    (c : MixedRatioDomain)
    (hreserve :
      ∃ Creserve : ℝ, 0 ≤ Creserve ∧
        HasReachableCompleteCapReserveRemainder
          c (mixedReserveDelta c) (mixedMass c) Creserve) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasReachableCompleteCappedBankRemainder
        c (mixedReserveDelta c) (mixedMass c) C := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_reachableParameterizedBaseRemainder hc
  obtain ⟨Creserve, hCreserve, hreserve⟩ := hreserve
  refine ⟨Cbase + Creserve, add_nonneg hCbase hCreserve, ?_⟩
  exact hasReachableCompleteCappedBankRemainder_of_components
    hbase hreserve

end

end SchedulingPaper
