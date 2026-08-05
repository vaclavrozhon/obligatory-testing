import SchedulingPaper.BankStateBounds
import SchedulingPaper.TaylorRemainder
import SchedulingPaper.FlatRemainder
import Mathlib.Tactic

/-!
# Uniform remainder for the glued bank potential

This module proves a finite uniform one-step Taylor remainder on the
nonterminal range `2 ≤ x`, including steps that cross the active/flat
interface `y = -1`.  It also isolates the remaining real-valued band
`0 < x < 2` needed by the older unrestricted formulation.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem activeRawGradient_eq_flatRawGradient_of_interface
    (s : AnalysisState) (hy : s.y = -1) (hb : 0 ≤ s.b) :
    activeRawGradient s = flatRawGradient s := by
  have hA : activeThreshold s.y = 1 := by
    rw [hy, activeThreshold_at_neg_one]
  have hH : bankH s.y = 0 := by
    rw [hy]
    simp [bankH, activeThreshold_at_neg_one]
  have hHp : bankHPrime s.y = 1 := by
    rw [hy]
    simp [bankHPrime, activeThreshold_at_neg_one]
  have hpart : positivePart (1 + s.eta) = RStar * s.b := by
    have heta : s.eta = -1 + RStar * s.b := by
      rw [AnalysisState.eta_eq_y_add, hy]
    rw [heta]
    simp only [show 1 + (-1 + RStar * s.b) = RStar * s.b by ring]
    unfold positivePart
    rw [max_eq_left]
    exact mul_nonneg (lt_trans zero_lt_one one_lt_RStar).le hb
  have hG : activeG s.y s.b = RStar * s.b ^ 2 / 2 := by
    rw [activeG, hy, bankF_at_neg_one]
    simp [bankH, activeThreshold_at_neg_one]
  have hGy : activeGy s.y s.b = s.b := by
    simp [activeGy, hA, hHp]
  have hGb : activeGb s.y s.b = RStar * s.b := by
    simp [activeGb, hH]
  have hflatG : flatG s.eta = RStar * s.b ^ 2 / 2 := by
    unfold flatG
    rw [hpart]
    have hR : RStar ≠ 0 :=
      ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
    field_simp [hR]
  have hflatGp : flatGPrime s.eta = s.b := by
    unfold flatGPrime
    rw [hpart]
    have hR : RStar ≠ 0 :=
      ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
    field_simp [hR]
  unfold activeRawGradient flatRawGradient
  dsimp only
  rw [hG, hGy, hGb, hflatG, hflatGp, RawGradient.mk.injEq]
  rw [AnalysisState.eta_eq_y_add, hy]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem bankRawGradient_eq_active_of_interface
    (s : AnalysisState) (hy : s.y = -1) :
    bankRawGradient s = activeRawGradient s := by
  unfold bankRawGradient
  rw [if_pos]
  linarith

/-- The glued gradient has matching active/flat formulas at the interface. -/
theorem bankRawGradient_interface
    (s : AnalysisState) (hy : s.y = -1) (hb : 0 ≤ s.b) :
    bankRawGradient s = flatRawGradient s := by
  rw [bankRawGradient_eq_active_of_interface s hy,
    activeRawGradient_eq_flatRawGradient_of_interface s hy hb]

/-- The strongest flat branch result derivable immediately from the current
API: every feasible flat step with at least two units remaining has the
uniform saturated remainder. -/
theorem flat_uniform_remainder_above_two
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (hy : s.y < -1) (q : BoundaryOutcome) :
    bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        bankW s.x s.substantive s.epsilon s.deferred ≤
      (bankRawGradient s).dotDirection q + saturatedUniformRemainder := by
  have hx0 : 0 < s.x := hs.1
  have hxNext : 0 < (s.step q).x := by
    cases q <;> simp only [AnalysisState.step] <;> linarith
  have hyNext : (s.step q).y < -1 :=
    AnalysisState.flat_persists_after_step hs hx q hy
  have hflat := bankW_flat_step_le_gradient_add_remainder
    s q hx0 hy hxNext hyNext
  have hC := saturatedDirectionRemainder_le_uniform q
  linarith

/-- Chain rule for the active normalized potential along any differentiable
one-dimensional path. -/
theorem activeG_hasDerivAt_comp
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => activeG (Y u) (B u))
      (activeGy y b * y' + activeGb y b * b') t := by
  have hF : HasDerivAt (fun u => bankF (Y u))
      ((activeThreshold y - 1) * y') t := by
    have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
    convert (bankF_hasDerivAt hy0').comp t hY using 1 <;> simp [hy]
  have hH : HasDerivAt (fun u => bankH (Y u))
      (bankHPrime y * y') t := by
    have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
    convert (bankH_hasDerivAt hy0').comp t hY using 1 <;> simp [hy]
  have hquad : HasDerivAt (fun u => RStar * B u ^ 2 / 2)
      (RStar * b * b') t := by
    convert
      (((hasDerivAt_const t RStar).mul (hB.pow 2)).div_const 2)
        using 1 <;>
      simp [hb] <;> ring
  unfold activeG activeGy activeGb
  convert hF.add (hB.mul hH) |>.add hquad using 1 <;>
    simp [hy, hb] <;> ring

def interfaceCrossingTime (s : AnalysisState)
    (q : BoundaryOutcome) : ℝ :=
  s.x * (1 + s.y) / (1 - AnalysisState.yStepRate q)

theorem one_sub_yStepRate_pos (q : BoundaryOutcome) :
    0 < 1 - AnalysisState.yStepRate q := by
  cases q <;>
    simp only [AnalysisState.yStepRate] <;>
    nlinarith [one_lt_RStar]

/-- If an initially active step finishes in the flat region, the explicit
fractional-linear path meets the interface at a unique time in `[0,1)`. -/
theorem interfaceCrossingTime_mem_and_y
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) (hy0 : -1 ≤ s.y)
    (hy1 : (s.step q).y < -1) :
    interfaceCrossingTime s q ∈ Set.Ico (0 : ℝ) 1 ∧
      (s.interpolatedStep q (interfaceCrossingTime s q)).y = -1 := by
  let δ := AnalysisState.yStepRate q
  have hden : 0 < 1 - δ := by
    dsimp [δ]
    exact one_sub_yStepRate_pos q
  have hx0 : 0 < s.x := hs.1
  have hx1 : 0 < s.x - 1 := by linarith
  have hyAtOne :
      (s.step q).y = (s.x * s.y + δ) / (s.x - 1) := by
    rw [← AnalysisState.interpolatedStep_one s q,
      AnalysisState.interpolatedStep_y_formula q 1 hs.1.ne']
    · simp [δ]
    · exact ne_of_gt hx1
  have hcrossRaw : s.x * (1 + s.y) < 1 - δ := by
    rw [hyAtOne] at hy1
    have hmul := (div_lt_iff₀ hx1).1 hy1
    nlinarith
  have ht0 : 0 ≤ interfaceCrossingTime s q := by
    unfold interfaceCrossingTime
    exact div_nonneg
      (mul_nonneg hx0.le (by linarith))
      hden.le
  have ht1 : interfaceCrossingTime s q < 1 := by
    unfold interfaceCrossingTime
    exact (div_lt_one hden).2 hcrossRaw
  constructor
  · exact ⟨ht0, ht1⟩
  · have hxt : s.x - interfaceCrossingTime s q ≠ 0 := by
      apply ne_of_gt
      linarith
    rw [AnalysisState.interpolatedStep_y_formula q
      (interfaceCrossingTime s q) hs.1.ne' hxt]
    apply (div_eq_iff hxt).2
    unfold interfaceCrossingTime
    dsimp [δ] at hden hcrossRaw ⊢
    have hδ : 1 - AnalysisState.yStepRate q ≠ 0 := hden.ne'
    field_simp [hδ]
    ring

/-- Before the crossing time the path is active. -/
theorem active_before_interfaceCrossingTime
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) (hy0 : -1 ≤ s.y)
    (hy1 : (s.step q).y < -1)
    {t : ℝ} (_ht0 : 0 ≤ t)
    (ht : t ≤ interfaceCrossingTime s q) :
    -1 ≤ (s.interpolatedStep q t).y := by
  have hcross :=
    (interfaceCrossingTime_mem_and_y hs hx q hy0 hy1).2
  rw [← hcross]
  exact AnalysisState.y_interpolatedStep_antitone hs hx q
    ht (interfaceCrossingTime_mem_and_y hs hx q hy0 hy1).1.2.le

def normalizedAffinePath (x z δ t : ℝ) : ℝ :=
  (x * z + δ * t) / (x - t)

theorem normalizedAffinePath_hasDerivAt
    {x z δ t : ℝ} (hxt : x - t ≠ 0) :
    HasDerivAt (normalizedAffinePath x z δ)
      (x * (z + δ) / (x - t) ^ 2) t := by
  have hnum : HasDerivAt (fun u : ℝ => x * z + δ * u) δ t := by
    convert (hasDerivAt_const t (x * z)).add
      ((hasDerivAt_const t δ).mul (hasDerivAt_id t)) using 1 <;> ring
  have hden : HasDerivAt (fun u : ℝ => x - u) (-1) t := by
    convert (hasDerivAt_const t x).sub (hasDerivAt_id t) using 1 <;> ring
  unfold normalizedAffinePath
  convert hnum.div hden hxt using 1
  ring

def activePerspectivePath
    (x d y b δd δy δb t : ℝ) : ℝ :=
  (x - t) * (d + δd * t) +
    (x - t) ^ 2 *
      activeG (normalizedAffinePath x y δy t)
        (normalizedAffinePath x b δb t)

def activePerspectiveSlope
    (x d y b δd δy δb t : ℝ) : ℝ :=
  -(d + δd * t) + (x - t) * δd +
    (x - t) *
      (-2 * activeG
          (normalizedAffinePath x y δy t)
          (normalizedAffinePath x b δb t) +
        (normalizedAffinePath x y δy t + δy) *
          activeGy
            (normalizedAffinePath x y δy t)
            (normalizedAffinePath x b δb t) +
        (normalizedAffinePath x b δb t + δb) *
          activeGb
            (normalizedAffinePath x y δy t)
            (normalizedAffinePath x b δb t))

/-- Exact first derivative of the homogeneous active formula along an
affine raw-coordinate direction. -/
theorem activePerspectivePath_hasDerivAt
    {x d y b δd δy δb t : ℝ}
    (hxt : x - t ≠ 0)
    (hy0 : normalizedAffinePath x y δy t ≤ 0) :
    HasDerivAt (activePerspectivePath x d y b δd δy δb)
      (activePerspectiveSlope x d y b δd δy δb t) t := by
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
  have hG := activeG_hasDerivAt_comp hY rfl hB rfl hy0
  unfold activePerspectivePath activePerspectiveSlope
  dsimp [X, D, Y, B] at hX hD hY hB hG ⊢
  have hraw := (hX.mul hD).add ((hX.pow 2).mul hG)
  simp only [Pi.pow_apply] at hraw
  convert hraw using 1
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

def deferredStepRate : BoundaryOutcome → ℝ
  | .deferred => 1
  | _ => 0

def bStepRate : BoundaryOutcome → ℝ
  | .epsilon => 1
  | _ => 0

theorem activePerspectiveSlope_zero_eq_dotDirection
    (s : AnalysisState) (q : BoundaryOutcome) (hx : s.x ≠ 0) :
    activePerspectiveSlope s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q) 0 =
      (activeRawGradient s).dotDirection q := by
  cases q <;>
    simp only [activePerspectiveSlope, normalizedAffinePath,
      deferredStepRate, AnalysisState.yStepRate, bStepRate,
      RawGradient.dotDirection, activeRawGradient] <;>
    simp [hx] <;>
    ring

/-- The active raw expression has exactly the gradient proxy used by the
accounting layer as its initial path derivative. -/
theorem activePerspectivePath_hasDerivAt_zero
    (s : AnalysisState) (q : BoundaryOutcome)
    (hx : s.x ≠ 0) (hy0 : s.y ≤ 0) :
    HasDerivAt
      (activePerspectivePath s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q))
      ((activeRawGradient s).dotDirection q) 0 := by
  rw [← activePerspectiveSlope_zero_eq_dotDirection s q hx]
  apply activePerspectivePath_hasDerivAt (hxt := by simpa using hx)
  simpa [normalizedAffinePath, hx]

def bankHSecond (y : ℝ) : ℝ :=
  2 / (rhoStar - 2 * y) +
    2 * (1 + y) / (rhoStar - 2 * y) ^ 2

theorem bankHPrime_hasDerivAt {y : ℝ} (hy : y ≤ 0) :
    HasDerivAt bankHPrime (bankHSecond y) y := by
  have hA := activeThreshold_hasDerivAt hy
  have hnum : HasDerivAt (fun u : ℝ => 1 + u) 1 y := by
    convert (hasDerivAt_const y 1).add (hasDerivAt_id y) using 1 <;> ring
  have hden : HasDerivAt (fun u : ℝ => rhoStar - 2 * u) (-2) y := by
    convert (hasDerivAt_const y rhoStar).sub
      ((hasDerivAt_const y 2).mul (hasDerivAt_id y)) using 1 <;> ring
  have hden0 : rhoStar - 2 * y ≠ 0 :=
    (active_denominator_pos hy).ne'
  unfold bankHPrime bankHSecond
  convert hA.add (hnum.div hden hden0) using 1
  field_simp [hden0]
  ring

def activeGyy (y b : ℝ) : ℝ :=
  1 / (rhoStar - 2 * y) + b * bankHSecond y

theorem activeGy_hasDerivAt_comp
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => activeGy (Y u) (B u))
      (activeGyy y b * y' + bankHPrime y * b') t := by
  have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
  have hA := (activeThreshold_hasDerivAt hy0').comp t hY
  have hHp := (bankHPrime_hasDerivAt hy0').comp t hY
  unfold activeGy activeGyy
  convert (hA.sub_const 1).add (hB.mul hHp) using 1 <;>
    simp [hy, hb] <;> ring

theorem activeGb_hasDerivAt_comp
    {Y B : ℝ → ℝ} {t y b y' b' : ℝ}
    (hY : HasDerivAt Y y' t) (hy : Y t = y)
    (hB : HasDerivAt B b' t) (hb : B t = b)
    (hy0 : y ≤ 0) :
    HasDerivAt (fun u => activeGb (Y u) (B u))
      (bankHPrime y * y' + RStar * b') t := by
  have hy0' : Y t ≤ 0 := by simpa [hy] using hy0
  have hH := (bankH_hasDerivAt hy0').comp t hY
  unfold activeGb
  convert hH.add ((hasDerivAt_const t RStar).mul hB) using 1 <;>
    simp [hy, hb] <;> ring

def activePerspectiveCurvature
    (y b δd δy δb : ℝ) : ℝ :=
  -2 * δd + 2 * activeG y b -
    2 * (y + δy) * activeGy y b -
    2 * (b + δb) * activeGb y b +
    activeGyy y b * (y + δy) ^ 2 +
    2 * bankHPrime y * (y + δy) * (b + δb) +
    RStar * (b + δb) ^ 2

/-- Exact second derivative on the active side.  Crucially, the formula is
independent of the raw scale `x`; only bounded normalized coordinates occur. -/
theorem activePerspectiveSlope_hasDerivAt
    {x d y b δd δy δb t : ℝ}
    (hxt : x - t ≠ 0)
    (hy0 : normalizedAffinePath x y δy t ≤ 0) :
    HasDerivAt (activePerspectiveSlope x d y b δd δy δb)
      (activePerspectiveCurvature
        (normalizedAffinePath x y δy t)
        (normalizedAffinePath x b δb t)
        δd δy δb) t := by
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
      (x * (y + δy) / (x - t) ^ 2) t := by
    exact hY.add_const δy
  have hV : HasDerivAt V
      (x * (b + δb) / (x - t) ^ 2) t := by
    exact hB.add_const δb
  have hG := activeG_hasDerivAt_comp hY rfl hB rfl hy0
  have hGy := activeGy_hasDerivAt_comp hY rfl hB rfl hy0
  have hGb := activeGb_hasDerivAt_comp hY rfl hB rfl hy0
  have hQ :=
    (((hasDerivAt_const t (-2)).mul hG).add (hU.mul hGy)).add
      (hV.mul hGb)
  have hSlope :=
    ((hD.neg).add (hX.mul_const δd)).add (hX.mul hQ)
  unfold activePerspectiveSlope activePerspectiveCurvature
  dsimp [X, D, Y, B, U, V] at hX hD hY hB hU hV hG hGy hGb hQ hSlope ⊢
  convert hSlope using 1
  unfold normalizedAffinePath
  field_simp [hxt]
  ring

def activeCurvatureFor (q : BoundaryOutcome) (p : ℝ × ℝ) : ℝ :=
  activePerspectiveCurvature p.1 p.2
    (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)

theorem activeCurvatureFor_continuousOn (q : BoundaryOutcome) :
    ContinuousOn (activeCurvatureFor q)
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
  unfold activeCurvatureFor activePerspectiveCurvature activeGyy
    bankHSecond activeG activeGy activeGb bankHPrime bankF bankH
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp [hden])

/-- Abstract compactness form of the missing active curvature estimate. -/
theorem exists_activeUniformCurvature :
    ∃ C : ℝ, ∀ q : BoundaryOutcome,
      ∀ y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ b ∈ Set.Icc (0 : ℝ) (1 / RStar),
        activePerspectiveCurvature y b
          (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q) ≤ C := by
  have hcompact :
      IsCompact (Set.Icc (-1 : ℝ) 0 ×ˢ
        Set.Icc (0 : ℝ) (1 / RStar)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound (q : BoundaryOutcome) :
      ∃ C : ℝ, ∀ p ∈
          (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (0 : ℝ) (1 / RStar)),
        activeCurvatureFor q p ≤ C := by
    obtain ⟨C, hC⟩ :=
      hcompact.exists_bound_of_continuousOn
        (activeCurvatureFor_continuousOn q)
    refine ⟨C, ?_⟩
    intro p hp
    simpa [Real.norm_eq_abs] using
      (le_abs_self (activeCurvatureFor q p)).trans (by
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

/-- A convenient second-derivative wrapper around the mean-value Taylor
lemma already present in `TaylorRemainder`. -/
theorem unit_taylor_upper_of_second_deriv_le
    {φ d dd : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (d t) t)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt d (dd t) t)
    (hdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, dd t ≤ C) :
    φ 1 - φ 0 ≤ d 0 + C := by
  apply unit_taylor_upper_of_hasDerivAt hφ
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hcont : ContinuousOn d (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ d (Set.Ioo (0 : ℝ) 1) := by
    intro u hu
    exact (hd u ⟨hu.1.le, hu.2.le⟩).differentiableAt.differentiableWithinAt
  have hvar :=
    (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
      (C := C) hcont (by simpa using hdiff) (by
        intro u hu
        have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hu
        rw [(hd u ⟨hu'.1.le, hu'.2.le⟩).deriv]
        exact hdd u ⟨hu'.1.le, hu'.2.le⟩)
      0 (by simp) t htIcc ht.1.le
  have hCt : C * t ≤ C := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2.le hC]
  norm_num at hvar
  linarith

theorem activePerspective_unit_remainder
    {x d y b C : ℝ} (hx : 2 ≤ x) (hC : 0 ≤ C)
    (q : BoundaryOutcome)
    (hregion : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      normalizedAffinePath x y (AnalysisState.yStepRate q) t ∈
          Set.Icc (-1 : ℝ) 0 ∧
        normalizedAffinePath x b (bStepRate q) t ∈
          Set.Icc (0 : ℝ) (1 / RStar))
    (hcurvature : ∀ Y ∈ Set.Icc (-1 : ℝ) 0,
      ∀ B ∈ Set.Icc (0 : ℝ) (1 / RStar),
        activePerspectiveCurvature Y B
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) ≤ C) :
    activePerspectivePath x d y b
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) 1 -
        activePerspectivePath x d y b
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) 0 ≤
      activePerspectiveSlope x d y b
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) 0 + C := by
  let φ := activePerspectivePath x d y b
    (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  let slope := activePerspectiveSlope x d y b
    (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  let curvature := fun t =>
    activePerspectiveCurvature
      (normalizedAffinePath x y (AnalysisState.yStepRate q) t)
      (normalizedAffinePath x b (bStepRate q) t)
      (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  have hxt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      x - t ≠ 0 := ne_of_gt (by linarith [ht.2])
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact activePerspectivePath_hasDerivAt (hxt t ht)
      (hregion t ht).1.2
  have hslope : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact activePerspectiveSlope_hasDerivAt (hxt t ht)
      (hregion t ht).1.2
  have hcurv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      curvature t ≤ C := by
    intro t ht
    exact hcurvature _ (hregion t ht).1 _ (hregion t ht).2
  exact unit_taylor_upper_of_second_deriv_le hC hφ hslope hcurv

theorem interpolatedStep_b_formula
    {s : AnalysisState} (q : BoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).b =
      normalizedAffinePath s.x s.b (bStepRate q) t := by
  cases q <;>
    simp only [AnalysisState.interpolatedStep, AnalysisState.b,
      normalizedAffinePath, bStepRate] <;>
    field_simp [hx, hxt] <;>
    ring

theorem interpolatedStep_deferred_formula
    (s : AnalysisState) (q : BoundaryOutcome) (t : ℝ) :
    (s.interpolatedStep q t).deferred =
      s.deferred + deferredStepRate q * t := by
  cases q <;>
    simp [AnalysisState.interpolatedStep, deferredStepRate]

theorem interpolatedStep_x_formula
    (s : AnalysisState) (q : BoundaryOutcome) (t : ℝ) :
    (s.interpolatedStep q t).x = s.x - t := by
  cases q <;> rfl

theorem activePerspectivePath_eq_bankW_interpolated
    {s : AnalysisState} (q : BoundaryOutcome) {t : ℝ}
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0)
    (hy : -1 ≤ (s.interpolatedStep q t).y) :
    activePerspectivePath s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q) t =
      bankW (s.interpolatedStep q t).x
        (s.interpolatedStep q t).substantive
        (s.interpolatedStep q t).epsilon
        (s.interpolatedStep q t).deferred := by
  have hxcoord := interpolatedStep_x_formula s q t
  have hdcoord := interpolatedStep_deferred_formula s q t
  have hycoord :=
    AnalysisState.interpolatedStep_y_formula q t hx hxt
  have hbcoord := interpolatedStep_b_formula q t hx hxt
  unfold bankW
  rw [if_neg]
  · dsimp only
    change
      activePerspectivePath s.x s.deferred s.y s.b
          (deferredStepRate q) (AnalysisState.yStepRate q)
          (bStepRate q) t =
        (s.interpolatedStep q t).x *
            (s.interpolatedStep q t).deferred +
          (s.interpolatedStep q t).x ^ 2 *
            bankG (s.interpolatedStep q t).y
              (s.interpolatedStep q t).b
    rw [bankG, if_pos hy, activePerspectivePath, hxcoord,
      hdcoord, hycoord, hbcoord]
    rfl
  · rw [hxcoord]
    exact hxt

/-- There is one constant that controls every active-to-active unit step
above the terminal layer. -/
theorem exists_active_to_active_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : AnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ q : BoundaryOutcome, -1 ≤ s.y → -1 ≤ (s.step q).y →
        bankW (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            bankW s.x s.substantive s.epsilon s.deferred ≤
          (bankRawGradient s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ := exists_activeUniformCurvature
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro s hs hx q hyStart hyEnd
  have hregion : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      normalizedAffinePath s.x s.y (AnalysisState.yStepRate q) t ∈
          Set.Icc (-1 : ℝ) 0 ∧
        normalizedAffinePath s.x s.b (bStepRate q) t ∈
          Set.Icc (0 : ℝ) (1 / RStar) := by
    intro t ht
    have hfeas :=
      AnalysisState.interpolatedStep_feasible hs hx q ht
    have hylower :
        -1 ≤ (s.interpolatedStep q t).y := by
      have hmono :=
        AnalysisState.y_interpolatedStep_antitone hs hx q
          (t := t) (u := 1) ht.2 le_rfl
      simpa using hyEnd.trans hmono
    have hyupper :
        (s.interpolatedStep q t).y ≤ 0 :=
      AnalysisState.y_nonpos hfeas
    have hb :=
      AnalysisState.active_eta_b_bounds hfeas hylower
    have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith [ht.2])
    have hyformula :=
      AnalysisState.interpolatedStep_y_formula q t hs.1.ne' hxt
    have hbformula := interpolatedStep_b_formula q t hs.1.ne' hxt
    constructor
    · unfold normalizedAffinePath
      rw [← hyformula]
      exact ⟨hylower, hyupper⟩
    · rw [← hbformula]
      exact ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hrem := activePerspective_unit_remainder
    (x := s.x) (d := s.deferred) (y := s.y) (b := s.b)
    (C := max C₀ 0) hx
    (le_max_right C₀ 0) q hregion (by
      intro Y hY B hB
      exact (hC₀ q Y hY B hB).trans (le_max_left _ _))
  have hxOne : s.x - 1 ≠ 0 := ne_of_gt (by linarith)
  have hpathOne :=
    activePerspectivePath_eq_bankW_interpolated
      (s := s) q (t := 1) hs.1.ne' hxOne (by simpa using hyEnd)
  have hpathZero :=
    activePerspectivePath_eq_bankW_interpolated
      (s := s) q (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hyStart)
  simp only [AnalysisState.interpolatedStep_one] at hpathOne
  simp only [AnalysisState.interpolatedStep_zero] at hpathZero
  rw [hpathOne, hpathZero,
    activePerspectiveSlope_zero_eq_dotDirection s q hs.1.ne'] at hrem
  unfold bankRawGradient
  rw [if_pos hyStart]
  exact hrem

theorem saturatedBank_increment_le
    (x S d Δx ΔS Δd : ℝ) :
    saturatedBank (x + Δx) (S + ΔS) (d + Δd) -
        saturatedBank x S d ≤
      (d + positivePart (x + d - RStar * S) / RStar) * Δx -
        positivePart (x + d - RStar * S) * ΔS +
        (x + positivePart (x + d - RStar * S) / RStar) * Δd +
        Δx * Δd +
        (Δx + Δd - RStar * ΔS) ^ 2 / (2 * RStar) := by
  rw [saturatedBank_increment]
  have hden : 0 < 2 * RStar :=
    mul_pos (by norm_num) (lt_trans zero_lt_one one_lt_RStar)
  have hscalar :=
    positivePart_sq_remainder
      (x + d - RStar * S) (Δx + Δd - RStar * ΔS)
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hscalar
  linarith

theorem saturatedBank_interpolated_subsegment
    (s : AnalysisState) (q : BoundaryOutcome) (t u : ℝ) :
    saturatedBank (s.interpolatedStep q u).x
          (s.interpolatedStep q u).substantive
          (s.interpolatedStep q u).deferred -
        saturatedBank (s.interpolatedStep q t).x
          (s.interpolatedStep q t).substantive
          (s.interpolatedStep q t).deferred ≤
      (saturatedBankGradient
          (s.interpolatedStep q t).x
          (s.interpolatedStep q t).substantive
          (s.interpolatedStep q t).deferred).dotDirection q *
          (u - t) +
        saturatedDirectionRemainder q * (u - t) ^ 2 := by
  have hR : RStar ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
  cases q with
  | zero =>
      simp only [AnalysisState.interpolatedStep]
      have h := saturatedBank_increment_le
        (s.x - t) s.substantive s.deferred (-(u - t)) 0 0
      convert h using 1
      all_goals try simp only [saturatedBankGradient,
        RawGradient.dotDirection, saturatedDirectionRemainder]
      all_goals ring_nf
  | epsilon =>
      simp only [AnalysisState.interpolatedStep]
      have h := saturatedBank_increment_le
        (s.x - t) s.substantive s.deferred (-(u - t)) 0 0
      convert h using 1
      all_goals try simp only [saturatedBankGradient,
        RawGradient.dotDirection, saturatedDirectionRemainder]
      all_goals ring_nf
  | immediate =>
      simp only [AnalysisState.interpolatedStep]
      have h := saturatedBank_increment_le
        (s.x - t) (s.substantive + t) s.deferred
          (-(u - t)) (u - t) 0
      convert h using 1
      all_goals try simp only [saturatedBankGradient,
        RawGradient.dotDirection, saturatedDirectionRemainder]
      all_goals ring_nf
  | deferred =>
      simp only [AnalysisState.interpolatedStep]
      have h := saturatedBank_increment_le
        (s.x - t) (s.substantive + t) (s.deferred + t)
          (-(u - t)) (u - t) (u - t)
      convert h using 1
      all_goals try simp only [saturatedBankGradient,
        RawGradient.dotDirection, saturatedDirectionRemainder]
      all_goals field_simp [hR]
      all_goals ring_nf

theorem activePerspectiveSlope_eq_interpolated_gradient
    {s : AnalysisState} (q : BoundaryOutcome) {t : ℝ}
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    activePerspectiveSlope s.x s.deferred s.y s.b
        (deferredStepRate q) (AnalysisState.yStepRate q)
        (bStepRate q) t =
      (activeRawGradient (s.interpolatedStep q t)).dotDirection q := by
  have hxcoord := interpolatedStep_x_formula s q t
  have hdcoord := interpolatedStep_deferred_formula s q t
  have hycoord :=
    AnalysisState.interpolatedStep_y_formula q t hx hxt
  have hbcoord :=
    interpolatedStep_b_formula q t hx hxt
  have hY :
      normalizedAffinePath s.x s.y (AnalysisState.yStepRate q) t =
        (s.interpolatedStep q t).y := by
    unfold normalizedAffinePath
    exact hycoord.symm
  have hB :
      normalizedAffinePath s.x s.b (bStepRate q) t =
        (s.interpolatedStep q t).b :=
    hbcoord.symm
  have hcX : (s.interpolatedStep q t).x ≠ 0 := by
    rw [hxcoord]
    exact hxt
  rw [← activePerspectiveSlope_zero_eq_dotDirection
    (s.interpolatedStep q t) q hcX]
  unfold activePerspectiveSlope
  rw [hY, hB, ← hxcoord, ← hdcoord]
  simp [normalizedAffinePath, hcX]

theorem bankW_eq_saturatedBank_of_interface
    (s : AnalysisState) (hx : 0 < s.x)
    (hy : s.y = -1) (hb : 0 ≤ s.b) :
    bankW s.x s.substantive s.epsilon s.deferred =
      saturatedBank s.x s.substantive s.deferred := by
  have hactive : -1 ≤ s.y := by linarith
  have hbank :
      bankW s.x s.substantive s.epsilon s.deferred =
        s.x * s.deferred + s.x ^ 2 * activeG s.y s.b := by
    unfold bankW
    rw [if_neg hx.ne']
    dsimp only
    change
      s.x * s.deferred +
          s.x ^ 2 * bankG s.y s.b =
        s.x * s.deferred + s.x ^ 2 * activeG s.y s.b
    unfold bankG
    rw [if_pos hactive]
  rw [hbank, hy, bankG_interface hb]
  rw [← hy, ← AnalysisState.eta_eq_y_add s]
  exact saturatedBank_eq_flat_normalized hx |>.symm

/-- Taylor's inequality and derivative variation on an arbitrary prefix
`[0,τ]`. -/
theorem segment_taylor_of_second_deriv_le
    {φ d dd : ℝ → ℝ} {C τ : ℝ}
    (hC : 0 ≤ C) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) τ, HasDerivAt φ (d t) t)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) τ, HasDerivAt d (dd t) t)
    (hdd : ∀ t ∈ Set.Icc (0 : ℝ) τ, dd t ≤ C) :
    φ τ - φ 0 ≤ d 0 * τ + C * τ ^ 2 ∧
      d τ ≤ d 0 + C * τ := by
  have hcontD : ContinuousOn d (Set.Icc (0 : ℝ) τ) := by
    intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  have hdiffD : DifferentiableOn ℝ d (interior (Set.Icc (0 : ℝ) τ)) := by
    intro u hu
    exact (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hvar (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) τ) :
      d u - d 0 ≤ C * u := by
    have h :=
      (convex_Icc (0 : ℝ) τ).image_sub_le_mul_sub_of_deriv_le
        (C := C) hcontD hdiffD (by
          intro v hv
          rw [(hd v (interior_subset hv)).deriv]
          exact hdd v (interior_subset hv))
        0 ⟨le_rfl, hτ.1⟩ u hu hu.1
    simpa using h
  have hcontΦ : ContinuousOn φ (Set.Icc (0 : ℝ) τ) := by
    intro u hu
    exact (hφ u hu).continuousAt.continuousWithinAt
  have hdiffΦ :
      DifferentiableOn ℝ φ (interior (Set.Icc (0 : ℝ) τ)) := by
    intro u hu
    exact (hφ u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hmain :=
    (convex_Icc (0 : ℝ) τ).image_sub_le_mul_sub_of_deriv_le
      (C := d 0 + C * τ) hcontΦ hdiffΦ (by
        intro u hu
        rw [(hφ u (interior_subset hu)).deriv]
        have hv := hvar u (interior_subset hu)
        have hCu : C * u ≤ C * τ :=
          mul_le_mul_of_nonneg_left (interior_subset hu).2 hC
        linarith)
      0 ⟨le_rfl, hτ.1⟩ τ ⟨hτ.1, le_rfl⟩ hτ.1
  constructor
  · nlinarith
  · have h := hvar τ ⟨hτ.1, le_rfl⟩
    linarith

/-- Active-to-flat crossings also have one uniform remainder constant. -/
theorem exists_active_to_flat_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : AnalysisState), s.Feasible → 2 ≤ s.x →
      ∀ q : BoundaryOutcome, -1 ≤ s.y → (s.step q).y < -1 →
        bankW (s.step q).x (s.step q).substantive
              (s.step q).epsilon (s.step q).deferred -
            bankW s.x s.substantive s.epsilon s.deferred ≤
          (bankRawGradient s).dotDirection q + C := by
  obtain ⟨C₀, hC₀⟩ := exists_activeUniformCurvature
  let Cactive := max C₀ 0
  let C := Cactive + saturatedUniformRemainder
  have hCactive : 0 ≤ Cactive := le_max_right _ _
  have hCflat : 0 ≤ saturatedUniformRemainder := by
    unfold saturatedUniformRemainder
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num)
        (lt_trans zero_lt_one one_lt_RStar).le)
  refine ⟨C, add_nonneg hCactive hCflat, ?_⟩
  intro s hs hx q hyStart hyEnd
  let τ := interfaceCrossingTime s q
  have hτraw :=
    interfaceCrossingTime_mem_and_y hs hx q hyStart hyEnd
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hτraw.1.1, hτraw.1.2.le⟩
  have hyτ : (s.interpolatedStep q τ).y = -1 := hτraw.2
  have hxt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
      s.x - t ≠ 0 := ne_of_gt (by linarith [ht.2, hτ.2])
  let φ := activePerspectivePath s.x s.deferred s.y s.b
    (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  let slope := activePerspectiveSlope s.x s.deferred s.y s.b
    (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  let curvature := fun t =>
    activePerspectiveCurvature
      (normalizedAffinePath s.x s.y (AnalysisState.yStepRate q) t)
      (normalizedAffinePath s.x s.b (bStepRate q) t)
      (deferredStepRate q) (AnalysisState.yStepRate q) (bStepRate q)
  have hregion (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
      normalizedAffinePath s.x s.y (AnalysisState.yStepRate q) t ∈
          Set.Icc (-1 : ℝ) 0 ∧
        normalizedAffinePath s.x s.b (bStepRate q) t ∈
          Set.Icc (0 : ℝ) (1 / RStar) := by
    have htUnit : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨ht.1, ht.2.trans hτ.2⟩
    have hfeas :=
      AnalysisState.interpolatedStep_feasible hs hx q htUnit
    have hylower :=
      active_before_interfaceCrossingTime hs hx q hyStart hyEnd ht.1 ht.2
    have hyupper :=
      AnalysisState.y_nonpos hfeas
    have hb :=
      AnalysisState.active_eta_b_bounds hfeas hylower
    have hyformula :=
      AnalysisState.interpolatedStep_y_formula q t hs.1.ne' (hxt t ht)
    have hbformula :=
      interpolatedStep_b_formula q t hs.1.ne' (hxt t ht)
    constructor
    · unfold normalizedAffinePath
      rw [← hyformula]
      exact ⟨hylower, hyupper⟩
    · rw [← hbformula]
      exact ⟨hb.2.2.2.1, hb.2.2.2.2⟩
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivAt φ (slope t) t := by
    intro t ht
    exact activePerspectivePath_hasDerivAt (hxt t ht) (hregion t ht).1.2
  have hslope : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivAt slope (curvature t) t := by
    intro t ht
    exact activePerspectiveSlope_hasDerivAt
      (hxt t ht) (hregion t ht).1.2
  have hcurv : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      curvature t ≤ Cactive := by
    intro t ht
    exact (hC₀ q _ (hregion t ht).1 _ (hregion t ht).2).trans
      (le_max_left _ _)
  have hprefix :=
    segment_taylor_of_second_deriv_le hCactive hτ hφ hslope hcurv
  have hpathτ :=
    activePerspectivePath_eq_bankW_interpolated
      (s := s) q (t := τ) hs.1.ne' (hxt τ ⟨hτ.1, le_rfl⟩)
      (by rw [hyτ])
  have hpath0 :=
    activePerspectivePath_eq_bankW_interpolated
      (s := s) q (t := 0) hs.1.ne' (by simpa using hs.1.ne')
      (by simpa using hyStart)
  simp only [AnalysisState.interpolatedStep_zero] at hpath0
  have hslope0 :
      slope 0 = (bankRawGradient s).dotDirection q := by
    dsimp [slope]
    rw [activePerspectiveSlope_zero_eq_dotDirection s q hs.1.ne']
    unfold bankRawGradient
    rw [if_pos hyStart]
  have hslopeτ :
      slope τ =
        (saturatedBankGradient
          (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).deferred).dotDirection q := by
    have hcFeas :=
      AnalysisState.interpolatedStep_feasible hs hx q hτ
    have hcX : 0 < (s.interpolatedStep q τ).x := hcFeas.1
    have hcB : 0 ≤ (s.interpolatedStep q τ).b :=
      AnalysisState.b_nonneg hcFeas
    have hactiveFlat :=
      activeRawGradient_eq_flatRawGradient_of_interface
        (s.interpolatedStep q τ) hyτ hcB
    have hsatFlat :=
      saturatedBankGradient_eq_flatRawGradient
        (s.interpolatedStep q τ) hcX
    dsimp [slope]
    rw [activePerspectiveSlope_eq_interpolated_gradient
      q hs.1.ne' (hxt τ ⟨hτ.1, le_rfl⟩)]
    rw [hsatFlat, ← hactiveFlat]
  have hprefixValue :
      bankW (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).epsilon
          (s.interpolatedStep q τ).deferred -
        bankW s.x s.substantive s.epsilon s.deferred ≤
      (bankRawGradient s).dotDirection q * τ +
        Cactive * τ ^ 2 := by
    rw [← hpathτ, ← hpath0, ← hslope0]
    exact hprefix.1
  have hslopeVar :
      (saturatedBankGradient
          (s.interpolatedStep q τ).x
          (s.interpolatedStep q τ).substantive
          (s.interpolatedStep q τ).deferred).dotDirection q ≤
        (bankRawGradient s).dotDirection q + Cactive * τ := by
    rw [← hslopeτ, ← hslope0]
    exact hprefix.2
  have hflatRaw :=
    saturatedBank_interpolated_subsegment s q τ 1
  have hxNext : 0 < (s.step q).x := by
    cases q <;> simp only [AnalysisState.step] <;> linarith
  have hbankNext :=
    bankW_eq_saturatedBank_of_flat (s.step q) hxNext hyEnd
  have hcFeas :=
    AnalysisState.interpolatedStep_feasible hs hx q hτ
  have hbankτ :=
    bankW_eq_saturatedBank_of_interface
      (s.interpolatedStep q τ) hcFeas.1 hyτ
      (AnalysisState.b_nonneg hcFeas)
  simp only [AnalysisState.interpolatedStep_one] at hflatRaw
  rw [← hbankNext, ← hbankτ] at hflatRaw
  have hDirection :=
    saturatedDirectionRemainder_le_uniform q
  have hr0 : 0 ≤ 1 - τ := by linarith [hτ.2]
  have hr2 : (1 - τ) ^ 2 ≤ 1 := by
    nlinarith [hτ.1, hτ.2, sq_nonneg (1 - τ)]
  have hflatConst :
      saturatedDirectionRemainder q * (1 - τ) ^ 2 ≤
        saturatedUniformRemainder := by
    calc
      saturatedDirectionRemainder q * (1 - τ) ^ 2 ≤
          saturatedUniformRemainder * (1 - τ) ^ 2 :=
        mul_le_mul_of_nonneg_right hDirection (sq_nonneg _)
      _ ≤ saturatedUniformRemainder :=
        mul_le_of_le_one_right hCflat hr2
  have hslopeScaled :=
    mul_le_mul_of_nonneg_right hslopeVar hr0
  have hactiveConst :
      Cactive * τ ^ 2 + Cactive * τ * (1 - τ) ≤ Cactive := by
    nlinarith [hCactive, hτ.1, hτ.2]
  have hgradSplit :
      (bankRawGradient s).dotDirection q * τ +
          (bankRawGradient s).dotDirection q * (1 - τ) =
        (bankRawGradient s).dotDirection q := by ring
  dsimp [C]
  linarith

def HasUniformBankRemainderAboveTwo (C : ℝ) : Prop :=
  ∀ (s : AnalysisState), s.Feasible → 2 ≤ s.x →
    ∀ q : BoundaryOutcome,
      bankW (s.step q).x (s.step q).substantive
            (s.step q).epsilon (s.step q).deferred -
          bankW s.x s.substantive s.epsilon s.deferred ≤
        (bankRawGradient s).dotDirection q + C

/-- Complete nonterminal result, including active-to-flat crossings. -/
theorem exists_uniformBankRemainderAboveTwo :
    ∃ C : ℝ, 0 ≤ C ∧ HasUniformBankRemainderAboveTwo C := by
  obtain ⟨Caa, hCaa, haa⟩ :=
    exists_active_to_active_uniform_remainder
  obtain ⟨Caf, hCaf, haf⟩ :=
    exists_active_to_flat_uniform_remainder
  let C := max (max Caa Caf) saturatedUniformRemainder
  have hCflat : 0 ≤ saturatedUniformRemainder := by
    unfold saturatedUniformRemainder
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num)
        (lt_trans zero_lt_one one_lt_RStar).le)
  have hC : 0 ≤ C := by
    exact le_trans hCaa
      (le_max_of_le_left (le_max_left _ _))
  refine ⟨C, hC, ?_⟩
  intro s hs hx q
  by_cases hyStart : -1 ≤ s.y
  · by_cases hyEnd : -1 ≤ (s.step q).y
    · have h := haa s hs hx q hyStart hyEnd
      have hle : Caa ≤ C :=
        le_max_of_le_left (le_max_left _ _)
      linarith
    · have h := haf s hs hx q hyStart (lt_of_not_ge hyEnd)
      have hle : Caf ≤ C :=
        le_max_of_le_left (le_max_right _ _)
      linarith
  · have hyFlat : s.y < -1 := lt_of_not_ge hyStart
    have hflat :=
      flat_uniform_remainder_above_two hs hx hyFlat q
    have hle : saturatedUniformRemainder ≤ C :=
      le_max_right _ _
    linarith

noncomputable def uniformBankRemainderAboveTwoConstant : ℝ :=
  exists_uniformBankRemainderAboveTwo.choose

theorem uniformBankRemainderAboveTwoConstant_nonneg :
    0 ≤ uniformBankRemainderAboveTwoConstant :=
  exists_uniformBankRemainderAboveTwo.choose_spec.1

theorem uniformBankRemainderAboveTwo :
    HasUniformBankRemainderAboveTwo
      uniformBankRemainderAboveTwoConstant :=
  exists_uniformBankRemainderAboveTwo.choose_spec.2

def HasUniformBankRemainderBelowTwo (C : ℝ) : Prop :=
  ∀ (s : AnalysisState), s.Feasible → s.x < 2 →
    ∀ q : BoundaryOutcome,
      bankW (s.step q).x (s.step q).substantive
            (s.step q).epsilon (s.step q).deferred -
          bankW s.x s.substantive s.epsilon s.deferred ≤
        (bankRawGradient s).dotDirection q + C

/-- Exact bridge to the original unrestricted property.  The only missing
input is the real-valued band `0 < x < 2`. -/
theorem hasUniformBankRemainder_of_aboveTwo_belowTwo
    {Cabove Cbelow : ℝ}
    (habove : HasUniformBankRemainderAboveTwo Cabove)
    (hbelow : HasUniformBankRemainderBelowTwo Cbelow) :
    HasUniformBankRemainder (max Cabove Cbelow) := by
  intro s hs q
  by_cases hx : 2 ≤ s.x
  · have h := habove s hs hx q
    have hC : Cabove ≤ max Cabove Cbelow := le_max_left _ _
    linarith
  · have h := hbelow s hs (lt_of_not_ge hx) q
    have hC : Cbelow ≤ max Cabove Cbelow := le_max_right _ _
    linarith

/-- The flat terminal step `x = 1 → 0` is also covered by the explicit
saturated estimate: the artificial saturated value at `x = 0` is
nonnegative, while the glued bank is defined to be zero there. -/
theorem flat_terminal_uniform_remainder
    {s : AnalysisState} (hs : s.Feasible) (hx : s.x = 1)
    (hy : s.y < -1) (q : BoundaryOutcome) :
    bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred -
        bankW s.x s.substantive s.epsilon s.deferred ≤
      (bankRawGradient s).dotDirection q +
        saturatedUniformRemainder := by
  have hsat :=
    saturatedBank_step_le_gradient_add_remainder s q
  have hnext0 : (s.step q).x = 0 := by
    cases q <;> simp [AnalysisState.step, hx]
  have hbankNext :
      bankW (s.step q).x (s.step q).substantive
          (s.step q).epsilon (s.step q).deferred = 0 := by
    rw [hnext0]
    exact bankW_at_terminal _ _ _
  have hsatNext :
      0 ≤ saturatedBank (s.step q).x
          (s.step q).substantive (s.step q).deferred := by
    rw [hnext0]
    unfold saturatedBank
    simp only [zero_mul, zero_add]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num)
        (lt_trans zero_lt_one one_lt_RStar).le)
  have hbankStart :=
    bankW_eq_saturatedBank_of_flat s hs.1 hy
  have hgrad :=
    bankRawGradient_eq_saturatedBankGradient_of_flat s hs.1 hy
  have hdir := saturatedDirectionRemainder_le_uniform q
  rw [hbankNext, hbankStart, hgrad]
  linarith

end

end SchedulingPaper
