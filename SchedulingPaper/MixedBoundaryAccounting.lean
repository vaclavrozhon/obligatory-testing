import SchedulingPaper.MixedEndpointReduction
import SchedulingPaper.CapEndpointAccounting

/-!
# Exact five-endpoint boundary accounting

This module evaluates a capped endpoint word in chronological test order.
The only running correction is `x` times the sum of earlier immediate
thresholds; it telescopes to zero.  Capped steps use the already-proved
state-envelope theorem.
-/

namespace SchedulingPaper

noncomputable section

open Set

theorem ParameterizedAnalysisState.y_eq_raw
    (c : ℝ) (s : ParameterizedAnalysisState) :
    s.y c =
      (s.deferred - (1 + c) *
        (s.substantive + s.epsilon)) / s.x := by
  unfold ParameterizedAnalysisState.y
    ParameterizedAnalysisState.eta
    ParameterizedAnalysisState.b
  ring

theorem ParameterizedAnalysisState.y_step_le
    {c : ℝ} (hc : 0 ≤ c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome) :
    (s.step q).y c ≤ s.y c := by
  have hx0 : 0 < s.x := hs.1
  have hx1 : 0 < s.x - 1 := by linarith
  rw [ParameterizedAnalysisState.y_eq_raw,
    ParameterizedAnalysisState.y_eq_raw]
  cases q <;>
    simp only [ParameterizedAnalysisState.step] <;>
    field_simp [hx0.ne', hx1.ne'] <;>
    nlinarith [hs.2.1, hs.2.2.1,
      hs.2.2.2.2.2.1]

theorem parameterizedAdaptiveThreshold_le_of_le
    {c left right : ℝ} (hc : 0 < c)
    (hle : left ≤ right) (hright : right ≤ 0) :
    parameterizedAdaptiveThreshold c left ≤
      parameterizedAdaptiveThreshold c right := by
  unfold parameterizedAdaptiveThreshold
  by_cases hleft : left ≤ -1
  · rw [if_pos hleft]
    by_cases hrightFlat : right ≤ -1
    · rw [if_pos hrightFlat]
    · rw [if_neg hrightFlat]
      exact parameterizedThreshold_ge_one hc
        (lt_of_not_ge hrightFlat).le hright
  · rw [if_neg hleft]
    have hleftLower : -1 ≤ left := (lt_of_not_ge hleft).le
    have hrightLower : -1 < right :=
      (lt_of_not_ge hleft).trans_le hle
    rw [if_neg (not_le.mpr hrightLower)]
    exact
      (parameterizedThreshold_monoOn_Iic hc)
        (show left ∈ Iic 0 from hle.trans hright)
        (show right ∈ Iic 0 from hright)
        hle

theorem ParameterizedAnalysisState.threshold_step_le
    {c : ℝ} (hc : 0 < c)
    {s : ParameterizedAnalysisState} (hs : s.Feasible)
    (hx : 2 ≤ s.x) (q : CappedBoundaryOutcome) :
    (s.step q).threshold c ≤ s.threshold c := by
  rw [parameterized_state_threshold_eq_adaptive,
    parameterized_state_threshold_eq_adaptive]
  exact parameterizedAdaptiveThreshold_le_of_le hc
    (s.y_step_le hc.le hs hx q)
    (s.y_nonpos hc.le hs)

theorem parameterizedAdaptiveThreshold_lt_one_add_inv
    {c y : ℝ} (hc : 0 < c) (hcOne : c ≤ 1)
    (hy : y ≤ 0) :
    parameterizedAdaptiveThreshold c y < 1 + 1 / c := by
  by_cases hflat : y ≤ -1
  · rw [show parameterizedAdaptiveThreshold c y = 1 by
      simp [parameterizedAdaptiveThreshold, hflat]]
    linarith [one_div_pos.mpr hc]
  · have hLower : -1 ≤ y := (lt_of_not_ge hflat).le
    rw [parameterizedAdaptiveThreshold, if_neg hflat]
    have hmono :=
      (parameterizedThreshold_monoOn_Iic hc)
        (show y ∈ Iic 0 from hy)
        (show (0 : ℝ) ∈ Iic 0 by simp)
        hy
    have hzero :
        parameterizedThreshold c 0 < 1 + 1 / c := by
      rw [parameterizedThreshold_eq_log_div hc (by simp)]
      have harg : 0 < (c + 2) / c := by positivity
      have hlog :=
        Real.log_lt_sub_one_of_pos harg (by
          intro heq
          field_simp [hc.ne'] at heq
          linarith)
      have hquot : (c + 2) / c - 1 = 2 / c := by
        field_simp [hc.ne']
        ring
      rw [hquot] at hlog
      have hhalf :=
        mul_lt_mul_of_pos_left hlog
          (show (0 : ℝ) < 1 / 2 by norm_num)
      have hhalfEq :
          (1 / 2 : ℝ) * (2 / c) = 1 / c := by ring
      rw [hhalfEq] at hhalf
      norm_num only [mul_zero, sub_zero]
      linarith
    exact hmono.trans_lt hzero

theorem mixed_parameterizedThreshold_lt_capBoundary
    (c : MixedRatioDomain)
    {s : ParameterizedAnalysisState} (hs : s.Feasible) :
    s.threshold c < mixedUpperCurve c - 1 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hcOne : (c : ℝ) ≤ 1 :=
    c.property.2.trans inv_goldenRatio_lt_one.le
  have hthreshold :
      s.threshold c < 1 + 1 / (c : ℝ) := by
    rw [parameterized_state_threshold_eq_adaptive]
    exact parameterizedAdaptiveThreshold_lt_one_add_inv hc hcOne
      (s.y_nonpos hc.le hs)
  have hmassInv :
      1 + (mixedMass c : ℝ) ≤ 1 / (c : ℝ) := by
    exact (le_div_iff₀ hc).2 (by
      simpa [mul_comm] using mixed_c_mul_one_add_mass_le_one c)
  have htwo :
      2 / (c : ℝ) =
        1 / (c : ℝ) + 1 / (c : ℝ) := by ring
  unfold mixedUpperCurve mixedUpperParameter
  rw [htwo]
  linarith

def mixedBoundaryValue
    (c : ℝ) (u : ℝ) (s : ParameterizedAnalysisState) :
    CappedBoundaryOutcome → ℝ
  | .zero | .epsilon => 0
  | .immediate | .deferred => s.threshold c
  | .cap => u

structure MixedEndpointJob where
  outcome : CappedBoundaryOutcome
  processing : ℝ

def mixedEndpointPairExcess
    (c u : ℝ) (left right : MixedEndpointJob) : ℝ :=
  mixedFinitePairExcessAt c u
    (eraseCapOutcome left.outcome)
    (eraseCapOutcome right.outcome)
    left.processing right.processing

def mixedEndpointSelfExcess
    (c u : ℝ) (job : MixedEndpointJob) : ℝ :=
  mixedFiniteSelfExcessAt c u job.processing

structure MixedBoundaryPrefix where
  state : ParameterizedAnalysisState
  jobs : List MixedEndpointJob
  immediateSum : ℝ
  deferredSum : ℝ
  actual : ℝ
  target : ℝ

def initialMixedBoundaryPrefix (n : ℕ) :
    MixedBoundaryPrefix where
  state := initialParameterizedAnalysisState n
  jobs := []
  immediateSum := 0
  deferredSum := 0
  actual := 0
  target := 0

def MixedBoundaryPrefix.incoming
    (history : MixedBoundaryPrefix) (c u : ℝ)
    (outcome : CappedBoundaryOutcome) (p : ℝ) : ℝ :=
  (history.jobs.map fun left =>
    mixedEndpointPairExcess c u left ⟨outcome, p⟩).sum

def MixedBoundaryPrefix.potential
    (history : MixedBoundaryPrefix) : ℝ :=
  history.state.x * history.immediateSum

def MixedBoundaryPrefix.step
    (history : MixedBoundaryPrefix)
    (c : MixedRatioDomain) (outcome : CappedBoundaryOutcome) :
    MixedBoundaryPrefix :=
  let u := mixedUpperCurve c
  let p := mixedBoundaryValue c u history.state outcome
  let job : MixedEndpointJob := ⟨outcome, p⟩
  {
    state := history.state.step outcome
    jobs := history.jobs ++ [job]
    immediateSum :=
      history.immediateSum +
        if outcome = .immediate then p else 0
    deferredSum :=
      history.deferredSum +
        if outcome = .deferred then p else 0
    actual :=
      history.actual +
        mixedEndpointSelfExcess c u job +
        history.incoming c u outcome p
    target :=
      history.target -
        (c : ℝ) * (history.jobs.length + 1) +
        mixedCappedEnvelopeReward c history.state outcome
  }

def foldMixedBoundaryPrefix
    (c : MixedRatioDomain) (n : ℕ) :
    List CappedBoundaryOutcome → MixedBoundaryPrefix :=
  List.foldl (MixedBoundaryPrefix.step · c)
    (initialMixedBoundaryPrefix n)

def MixedBoundaryPrefix.Accounted
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix) : Prop :=
  (∀ (outcome : CappedBoundaryOutcome), outcome ≠ .cap →
      ∀ p, 0 ≤ p → p ≤ history.state.threshold c →
        history.incoming c (mixedUpperCurve c) outcome p =
          -(c : ℝ) * history.jobs.length +
            history.state.deferred + history.immediateSum +
            p * (history.state.deferred -
              (1 + (c : ℝ)) * history.state.substantive)) ∧
  history.incoming c (mixedUpperCurve c)
      .cap (mixedUpperCurve c) =
    -(c : ℝ) * history.jobs.length +
      history.state.deferred -
      (c : ℝ) * (history.immediateSum + history.deferredSum) +
      history.state.capped *
        (1 + (c : ℝ) -
          (c : ℝ) * mixedUpperCurve c) ∧
  history.state.threshold c *
      (history.state.substantive - history.state.deferred) ≤
    history.immediateSum ∧
  history.state.threshold c *
      (history.state.deferred - history.state.capped) ≤
    history.deferredSum ∧
  history.state.capped ≤ history.state.deferred

theorem initialMixedBoundaryPrefix_accounted
    (c : MixedRatioDomain) (n : ℕ) :
    (initialMixedBoundaryPrefix n).Accounted c := by
  constructor
  · intro outcome _hcap p _hp0 _hp
    simp [initialMixedBoundaryPrefix,
      MixedBoundaryPrefix.incoming,
      initialParameterizedAnalysisState]
  constructor
  · simp [initialMixedBoundaryPrefix,
      MixedBoundaryPrefix.incoming,
      initialParameterizedAnalysisState]
  constructor
  · simp [initialMixedBoundaryPrefix,
      initialParameterizedAnalysisState]
  constructor
  · simp [initialMixedBoundaryPrefix,
      initialParameterizedAnalysisState]
  · simp [initialMixedBoundaryPrefix,
      initialParameterizedAnalysisState]

private theorem mixedEndpointPairExcess_zero_left
    {c u p : ℝ} (hu : 1 ≤ u) (hp : 0 ≤ p)
    (outcome : CappedBoundaryOutcome) (hcap : outcome ≠ .cap) :
    mixedEndpointPairExcess c u
        ⟨.zero, 0⟩ ⟨outcome, p⟩ = -c := by
  cases outcome <;>
    simp_all [mixedEndpointPairExcess, mixedFinitePairExcessAt,
      eraseCapOutcome, obligatoryALGPairCharge,
      plateauClippedProcessing, min_eq_left hp,
      min_eq_right (by linarith : (0 : ℝ) ≤ u - 1)] <;>
    ring

private theorem mixedEndpointPairExcess_epsilon_left
    {c u p : ℝ} (hu : 1 ≤ u) (hp : 0 ≤ p)
    (outcome : CappedBoundaryOutcome) (hcap : outcome ≠ .cap) :
    mixedEndpointPairExcess c u
        ⟨.epsilon, 0⟩ ⟨outcome, p⟩ = -c := by
  cases outcome <;>
    simp_all [mixedEndpointPairExcess, mixedFinitePairExcessAt,
      eraseCapOutcome, obligatoryALGPairCharge,
      plateauClippedProcessing, min_eq_left hp,
      min_eq_right (by linarith : (0 : ℝ) ≤ u - 1)] <;>
    ring

private theorem mixedEndpointPairExcess_immediate_left
    {c u a p : ℝ} (ha : 0 ≤ a) (hau : a ≤ u - 1)
    (hp : 0 ≤ p) (hpa : p ≤ a)
    (outcome : CappedBoundaryOutcome) (hcap : outcome ≠ .cap) :
    mixedEndpointPairExcess c u
        ⟨.immediate, a⟩ ⟨outcome, p⟩ =
      a - p - c * (1 + p) := by
  have hpu : p ≤ u - 1 := hpa.trans hau
  cases outcome <;>
    simp_all [mixedEndpointPairExcess, mixedFinitePairExcessAt,
      eraseCapOutcome, obligatoryALGPairCharge,
      plateauClippedProcessing, min_eq_left hau,
      min_eq_left hpu, min_eq_right hpa] <;>
    ring

private theorem mixedEndpointPairExcess_deferred_left
    {c u a p : ℝ} (ha : 0 ≤ a) (hau : a ≤ u - 1)
    (hp : 0 ≤ p) (hpa : p ≤ a)
    (outcome : CappedBoundaryOutcome) (hcap : outcome ≠ .cap) :
    mixedEndpointPairExcess c u
        ⟨.deferred, a⟩ ⟨outcome, p⟩ =
      1 - c * (1 + p) := by
  have hpu : p ≤ u - 1 := hpa.trans hau
  cases outcome <;>
    simp_all [mixedEndpointPairExcess, mixedFinitePairExcessAt,
      eraseCapOutcome, obligatoryALGPairCharge,
      plateauClippedProcessing, min_eq_left hau,
      min_eq_left hpu, min_eq_right hpa] <;>
    ring

private theorem mixedEndpointPairExcess_cap_left
    {c u p : ℝ} (hu : 1 ≤ u)
    (hp : 0 ≤ p) (hpu : p ≤ u - 1)
    (outcome : CappedBoundaryOutcome) (hcap : outcome ≠ .cap) :
    mixedEndpointPairExcess c u
        ⟨.cap, u⟩ ⟨outcome, p⟩ =
      1 - c * (1 + p) := by
  have huu : u - 1 ≤ u := by linarith
  have hpu' : p ≤ u := hpu.trans huu
  cases outcome <;>
    simp_all [mixedEndpointPairExcess, mixedFinitePairExcessAt,
      eraseCapOutcome, obligatoryALGPairCharge,
      plateauClippedProcessing, min_eq_right huu,
      min_eq_left hpu, min_eq_right hpu'] <;>
    ring

private theorem mixedEndpointPairExcess_zero_cap
    {c u : ℝ} (hu : 1 ≤ u) :
    mixedEndpointPairExcess c u
        ⟨.zero, 0⟩ ⟨.cap, u⟩ = -c := by
  simp [mixedEndpointPairExcess, mixedFinitePairExcessAt,
    eraseCapOutcome, obligatoryALGPairCharge,
    plateauClippedProcessing,
    min_eq_left (by linarith : (0 : ℝ) ≤ u - 1),
    min_eq_right (by linarith : u - 1 ≤ u)]

private theorem mixedEndpointPairExcess_epsilon_cap
    {c u : ℝ} (hu : 1 ≤ u) :
    mixedEndpointPairExcess c u
        ⟨.epsilon, 0⟩ ⟨.cap, u⟩ = -c := by
  simp [mixedEndpointPairExcess, mixedFinitePairExcessAt,
    eraseCapOutcome, obligatoryALGPairCharge,
    plateauClippedProcessing,
    min_eq_left (by linarith : (0 : ℝ) ≤ u - 1),
    min_eq_right (by linarith : u - 1 ≤ u)]

private theorem mixedEndpointPairExcess_immediate_cap
    {c u a : ℝ} (ha : 0 ≤ a) (hau : a ≤ u - 1) :
    mixedEndpointPairExcess c u
        ⟨.immediate, a⟩ ⟨.cap, u⟩ =
      -c * (1 + a) := by
  have hau' : a ≤ u := hau.trans (by linarith)
  simp [mixedEndpointPairExcess, mixedFinitePairExcessAt,
    eraseCapOutcome, obligatoryALGPairCharge,
    plateauClippedProcessing, min_eq_left hau,
    min_eq_left hau']
  ring

private theorem mixedEndpointPairExcess_deferred_cap
    {c u a : ℝ} (ha : 0 ≤ a) (hau : a ≤ u - 1) :
    mixedEndpointPairExcess c u
        ⟨.deferred, a⟩ ⟨.cap, u⟩ =
      1 - c * (1 + a) := by
  have hau' : a ≤ u := hau.trans (by linarith)
  simp [mixedEndpointPairExcess, mixedFinitePairExcessAt,
    eraseCapOutcome, obligatoryALGPairCharge,
    plateauClippedProcessing, min_eq_left hau,
    min_eq_left hau']
  ring

private theorem mixedEndpointPairExcess_cap_cap
    {c u : ℝ} (hu : 1 ≤ u) :
    mixedEndpointPairExcess c u
        ⟨.cap, u⟩ ⟨.cap, u⟩ =
      2 - c * u := by
  simp [mixedEndpointPairExcess, mixedFinitePairExcessAt,
    eraseCapOutcome, obligatoryALGPairCharge,
    plateauClippedProcessing,
    min_eq_right (by linarith : u - 1 ≤ u)]
  ring

theorem MixedBoundaryPrefix.Accounted.step
    (c : MixedRatioDomain)
    {history : MixedBoundaryPrefix}
    (haccounted : history.Accounted c)
    (hfeasible : history.state.Feasible)
    (hx : 2 ≤ history.state.x)
    (outcome : CappedBoundaryOutcome) :
    (history.step c outcome).Accounted c := by
  rcases haccounted with
    ⟨hordinary, hcap, himmediateSum, hdeferredSum, hKD⟩
  let u := mixedUpperCurve c
  let a := history.state.threshold (c : ℝ)
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have haOne : 1 ≤ a := by
    simpa [a] using
      ParameterizedAnalysisState.threshold_ge_one hc hfeasible
  have ha0 : 0 ≤ a := zero_le_one.trans haOne
  have hau : a ≤ u - 1 := by
    exact (mixed_parameterizedThreshold_lt_capBoundary
      c hfeasible).le
  have hu : 1 ≤ u := by linarith
  have hnextThreshold :
      (history.state.step outcome).threshold c ≤ a := by
    simpa [a] using
      ParameterizedAnalysisState.threshold_step_le
        hc hfeasible hx outcome
  constructor
  · intro right hright p hp0 hpnext
    have hpold : p ≤ a := hpnext.trans hnextThreshold
    have hold :=
      hordinary right hright p hp0 (by simpa [a] using hpold)
    have hincoming :
        (history.step c outcome).incoming c u right p =
          history.incoming c u right p +
            mixedEndpointPairExcess c u
              ⟨outcome,
                mixedBoundaryValue c u history.state outcome⟩
              ⟨right, p⟩ := by
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.incoming, u]
    rw [hincoming, hold]
    cases outcome with
    | zero =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_zero_left hu hp0 right hright]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
    | epsilon =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_epsilon_left hu hp0 right hright]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
    | immediate =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_immediate_left
          ha0 hau hp0 hpold right hright]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u, a]
        ring
    | deferred =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_deferred_left
          ha0 hau hp0 hpold right hright]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u, a]
        ring
    | cap =>
        simp only [mixedBoundaryValue]
        have hpu : p ≤ u - 1 := hpold.trans hau
        rw [mixedEndpointPairExcess_cap_left
          hu hp0 hpu right hright]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
  constructor
  · have hincoming :
        (history.step c outcome).incoming c u .cap u =
          history.incoming c u .cap u +
            mixedEndpointPairExcess c u
              ⟨outcome,
                mixedBoundaryValue c u history.state outcome⟩
              ⟨.cap, u⟩ := by
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.incoming, u]
    rw [hincoming, hcap]
    cases outcome with
    | zero =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_zero_cap hu]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
    | epsilon =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_epsilon_cap hu]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
    | immediate =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_immediate_cap ha0 hau]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u, a]
        ring
    | deferred =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_deferred_cap ha0 hau]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u, a]
        ring
    | cap =>
        simp only [mixedBoundaryValue]
        rw [mixedEndpointPairExcess_cap_cap hu]
        simp [MixedBoundaryPrefix.step,
          ParameterizedAnalysisState.step,
          mixedBoundaryValue, u]
        ring
  constructor
  · have hI :
        0 ≤ history.state.substantive -
          history.state.deferred :=
      sub_nonneg.mpr hfeasible.2.2.2.2.2.1
    have hscaled :=
      mul_le_mul_of_nonneg_right hnextThreshold hI
    cases outcome <;>
      simp [MixedBoundaryPrefix.step,
        ParameterizedAnalysisState.step,
        mixedBoundaryValue, u, a] at * <;>
      nlinarith
  constructor
  · have hd :
        0 ≤ history.state.deferred -
          history.state.capped :=
      sub_nonneg.mpr hKD
    have hscaled :=
      mul_le_mul_of_nonneg_right hnextThreshold hd
    cases outcome <;>
      simp [MixedBoundaryPrefix.step,
        ParameterizedAnalysisState.step,
        mixedBoundaryValue, u, a] at * <;>
      nlinarith
  · cases outcome <;>
      simp [MixedBoundaryPrefix.step,
        ParameterizedAnalysisState.step] at * <;>
      linarith

theorem MixedBoundaryPrefix.step_actual_add_potential_le
    (c : MixedRatioDomain)
    {history : MixedBoundaryPrefix}
    (haccounted : history.Accounted c)
    (hfeasible : history.state.Feasible)
    (outcome : CappedBoundaryOutcome) :
    (history.step c outcome).actual +
        (history.step c outcome).potential ≤
      history.actual + history.potential -
        (c : ℝ) * (history.jobs.length + 1) +
        mixedCappedEnvelopeReward c history.state outcome := by
  rcases haccounted with
    ⟨hordinary, hcap, himmediateSum, hdeferredSum, _hKD⟩
  let u := mixedUpperCurve c
  let a := history.state.threshold (c : ℝ)
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have haOne : 1 ≤ a := by
    simpa [a] using
      ParameterizedAnalysisState.threshold_ge_one hc hfeasible
  have ha0 : 0 ≤ a := zero_le_one.trans haOne
  have hau : a ≤ u - 1 := by
    exact (mixed_parameterizedThreshold_lt_capBoundary
      c hfeasible).le
  have hu : 1 ≤ u := by linarith
  cases outcome with
  | zero =>
      have hincoming :=
        hordinary .zero (by simp) 0 (by norm_num)
          (by simpa [a] using ha0)
      have hrewards :=
        parameterizedExactOrdinaryReward_le
          hc hfeasible CappedBoundaryOutcome.zero
      simp only [parameterizedExactOrdinaryReward] at hrewards
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.potential,
        ParameterizedAnalysisState.step,
        mixedEndpointSelfExcess,
        mixedFiniteSelfExcessAt,
        mixedBoundaryValue, plateauClippedProcessing,
        min_eq_left (by linarith : (0 : ℝ) ≤ u - 1),
        mixedCappedEnvelopeReward,
        parameterizedOrdinaryReward, u] at hincoming hrewards ⊢
      nlinarith
  | epsilon =>
      have hincoming :=
        hordinary .epsilon (by simp) 0 (by norm_num)
          (by simpa [a] using ha0)
      have hrewards :=
        parameterizedExactOrdinaryReward_le
          hc hfeasible CappedBoundaryOutcome.epsilon
      simp only [parameterizedExactOrdinaryReward] at hrewards
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.potential,
        ParameterizedAnalysisState.step,
        mixedEndpointSelfExcess,
        mixedFiniteSelfExcessAt,
        mixedBoundaryValue, plateauClippedProcessing,
        min_eq_left (by linarith : (0 : ℝ) ≤ u - 1),
        mixedCappedEnvelopeReward,
        parameterizedOrdinaryReward, u] at hincoming hrewards ⊢
      nlinarith
  | immediate =>
      have hincoming :=
        hordinary .immediate (by simp) a ha0
          (by simp [a])
      have hrewards :=
        parameterizedExactOrdinaryReward_le
          hc hfeasible CappedBoundaryOutcome.immediate
      simp only [parameterizedExactOrdinaryReward] at hrewards
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.potential,
        ParameterizedAnalysisState.step,
        mixedEndpointSelfExcess,
        mixedFiniteSelfExcessAt,
        mixedBoundaryValue, plateauClippedProcessing,
        min_eq_left hau,
        mixedCappedEnvelopeReward, u, a] at hincoming hrewards ⊢
      nlinarith
  | deferred =>
      have hincoming :=
        hordinary .deferred (by simp) a ha0
          (by simp [a])
      have hrewards :=
        parameterizedExactOrdinaryReward_le
          hc hfeasible CappedBoundaryOutcome.deferred
      simp only [parameterizedExactOrdinaryReward] at hrewards
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.potential,
        ParameterizedAnalysisState.step,
        mixedEndpointSelfExcess,
        mixedFiniteSelfExcessAt,
        mixedBoundaryValue, plateauClippedProcessing,
        min_eq_left hau,
        mixedCappedEnvelopeReward, u, a] at hincoming hrewards ⊢
      nlinarith
  | cap =>
      have hP :
          history.state.substantive =
            (history.state.substantive - history.state.deferred) +
              (history.state.deferred - history.state.capped) +
              history.state.capped := by ring
      have hD :
          history.state.deferred =
            (history.state.deferred - history.state.capped) +
              history.state.capped := by ring
      rw [parameterized_state_threshold_eq_adaptive] at himmediateSum hdeferredSum
      have henvelope :=
        mixed_exactCappedCharge_le_stateEnvelope c hfeasible
          hP hD himmediateSum hdeferredSum
      have henvelope' :
          history.state.deferred -
                (1 + (c : ℝ)) * history.immediateSum -
                (c : ℝ) * history.deferredSum +
              history.state.capped *
                (1 + (c : ℝ) - (c : ℝ) * mixedUpperCurve c) ≤
            mixedCappedEnvelopeReward c history.state .cap := by
        dsimp [exactCappedCharge, cappedSelfCoefficient] at henvelope
        nlinarith
      have hflat := mixed_flat_cap_bracket_nonpos c
      have hA :
          1 + (c : ℝ) - (c : ℝ) * u ≤ 0 := by
        dsimp [u]
        linarith
      have huu : u - 1 ≤ u := by linarith
      simp [MixedBoundaryPrefix.step,
        MixedBoundaryPrefix.potential,
        ParameterizedAnalysisState.step,
        mixedEndpointSelfExcess,
        mixedFiniteSelfExcessAt,
        mixedBoundaryValue, plateauClippedProcessing,
        min_eq_right huu, u] at hcap ⊢
      nlinarith [henvelope']

end

end SchedulingPaper
