import SchedulingPaper.MixedBoundaryAccounting
import SchedulingPaper.PlateauRuntimeObjective
import SchedulingPaper.UpperBoundAssembly

/-!
# Verified finite mixed runtime bridge

This module closes the operational bridge for the five-endpoint mixed
branch.  The first section turns the checked one-step allocation in
`MixedBoundaryAccounting` into a bound for every complete boundary word.
-/

namespace SchedulingPaper

noncomputable section

open Set
open Online
open LowerBound

def mixedBoundaryJobs
    (c : MixedRatioDomain) :
    ParameterizedAnalysisState → List CappedBoundaryOutcome →
      List MixedEndpointJob
  | _, [] => []
  | state, outcome :: outcomes =>
      let u := mixedUpperCurve c
      let p := mixedBoundaryValue c u state outcome
      ⟨outcome, p⟩ ::
        mixedBoundaryJobs c (state.step outcome) outcomes

@[simp] theorem mixedBoundaryJobs_length
    (c : MixedRatioDomain) (state : ParameterizedAnalysisState)
    (outcomes : List CappedBoundaryOutcome) :
    (mixedBoundaryJobs c state outcomes).length = outcomes.length := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome outcomes ih =>
      simp [mixedBoundaryJobs, ih]

theorem foldMixedBoundaryPrefix_state
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix)
    (outcomes : List CappedBoundaryOutcome) :
    (outcomes.foldl (MixedBoundaryPrefix.step · c) history).state =
      trajectoryFinal ParameterizedAnalysisState.step
        history.state outcomes := by
  induction outcomes generalizing history with
  | nil =>
      rfl
  | cons outcome outcomes ih =>
      simp only [List.foldl_cons, trajectoryFinal]
      rw [ih]
      rfl

theorem foldMixedBoundaryPrefix_jobs
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix)
    (outcomes : List CappedBoundaryOutcome) :
    (outcomes.foldl (MixedBoundaryPrefix.step · c) history).jobs =
      history.jobs ++ mixedBoundaryJobs c history.state outcomes := by
  induction outcomes generalizing history with
  | nil =>
      simp [mixedBoundaryJobs]
  | cons outcome outcomes ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [MixedBoundaryPrefix.step, mixedBoundaryJobs,
        List.append_assoc]

private theorem listPairObjective_append_singleton
    {α : Type*} (self : α → ℝ) (pair : α → α → ℝ)
    (values : List α) (value : α) :
    listPairObjective self pair (values ++ [value]) =
      listPairObjective self pair values + self value +
        (values.map (fun left => pair left value)).sum := by
  induction values with
  | nil =>
      simp [listPairObjective]
  | cons head values ih =>
      simp only [List.cons_append, listPairObjective, List.map_cons,
        List.sum_cons, List.map_append, List.sum_append]
      rw [ih]
      simp only [List.map_nil, List.sum_nil, add_zero]
      ring

theorem MixedBoundaryPrefix.step_actual_eq_listPairObjective
    (c : MixedRatioDomain) {history : MixedBoundaryPrefix}
    (hactual :
      history.actual =
        listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c))
          history.jobs)
    (outcome : CappedBoundaryOutcome) :
    (history.step c outcome).actual =
      listPairObjective
        (mixedEndpointSelfExcess c (mixedUpperCurve c))
        (mixedEndpointPairExcess c (mixedUpperCurve c))
        (history.step c outcome).jobs := by
  let job : MixedEndpointJob :=
    ⟨outcome,
      mixedBoundaryValue c (mixedUpperCurve c) history.state outcome⟩
  rw [show (history.step c outcome).jobs =
      history.jobs ++ [job] by
    simp [MixedBoundaryPrefix.step, job]]
  rw [listPairObjective_append_singleton]
  simp [MixedBoundaryPrefix.step, MixedBoundaryPrefix.incoming,
    hactual, job]

theorem foldMixedBoundaryPrefix_actual_eq_listPairObjective_from
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix)
    (outcomes : List CappedBoundaryOutcome)
    (hactual :
      history.actual =
        listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c))
          history.jobs) :
    let final :=
      outcomes.foldl (MixedBoundaryPrefix.step · c) history
    final.actual =
      listPairObjective
        (mixedEndpointSelfExcess c (mixedUpperCurve c))
        (mixedEndpointPairExcess c (mixedUpperCurve c))
        final.jobs := by
  induction outcomes generalizing history with
  | nil =>
      simpa using hactual
  | cons outcome outcomes ih =>
      simp only [List.foldl_cons]
      exact ih (history.step c outcome)
        (history.step_actual_eq_listPairObjective c hactual outcome)

theorem foldMixedBoundaryPrefix_actual_eq_listPairObjective
    (c : MixedRatioDomain) (n : ℕ)
    (outcomes : List CappedBoundaryOutcome) :
    let final := foldMixedBoundaryPrefix c n outcomes
    final.actual =
      listPairObjective
        (mixedEndpointSelfExcess c (mixedUpperCurve c))
        (mixedEndpointPairExcess c (mixedUpperCurve c))
        final.jobs := by
  apply foldMixedBoundaryPrefix_actual_eq_listPairObjective_from
  simp [initialMixedBoundaryPrefix, listPairObjective]

theorem foldMixedBoundaryPrefix_target
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix)
    (outcomes : List CappedBoundaryOutcome) :
    (outcomes.foldl (MixedBoundaryPrefix.step · c) history).target =
      history.target -
        (c : ℝ) *
          ((outcomes.length : ℝ) * history.jobs.length +
            (outcomes.length : ℝ) * (outcomes.length + 1) / 2) +
        trajectoryReward ParameterizedAnalysisState.step
          (mixedCappedEnvelopeReward c) history.state outcomes := by
  induction outcomes generalizing history with
  | nil =>
      simp [trajectoryReward]
  | cons outcome outcomes ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [MixedBoundaryPrefix.step, trajectoryReward]
      ring

private theorem foldMixedBoundaryPrefix_bound_from
    (c : MixedRatioDomain) (history : MixedBoundaryPrefix)
    (outcomes : List CappedBoundaryOutcome)
    (hx : history.state.x = outcomes.length)
    (haccounted : history.Accounted c)
    (hgood :
      TrajectoryGood ParameterizedAnalysisState.step
        ParameterizedAnalysisState.Reachable history.state outcomes)
    (hbound :
      history.actual + history.potential ≤ history.target) :
    let final :=
      outcomes.foldl (MixedBoundaryPrefix.step · c) history
    final.actual + final.potential ≤ final.target := by
  induction outcomes generalizing history with
  | nil =>
      simpa using hbound
  | cons outcome outcomes ih =>
      rcases hgood with ⟨hreachable, hgoodTail⟩
      have hlocal :=
        history.step_actual_add_potential_le
          c haccounted hreachable.1 outcome
      have hnextBound :
          (history.step c outcome).actual +
              (history.step c outcome).potential ≤
            (history.step c outcome).target := by
        calc
          (history.step c outcome).actual +
                (history.step c outcome).potential ≤
              history.actual + history.potential -
                (c : ℝ) * (history.jobs.length + 1) +
                  mixedCappedEnvelopeReward c history.state outcome :=
            hlocal
          _ ≤ history.target -
                (c : ℝ) * (history.jobs.length + 1) +
                  mixedCappedEnvelopeReward c history.state outcome := by
            linarith
          _ = (history.step c outcome).target := by
            rfl
      cases outcomes with
      | nil =>
          simpa using hnextBound
      | cons next outcomes =>
          have hxTwo : 2 ≤ history.state.x := by
            rw [hx]
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            have hlen : (0 : ℝ) ≤ outcomes.length := by positivity
            linarith
          have hnextAccounted :=
            haccounted.step c hreachable.1 hxTwo outcome
          have hxNext :
              (history.step c outcome).state.x =
                (next :: outcomes).length := by
            cases outcome <;>
              simp [MixedBoundaryPrefix.step,
                ParameterizedAnalysisState.step] at hx ⊢ <;>
              linarith
          simp only [List.foldl_cons]
          exact ih (history.step c outcome) hxNext
            hnextAccounted hgoodTail hnextBound

theorem foldMixedBoundaryPrefix_actual_le_target
    (c : MixedRatioDomain) (outcomes : List CappedBoundaryOutcome) :
    let final := foldMixedBoundaryPrefix c outcomes.length outcomes
    final.actual ≤ final.target := by
  have hinvariant :
      let final := foldMixedBoundaryPrefix c outcomes.length outcomes
      final.actual + final.potential ≤ final.target := by
    change
      let final :=
        outcomes.foldl (MixedBoundaryPrefix.step · c)
          (initialMixedBoundaryPrefix outcomes.length)
      final.actual + final.potential ≤ final.target
    apply foldMixedBoundaryPrefix_bound_from c
      (initialMixedBoundaryPrefix outcomes.length) outcomes
    · simp [initialMixedBoundaryPrefix,
        initialParameterizedAnalysisState]
    · exact initialMixedBoundaryPrefix_accounted c outcomes.length
    · exact initialParameterizedAnalysisState_trajectory_good outcomes
    · simp [initialMixedBoundaryPrefix,
        MixedBoundaryPrefix.potential]
  have hstate :
      (foldMixedBoundaryPrefix c outcomes.length outcomes).state.x = 0 := by
    unfold foldMixedBoundaryPrefix
    rw [foldMixedBoundaryPrefix_state]
    exact trajectoryFinal_initialParameterizedAnalysisState_x outcomes
  dsimp only at hinvariant
  simpa [MixedBoundaryPrefix.potential, hstate] using hinvariant

theorem foldMixedBoundaryPrefix_actual_le_rewards
    (c : MixedRatioDomain) (outcomes : List CappedBoundaryOutcome) :
    (foldMixedBoundaryPrefix c outcomes.length outcomes).actual ≤
      -(c : ℝ) * outcomes.length * (outcomes.length + 1) / 2 +
        trajectoryReward ParameterizedAnalysisState.step
          (mixedCappedEnvelopeReward c)
          (initialParameterizedAnalysisState outcomes.length)
          outcomes := by
  have hbound :=
    foldMixedBoundaryPrefix_actual_le_target c outcomes
  have htarget :=
    foldMixedBoundaryPrefix_target c
      (initialMixedBoundaryPrefix outcomes.length) outcomes
  have htarget' :
      (foldMixedBoundaryPrefix c outcomes.length outcomes).target =
        -(c : ℝ) * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState outcomes.length)
            outcomes := by
    unfold foldMixedBoundaryPrefix
    convert htarget using 1 <;>
      simp [initialMixedBoundaryPrefix] <;>
      ring
  exact hbound.trans_eq htarget'

def mixedEndpointJobsOutcome
    (jobs : List MixedEndpointJob) :
    Fin jobs.length → BoundaryOutcome :=
  fun i => eraseCapOutcome (jobs.get i).outcome

def mixedEndpointJobsProcessing
    (jobs : List MixedEndpointJob) :
    Fin jobs.length → ℝ :=
  fun i => (jobs.get i).processing

theorem mixedFiniteFixedWordExcess_jobs_eq_listPairObjective
    (c u : ℝ) (jobs : List MixedEndpointJob) :
    mixedFiniteFixedWordExcess c u
        (mixedEndpointJobsOutcome jobs)
        (mixedEndpointJobsProcessing jobs) =
      listPairObjective
        (mixedEndpointSelfExcess c u)
        (mixedEndpointPairExcess c u) jobs := by
  unfold mixedFiniteFixedWordExcess
  have h :=
    finSelfPairSum_eq_listPairObjective
      (mixedEndpointSelfExcess c u)
      (mixedEndpointPairExcess c u)
      (fun i : Fin jobs.length => jobs.get i)
  simpa [mixedEndpointJobsOutcome, mixedEndpointJobsProcessing,
    mixedEndpointSelfExcess, mixedEndpointPairExcess] using h

theorem mixedBoundary_word_excess_le_rewards
    (c : MixedRatioDomain) (outcomes : List CappedBoundaryOutcome) :
    let jobs :=
      mixedBoundaryJobs c
        (initialParameterizedAnalysisState outcomes.length) outcomes
    mixedFiniteFixedWordExcess c (mixedUpperCurve c)
        (mixedEndpointJobsOutcome jobs)
        (mixedEndpointJobsProcessing jobs) ≤
      -(c : ℝ) * outcomes.length * (outcomes.length + 1) / 2 +
        trajectoryReward ParameterizedAnalysisState.step
          (mixedCappedEnvelopeReward c)
          (initialParameterizedAnalysisState outcomes.length)
          outcomes := by
  let final := foldMixedBoundaryPrefix c outcomes.length outcomes
  let jobs :=
    mixedBoundaryJobs c
      (initialParameterizedAnalysisState outcomes.length) outcomes
  have hjobs : final.jobs = jobs := by
    dsimp [final, jobs, foldMixedBoundaryPrefix]
    simpa using
      foldMixedBoundaryPrefix_jobs c
        (initialMixedBoundaryPrefix outcomes.length) outcomes
  have hactual :=
    foldMixedBoundaryPrefix_actual_eq_listPairObjective
      c outcomes.length outcomes
  have hbound :=
    foldMixedBoundaryPrefix_actual_le_rewards c outcomes
  dsimp only at hactual hbound ⊢
  calc
    mixedFiniteFixedWordExcess (c : ℝ) (mixedUpperCurve c)
          (mixedEndpointJobsOutcome jobs)
          (mixedEndpointJobsProcessing jobs) =
        listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c)) jobs :=
      mixedFiniteFixedWordExcess_jobs_eq_listPairObjective _ _ _
    _ = listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c))
          final.jobs := by rw [hjobs]
    _ = final.actual := hactual.symm
    _ ≤ _ := hbound

/-! ## Exact objective of the executable parameterized strategy -/

theorem mixedFiniteFixedWordExcess_eq_pairObjectives
    {n : ℕ} (c u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    mixedFiniteFixedWordExcess c u outcome processing =
      obligatoryALGPairObjective
          (obligatoryJobsOfFunctions outcome processing) -
        (1 + c) *
          obligatoryOPTPairObjective
            (obligatoryJobsOfFunctions outcome
              (fun i => plateauClippedProcessing u (processing i))) := by
  rw [Online.obligatoryALGPairObjective_jobsOfFunctions_eq_finSums,
    obligatoryOPTPairObjective_jobsOfFunctions_eq_finSums]
  unfold mixedFiniteFixedWordExcess mixedFiniteSelfExcessAt
    mixedFinitePairExcessAt
  simp only [Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add, mul_one]
  ring

theorem obligatoryOPTPairObjective_clipped_eq_vectorOfflineCost_finite
    (u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processingTime : Online.Label n → ℝ) :
    obligatoryOPTPairObjective
        (obligatoryJobsOfFunctions outcome
          (fun i => plateauClippedProcessing u (processingTime i))) =
      vectorOfflineCost (.finite u) processingTime := by
  rw [obligatoryOPTPairObjective_jobsOfFunctions]
  unfold vectorOfflineCost vectorEffectiveLengths
  congr 2
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    simp [plateauClippedProcessing, effectiveLength]
    calc
      1 + min (processingTime ⟨index, by simpa using hright⟩)
            (u - 1) =
          min (1 + processingTime ⟨index, by simpa using hright⟩)
            (1 + (u - 1)) :=
        (min_add_add_left 1
          (processingTime ⟨index, by simpa using hright⟩)
          (u - 1)).symm
      _ = min u
            (1 + processingTime ⟨index, by simpa using hright⟩) := by
        rw [min_comm]
        congr 2 <;> ring

theorem parameterizedRuntime_mixedExcess_eq
    (n : ℕ) (c u : ℝ) (hc : 0 < c)
    (processingTime : Online.Label n → ℝ) :
    let result :=
      Online.run (.finite u) (Online.fixedOracle processingTime)
        (Online.parameterizedAdaptiveThresholdStrategy n c)
        (2 * n + 1)
    Online.runCompletionCost (.finite u) processingTime result -
        (1 + c) * vectorOfflineCost (.finite u) processingTime =
      mixedFiniteFixedWordExcess c u
        (Online.parameterizedRuntimeOutcomeByLabel c processingTime)
        processingTime := by
  dsimp only
  rw [Online.run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_ALG_generic
    n hc (.finite u) processingTime]
  rw [mixedFiniteFixedWordExcess_eq_pairObjectives]
  rw [obligatoryOPTPairObjective_clipped_eq_vectorOfflineCost_finite]

/-! ## Moving the saturated interval to the literal cap endpoint -/

def raiseMixedCap (u p : ℝ) : ℝ :=
  if u - 1 ≤ p then u else p

theorem mixedFiniteSelfExcessAt_le_raiseMixedCap
    {c u p : ℝ} (hpUpper : p ≤ u) :
    mixedFiniteSelfExcessAt c u p ≤
      mixedFiniteSelfExcessAt c u (raiseMixedCap u p) := by
  by_cases hcap : u - 1 ≤ p
  · have huu : u - 1 ≤ u := by linarith
    simp [raiseMixedCap, hcap, mixedFiniteSelfExcessAt,
      plateauClippedProcessing, min_eq_right hcap,
      min_eq_right huu]
    linarith
  · simp [raiseMixedCap, hcap]

theorem mixedFinitePairExcessAt_le_raiseMixedCap
    {c u p q : ℝ} {left right : BoundaryOutcome}
    (hpUpper : p ≤ u) (hqUpper : q ≤ u)
    (hleftCap : u - 1 ≤ p → left = .deferred)
    (hrightCap : u - 1 ≤ q → right = .deferred) :
    mixedFinitePairExcessAt c u left right p q ≤
      mixedFinitePairExcessAt c u left right
        (raiseMixedCap u p) (raiseMixedCap u q) := by
  by_cases hpCap : u - 1 ≤ p
  · have hleft := hleftCap hpCap
    subst left
    by_cases hqCap : u - 1 ≤ q
    · have hright := hrightCap hqCap
      subst right
      have hminUpper : min p q ≤ u :=
        (min_le_left p q).trans hpUpper
      have huu : u - 1 ≤ u := by linarith
      simp [raiseMixedCap, hpCap, hqCap,
        mixedFinitePairExcessAt, obligatoryALGPairCharge,
        plateauClippedProcessing, min_eq_right hpCap,
        min_eq_right hqCap, min_eq_right huu]
      exact Or.inl hpUpper
    · have hqBelow : q ≤ u - 1 := (lt_of_not_ge hqCap).le
      have hqp : q ≤ p := hqBelow.trans hpCap
      have hqu : q ≤ u := hqBelow.trans (by linarith)
      simp [raiseMixedCap, hpCap, hqCap,
        mixedFinitePairExcessAt, obligatoryALGPairCharge,
        plateauClippedProcessing, min_eq_right hpCap,
        min_eq_left hqBelow, min_eq_right hqp,
        min_eq_right hqu]
  · have hpBelow : p ≤ u - 1 := (lt_of_not_ge hpCap).le
    by_cases hqCap : u - 1 ≤ q
    · have hright := hrightCap hqCap
      subst right
      have hpq : p ≤ q := hpBelow.trans hqCap
      have hpu : p ≤ u := hpBelow.trans (by linarith)
      cases left <;>
        simp [raiseMixedCap, hpCap, hqCap,
          mixedFinitePairExcessAt, obligatoryALGPairCharge,
          plateauClippedProcessing, min_eq_left hpBelow,
          min_eq_right hqCap, min_eq_left hpq,
          min_eq_left hpu]
    · simp [raiseMixedCap, hpCap, hqCap]

def raiseMixedCaps {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i => raiseMixedCap u (processing i)

theorem mixedFiniteFixedWordExcess_le_raiseMixedCaps
    {n : ℕ} {c u : ℝ}
    {outcome : Fin n → BoundaryOutcome}
    {processing : Fin n → ℝ}
    (hprocessing : ∀ i, processing i ≤ u)
    (hcap :
      ∀ i, u - 1 ≤ processing i → outcome i = .deferred) :
    mixedFiniteFixedWordExcess c u outcome processing ≤
      mixedFiniteFixedWordExcess c u outcome
        (raiseMixedCaps u processing) := by
  classical
  unfold mixedFiniteFixedWordExcess
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _hi
    exact mixedFiniteSelfExcessAt_le_raiseMixedCap
      (hprocessing i)
  · apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact mixedFinitePairExcessAt_le_raiseMixedCap
      (hprocessing i) (hprocessing j) (hcap i) (hcap j)

def expandMixedCapMask {n : ℕ}
    (u : ℝ) (cap : Fin n → Bool) (processing : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => if cap i then u else processing i

def mixedCapMaskCorrection {n : ℕ}
    (cap : Fin n → Bool) : ℝ :=
  (∑ i, if cap i then (1 : ℝ) else 0) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      if cap i then (if cap j then (1 : ℝ) else 0) else 0

private theorem mixedFiniteSelfExcessAt_expandCapMask
    {c u : ℝ} {cap : Bool} {p : ℝ}
    (hu : 1 ≤ u)
    (hcap :
      cap = true → p = u - 1)
    (hbelow :
      cap = false → p ≤ u - 1) :
    mixedFiniteSelfExcessAt c u (if cap then u else p) =
      mixedNormalizedSelfExcessAt c p +
        (if cap then (1 : ℝ) else 0) := by
  cases h : cap with
  | false =>
      have hp := hbelow h
      simp [h, mixedFiniteSelfExcessAt,
        mixedNormalizedSelfExcessAt, plateauClippedProcessing,
        min_eq_left hp]
  | true =>
      have hp := hcap h
      have huu : u - 1 ≤ u := by linarith
      simp [h, hp, mixedFiniteSelfExcessAt,
        mixedNormalizedSelfExcessAt, plateauClippedProcessing,
        min_eq_right huu]
      ring

private theorem mixedFinitePairExcessAt_expandCapMask
    {c u p q : ℝ} {left right : BoundaryOutcome}
    {capLeft capRight : Bool}
    (hu : 1 ≤ u)
    (hleft :
      capLeft = true → left = .deferred ∧ p = u - 1)
    (hright :
      capRight = true → right = .deferred ∧ q = u - 1)
    (hpBelow : capLeft = false → p ≤ u - 1)
    (hqBelow : capRight = false → q ≤ u - 1) :
    mixedFinitePairExcessAt c u left right
        (if capLeft then u else p)
        (if capRight then u else q) =
      mixedNormalizedPairExcessAt c left right p q +
        (if capLeft then
          (if capRight then (1 : ℝ) else 0) else 0) := by
  have huu : u - 1 ≤ u := by linarith
  cases hl : capLeft with
  | false =>
      have hp := hpBelow hl
      cases hr : capRight with
      | false =>
          have hq := hqBelow hr
          simp [hl, hr, mixedFinitePairExcessAt,
            mixedNormalizedPairExcessAt, plateauClippedProcessing,
            min_eq_left hp, min_eq_left hq]
      | true =>
          rcases hright hr with ⟨hrightOutcome, hq⟩
          subst right
          rw [hq]
          have hpu : p ≤ u := hp.trans huu
          cases left <;>
            simp [hl, hr, mixedFinitePairExcessAt,
              mixedNormalizedPairExcessAt, obligatoryALGPairCharge,
              plateauClippedProcessing, min_eq_left hp,
              min_eq_right huu, min_eq_left hpu]
  | true =>
      rcases hleft hl with ⟨hleftOutcome, hp⟩
      subst left
      rw [hp]
      cases hr : capRight with
      | false =>
          have hq := hqBelow hr
          have hqu : q ≤ u := hq.trans huu
          cases right <;>
            simp [hl, hr, mixedFinitePairExcessAt,
              mixedNormalizedPairExcessAt, obligatoryALGPairCharge,
              plateauClippedProcessing, min_eq_right huu,
              min_eq_left hq, min_eq_right hqu] <;>
            try exact hq
      | true =>
          rcases hright hr with ⟨hrightOutcome, hq⟩
          subst right
          rw [hq]
          simp [hl, hr, mixedFinitePairExcessAt,
            mixedNormalizedPairExcessAt, obligatoryALGPairCharge,
            plateauClippedProcessing, min_eq_right huu]
          ring

theorem mixedFiniteFixedWordExcess_expandCapMask
    {n : ℕ} {c u : ℝ}
    {outcome : Fin n → BoundaryOutcome}
    {cap : Fin n → Bool} {processing : Fin n → ℝ}
    (hu : 1 ≤ u)
    (hcap :
      ∀ i, cap i = true →
        outcome i = .deferred ∧ processing i = u - 1)
    (hbelow :
      ∀ i, cap i = false → processing i ≤ u - 1) :
    mixedFiniteFixedWordExcess c u outcome
        (expandMixedCapMask u cap processing) =
      mixedNormalizedFixedWordExcess c outcome processing +
        mixedCapMaskCorrection cap := by
  classical
  unfold mixedFiniteFixedWordExcess
    mixedNormalizedFixedWordExcess mixedCapMaskCorrection
    expandMixedCapMask
  simp_rw [mixedFiniteSelfExcessAt_expandCapMask
    hu (fun h => (hcap _ h).2) (hbelow _)]
  simp_rw [mixedFinitePairExcessAt_expandCapMask
    hu (hcap _) (hcap _) (hbelow _) (hbelow _)]
  simp only [Finset.sum_add_distrib]
  ring

def mixedOriginalCapMask {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) : Fin n → Bool :=
  fun i => decide (u - 1 ≤ processing i)

def mixedReducedAfterCapRaise {n : ℕ}
    (u : ℝ) (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if mixedOriginalCapMask u processing i
      then u - 1 else processing i

def mixedReducedLower {n : ℕ}
    (u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (threshold processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if mixedOriginalCapMask u processing i then u - 1
    else
      match outcome i with
      | .zero | .epsilon | .immediate => 0
      | .deferred => threshold i

def mixedReducedUpper {n : ℕ}
    (u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (threshold processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if mixedOriginalCapMask u processing i then u - 1
    else
      match outcome i with
      | .zero | .epsilon => 0
      | .immediate => threshold i
      | .deferred => u - 1

theorem exists_mixedFinite_endpoint_ge
    {n : ℕ} {c u : ℝ}
    (outcome : Fin n → BoundaryOutcome)
    (threshold processing : Fin n → ℝ)
    (hc : 0 ≤ c) (hu : 1 < u)
    (hthreshold0 : ∀ i, 0 ≤ threshold i)
    (hthresholdCap : ∀ i, threshold i < u - 1)
    (hprocessingUpper : ∀ i, processing i ≤ u)
    (hzero :
      ∀ i, outcome i = .zero ∨ outcome i = .epsilon →
        processing i = 0)
    (himmediate :
      ∀ i, outcome i = .immediate →
        0 ≤ processing i ∧ processing i ≤ threshold i)
    (hdeferred :
      ∀ i, outcome i = .deferred →
        threshold i ≤ processing i)
    (hcap :
      ∀ i, u - 1 ≤ processing i → outcome i = .deferred) :
    ∃ endpoint : Fin n → ℝ,
      mixedFiniteFixedWordExcess c u outcome processing ≤
        mixedFiniteFixedWordExcess c u outcome endpoint ∧
      ∀ i,
        match outcome i with
        | .zero | .epsilon => endpoint i = 0
        | .immediate =>
            endpoint i = 0 ∨ endpoint i = threshold i
        | .deferred =>
            endpoint i = threshold i ∨ endpoint i = u := by
  classical
  let cap := mixedOriginalCapMask u processing
  let reduced := mixedReducedAfterCapRaise u processing
  let lower := mixedReducedLower u outcome threshold processing
  let upper := mixedReducedUpper u outcome threshold processing
  have hcapTrue :
      ∀ i, cap i = true ↔ u - 1 ≤ processing i := by
    intro i
    simp [cap, mixedOriginalCapMask]
  have hcapFalse :
      ∀ i, cap i = false ↔ ¬ u - 1 ≤ processing i := by
    intro i
    simp [cap, mixedOriginalCapMask]
  have horder : ∀ i, lower i ≤ upper i := by
    intro i
    by_cases hi : cap i = true
    · simp [lower, upper, mixedReducedLower, mixedReducedUpper,
        cap, hi]
    · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
      cases hout : outcome i <;>
        simp [lower, upper, mixedReducedLower, mixedReducedUpper,
          cap, hiFalse, hout, hthreshold0 i,
          (hthresholdCap i).le]
  have hreducedBox : reduced ∈ coordinateBox lower upper := by
    intro i
    by_cases hi : cap i = true
    · simp [reduced, lower, upper, mixedReducedAfterCapRaise,
        mixedReducedLower, mixedReducedUpper, cap, hi]
    · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
      have hpBelow : processing i ≤ u - 1 :=
        (lt_of_not_ge ((hcapFalse i).mp hiFalse)).le
      cases hout : outcome i with
      | zero =>
          have hp := hzero i (Or.inl hout)
          simp [reduced, lower, upper, mixedReducedAfterCapRaise,
            mixedReducedLower, mixedReducedUpper, cap, hiFalse,
            hout, hp]
      | epsilon =>
          have hp := hzero i (Or.inr hout)
          simp [reduced, lower, upper, mixedReducedAfterCapRaise,
            mixedReducedLower, mixedReducedUpper, cap, hiFalse,
            hout, hp]
      | immediate =>
          have hp := himmediate i hout
          simpa [reduced, lower, upper, mixedReducedAfterCapRaise,
            mixedReducedLower, mixedReducedUpper, cap, hiFalse,
            hout] using hp
      | deferred =>
          exact ⟨by
            simpa [reduced, lower, mixedReducedAfterCapRaise,
              mixedReducedLower, cap, hiFalse, hout] using
                hdeferred i hout,
            by
              simpa [reduced, upper, mixedReducedAfterCapRaise,
                mixedReducedUpper, cap, hiFalse, hout] using hpBelow⟩
  obtain ⟨vertex, hvbox, hvvertex, hvge⟩ :=
    exists_mixedNormalizedFixedWord_endpoint_ge
      hc outcome lower upper reduced horder hreducedBox
  have hcapReduced :
      ∀ i, cap i = true →
        outcome i = .deferred ∧ reduced i = u - 1 := by
    intro i hi
    have hpCap := (hcapTrue i).mp hi
    exact ⟨hcap i hpCap, by
      simp [reduced, mixedReducedAfterCapRaise, cap, hi]⟩
  have hbelowReduced :
      ∀ i, cap i = false → reduced i ≤ u - 1 := by
    intro i hi
    have hpBelow :=
      (lt_of_not_ge ((hcapFalse i).mp hi)).le
    simpa [reduced, mixedReducedAfterCapRaise, cap, hi] using hpBelow
  have hcapVertex :
      ∀ i, cap i = true →
        outcome i = .deferred ∧ vertex i = u - 1 := by
    intro i hi
    have hpCap := (hcapTrue i).mp hi
    have hv : vertex i = u - 1 := by
      simpa [lower, upper, mixedReducedLower, mixedReducedUpper,
        cap, hi] using hvbox i
    exact ⟨hcap i hpCap, hv⟩
  have hbelowVertex :
      ∀ i, cap i = false → vertex i ≤ u - 1 := by
    intro i hi
    have hv := (hvbox i).2
    cases hout : outcome i <;>
      simp [upper, mixedReducedUpper, cap, hi, hout] at hv ⊢ <;>
      linarith [hthresholdCap i]
  have hexpandReduced :
      expandMixedCapMask u cap reduced =
        raiseMixedCaps u processing := by
    funext i
    by_cases hi : cap i = true
    · have hpCap := (hcapTrue i).mp hi
      simp [expandMixedCapMask, raiseMixedCaps, raiseMixedCap,
        reduced, mixedReducedAfterCapRaise, cap, hi, hpCap]
    · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
      have hpNot := (hcapFalse i).mp hiFalse
      simp [expandMixedCapMask, raiseMixedCaps, raiseMixedCap,
        reduced, mixedReducedAfterCapRaise, cap, hiFalse, hpNot]
  have hnormalizedReduced :=
    mixedFiniteFixedWordExcess_expandCapMask
      (c := c) (u := u) (outcome := outcome)
      (cap := cap) (processing := reduced)
      hu.le hcapReduced hbelowReduced
  have hnormalizedVertex :=
    mixedFiniteFixedWordExcess_expandCapMask
      (c := c) (u := u) (outcome := outcome)
      (cap := cap) (processing := vertex)
      hu.le hcapVertex hbelowVertex
  let expandedVertex := expandMixedCapMask u cap vertex
  have hexpandedUpper : ∀ i, expandedVertex i ≤ u := by
    intro i
    by_cases hi : cap i = true
    · simp [expandedVertex, expandMixedCapMask, hi]
    · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
      have hv := hbelowVertex i hiFalse
      simp [expandedVertex, expandMixedCapMask, hiFalse]
      linarith
  have hexpandedCap :
      ∀ i, u - 1 ≤ expandedVertex i →
        outcome i = .deferred := by
    intro i hiValue
    by_cases hi : cap i = true
    · exact (hcapVertex i hi).1
    · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
      have hv := hvvertex i
      cases hout : outcome i with
      | zero =>
          have hvzero : vertex i = 0 := by
            rcases hv with hv | hv <;>
              simpa [lower, upper, mixedReducedLower,
                mixedReducedUpper, cap, hiFalse, hout] using hv
          simp [expandedVertex, expandMixedCapMask, hiFalse,
            hvzero] at hiValue
          linarith
      | epsilon =>
          have hvzero : vertex i = 0 := by
            rcases hv with hv | hv <;>
              simpa [lower, upper, mixedReducedLower,
                mixedReducedUpper, cap, hiFalse, hout] using hv
          simp [expandedVertex, expandMixedCapMask, hiFalse,
            hvzero] at hiValue
          linarith
      | immediate =>
          rcases hv with hv | hv
          · have hvzero : vertex i = 0 := by
              simpa [lower, mixedReducedLower, cap, hiFalse,
                hout] using hv
            simp [expandedVertex, expandMixedCapMask, hiFalse,
              hvzero] at hiValue
            linarith
          · have hvthreshold : vertex i = threshold i := by
              simpa [upper, mixedReducedUpper, cap, hiFalse,
                hout] using hv
            simp [expandedVertex, expandMixedCapMask, hiFalse,
              hvthreshold] at hiValue
            linarith [hthresholdCap i]
      | deferred =>
          rfl
  let endpoint := raiseMixedCaps u expandedVertex
  have htoEndpoint :
      mixedFiniteFixedWordExcess c u outcome processing ≤
        mixedFiniteFixedWordExcess c u outcome endpoint := by
    calc
      mixedFiniteFixedWordExcess c u outcome processing ≤
          mixedFiniteFixedWordExcess c u outcome
            (raiseMixedCaps u processing) :=
        mixedFiniteFixedWordExcess_le_raiseMixedCaps
          hprocessingUpper hcap
      _ = mixedFiniteFixedWordExcess c u outcome
            (expandMixedCapMask u cap reduced) := by
        rw [hexpandReduced]
      _ = mixedNormalizedFixedWordExcess c outcome reduced +
            mixedCapMaskCorrection cap := hnormalizedReduced
      _ ≤ mixedNormalizedFixedWordExcess c outcome vertex +
            mixedCapMaskCorrection cap := by linarith
      _ = mixedFiniteFixedWordExcess c u outcome
            expandedVertex := by
        simpa [expandedVertex] using hnormalizedVertex.symm
      _ ≤ mixedFiniteFixedWordExcess c u outcome endpoint :=
        mixedFiniteFixedWordExcess_le_raiseMixedCaps
          hexpandedUpper hexpandedCap
  refine ⟨endpoint, htoEndpoint, ?_⟩
  intro i
  by_cases hi : cap i = true
  · have hdefer := (hcapVertex i hi).1
    rw [hdefer]
    right
    simp [endpoint, raiseMixedCaps, expandedVertex,
      expandMixedCapMask, raiseMixedCap, hi]
  · have hiFalse : cap i = false := Bool.eq_false_of_not_eq_true hi
    have hv := hvvertex i
    cases hout : outcome i with
    | zero =>
        have hvzero : vertex i = 0 := by
          rcases hv with hv | hv <;>
            simpa [lower, upper, mixedReducedLower,
              mixedReducedUpper, cap, hiFalse, hout] using hv
        have hzeroBelow : ¬ u - 1 ≤ (0 : ℝ) := by linarith
        simp [endpoint, raiseMixedCaps, expandedVertex,
          expandMixedCapMask, raiseMixedCap, hiFalse, hvzero,
          hzeroBelow]
    | epsilon =>
        have hvzero : vertex i = 0 := by
          rcases hv with hv | hv <;>
            simpa [lower, upper, mixedReducedLower,
              mixedReducedUpper, cap, hiFalse, hout] using hv
        have hzeroBelow : ¬ u - 1 ≤ (0 : ℝ) := by linarith
        simp [endpoint, raiseMixedCaps, expandedVertex,
          expandMixedCapMask, raiseMixedCap, hiFalse, hvzero,
          hzeroBelow]
    | immediate =>
        rcases hv with hv | hv
        · left
          have hvzero : vertex i = 0 := by
            simpa [lower, mixedReducedLower, cap, hiFalse,
              hout] using hv
          have hzeroBelow : ¬ u - 1 ≤ (0 : ℝ) := by linarith
          simp [endpoint, raiseMixedCaps, expandedVertex,
            expandMixedCapMask, raiseMixedCap, hiFalse, hvzero,
            hzeroBelow]
        · right
          have hvthreshold : vertex i = threshold i := by
            simpa [upper, mixedReducedUpper, cap, hiFalse,
              hout] using hv
          have hthresholdBelow :
              ¬ u - 1 ≤ threshold i :=
            not_le.mpr (hthresholdCap i)
          simp [endpoint, raiseMixedCaps, expandedVertex,
            expandMixedCapMask, raiseMixedCap, hiFalse,
            hvthreshold, hthresholdBelow]
    | deferred =>
        rcases hv with hv | hv
        · left
          have hvthreshold : vertex i = threshold i := by
            simpa [lower, mixedReducedLower, cap, hiFalse,
              hout] using hv
          have hthresholdBelow :
              ¬ u - 1 ≤ threshold i :=
            not_le.mpr (hthresholdCap i)
          simp [endpoint, raiseMixedCaps, expandedVertex,
            expandMixedCapMask, raiseMixedCap, hiFalse,
            hvthreshold, hthresholdBelow]
        · right
          have hvupper : vertex i = u - 1 := by
            simpa [upper, mixedReducedUpper, cap, hiFalse,
              hout] using hv
          simp [endpoint, raiseMixedCaps, expandedVertex,
            expandMixedCapMask, raiseMixedCap, hiFalse, hvupper]

/-! ## The executable counter path as a symbolic mixed word -/

def classifyParameterizedRuntime
    (threshold processing : ℝ) : BoundaryOutcome :=
  if processing = 0 then .zero
  else if processing ≤ threshold then .immediate else .deferred

structure ParameterizedMixedRuntimeJob (n : ℕ) where
  label : Online.Label n
  processing : ℝ
  threshold : ℝ
  outcome : BoundaryOutcome

def buildParameterizedMixedRuntimeJobs
    (n : ℕ) (c : ℝ) :
    Online.ParameterizedThresholdCounters →
      List (Online.Label n × ℝ) →
        List (ParameterizedMixedRuntimeJob n)
  | _, [] => []
  | counters, result :: results =>
      let threshold := counters.threshold n c
      let outcome :=
        classifyParameterizedRuntime threshold result.2
      {
        label := result.1
        processing := result.2
        threshold := threshold
        outcome := outcome
      } ::
        buildParameterizedMixedRuntimeJobs n c
          (counters.observe n c result.2) results

@[simp] theorem buildParameterizedMixedRuntimeJobs_length
    (n : ℕ) (c : ℝ)
    (counters : Online.ParameterizedThresholdCounters)
    (results : List (Online.Label n × ℝ)) :
    (buildParameterizedMixedRuntimeJobs n c counters results).length =
      results.length := by
  induction results generalizing counters with
  | nil => rfl
  | cons result results ih =>
      simp [buildParameterizedMixedRuntimeJobs, ih]

def parameterizedMixedRuntimeJobs
    (c : ℝ) (processingTime : Online.Label n → ℝ) :
    List (ParameterizedMixedRuntimeJob n) :=
  buildParameterizedMixedRuntimeJobs n c
    Online.ParameterizedThresholdCounters.initial
    (Online.fixedTestResults processingTime)

@[simp] theorem parameterizedMixedRuntimeJobs_length
    (c : ℝ) (processingTime : Online.Label n → ℝ) :
    (parameterizedMixedRuntimeJobs c processingTime).length = n := by
  simp [parameterizedMixedRuntimeJobs,
    Online.fixedTestResults]

def ParameterizedAnalysisState.MatchesCounters
    (n : ℕ) (state : ParameterizedAnalysisState)
    (counters : Online.ParameterizedThresholdCounters) : Prop :=
  state.x = counters.remaining n ∧
    state.substantive + state.epsilon = counters.positive ∧
    state.deferred = counters.deferred

theorem ParameterizedAnalysisState.matchesCounters_initial
    (n : ℕ) :
    (initialParameterizedAnalysisState n).MatchesCounters n
      Online.ParameterizedThresholdCounters.initial := by
  simp [ParameterizedAnalysisState.MatchesCounters,
    initialParameterizedAnalysisState,
    Online.ParameterizedThresholdCounters.initial,
    Online.ParameterizedThresholdCounters.remaining]

theorem ParameterizedAnalysisState.MatchesCounters.y_eq
    {n : ℕ} {c : ℝ} {state : ParameterizedAnalysisState}
    {counters : Online.ParameterizedThresholdCounters}
    (hmatch : state.MatchesCounters n counters) :
    state.y c = counters.y n c := by
  rcases hmatch with ⟨hx, hpositive, hdeferred⟩
  rw [ParameterizedAnalysisState.y_eq_raw]
  unfold Online.ParameterizedThresholdCounters.y
  rw [hx, hpositive, hdeferred]

theorem ParameterizedAnalysisState.MatchesCounters.threshold_eq
    {n : ℕ} {c : ℝ} {state : ParameterizedAnalysisState}
    {counters : Online.ParameterizedThresholdCounters}
    (hmatch : state.MatchesCounters n counters) :
    state.threshold c = counters.threshold n c := by
  rw [parameterized_state_threshold_eq_adaptive]
  unfold Online.ParameterizedThresholdCounters.threshold
  rw [hmatch.y_eq]

theorem parameterizedCounters_threshold_nonneg_of_invariant
    {n : ℕ} {c : ℝ} (hc : 0 < c)
    {counters : Online.ParameterizedThresholdCounters}
    (htested : counters.tested < n)
    (hpositive : 0 ≤ counters.positive)
    (hbalance : counters.deferred ≤ counters.positive) :
    0 ≤ counters.threshold n c := by
  have hremaining :
      0 < (counters.remaining n : ℝ) := by
    simp [Online.ParameterizedThresholdCounters.remaining, htested]
  have hscale :
      counters.positive ≤ (1 + c) * counters.positive := by
    nlinarith [mul_nonneg hc.le hpositive]
  have hy : counters.y n c ≤ 0 := by
    unfold Online.ParameterizedThresholdCounters.y
    exact div_nonpos_of_nonpos_of_nonneg
      (by linarith) hremaining.le
  exact zero_le_one.trans
    (Online.parameterizedAdaptiveThreshold_ge_one_of_nonpos hc hy)

theorem ParameterizedAnalysisState.MatchesCounters.step_classify
    {n : ℕ} {c : ℝ}
    {state : ParameterizedAnalysisState}
    {counters : Online.ParameterizedThresholdCounters}
    (hmatch : state.MatchesCounters n counters)
    {p : ℝ} (hp : 0 ≤ p)
    (htested : counters.tested < n)
    (hthreshold : 0 ≤ counters.threshold n c) :
    let outcome :=
      classifyParameterizedRuntime (state.threshold c) p
    (state.step (liftOrdinaryOutcome outcome)).MatchesCounters n
      (counters.observe n c p) := by
  have hthresholdEq :=
    hmatch.threshold_eq (c := c)
  have hremaining :
      (↑(n - counters.tested) : ℝ) - 1 =
        ↑(n - (counters.tested + 1)) := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega :
      1 ≤ n - counters.tested)]
    congr 1
  rcases hmatch with ⟨hx, hpositive, hdeferred⟩
  dsimp only
  unfold classifyParameterizedRuntime
  by_cases hpzero : p = 0
  · subst p
    simp [liftOrdinaryOutcome,
      ParameterizedAnalysisState.step,
      Online.ParameterizedThresholdCounters.observe,
      ParameterizedAnalysisState.MatchesCounters,
      hthresholdEq, hthreshold, hx, hpositive, hdeferred,
      Online.ParameterizedThresholdCounters.remaining]
    exact hremaining
  · have hppos : 0 < p :=
      lt_of_le_of_ne hp (Ne.symm hpzero)
    by_cases himmediate : p ≤ state.threshold c
    · have hnotDeferred :
          ¬ counters.threshold n c < p := by
        rw [← hthresholdEq]
        exact not_lt_of_ge himmediate
      simp [hpzero, himmediate, hppos, hnotDeferred,
        liftOrdinaryOutcome, ParameterizedAnalysisState.step,
        Online.ParameterizedThresholdCounters.observe,
        ParameterizedAnalysisState.MatchesCounters,
        hx, hpositive, hdeferred,
        Online.ParameterizedThresholdCounters.remaining]
      exact ⟨hremaining, by linarith⟩
    · have hdeferState : state.threshold c < p :=
        lt_of_not_ge himmediate
      have hdeferCounters : counters.threshold n c < p := by
        rwa [← hthresholdEq]
      simp [hpzero, himmediate, hppos, hdeferState,
        hdeferCounters, liftOrdinaryOutcome,
        ParameterizedAnalysisState.step,
        Online.ParameterizedThresholdCounters.observe,
        ParameterizedAnalysisState.MatchesCounters,
        hx, hpositive, hdeferred,
        Online.ParameterizedThresholdCounters.remaining]
      exact ⟨hremaining, by linarith⟩

def parameterizedMixedSymbolicThresholds
    (c : ℝ) :
    ParameterizedAnalysisState → List BoundaryOutcome → List ℝ
  | _, [] => []
  | state, outcome :: outcomes =>
      state.threshold c ::
        parameterizedMixedSymbolicThresholds c
          (state.step (liftOrdinaryOutcome outcome)) outcomes

@[simp] theorem parameterizedMixedSymbolicThresholds_length
    (c : ℝ) (state : ParameterizedAnalysisState)
    (outcomes : List BoundaryOutcome) :
    (parameterizedMixedSymbolicThresholds c state outcomes).length =
      outcomes.length := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome outcomes ih =>
      simp [parameterizedMixedSymbolicThresholds, ih]

theorem buildParameterizedMixedRuntimeJobs_thresholds
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (results : List (Online.Label n × ℝ))
    (state : ParameterizedAnalysisState)
    (counters : Online.ParameterizedThresholdCounters)
    (hmatch : state.MatchesCounters n counters)
    (htotal : counters.tested + results.length = n)
    (hpositive : 0 ≤ counters.positive)
    (hbalance : counters.deferred ≤ counters.positive)
    (hnonneg : ∀ result ∈ results, 0 ≤ result.2) :
    (buildParameterizedMixedRuntimeJobs n c counters results).map
        ParameterizedMixedRuntimeJob.threshold =
      parameterizedMixedSymbolicThresholds c state
        ((buildParameterizedMixedRuntimeJobs n c counters results).map
          ParameterizedMixedRuntimeJob.outcome) := by
  induction results generalizing state counters with
  | nil =>
      rfl
  | cons result results ih =>
      have htested : counters.tested < n := by
        simp only [List.length_cons] at htotal
        omega
      have hp : 0 ≤ result.2 :=
        hnonneg result (by simp)
      have hthreshold :
          0 ≤ counters.threshold n c :=
        parameterizedCounters_threshold_nonneg_of_invariant
          hc htested hpositive hbalance
      have hthresholdEq :=
        hmatch.threshold_eq (c := c)
      let outcome :=
        classifyParameterizedRuntime
          (state.threshold c) result.2
      have hnextMatch :
          (state.step (liftOrdinaryOutcome outcome)).MatchesCounters n
            (counters.observe n c result.2) := by
        exact hmatch.step_classify hp htested hthreshold
      have hnextPositive :
          0 ≤ (counters.observe n c result.2).positive := by
        unfold Online.ParameterizedThresholdCounters.observe
        dsimp only
        split_ifs <;> linarith
      have hnextBalance :
          (counters.observe n c result.2).deferred ≤
            (counters.observe n c result.2).positive :=
        counters.observe_deferred_le_positive hc htested
          hpositive hbalance
      have hnextTotal :
          (counters.observe n c result.2).tested +
              results.length = n := by
        simp only [Online.ParameterizedThresholdCounters.observe,
          List.length_cons] at htotal ⊢
        omega
      have htailNonneg :
          ∀ tailResult ∈ results, 0 ≤ tailResult.2 := by
        intro tailResult hmem
        exact hnonneg tailResult (by simp [hmem])
      have htail :=
        ih
          (state.step (liftOrdinaryOutcome outcome))
          (counters.observe n c result.2)
          hnextMatch hnextTotal hnextPositive hnextBalance
          htailNonneg
      have houtcome :
          classifyParameterizedRuntime
              (counters.threshold n c) result.2 =
            outcome := by
        simp [outcome, hthresholdEq]
      simp only [buildParameterizedMixedRuntimeJobs,
        List.map_cons, parameterizedMixedSymbolicThresholds]
      rw [hthresholdEq, houtcome]
      exact congrArg (List.cons (counters.threshold n c)) htail

theorem parameterizedMixedRuntimeJobs_thresholds
    {c : ℝ} (hc : 0 < c)
    (processingTime : Online.Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    (parameterizedMixedRuntimeJobs c processingTime).map
        ParameterizedMixedRuntimeJob.threshold =
      parameterizedMixedSymbolicThresholds c
        (initialParameterizedAnalysisState n)
        ((parameterizedMixedRuntimeJobs c processingTime).map
          ParameterizedMixedRuntimeJob.outcome) := by
  apply buildParameterizedMixedRuntimeJobs_thresholds n hc
  · exact ParameterizedAnalysisState.matchesCounters_initial n
  · simp [Online.ParameterizedThresholdCounters.initial,
      Online.fixedTestResults]
  · simp [Online.ParameterizedThresholdCounters.initial]
  · simp [Online.ParameterizedThresholdCounters.initial]
  · intro result hmem
    simp only [Online.fixedTestResults, List.mem_ofFn] at hmem
    rcases hmem with ⟨job, rfl⟩
    exact hnonneg job

theorem buildParameterizedMixedRuntimeJobs_get
    (n : ℕ) (c : ℝ)
    (counters : Online.ParameterizedThresholdCounters)
    (results : List (Online.Label n × ℝ))
    (index : ℕ) (hindex : index < results.length) :
    let result := results.get ⟨index, hindex⟩
    let job :=
      (buildParameterizedMixedRuntimeJobs n c counters results).get
        ⟨index, by simpa using hindex⟩
    let prefixCounters :=
      (results.take index).foldl
        (fun state result => state.observe n c result.2) counters
    job.label = result.1 ∧
      job.processing = result.2 ∧
      job.threshold = prefixCounters.threshold n c ∧
      job.outcome =
        classifyParameterizedRuntime
          (prefixCounters.threshold n c) result.2 := by
  induction results generalizing counters index with
  | nil =>
      simp at hindex
  | cons result results ih =>
      cases index with
      | zero =>
          simp [buildParameterizedMixedRuntimeJobs]
      | succ index =>
          have htail : index < results.length := by
            simpa using hindex
          simpa [buildParameterizedMixedRuntimeJobs] using
            ih (counters.observe n c result.2) index htail

theorem parameterizedMixedRuntimeJob_data
    (c : ℝ) (processingTime : Online.Label n → ℝ)
    (index : Fin (parameterizedMixedRuntimeJobs c processingTime).length) :
    let runtimeIndex : Online.Label n :=
      ⟨index.val, by simpa using index.isLt⟩
    let job :=
      (parameterizedMixedRuntimeJobs c processingTime).get index
    job.label = runtimeIndex ∧
      job.processing = processingTime runtimeIndex ∧
      job.threshold =
        Online.parameterizedRuntimeThreshold c processingTime runtimeIndex ∧
      job.outcome =
        Online.parameterizedRuntimeOutcomeByLabel
          c processingTime runtimeIndex := by
  have hindex :
      index.val < (Online.fixedTestResults processingTime).length := by
    simpa [parameterizedMixedRuntimeJobs] using index.isLt
  have hget :=
    buildParameterizedMixedRuntimeJobs_get n c
      Online.ParameterizedThresholdCounters.initial
      (Online.fixedTestResults processingTime) index.val hindex
  simpa [parameterizedMixedRuntimeJobs,
    Online.fixedTestResults,
    Online.parameterizedRuntimeThreshold,
    Online.parameterizedCountersFromResults,
    Online.parameterizedRuntimeOutcomeByLabel,
    classifyParameterizedRuntime] using hget

/-! ## Turning endpoint coordinates into the literal five-letter word -/

def ParameterizedAnalysisState.SymbolicallyEquivalent
    (left right : ParameterizedAnalysisState) : Prop :=
  left.x = right.x ∧
    left.deferred = right.deferred ∧
    left.substantive + left.epsilon =
      right.substantive + right.epsilon

theorem ParameterizedAnalysisState.SymbolicallyEquivalent.refl
    (state : ParameterizedAnalysisState) :
    state.SymbolicallyEquivalent state :=
  ⟨rfl, rfl, rfl⟩

theorem ParameterizedAnalysisState.SymbolicallyEquivalent.y_eq
    {c : ℝ} {left right : ParameterizedAnalysisState}
    (heq : left.SymbolicallyEquivalent right) :
    left.y c = right.y c := by
  rcases heq with ⟨hx, hdeferred, hpositive⟩
  rw [ParameterizedAnalysisState.y_eq_raw,
    ParameterizedAnalysisState.y_eq_raw,
    hx, hdeferred, hpositive]

theorem ParameterizedAnalysisState.SymbolicallyEquivalent.threshold_eq
    {c : ℝ} {left right : ParameterizedAnalysisState}
    (heq : left.SymbolicallyEquivalent right) :
    left.threshold c = right.threshold c := by
  rw [parameterized_state_threshold_eq_adaptive,
    parameterized_state_threshold_eq_adaptive, heq.y_eq]

def mixedEndpointOutcome
    (symbol : BoundaryOutcome) (value u : ℝ) :
    CappedBoundaryOutcome :=
  match symbol with
  | .zero => .zero
  | .epsilon => .epsilon
  | .immediate =>
      if value = 0 then .epsilon else .immediate
  | .deferred =>
      if value = u then .cap else .deferred

theorem ParameterizedAnalysisState.SymbolicallyEquivalent.step_endpoint
    {left right : ParameterizedAnalysisState}
    (heq : left.SymbolicallyEquivalent right)
    (symbol : BoundaryOutcome) (value u : ℝ) :
    (left.step (liftOrdinaryOutcome symbol)).SymbolicallyEquivalent
      (right.step (mixedEndpointOutcome symbol value u)) := by
  rcases heq with ⟨hx, hdeferred, hpositive⟩
  cases symbol with
  | zero =>
      simp [liftOrdinaryOutcome, mixedEndpointOutcome,
        ParameterizedAnalysisState.SymbolicallyEquivalent,
        ParameterizedAnalysisState.step, hx, hdeferred]
      exact hpositive
  | epsilon =>
      simp [liftOrdinaryOutcome, mixedEndpointOutcome,
        ParameterizedAnalysisState.SymbolicallyEquivalent,
        ParameterizedAnalysisState.step, hx, hdeferred]
      linarith
  | immediate =>
      by_cases hzero : value = 0
      · simp [liftOrdinaryOutcome, mixedEndpointOutcome, hzero,
          ParameterizedAnalysisState.SymbolicallyEquivalent,
          ParameterizedAnalysisState.step, hx, hdeferred]
        linarith
      · simp [liftOrdinaryOutcome, mixedEndpointOutcome, hzero,
          ParameterizedAnalysisState.SymbolicallyEquivalent,
          ParameterizedAnalysisState.step, hx, hdeferred]
        linarith
  | deferred =>
      by_cases hcap : value = u
      · simp [liftOrdinaryOutcome, mixedEndpointOutcome, hcap,
          ParameterizedAnalysisState.SymbolicallyEquivalent,
          ParameterizedAnalysisState.step, hx, hdeferred]
        linarith
      · simp [liftOrdinaryOutcome, mixedEndpointOutcome, hcap,
          ParameterizedAnalysisState.SymbolicallyEquivalent,
          ParameterizedAnalysisState.step, hx, hdeferred]
        linarith

def MixedEndpointChoices
    (c u : ℝ) :
    ParameterizedAnalysisState → List BoundaryOutcome → List ℝ → Prop
  | _, [], values => values = []
  | _, _ :: _, [] => False
  | state, symbol :: symbols, value :: values =>
      (match symbol with
      | .zero | .epsilon => value = 0
      | .immediate =>
          value = 0 ∨ value = state.threshold c
      | .deferred =>
          value = state.threshold c ∨ value = u) ∧
      MixedEndpointChoices c u
        (state.step (liftOrdinaryOutcome symbol)) symbols values

theorem MixedEndpointChoices.length_eq
    {c u : ℝ} {state : ParameterizedAnalysisState}
    {symbols : List BoundaryOutcome} {values : List ℝ}
    (hchoices : MixedEndpointChoices c u state symbols values) :
    values.length = symbols.length := by
  induction symbols generalizing state values with
  | nil =>
      simp [MixedEndpointChoices] at hchoices
      simp [hchoices]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [MixedEndpointChoices] at hchoices
      | cons value values =>
          simp only [MixedEndpointChoices] at hchoices
          simp [ih hchoices.2]

def mixedEndpointWord
    (u : ℝ) :
    List BoundaryOutcome → List ℝ → List CappedBoundaryOutcome
  | [], _ => []
  | _, [] => []
  | symbol :: symbols, value :: values =>
      mixedEndpointOutcome symbol value u ::
        mixedEndpointWord u symbols values

@[simp] theorem mixedEndpointWord_length
    {c u : ℝ} {state : ParameterizedAnalysisState}
    {symbols : List BoundaryOutcome} {values : List ℝ}
    (hchoices : MixedEndpointChoices c u state symbols values) :
    (mixedEndpointWord u symbols values).length = symbols.length := by
  induction symbols generalizing state values with
  | nil =>
      simp [mixedEndpointWord]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [MixedEndpointChoices] at hchoices
      | cons value values =>
          simp only [MixedEndpointChoices] at hchoices
          simp [mixedEndpointWord, ih hchoices.2]

def mixedSelectedEndpointJobs
    (u : ℝ) :
    List BoundaryOutcome → List ℝ → List MixedEndpointJob
  | [], _ => []
  | _, [] => []
  | symbol :: symbols, value :: values =>
      ⟨mixedEndpointOutcome symbol value u, value⟩ ::
        mixedSelectedEndpointJobs u symbols values

theorem mixedBoundaryJobs_endpointWord
    {c : MixedRatioDomain}
    {symbolicState boundaryState : ParameterizedAnalysisState}
    (heq : symbolicState.SymbolicallyEquivalent boundaryState)
    {symbols : List BoundaryOutcome} {values : List ℝ}
    (hchoices :
      MixedEndpointChoices c (mixedUpperCurve c)
        symbolicState symbols values) :
    mixedBoundaryJobs c boundaryState
        (mixedEndpointWord (mixedUpperCurve c) symbols values) =
      mixedSelectedEndpointJobs
        (mixedUpperCurve c) symbols values := by
  induction symbols generalizing symbolicState boundaryState values with
  | nil =>
      simp [mixedEndpointWord, mixedSelectedEndpointJobs,
        mixedBoundaryJobs]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [MixedEndpointChoices] at hchoices
      | cons value values =>
          rcases hchoices with ⟨hhead, htail⟩
          have hthreshold :=
            heq.threshold_eq (c := (c : ℝ))
          have hnext :=
            heq.step_endpoint symbol value (mixedUpperCurve c)
          cases symbol with
          | zero =>
              change value = 0 at hhead
              subst value
              simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                mixedEndpointOutcome, mixedBoundaryJobs,
                mixedBoundaryValue] using
                congrArg
                  (fun tail =>
                    MixedEndpointJob.mk .zero 0 :: tail)
                  (ih hnext htail)
          | epsilon =>
              change value = 0 at hhead
              subst value
              simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                mixedEndpointOutcome, mixedBoundaryJobs,
                mixedBoundaryValue] using
                congrArg
                  (fun tail =>
                    MixedEndpointJob.mk .epsilon 0 :: tail)
                  (ih hnext htail)
          | immediate =>
              by_cases hzero : value = 0
              · subst value
                simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                  mixedEndpointOutcome, mixedBoundaryJobs,
                  mixedBoundaryValue] using
                    congrArg
                      (fun tail =>
                        MixedEndpointJob.mk .epsilon 0 :: tail)
                      (ih hnext htail)
              · have hvalue :
                    value = symbolicState.threshold c := by
                  rcases hhead with h | h
                  · exact (hzero h).elim
                  · exact h
                have hvalueBoundary :
                    value = boundaryState.threshold c := by
                  rw [hvalue, hthreshold]
                have hboundaryNonzero :
                    boundaryState.threshold c ≠ 0 := by
                  intro hzeroBoundary
                  apply hzero
                  rw [hvalueBoundary, hzeroBoundary]
                simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                  mixedEndpointOutcome, mixedBoundaryJobs,
                  mixedBoundaryValue, hzero, hvalueBoundary,
                  hboundaryNonzero] using
                    congrArg
                      (fun tail =>
                        MixedEndpointJob.mk .immediate value :: tail)
                      (ih hnext htail)
          | deferred =>
              by_cases hcap : value = mixedUpperCurve c
              · simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                  mixedEndpointOutcome, mixedBoundaryJobs,
                  mixedBoundaryValue, hcap] using
                    congrArg
                      (fun tail =>
                        MixedEndpointJob.mk .cap value :: tail)
                      (ih hnext htail)
              · have hvalue :
                    value = symbolicState.threshold c := by
                  rcases hhead with h | h
                  · exact h
                  · exact (hcap h).elim
                have hvalueBoundary :
                    value = boundaryState.threshold c := by
                  rw [hvalue, hthreshold]
                have hboundaryNotCap :
                    boundaryState.threshold c ≠ mixedUpperCurve c := by
                  intro hthresholdCap
                  apply hcap
                  rw [hvalueBoundary, hthresholdCap]
                simpa [mixedEndpointWord, mixedSelectedEndpointJobs,
                  mixedEndpointOutcome, mixedBoundaryJobs,
                  mixedBoundaryValue, hcap, hvalueBoundary,
                  hboundaryNotCap] using
                    congrArg
                      (fun tail =>
                        MixedEndpointJob.mk .deferred value :: tail)
                      (ih hnext htail)

private theorem mixedEndpointChoices_of_get
    {c u : ℝ} {state : ParameterizedAnalysisState}
    {symbols : List BoundaryOutcome} {values : List ℝ}
    (hlength : values.length = symbols.length)
    (hget :
      ∀ i : Fin symbols.length,
        match symbols.get i with
        | .zero | .epsilon =>
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ = 0
        | .immediate =>
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ = 0 ∨
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ =
              (parameterizedMixedSymbolicThresholds c state symbols).get
                ⟨i, by simpa using i.isLt⟩
        | .deferred =>
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ =
                (parameterizedMixedSymbolicThresholds c state symbols).get
                  ⟨i, by simpa using i.isLt⟩ ∨
              values.get ⟨i, by simpa [hlength] using i.isLt⟩ = u) :
    MixedEndpointChoices c u state symbols values := by
  induction symbols generalizing state values with
  | nil =>
      have hnil : values = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using hlength)
      simpa [hnil, MixedEndpointChoices]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp at hlength
      | cons value values =>
          have htailLength : values.length = symbols.length := by
            simpa using hlength
          have hheadRaw :=
            hget (0 : Fin (symbol :: symbols).length)
          have htailGet :
              ∀ i : Fin symbols.length,
                match symbols.get i with
                | .zero | .epsilon =>
                    values.get
                      ⟨i, by simpa [htailLength] using i.isLt⟩ = 0
                | .immediate =>
                    values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ = 0 ∨
                    values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ =
                      (parameterizedMixedSymbolicThresholds c
                        (state.step (liftOrdinaryOutcome symbol))
                        symbols).get ⟨i, by simpa using i.isLt⟩
                | .deferred =>
                    values.get
                          ⟨i, by simpa [htailLength] using i.isLt⟩ =
                        (parameterizedMixedSymbolicThresholds c
                          (state.step (liftOrdinaryOutcome symbol))
                          symbols).get ⟨i, by simpa using i.isLt⟩ ∨
                      values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ = u := by
            intro i
            have htailRaw :=
              hget (Fin.succ i : Fin (symbol :: symbols).length)
            simpa [parameterizedMixedSymbolicThresholds] using htailRaw
          have htail := ih htailLength htailGet
          cases symbol with
          | zero =>
              have hhead : value = 0 := by
                simpa [parameterizedMixedSymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩
          | epsilon =>
              have hhead : value = 0 := by
                simpa [parameterizedMixedSymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩
          | immediate =>
              have hhead :
                  value = 0 ∨ value = state.threshold c := by
                simpa [parameterizedMixedSymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩
          | deferred =>
              have hhead :
                  value = state.threshold c ∨ value = u := by
                simpa [parameterizedMixedSymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩

private theorem mixedSelectedEndpointJobs_ofFn
    (u : ℝ) :
    ∀ (symbols : List BoundaryOutcome)
      (processing : Fin symbols.length → ℝ),
      mixedSelectedEndpointJobs u symbols (List.ofFn processing) =
        List.ofFn (fun i : Fin symbols.length =>
          MixedEndpointJob.mk
            (mixedEndpointOutcome (symbols.get i) (processing i) u)
            (processing i)) := by
  intro symbols
  induction symbols with
  | nil =>
      intro processing
      simp [mixedSelectedEndpointJobs]
  | cons symbol symbols ih =>
      intro processing
      let tailProcessing : Fin symbols.length → ℝ :=
        fun i => processing i.succ
      have htail := ih tailProcessing
      rw [show List.ofFn processing =
          processing 0 :: List.ofFn tailProcessing by
        simpa [tailProcessing] using List.ofFn_succ processing]
      rw [show
          List.ofFn (fun i : Fin (symbol :: symbols).length =>
            MixedEndpointJob.mk
              (mixedEndpointOutcome
                ((symbol :: symbols).get i) (processing i) u)
              (processing i)) =
            MixedEndpointJob.mk
              (mixedEndpointOutcome symbol (processing 0) u)
              (processing 0) ::
              List.ofFn (fun i : Fin symbols.length =>
                MixedEndpointJob.mk
                  (mixedEndpointOutcome
                    (symbols.get i) (tailProcessing i) u)
                  (tailProcessing i)) by
        simpa [tailProcessing] using
          List.ofFn_succ (fun i : Fin (symbol :: symbols).length =>
            MixedEndpointJob.mk
              (mixedEndpointOutcome
                ((symbol :: symbols).get i) (processing i) u)
              (processing i))]
      simp [mixedSelectedEndpointJobs, htail]

theorem mixedEndpointOutcome_pairCharge
    (left right : BoundaryOutcome) (p q u : ℝ) :
    obligatoryALGPairCharge
        ⟨eraseCapOutcome (mixedEndpointOutcome left p u), p⟩
        ⟨eraseCapOutcome (mixedEndpointOutcome right q u), q⟩ =
      obligatoryALGPairCharge ⟨left, p⟩ ⟨right, q⟩ := by
  cases left <;> cases right <;>
    simp [mixedEndpointOutcome, eraseCapOutcome,
      obligatoryALGPairCharge] <;>
    split_ifs <;> rfl

theorem mixedFinitePairExcessAt_endpointOutcome
    (c u : ℝ) (left right : BoundaryOutcome) (p q : ℝ) :
    mixedFinitePairExcessAt c u
        (eraseCapOutcome (mixedEndpointOutcome left p u))
        (eraseCapOutcome (mixedEndpointOutcome right q u)) p q =
      mixedFinitePairExcessAt c u left right p q := by
  unfold mixedFinitePairExcessAt
  rw [mixedEndpointOutcome_pairCharge]

theorem mixedFiniteFixedWordExcess_endpointOutcome
    {n : ℕ} (c u : ℝ)
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    mixedFiniteFixedWordExcess c u outcome processing =
      mixedFiniteFixedWordExcess c u
        (fun i =>
          eraseCapOutcome
            (mixedEndpointOutcome
              (outcome i) (processing i) u))
        processing := by
  classical
  unfold mixedFiniteFixedWordExcess
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  exact
    (mixedFinitePairExcessAt_endpointOutcome
      c u (outcome i) (outcome j)
      (processing i) (processing j)).symm

theorem mixedEndpointChoices_excess_le_rewards
    (c : MixedRatioDomain)
    (symbols : List BoundaryOutcome)
    (processing : Fin symbols.length → ℝ)
    (hchoices :
      MixedEndpointChoices c (mixedUpperCurve c)
        (initialParameterizedAnalysisState symbols.length)
        symbols (List.ofFn processing)) :
    let word :=
      mixedEndpointWord (mixedUpperCurve c)
        symbols (List.ofFn processing)
    mixedFiniteFixedWordExcess c (mixedUpperCurve c)
        (fun i => symbols.get i) processing ≤
      -(c : ℝ) * word.length * (word.length + 1) / 2 +
        trajectoryReward ParameterizedAnalysisState.step
          (mixedCappedEnvelopeReward c)
          (initialParameterizedAnalysisState word.length) word := by
  let values := List.ofFn processing
  let word :=
    mixedEndpointWord (mixedUpperCurve c) symbols values
  let selected :=
    mixedSelectedEndpointJobs (mixedUpperCurve c) symbols values
  have hwordLength : word.length = symbols.length := by
    exact mixedEndpointWord_length hchoices
  have hjobs :
      mixedBoundaryJobs c
          (initialParameterizedAnalysisState word.length) word =
        selected := by
    rw [hwordLength]
    exact mixedBoundaryJobs_endpointWord
      (ParameterizedAnalysisState.SymbolicallyEquivalent.refl _)
      hchoices
  have hselected :
      selected =
        List.ofFn (fun i : Fin symbols.length =>
          MixedEndpointJob.mk
            (mixedEndpointOutcome
              (symbols.get i) (processing i) (mixedUpperCurve c))
            (processing i)) := by
    simpa [selected, values] using
      mixedSelectedEndpointJobs_ofFn
        (mixedUpperCurve c) symbols processing
  have hfixedList :
      mixedFiniteFixedWordExcess c (mixedUpperCurve c)
          (fun i =>
            eraseCapOutcome
              (mixedEndpointOutcome
                (symbols.get i) (processing i)
                (mixedUpperCurve c)))
          processing =
        listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c))
          selected := by
    rw [hselected]
    unfold mixedFiniteFixedWordExcess
    simpa [mixedEndpointSelfExcess, mixedEndpointPairExcess] using
      finSelfPairSum_eq_listPairObjective
        (mixedEndpointSelfExcess c (mixedUpperCurve c))
        (mixedEndpointPairExcess c (mixedUpperCurve c))
        (fun i : Fin symbols.length =>
          MixedEndpointJob.mk
            (mixedEndpointOutcome
              (symbols.get i) (processing i) (mixedUpperCurve c))
            (processing i))
  have hboundary :=
    mixedBoundary_word_excess_le_rewards c word
  have hboundaryList :
      listPairObjective
          (mixedEndpointSelfExcess c (mixedUpperCurve c))
          (mixedEndpointPairExcess c (mixedUpperCurve c))
          selected ≤
        -(c : ℝ) * word.length * (word.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState word.length) word := by
    rw [← hjobs]
    rw [← mixedFiniteFixedWordExcess_jobs_eq_listPairObjective]
    exact hboundary
  dsimp only
  rw [mixedFiniteFixedWordExcess_endpointOutcome,
    hfixedList]
  exact hboundaryList

end

end SchedulingPaper

namespace SchedulingPaper

noncomputable section

open Set
open Online
open LowerBound

/-! ## The concrete runtime satisfies the endpoint hypotheses -/

theorem parameterizedRuntimeThreshold_lt_mixedCapBoundary
    (c : MixedRatioDomain)
    (processingTime : Online.Label n → ℝ)
    (job : Online.Label n) :
    Online.parameterizedRuntimeThreshold c processingTime job <
      mixedUpperCurve c - 1 := by
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hcOne : (c : ℝ) ≤ 1 :=
    c.property.2.trans inv_goldenRatio_lt_one.le
  have hlength :
      ((Online.fixedTestResults processingTime).take job.val).length < n := by
    rw [List.length_take, Online.fixedTestResults_length]
    omega
  have hy :=
    Online.parameterizedCountersFromResults_y_nonpos n hc
      ((Online.fixedTestResults processingTime).take job.val) hlength
  have hthreshold :
      Online.parameterizedRuntimeThreshold c processingTime job <
        1 + 1 / (c : ℝ) := by
    unfold Online.parameterizedRuntimeThreshold
    exact parameterizedAdaptiveThreshold_lt_one_add_inv
      hc hcOne hy
  have hmassInv :
      1 + (mixedMass c : ℝ) ≤ 1 / (c : ℝ) := by
    exact (le_div_iff₀ hc).2 (by
      simpa [mul_comm] using mixed_c_mul_one_add_mass_le_one c)
  have htwo :
      2 / (c : ℝ) =
        1 / (c : ℝ) + 1 / (c : ℝ) := by
    ring
  unfold mixedUpperCurve mixedUpperParameter
  rw [htwo]
  linarith

private theorem parameterizedMixedRuntimeJobs_outcomes
    (c : ℝ) (processingTime : Online.Label n → ℝ) :
    (parameterizedMixedRuntimeJobs c processingTime).map
        ParameterizedMixedRuntimeJob.outcome =
      List.ofFn
        (Online.parameterizedRuntimeOutcomeByLabel c processingTime) := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    let i : Fin (parameterizedMixedRuntimeJobs c processingTime).length :=
      ⟨index, by simpa using hleft⟩
    have hdata :=
      parameterizedMixedRuntimeJob_data c processingTime i
    simpa [i] using hdata.2.2.2

private theorem parameterizedMixedRuntimeJobs_thresholdValues
    (c : ℝ) (processingTime : Online.Label n → ℝ) :
    (parameterizedMixedRuntimeJobs c processingTime).map
        ParameterizedMixedRuntimeJob.threshold =
      List.ofFn
        (Online.parameterizedRuntimeThreshold c processingTime) := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    let i : Fin (parameterizedMixedRuntimeJobs c processingTime).length :=
      ⟨index, by simpa using hleft⟩
    have hdata :=
      parameterizedMixedRuntimeJob_data c processingTime i
    simpa [i] using hdata.2.2.1

theorem parameterizedRuntime_symbolicThresholds
    {c : ℝ} (hc : 0 < c)
    (processingTime : Online.Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    parameterizedMixedSymbolicThresholds c
        (initialParameterizedAnalysisState n)
        (List.ofFn
          (Online.parameterizedRuntimeOutcomeByLabel c processingTime)) =
      List.ofFn
        (Online.parameterizedRuntimeThreshold c processingTime) := by
  let jobs := parameterizedMixedRuntimeJobs c processingTime
  have hthresholds :=
    parameterizedMixedRuntimeJobs_thresholds hc processingTime hnonneg
  have houtcomes :=
    parameterizedMixedRuntimeJobs_outcomes c processingTime
  have hvalues :=
    parameterizedMixedRuntimeJobs_thresholdValues c processingTime
  change
    parameterizedMixedSymbolicThresholds c
        (initialParameterizedAnalysisState n)
        (List.ofFn
          (Online.parameterizedRuntimeOutcomeByLabel c processingTime)) =
      List.ofFn
        (Online.parameterizedRuntimeThreshold c processingTime)
  rw [← houtcomes, ← hvalues]
  exact hthresholds.symm

private theorem mixedFiniteFixedWordExcess_cast
    {n m : ℕ} (h : n = m) (c u : ℝ)
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    mixedFiniteFixedWordExcess c u outcome processing =
      mixedFiniteFixedWordExcess c u
        (fun i : Fin m => outcome (Fin.cast h.symm i))
        (fun i : Fin m => processing (Fin.cast h.symm i)) := by
  subst m
  rfl

theorem exists_parameterizedRuntime_mixedBoundaryWord
    (c : MixedRatioDomain)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job,
        Online.ValueAdmissible (.finite (mixedUpperCurve c))
          (processingTime job)) :
    ∃ word : List CappedBoundaryOutcome,
      word.length = n ∧
      mixedFiniteFixedWordExcess c (mixedUpperCurve c)
          (Online.parameterizedRuntimeOutcomeByLabel c processingTime)
          processingTime ≤
        -(c : ℝ) * word.length * (word.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState word.length) word := by
  let outcome : Fin n → BoundaryOutcome :=
    Online.parameterizedRuntimeOutcomeByLabel c processingTime
  let threshold : Fin n → ℝ :=
    Online.parameterizedRuntimeThreshold c processingTime
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  have hu : 1 < mixedUpperCurve c := by
    have hcurve := (mixedUpperCurve_mem c).1
    linarith [goldenRatio_pos]
  have hnonneg : ∀ i, 0 ≤ processingTime i :=
    fun i => (hadmissible i).1
  have hupper : ∀ i, processingTime i ≤ mixedUpperCurve c :=
    fun i => (hadmissible i).2
  have hthreshold0 : ∀ i, 0 ≤ threshold i := by
    intro i
    exact Online.parameterizedRuntimeThreshold_nonneg
      hc processingTime i
  have hthresholdCap :
      ∀ i, threshold i < mixedUpperCurve c - 1 := by
    intro i
    exact parameterizedRuntimeThreshold_lt_mixedCapBoundary
      c processingTime i
  have hzero :
      ∀ i, outcome i = .zero ∨ outcome i = .epsilon →
        processingTime i = 0 := by
    intro i hi
    dsimp [outcome] at hi
    unfold Online.parameterizedRuntimeOutcomeByLabel at hi
    by_cases hp : processingTime i = 0
    · exact hp
    · by_cases hle :
          processingTime i ≤
            Online.parameterizedRuntimeThreshold c processingTime i
      · simp [hp, hle] at hi
      · simp [hp, hle] at hi
  have himmediate :
      ∀ i, outcome i = .immediate →
        0 ≤ processingTime i ∧ processingTime i ≤ threshold i := by
    intro i hi
    refine ⟨hnonneg i, ?_⟩
    dsimp [outcome, threshold] at hi ⊢
    unfold Online.parameterizedRuntimeOutcomeByLabel at hi
    by_cases hp : processingTime i = 0
    · simp [hp] at hi
    · by_cases hle :
          processingTime i ≤
            Online.parameterizedRuntimeThreshold c processingTime i
      · exact hle
      · simp [hp, hle] at hi
  have hdeferred :
      ∀ i, outcome i = .deferred →
        threshold i ≤ processingTime i := by
    intro i hi
    have hstrict :=
      (Online.parameterizedRuntimeOutcome_deferred_iff
        hc processingTime i).mp (by simpa [outcome] using hi)
    exact hstrict.le
  have hcap :
      ∀ i, mixedUpperCurve c - 1 ≤ processingTime i →
        outcome i = .deferred := by
    intro i hp
    apply (Online.parameterizedRuntimeOutcome_deferred_iff
      hc processingTime i).mpr
    exact (hthresholdCap i).trans_le hp
  obtain ⟨endpoint, hendpointDominates, hendpointChoices⟩ :=
    exists_mixedFinite_endpoint_ge outcome threshold processingTime
      hc.le hu hthreshold0 hthresholdCap hupper
      hzero himmediate hdeferred hcap
  let symbols : List BoundaryOutcome := List.ofFn outcome
  have hnSymbols : n = symbols.length := by
    simp [symbols]
  let endpointOnSymbols : Fin symbols.length → ℝ :=
    fun i => endpoint (Fin.cast hnSymbols.symm i)
  have hsymbolic :
      parameterizedMixedSymbolicThresholds c
          (initialParameterizedAnalysisState symbols.length) symbols =
        List.ofFn threshold := by
    simpa [symbols, outcome, threshold] using
      parameterizedRuntime_symbolicThresholds
        hc processingTime hnonneg
  have hchoices :
      MixedEndpointChoices c (mixedUpperCurve c)
        (initialParameterizedAnalysisState symbols.length)
        symbols (List.ofFn endpointOnSymbols) := by
    refine mixedEndpointChoices_of_get (by simp) ?_
    intro i
    let runtimeIndex : Fin n :=
      Fin.cast hnSymbols.symm i
    let listedIndex : Fin n :=
      ⟨i.val, by simpa [symbols] using i.isLt⟩
    have hindex : listedIndex = runtimeIndex := by
      apply Fin.ext
      rfl
    have hi := hendpointChoices runtimeIndex
    have hs : symbols.get i = outcome runtimeIndex := by
      calc
        symbols.get i = outcome listedIndex := by
          simp [symbols, listedIndex]
        _ = outcome runtimeIndex := congrArg outcome hindex
    have ht :
        (parameterizedMixedSymbolicThresholds c
          (initialParameterizedAnalysisState symbols.length)
          symbols).get ⟨i, by simpa using i.isLt⟩ =
            threshold runtimeIndex := by
      have hlisted :
          (parameterizedMixedSymbolicThresholds c
            (initialParameterizedAnalysisState symbols.length)
            symbols).get ⟨i, by simpa using i.isLt⟩ =
              threshold listedIndex := by
        simp [hsymbolic, listedIndex]
      exact hlisted.trans (congrArg threshold hindex)
    rw [hs, ht]
    simpa [endpointOnSymbols, runtimeIndex] using hi
  let word :=
    mixedEndpointWord (mixedUpperCurve c)
      symbols (List.ofFn endpointOnSymbols)
  have hwordLength : word.length = n := by
    have hlength := mixedEndpointWord_length hchoices
    simpa [word, symbols] using hlength
  have hendpointBound :=
    mixedEndpointChoices_excess_le_rewards
      c symbols endpointOnSymbols hchoices
  refine ⟨word, hwordLength, ?_⟩
  calc
    mixedFiniteFixedWordExcess c (mixedUpperCurve c)
          (Online.parameterizedRuntimeOutcomeByLabel c processingTime)
          processingTime ≤
        mixedFiniteFixedWordExcess c (mixedUpperCurve c)
          outcome endpoint := by
      simpa [outcome] using hendpointDominates
    _ =
        mixedFiniteFixedWordExcess c (mixedUpperCurve c)
          (fun i : Fin symbols.length => symbols.get i)
          endpointOnSymbols := by
      rw [mixedFiniteFixedWordExcess_cast
        hnSymbols c (mixedUpperCurve c) outcome endpoint]
      apply congrArg₂
      · funext i
        let listedIndex : Fin n :=
          ⟨i.val, by simpa [symbols] using i.isLt⟩
        have hindex :
            listedIndex = Fin.cast hnSymbols.symm i := by
          apply Fin.ext
          rfl
        calc
          outcome (Fin.cast hnSymbols.symm i) =
              outcome listedIndex := congrArg outcome hindex.symm
          _ = symbols.get i := by
            simp [symbols, listedIndex]
      · rfl
    _ ≤
        -(c : ℝ) * word.length * (word.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState word.length) word := by
      simpa [word] using hendpointBound

end

end SchedulingPaper

namespace SchedulingPaper

noncomputable section

namespace UpperBound

open LowerBound

/-- The concrete executable mixed strategy satisfies the complete
five-endpoint boundary bridge, for every point of the mixed curve. -/
theorem verifiedMixedBoundaryBridge :
    ∀ c : MixedRatioDomain, MixedBoundaryBridge c := by
  intro c n input
  have hc : 0 < (c : ℝ) :=
    rhoStar_pos.trans_le c.property.1
  obtain ⟨outcomes, hlength, hbound⟩ :=
    exists_parameterizedRuntime_mixedBoundaryWord
      c input.processingTime input.admissible
  refine ⟨outcomes, hlength, ?_⟩
  calc
    strategyCost (.finite (mixedUpperCurve c)) (mixedStrategy c)
          n input -
        mixedCompetitiveRatio c * input.offlineCost =
      mixedFiniteFixedWordExcess c (mixedUpperCurve c)
        (Online.parameterizedRuntimeOutcomeByLabel
          c input.processingTime)
        input.processingTime := by
      simpa [strategyCost, FixedInput.onlineCost,
        FixedInput.runResult, analysisFuel, mixedStrategy,
        mixedCompetitiveRatio, FixedInput.offlineCost] using
        (parameterizedRuntime_mixedExcess_eq
          n c (mixedUpperCurve c) hc input.processingTime)
    _ ≤
        -(c : ℝ) * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState outcomes.length)
            outcomes := hbound

end UpperBound

end

end SchedulingPaper
