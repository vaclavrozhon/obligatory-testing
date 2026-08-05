import SchedulingPaper.AdaptiveRuntimeEndpoint
import SchedulingPaper.PlateauBank

/-!
# Reducing finite-cap plateau inputs to the obligatory endpoint word

On the high plateau (`u ≥ zStar`) every value in the optional-cap interval
is deferred.  Lowering such a value to its live threshold pays not only for
the algorithmic change but also for the loss caused by clipping the offline
effective length.  Consequently the finite-cap excess is bounded by the
ordinary obligatory fixed-word excess of the lowered vector.  The already
proved four-letter endpoint reduction can then be reused verbatim.
-/

namespace SchedulingPaper

noncomputable section

open Online

def plateauClippedProcessing (u p : ℝ) : ℝ :=
  min p (u - 1)

def plateauSelfExcessAt (u p : ℝ) : ℝ :=
  (1 + p) -
    RStar * (1 + plateauClippedProcessing u p)

def plateauPairExcessAt
    (u : ℝ) (left right : BoundaryOutcome)
    (p q : ℝ) : ℝ :=
  obligatoryALGPairCharge ⟨left, p⟩ ⟨right, q⟩ -
    RStar *
      (1 + min (plateauClippedProcessing u p)
        (plateauClippedProcessing u q))

def plateauFixedWordExcess {n : ℕ}
    (u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, plateauSelfExcessAt u (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      plateauPairExcessAt u
        (outcome i) (outcome j) (processing i) (processing j)

def lowerPlateauCaps {n : ℕ}
    (u : ℝ) (threshold processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if u - 1 ≤ processing i then threshold i else processing i

theorem plateau_threshold_distance
    {u a : ℝ} (hu : zStar ≤ u) (ha : a ≤ 1 / rhoStar) :
    1 ≤ rhoStar * (u - 1 - a) := by
  have hz : zStar - 1 = 2 / rhoStar := by
    rw [two_div_rhoStar]
  have hdistance : 2 / rhoStar ≤ u - 1 := by
    linarith
  have hsplit :
      2 / rhoStar = 1 / rhoStar + 1 / rhoStar := by
    ring
  rw [hsplit] at hdistance
  have hrho : 0 < rhoStar := rhoStar_pos
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (show 1 / rhoStar ≤ u - 1 - a by linarith)
      hrho.le
  have hcancel : rhoStar * (1 / rhoStar) = 1 := by
    field_simp [hrho.ne']
  linarith

theorem plateauSelfExcessAt_le_lowered
    {u p a : ℝ} (hu : zStar ≤ u)
    (hpUpper : p ≤ u) (ha : a ≤ 1 / rhoStar) :
    plateauSelfExcessAt u p ≤
      obligatorySelfExcessAt
        (if u - 1 ≤ p then a else p) := by
  by_cases hcap : u - 1 ≤ p
  · have hclip :
        plateauClippedProcessing u p = u - 1 := by
      simp [plateauClippedProcessing, min_eq_right hcap]
    rw [if_pos hcap]
    have hdistance := plateau_threshold_distance hu ha
    unfold plateauSelfExcessAt obligatorySelfExcessAt
      plateauClippedProcessing RStar
    rw [min_eq_right hcap]
    linarith
  · have hbelow : p ≤ u - 1 := (lt_of_not_ge hcap).le
    have hclip :
        plateauClippedProcessing u p = p := by
      simp [plateauClippedProcessing, min_eq_left hbelow]
    rw [if_neg hcap]
    unfold plateauSelfExcessAt obligatorySelfExcessAt
      plateauClippedProcessing
    rw [min_eq_left hbelow]

theorem plateauPairExcessAt_le_lowered
    {u p q a b : ℝ}
    {left right : BoundaryOutcome}
    (hu : zStar ≤ u)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hpUpper : p ≤ u) (hqUpper : q ≤ u)
    (ha : a ≤ 1 / rhoStar) (hb : b ≤ 1 / rhoStar)
    (hleftCap :
      u - 1 ≤ p → left = .deferred)
    (hrightCap :
      u - 1 ≤ q → right = .deferred) :
    plateauPairExcessAt u left right p q ≤
      obligatoryPairExcessAt left right
        (if u - 1 ≤ p then a else p)
        (if u - 1 ≤ q then b else q) := by
  by_cases hpCap : u - 1 ≤ p
  · have hleft : left = .deferred := hleftCap hpCap
    subst left
    have hpClip :
        plateauClippedProcessing u p = u - 1 := by
      simp [plateauClippedProcessing, min_eq_right hpCap]
    by_cases hqCap : u - 1 ≤ q
    · have hright : right = .deferred := hrightCap hqCap
      subst right
      have hqClip :
          plateauClippedProcessing u q = u - 1 := by
        simp [plateauClippedProcessing, min_eq_right hqCap]
      have hminActual : min p q ≤ u :=
        (min_le_left p q).trans hpUpper
      have hminThreshold : min a b ≤ 1 / rhoStar :=
        (min_le_left a b).trans ha
      have hdistance :=
        plateau_threshold_distance hu hminThreshold
      simp only [if_pos hpCap, if_pos hqCap]
      unfold plateauPairExcessAt obligatoryPairExcessAt
        obligatoryALGPairCharge obligatoryOPTPairCharge
      rw [hpClip, hqClip, min_self]
      unfold RStar
      nlinarith
    · have hqBelow : q ≤ u - 1 := (lt_of_not_ge hqCap).le
      have hqClip :
          plateauClippedProcessing u q = q := by
        simp [plateauClippedProcessing, min_eq_left hqBelow]
      have hpq : q ≤ p := hqBelow.trans hpCap
      have hminReduced : min a q ≤ q := min_le_right _ _
      have hminActual : min p q = q := min_eq_right hpq
      have hminClipped : min (u - 1) q = q :=
        min_eq_right hqBelow
      simp only [if_pos hpCap, if_neg hqCap]
      cases right <;>
        simp only [plateauPairExcessAt,
          obligatoryPairExcessAt, obligatoryALGPairCharge,
          obligatoryOPTPairCharge, hpClip, hqClip,
          hminActual, hminClipped] <;>
        unfold RStar <;>
        nlinarith [mul_nonneg rhoStar_pos.le
          (sub_nonneg.mpr hminReduced)]
  · have hpBelow : p ≤ u - 1 := (lt_of_not_ge hpCap).le
    have hpClip :
        plateauClippedProcessing u p = p := by
      simp [plateauClippedProcessing, min_eq_left hpBelow]
    by_cases hqCap : u - 1 ≤ q
    · have hright : right = .deferred := hrightCap hqCap
      subst right
      have hqClip :
          plateauClippedProcessing u q = u - 1 := by
        simp [plateauClippedProcessing, min_eq_right hqCap]
      have hpq : p ≤ q := hpBelow.trans hqCap
      have hminReduced : min p b ≤ p := min_le_left _ _
      have hminActual : min p q = p := min_eq_left hpq
      have hminClipped : min p (u - 1) = p :=
        min_eq_left hpBelow
      simp only [if_neg hpCap, if_pos hqCap]
      cases left <;>
        simp only [plateauPairExcessAt,
          obligatoryPairExcessAt, obligatoryALGPairCharge,
          obligatoryOPTPairCharge, hpClip, hqClip,
          hminActual, hminClipped] <;>
        unfold RStar <;>
        nlinarith [mul_nonneg rhoStar_pos.le
          (sub_nonneg.mpr hminReduced)]
    · have hqBelow : q ≤ u - 1 := (lt_of_not_ge hqCap).le
      have hqClip :
          plateauClippedProcessing u q = q := by
        simp [plateauClippedProcessing, min_eq_left hqBelow]
      simp [hpCap, hqCap, plateauPairExcessAt,
        obligatoryPairExcessAt, hpClip, hqClip,
        obligatoryOPTPairCharge]

theorem plateauFixedWordExcess_le_lowerPlateauCaps
    {n : ℕ} {u : ℝ}
    {outcome : Fin n → BoundaryOutcome}
    {threshold processing : Fin n → ℝ}
    (hu : zStar ≤ u)
    (hprocessing : ∀ i, 0 ≤ processing i ∧ processing i ≤ u)
    (hthreshold : ∀ i, threshold i ≤ 1 / rhoStar)
    (hcap :
      ∀ i, u - 1 ≤ processing i → outcome i = .deferred) :
    plateauFixedWordExcess u outcome processing ≤
      obligatoryFixedWordExcess outcome
        (lowerPlateauCaps u threshold processing) := by
  classical
  unfold plateauFixedWordExcess obligatoryFixedWordExcess
    lowerPlateauCaps
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    exact plateauSelfExcessAt_le_lowered hu
      (hprocessing i).2 (hthreshold i)
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact plateauPairExcessAt_le_lowered hu
      (hprocessing i).1 (hprocessing j).1
      (hprocessing i).2 (hprocessing j).2
      (hthreshold i) (hthreshold j)
      (hcap i) (hcap j)

theorem obligatorySymbolicThresholds_le_inv
    {state : AnalysisState}
    {symbols : List ObligatoryRuntimeClass}
    (hmatch :
      BoundaryStateMatches state
        (symbols.map ObligatoryRuntimeClass.outcome)) :
    ∀ threshold ∈ obligatorySymbolicThresholds state symbols,
      threshold ≤ 1 / rhoStar := by
  induction symbols generalizing state with
  | nil =>
      simp [obligatorySymbolicThresholds]
  | cons symbol symbols ih =>
      have hs := hmatch.feasible_of_cons
      have hhead :
          state.threshold ≤ 1 / rhoStar := by
        have hbound :=
          parameterizedAdaptiveThreshold_rhoStar_le_inv
            (AnalysisState.y_nonpos hs)
        rw [Online.AnalysisState.threshold_eq_adaptiveThreshold]
        simpa using hbound
      intro threshold hthreshold
      simp only [obligatorySymbolicThresholds,
        List.mem_cons] at hthreshold
      rcases hthreshold with rfl | htail
      · exact hhead
      · exact ih hmatch.step threshold htail

theorem obligatorySymbolThresholdFn_le_inv
    (symbols : List ObligatoryRuntimeClass) :
    ∀ i,
      obligatorySymbolThresholdFn
          (initialAnalysisState symbols.length) symbols i ≤
        1 / rhoStar := by
  intro i
  apply obligatorySymbolicThresholds_le_inv
    (state := initialAnalysisState symbols.length)
    (symbols := symbols)
  · simpa using
      boundaryStateMatches_initial
        (symbols.map ObligatoryRuntimeClass.outcome)
  · exact List.get_mem _ _

def liftOrdinaryOutcome :
    BoundaryOutcome → CappedBoundaryOutcome
  | .zero => .zero
  | .epsilon => .epsilon
  | .immediate => .immediate
  | .deferred => .deferred

@[simp] theorem eraseCapOutcome_liftOrdinaryOutcome
    (outcome : BoundaryOutcome) :
    eraseCapOutcome (liftOrdinaryOutcome outcome) = outcome := by
  cases outcome <;> rfl

@[simp] theorem map_eraseCapOutcome_liftOrdinaryOutcome
    (outcomes : List BoundaryOutcome) :
    (outcomes.map liftOrdinaryOutcome).map eraseCapOutcome =
      outcomes := by
  induction outcomes with
  | nil => rfl
  | cons outcome outcomes ih =>
      simp [Function.comp_def, ih]

theorem obligatoryBoundaryExcess_le_lifted_plateauReward
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryExcess outcomes ≤
      -rhoStar *
          (outcomes.map liftOrdinaryOutcome).length *
          ((outcomes.map liftOrdinaryOutcome).length + 1) / 2 +
        trajectoryReward ParameterizedAnalysisState.step
          (parameterizedOrdinaryReward rhoStar)
          (initialParameterizedAnalysisState
            (outcomes.map liftOrdinaryOutcome).length)
          (outcomes.map liftOrdinaryOutcome) := by
  have hreachable :=
    initialAnalysisState_trajectory_good outcomes
  have hfeasible :
      TrajectoryGood AnalysisState.step AnalysisState.Feasible
        (initialAnalysisState outcomes.length) outcomes :=
    hreachable.mono AnalysisState.step (fun _ hs => hs.1)
  have hrelaxed :=
    exact_trajectoryReward_le_relaxed
      (initialAnalysisState outcomes.length) outcomes hfeasible
  unfold obligatoryBoundaryExcess
  simp only [List.length_map]
  rw [plateau_trajectoryReward_erasure,
    initialParameterized_toObligatory,
    map_eraseCapOutcome_liftOrdinaryOutcome]
  linarith

theorem exists_plateauBoundaryWord_ge_adaptiveRuntime
    {u : ℝ} (hu : zStar ≤ u)
    (processingTime : Label n → ℝ)
    (hprocessing :
      ∀ job, 0 ≤ processingTime job ∧ processingTime job ≤ u) :
    ∃ outcomes : List CappedBoundaryOutcome,
      outcomes.length = n ∧
      plateauFixedWordExcess u
          (obligatorySymbolOutcomeFn
            (adaptiveRuntimeSymbols processingTime))
          (adaptiveRuntimeProcessing processingTime) ≤
        -rhoStar * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (parameterizedOrdinaryReward rhoStar)
            (initialParameterizedAnalysisState outcomes.length)
            outcomes := by
  let symbols := adaptiveRuntimeSymbols processingTime
  let processing := adaptiveRuntimeProcessing processingTime
  let threshold :=
    obligatorySymbolThresholdFn
      (initialAnalysisState symbols.length) symbols
  let reduced := lowerPlateauCaps u threshold processing
  have huOne : 1 < u := zStar_gt_one.trans_le hu
  have hthresholdUpper : ∀ i, threshold i ≤ 1 / rhoStar := by
    intro i
    exact obligatorySymbolThresholdFn_le_inv symbols i
  have hthresholdBelowCap : ∀ i, threshold i < u - 1 := by
    intro i
    have hinv : 1 / rhoStar < 2 / rhoStar := by
      exact (div_lt_div_iff_of_pos_right rhoStar_pos).2 one_lt_two
    rw [two_div_rhoStar] at hinv
    exact (hthresholdUpper i).trans_lt (hinv.trans_le (by linarith))
  have hprocessingBounds :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ u := by
    intro i
    let runtimeIndex : Label n :=
      ⟨i.val, by
        simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    simpa [processing, adaptiveRuntimeProcessing, runtimeIndex] using
      hprocessing runtimeIndex
  have hcap :
      ∀ i, u - 1 ≤ processing i →
        obligatorySymbolOutcomeFn symbols i = .deferred := by
    intro i hi
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by
          simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobProcessing : job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hjobThreshold : job.threshold = threshold i := by
      simpa [job, threshold, symbols] using
        adaptiveRuntimeJob_threshold processingTime i
    have hgt : job.threshold < job.processing := by
      rw [hjobProcessing, hjobThreshold]
      exact (hthresholdBelowCap i).trans_le hi
    have hthresholdNonneg : 0 ≤ job.threshold := by
      rw [hjobThreshold]
      exact obligatorySymbolThresholdFn_nonneg symbols i
    have hprocessingPos : 0 < job.processing :=
      hthresholdNonneg.trans_lt hgt
    have hsymbol : job.symbol = .deferred := by
      rw [← hclass]
      simp [classifyAdaptive, ne_of_gt hprocessingPos,
        not_le.mpr hgt]
    change (symbols.get i).outcome = .deferred
    have hsymbolGet : symbols.get i = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_symbol processingTime i
    rw [hsymbolGet, hsymbol]
    rfl
  have hlowering :
      plateauFixedWordExcess u
          (obligatorySymbolOutcomeFn symbols) processing ≤
        obligatoryFixedWordExcess
          (obligatorySymbolOutcomeFn symbols) reduced :=
    plateauFixedWordExcess_le_lowerPlateauCaps hu
      hprocessingBounds hthresholdUpper hcap
  have hzero :
      ∀ i, symbols.get i = .zero → reduced i = 0 := by
    intro i hsymbol
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by
          simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .zero := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hjobProcessing : job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hpzero :
        processing i = 0 := by
      rw [← hjobProcessing]
      exact
        (classifyAdaptive_eq_zero_iff
          job.threshold job.processing).mp
          (hclass.trans hjobsymbol)
    have hnotCap : ¬u - 1 ≤ processing i := by
      rw [hpzero]
      linarith
    have hreduced : reduced i = processing i := by
      simp [reduced, lowerPlateauCaps, hnotCap]
    rw [hreduced, hpzero]
  have himmediate :
      ∀ i, symbols.get i = .immediate →
        0 ≤ reduced i ∧ reduced i ≤ threshold i := by
    intro i hsymbol
    let runtimeIndex : Label n :=
      ⟨i.val, by
        simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by
          simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .immediate := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hjobProcessing : job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hjobThreshold : job.threshold = threshold i := by
      simpa [job, threshold, symbols] using
        adaptiveRuntimeJob_threshold processingTime i
    have hinterval :=
      (classifyAdaptive_eq_immediate_iff
        job.threshold job.processing).mp
        (hclass.trans hjobsymbol)
    have hnotCap : ¬u - 1 ≤ processing i := by
      intro hcapValue
      have :
          job.threshold < job.processing := by
        rw [hjobProcessing, hjobThreshold]
        exact (hthresholdBelowCap i).trans_le hcapValue
      exact (not_lt_of_ge hinterval.2) this
    simp only [reduced, lowerPlateauCaps, if_neg hnotCap]
    rw [← hjobProcessing, ← hjobThreshold]
    exact ⟨by
      rw [hjobProcessing]
      exact (hprocessing runtimeIndex).1, hinterval.2⟩
  have hdeferred :
      ∀ i, symbols.get i = .deferred →
        threshold i ≤ reduced i := by
    intro i hsymbol
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by
          simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .deferred := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hjobProcessing : job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hjobThreshold : job.threshold = threshold i := by
      simpa [job, threshold, symbols] using
        adaptiveRuntimeJob_threshold processingTime i
    have hinterval :=
      (classifyAdaptive_eq_deferred_iff
        job.threshold job.processing).mp
        (hclass.trans hjobsymbol)
    unfold reduced lowerPlateauCaps
    split_ifs
    · exact le_rfl
    · rw [← hjobProcessing, ← hjobThreshold]
      exact hinterval.2.le
  obtain ⟨ordinaryOutcomes, hlength, hendpoint⟩ :=
    exists_obligatoryBoundaryWord_ge_symbolic
      symbols reduced hzero himmediate hdeferred
  let outcomes :=
    ordinaryOutcomes.map liftOrdinaryOutcome
  have hlift :=
    obligatoryBoundaryExcess_le_lifted_plateauReward
      ordinaryOutcomes
  refine ⟨outcomes, ?_, hlowering.trans (hendpoint.trans hlift)⟩
  simpa [outcomes, symbols] using hlength

end

end SchedulingPaper
