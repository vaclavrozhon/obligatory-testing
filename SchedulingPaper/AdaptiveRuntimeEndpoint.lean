import SchedulingPaper.AdaptiveSymbolicRuntime

/-!
# Endpoint domination for the symbolic word of an AdaptiveThreshold run

The job records built from the live threshold trajectory remember exactly the
three data needed by the obligatory endpoint theorem: the runtime class, the
revealed processing time, and the live threshold.  This module packages those
records as a word indexed by the original labels and verifies all three
interval conditions.
-/

namespace SchedulingPaper.Online

noncomputable section

open SchedulingPaper

@[simp] theorem buildAdaptiveJobs_map_result
    (state : AnalysisState)
    (results : List (Label n × ℝ)) :
    (buildAdaptiveJobs state results).map
        (fun job => (job.label, job.processing)) =
      results := by
  induction results generalizing state with
  | nil => rfl
  | cons result results ih =>
      simp [buildAdaptiveJobs, ih]

@[simp] theorem buildAdaptiveJobs_map_symbol
    (state : AnalysisState)
    (result : Label n × ℝ)
    (results : List (Label n × ℝ)) :
    (buildAdaptiveJobs state (result :: results)).map
        AdaptiveRuntimeJob.symbol =
      classifyAdaptive state.threshold result.2 ::
        (buildAdaptiveJobs
          (state.step
            (classifyAdaptive state.threshold result.2).outcome)
          results).map AdaptiveRuntimeJob.symbol := by
  simp [buildAdaptiveJobs]

theorem buildAdaptiveJobs_map_threshold
    (state : AnalysisState)
    (results : List (Label n × ℝ)) :
    (buildAdaptiveJobs state results).map
        AdaptiveRuntimeJob.threshold =
      obligatorySymbolicThresholds state
        ((buildAdaptiveJobs state results).map
          AdaptiveRuntimeJob.symbol) := by
  induction results generalizing state with
  | nil =>
      rfl
  | cons result results ih =>
      simp only [buildAdaptiveJobs, List.map_cons,
        obligatorySymbolicThresholds]
      exact congrArg (List.cons state.threshold)
        (ih
          (state.step
            (classifyAdaptive state.threshold result.2).outcome))

theorem buildAdaptiveJobs_get_result
    (state : AnalysisState)
    (results : List (Label n × ℝ))
    (index : ℕ) (hindex : index < results.length) :
    let result := results.get ⟨index, hindex⟩
    let job :=
      (buildAdaptiveJobs state results).get
        ⟨index, by simpa using hindex⟩
    job.label = result.1 ∧ job.processing = result.2 := by
  induction results generalizing state index with
  | nil =>
      simp at hindex
  | cons result results ih =>
      cases index with
      | zero =>
          simp [buildAdaptiveJobs]
      | succ index =>
          have htail : index < results.length := by
            simpa using hindex
          simpa [buildAdaptiveJobs] using
            ih
              (state.step
                (classifyAdaptive state.threshold result.2).outcome)
              index htail

theorem classifyAdaptive_eq_zero_iff
    (threshold processing : ℝ) :
    classifyAdaptive threshold processing = .zero ↔
      processing = 0 := by
  unfold classifyAdaptive
  by_cases hzero : processing = 0
  · simp [hzero]
  · by_cases himmediate : processing ≤ threshold <;>
      simp [hzero, himmediate]

theorem classifyAdaptive_eq_immediate_iff
    (threshold processing : ℝ) :
    classifyAdaptive threshold processing = .immediate ↔
      processing ≠ 0 ∧ processing ≤ threshold := by
  unfold classifyAdaptive
  by_cases hzero : processing = 0
  · simp [hzero]
  · by_cases himmediate : processing ≤ threshold <;>
      simp [hzero, himmediate]

theorem classifyAdaptive_eq_deferred_iff
    (threshold processing : ℝ) :
    classifyAdaptive threshold processing = .deferred ↔
      processing ≠ 0 ∧ threshold < processing := by
  unfold classifyAdaptive
  by_cases hzero : processing = 0
  · simp [hzero]
  · by_cases himmediate : processing ≤ threshold
    · simp [hzero, himmediate]
    · simp [hzero, himmediate, lt_of_not_ge himmediate]

theorem buildAdaptiveJobs_classification
    (state : AnalysisState)
    (results : List (Label n × ℝ)) :
    ∀ job ∈ buildAdaptiveJobs state results,
      classifyAdaptive job.threshold job.processing =
        job.symbol := by
  induction results generalizing state with
  | nil =>
      simp [buildAdaptiveJobs]
  | cons result results ih =>
      intro job hjob
      simp only [buildAdaptiveJobs, List.mem_cons] at hjob
      rcases hjob with rfl | htail
      · rfl
      · exact ih
          (state.step
            (classifyAdaptive state.threshold result.2).outcome)
          job htail

def adaptiveRuntimeSymbols
    (processingTime : Label n → ℝ) :
    List ObligatoryRuntimeClass :=
  (adaptiveRuntimeJobs processingTime).map
    AdaptiveRuntimeJob.symbol

@[simp] theorem adaptiveRuntimeSymbols_length
    (processingTime : Label n → ℝ) :
    (adaptiveRuntimeSymbols processingTime).length = n := by
  simp [adaptiveRuntimeSymbols]

def adaptiveRuntimeProcessing
    (processingTime : Label n → ℝ) :
    Fin (adaptiveRuntimeSymbols processingTime).length → ℝ :=
  fun index =>
    processingTime
      ⟨index.val, by
        simpa [adaptiveRuntimeSymbols] using index.isLt⟩

theorem adaptiveRuntimeJobs_get_label_processing
    (processingTime : Label n → ℝ)
    (index : Fin (adaptiveRuntimeSymbols processingTime).length) :
    let runtimeIndex : Label n :=
      ⟨index.val, by
        simpa [adaptiveRuntimeSymbols] using index.isLt⟩
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨index.val, by
          simpa [adaptiveRuntimeSymbols] using index.isLt⟩
    job.label = runtimeIndex ∧
      job.processing = adaptiveRuntimeProcessing processingTime index := by
  have hindex : index.val < (fixedTestResults processingTime).length := by
    simpa [adaptiveRuntimeSymbols] using index.isLt
  have hget :=
    buildAdaptiveJobs_get_result
      (initialAnalysisState n)
      (fixedTestResults processingTime)
      index.val hindex
  simpa [adaptiveRuntimeJobs, fixedTestResults,
    adaptiveRuntimeProcessing, adaptiveRuntimeSymbols] using hget

theorem adaptiveRuntimeJob_symbol
    (processingTime : Label n → ℝ)
    (index : Fin (adaptiveRuntimeSymbols processingTime).length) :
    (adaptiveRuntimeSymbols processingTime).get index =
      ((adaptiveRuntimeJobs processingTime).get
        ⟨index.val, by
          simpa [adaptiveRuntimeSymbols] using index.isLt⟩).symbol := by
  simp [adaptiveRuntimeSymbols]

theorem adaptiveRuntimeJob_threshold
    (processingTime : Label n → ℝ)
    (index : Fin (adaptiveRuntimeSymbols processingTime).length) :
    ((adaptiveRuntimeJobs processingTime).get
        ⟨index.val, by
          simpa [adaptiveRuntimeSymbols] using index.isLt⟩).threshold =
      obligatorySymbolThresholdFn
        (initialAnalysisState
          (adaptiveRuntimeSymbols processingTime).length)
        (adaptiveRuntimeSymbols processingTime) index := by
  have hthresholds :=
    buildAdaptiveJobs_map_threshold
      (initialAnalysisState n)
      (fixedTestResults processingTime)
  have hlength :
      (adaptiveRuntimeSymbols processingTime).length = n := by
    simp
  have hinitial :
      initialAnalysisState
          (adaptiveRuntimeSymbols processingTime).length =
        initialAnalysisState n := by
    rw [hlength]
  have hthresholds' :
      (adaptiveRuntimeJobs processingTime).map
          AdaptiveRuntimeJob.threshold =
        obligatorySymbolicThresholds
          (initialAnalysisState
            (adaptiveRuntimeSymbols processingTime).length)
          (adaptiveRuntimeSymbols processingTime) := by
    rw [hinitial]
    simpa [adaptiveRuntimeJobs, adaptiveRuntimeSymbols] using
      hthresholds
  have hindex :
      index.val <
        ((adaptiveRuntimeJobs processingTime).map
          AdaptiveRuntimeJob.threshold).length := by
    simpa [adaptiveRuntimeSymbols] using index.isLt
  have hget :=
    List.getElem_of_eq hthresholds' hindex
  unfold obligatorySymbolThresholdFn
  simpa [List.get_eq_getElem] using hget

theorem adaptiveRuntimeJob_classification
    (processingTime : Label n → ℝ)
    (index : Fin (adaptiveRuntimeSymbols processingTime).length) :
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨index.val, by
          simpa [adaptiveRuntimeSymbols] using index.isLt⟩
    classifyAdaptive job.threshold job.processing =
      job.symbol := by
  dsimp only
  apply buildAdaptiveJobs_classification
  exact List.get_mem _ _

/-- The complete static endpoint reduction for the symbolic word generated
by a nonnegative fixed input. -/
theorem exists_obligatoryBoundaryWord_ge_adaptiveRuntime
    (processingTime : Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    ∃ outcomes : List BoundaryOutcome,
      outcomes.length = n ∧
      obligatoryFixedWordExcess
          (obligatorySymbolOutcomeFn
            (adaptiveRuntimeSymbols processingTime))
          (adaptiveRuntimeProcessing processingTime) ≤
        obligatoryBoundaryExcess outcomes := by
  let symbols := adaptiveRuntimeSymbols processingTime
  let processing := adaptiveRuntimeProcessing processingTime
  have hzero :
      ∀ i, symbols.get i = .zero → processing i = 0 := by
    intro i hsymbol
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .zero := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hprocessing :
        job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    rw [← hprocessing]
    exact
      (classifyAdaptive_eq_zero_iff
        job.threshold job.processing).mp
        (hclass.trans hjobsymbol)
  have himmediate :
      ∀ i, symbols.get i = .immediate →
        0 ≤ processing i ∧
          processing i ≤
            obligatorySymbolThresholdFn
              (initialAnalysisState symbols.length) symbols i := by
    intro i hsymbol
    let runtimeIndex : Label n :=
      ⟨i.val, by
        simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .immediate := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hprocessing :
        job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hthreshold :
        job.threshold =
          obligatorySymbolThresholdFn
            (initialAnalysisState symbols.length) symbols i := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_threshold processingTime i
    have hinterval :=
      (classifyAdaptive_eq_immediate_iff
        job.threshold job.processing).mp
        (hclass.trans hjobsymbol)
    rw [← hprocessing, ← hthreshold]
    exact ⟨by
      rw [hprocessing]
      exact hnonneg runtimeIndex, hinterval.2⟩
  have hdeferred :
      ∀ i, symbols.get i = .deferred →
        obligatorySymbolThresholdFn
            (initialAnalysisState symbols.length) symbols i ≤
          processing i := by
    intro i hsymbol
    let job :=
      (adaptiveRuntimeJobs processingTime).get
        ⟨i.val, by simpa [symbols, adaptiveRuntimeSymbols] using i.isLt⟩
    have hclass :
        classifyAdaptive job.threshold job.processing = job.symbol := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_classification processingTime i
    have hjobsymbol : job.symbol = .deferred := by
      rw [← hsymbol]
      simpa [job, symbols] using
        (adaptiveRuntimeJob_symbol processingTime i).symm
    have hprocessing :
        job.processing = processing i := by
      simpa [job, processing, symbols] using
        (adaptiveRuntimeJobs_get_label_processing
          processingTime i).2
    have hthreshold :
        job.threshold =
          obligatorySymbolThresholdFn
            (initialAnalysisState symbols.length) symbols i := by
      simpa [job, symbols] using
        adaptiveRuntimeJob_threshold processingTime i
    have hinterval :=
      (classifyAdaptive_eq_deferred_iff
        job.threshold job.processing).mp
        (hclass.trans hjobsymbol)
    rw [← hprocessing, ← hthreshold]
    exact hinterval.2.le
  obtain ⟨outcomes, hlength, hbound⟩ :=
    exists_obligatoryBoundaryWord_ge_symbolic
      symbols processing hzero himmediate hdeferred
  refine ⟨outcomes, ?_, hbound⟩
  simpa [symbols] using hlength

end

end SchedulingPaper.Online
