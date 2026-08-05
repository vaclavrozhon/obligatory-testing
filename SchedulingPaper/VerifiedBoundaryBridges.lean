import SchedulingPaper.UpperBoundAssembly
import SchedulingPaper.PlateauRuntimeObjective

/-!
# Verified obligatory and high-plateau runtime bridges

The executable AdaptiveThreshold trace is connected here to the static
endpoint reductions, closing the two operational bridge interfaces used by
the obligatory endpoint and by the finite high plateau.
-/

namespace SchedulingPaper

noncomputable section

open LowerBound

/-- Exact obligatory competitive excess of the executable adaptive run. -/
theorem adaptiveRuntime_obligatoryExcess_eq
    (n : ℕ) (processingTime : Online.Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    let result :=
      Online.run .infinite (Online.fixedOracle processingTime)
        (Online.parameterizedAdaptiveThresholdStrategy n rhoStar)
        (2 * n + 1)
    Online.runCompletionCost .infinite processingTime result -
        RStar * vectorOfflineCost .infinite processingTime =
      obligatoryFixedWordExcess
        (obligatorySymbolOutcomeFn
          (Online.adaptiveRuntimeSymbols processingTime))
        (Online.adaptiveRuntimeProcessing processingTime) := by
  dsimp only
  rw [Online.run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_symbolicALG
    n .infinite processingTime hnonneg]
  rw [obligatoryFixedWordExcess_eq_pairObjectives]
  rw [adaptiveRuntime_vectorOfflineCost_infinite]

/-- Exact finite-cap competitive excess of the same executable adaptive run,
with the offline processing coordinates clipped at `u - 1`. -/
theorem adaptiveRuntime_plateauExcess_eq
    (n : ℕ) (u : ℝ) (processingTime : Online.Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    let result :=
      Online.run (.finite u) (Online.fixedOracle processingTime)
        (Online.parameterizedAdaptiveThresholdStrategy n rhoStar)
        (2 * n + 1)
    Online.runCompletionCost (.finite u) processingTime result -
        RStar * vectorOfflineCost (.finite u) processingTime =
      plateauFixedWordExcess u
        (obligatorySymbolOutcomeFn
          (Online.adaptiveRuntimeSymbols processingTime))
        (Online.adaptiveRuntimeProcessing processingTime) := by
  dsimp only
  rw [Online.run_parameterizedAdaptiveThresholdStrategy_completionCost_eq_symbolicALG
    n (.finite u) processingTime hnonneg]
  rw [plateauFixedWordExcess_eq_pairObjectives]
  rw [adaptiveRuntime_vectorOfflineCost_finite]

namespace UpperBound

/-- The operational-to-static bridge required at the obligatory endpoint. -/
theorem obligatoryBoundaryBridge_verified :
    ObligatoryBoundaryBridge := by
  intro n input
  have hnonneg : ∀ job, 0 ≤ input.processingTime job :=
    fun job => input.admissible job
  obtain ⟨outcomes, hlength, hbound⟩ :=
    Online.exists_obligatoryBoundaryWord_ge_adaptiveRuntime
      input.processingTime hnonneg
  refine ⟨outcomes, hlength, ?_⟩
  calc
    strategyCost .infinite obligatoryStrategy n input -
          RStar * input.offlineCost =
        obligatoryFixedWordExcess
          (obligatorySymbolOutcomeFn
            (Online.adaptiveRuntimeSymbols input.processingTime))
          (Online.adaptiveRuntimeProcessing input.processingTime) := by
      simpa [strategyCost, FixedInput.onlineCost, FixedInput.runResult,
        analysisFuel, obligatoryStrategy, FixedInput.offlineCost,
        Online.parameterizedAdaptiveThresholdStrategy_rhoStar] using
        (adaptiveRuntime_obligatoryExcess_eq
          n input.processingTime hnonneg)
    _ ≤ obligatoryBoundaryExcess outcomes := hbound

/-- The operational-to-static bridge on the finite high plateau. -/
theorem plateauBoundaryBridge_verified
    {u : ℝ} (hu : zStar ≤ u) :
    PlateauBoundaryBridge u := by
  intro n input
  have hprocessing :
      ∀ job, 0 ≤ input.processingTime job ∧
        input.processingTime job ≤ u :=
    fun job => input.admissible job
  have hnonneg : ∀ job, 0 ≤ input.processingTime job :=
    fun job => (hprocessing job).1
  obtain ⟨outcomes, hlength, hbound⟩ :=
    exists_plateauBoundaryWord_ge_adaptiveRuntime
      hu input.processingTime hprocessing
  refine ⟨outcomes, hlength, ?_⟩
  calc
    strategyCost (.finite u) plateauStrategy n input -
          RStar * input.offlineCost =
        plateauFixedWordExcess u
          (obligatorySymbolOutcomeFn
            (Online.adaptiveRuntimeSymbols input.processingTime))
          (Online.adaptiveRuntimeProcessing input.processingTime) := by
      simpa [strategyCost, FixedInput.onlineCost, FixedInput.runResult,
        analysisFuel, plateauStrategy, FixedInput.offlineCost] using
        (adaptiveRuntime_plateauExcess_eq
          n u input.processingTime hnonneg)
    _ ≤
        -rhoStar * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (parameterizedOrdinaryReward rhoStar)
            (initialParameterizedAnalysisState outcomes.length)
            outcomes := hbound

end UpperBound

end

end SchedulingPaper
