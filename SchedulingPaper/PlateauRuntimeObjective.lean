import SchedulingPaper.AdaptiveRuntimeAccounting
import SchedulingPaper.PlateauEndpointReduction
import SchedulingPaper.FinPairObjective

/-!
# Exact finite-cap objective of the adaptive runtime word

This file identifies the clipped pair objective used by the high-plateau
endpoint reduction with the genuine finite-cap offline optimum.
-/

namespace SchedulingPaper

noncomputable section

open Online
open LowerBound

/-- Finite-index normal form of the recursive obligatory offline pair
objective. -/
theorem obligatoryOPTPairObjective_jobsOfFunctions_eq_finSums
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    obligatoryOPTPairObjective
        (obligatoryJobsOfFunctions outcome processing) =
      Finset.univ.sum
          (fun i : Fin n => (1 : ℝ) + processing i) +
        Finset.univ.sum (fun i : Fin n =>
          (Finset.univ.filter
            (fun j : Fin n => i < j)).sum
              (fun j =>
                1 + min (processing i) (processing j))) := by
  rw [obligatoryOPTPairObjective_eq_pairCost]
  rw [show
      (obligatoryJobsOfFunctions outcome processing).map
          (fun job => 1 + job.processing) =
        List.ofFn (fun i => 1 + processing i) by
    unfold obligatoryJobsOfFunctions
    simp only [List.map_ofFn]
    rfl]
  rw [pairCost_ofFn_eq_finSelfPairSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simpa [add_comm] using min_add_add_left 1 (processing i) (processing j)

/-- The finite-cap fixed-word functional is the concrete ALG pair objective
minus `RStar` times the same word's clipped offline pair objective. -/
theorem plateauFixedWordExcess_eq_pairObjectives
    {n : ℕ} (u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    plateauFixedWordExcess u outcome processing =
      obligatoryALGPairObjective
          (obligatoryJobsOfFunctions outcome processing) -
        RStar *
          obligatoryOPTPairObjective
            (obligatoryJobsOfFunctions outcome
              (fun i => plateauClippedProcessing u (processing i))) := by
  rw [Online.obligatoryALGPairObjective_jobsOfFunctions_eq_finSums,
    obligatoryOPTPairObjective_jobsOfFunctions_eq_finSums]
  unfold plateauFixedWordExcess plateauSelfExcessAt
    plateauPairExcessAt
  simp only [Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add, mul_one]
  ring

/-- Clipping runtime processing at `u - 1` produces exactly the effective
lengths of the genuine finite-cap instance. -/
theorem adaptiveRuntime_vectorOfflineCost_finite
    (u : ℝ) (processingTime : Online.Label n → ℝ) :
    obligatoryOPTPairObjective
        (obligatoryJobsOfFunctions
          (obligatorySymbolOutcomeFn
            (Online.adaptiveRuntimeSymbols processingTime))
          (fun i =>
            plateauClippedProcessing u
              (Online.adaptiveRuntimeProcessing processingTime i))) =
      vectorOfflineCost (.finite u) processingTime := by
  rw [obligatoryOPTPairObjective_jobsOfFunctions]
  unfold vectorOfflineCost vectorEffectiveLengths
  congr 2
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_eq_getElem]
    simp only [List.getElem_ofFn]
    simp [plateauClippedProcessing, Online.adaptiveRuntimeProcessing,
      effectiveLength]
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

end

end SchedulingPaper
