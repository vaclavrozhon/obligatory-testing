import SchedulingPaper.AdaptiveRuntimeEndpoint
import SchedulingPaper.LowerBoundAssembly

/-!
# Static objective identities for the obligatory runtime word

These are the order-independent algebraic identities needed after the
operational transcript has been reduced to diagonal and unordered-pair
charges.
-/

namespace SchedulingPaper

noncomputable section

open LowerBound

theorem obligatoryOPTPairObjective_eq_pairCost :
    ∀ jobs : List ObligatoryBoundaryJob,
      obligatoryOPTPairObjective jobs =
        pairCost
          (jobs.map fun job => 1 + job.processing) := by
  intro jobs
  induction jobs with
  | nil =>
      simp [obligatoryOPTPairObjective, pairCost]
  | cons job jobs ih =>
      simp only [obligatoryOPTPairObjective, List.map_cons]
      rw [ih]
      unfold pairCost
      simp only [List.sum_cons, pairMinCost_cons]
      have hrow :
          (jobs.map (obligatoryOPTPairCharge job)).sum =
            ((jobs.map fun tail => 1 + tail.processing).map
              (min (1 + job.processing))).sum := by
        apply congrArg List.sum
        simp only [List.map_map]
        apply List.map_congr_left
        intro tail htail
        simp only [Function.comp_apply]
        unfold obligatoryOPTPairCharge
        rw [show
          min (1 + job.processing) (1 + tail.processing) =
            1 + min job.processing tail.processing by
              exact min_add_add_left 1 _ _]
      rw [hrow]
      ring

theorem obligatoryOPTPairObjective_jobsOfFunctions
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    obligatoryOPTPairObjective
        (obligatoryJobsOfFunctions outcome processing) =
      prefixCost
        (shortestFirst
          (List.ofFn fun job => 1 + processing job)) := by
  rw [obligatoryOPTPairObjective_eq_pairCost,
    ← shortestFirst_pair_formula]
  congr 2
  unfold obligatoryJobsOfFunctions
  simp only [List.map_ofFn]
  rfl

theorem adaptiveRuntimeProcessing_cast
    (processingTime : Online.Label n → ℝ)
    (job : Online.Label n) :
    Online.adaptiveRuntimeProcessing processingTime
        ⟨job.val, by
          simpa using job.isLt⟩ =
      processingTime job := by
  simp [Online.adaptiveRuntimeProcessing]

theorem adaptiveRuntime_vectorOfflineCost_infinite
    (processingTime : Online.Label n → ℝ) :
    obligatoryOPTPairObjective
        (obligatoryJobsOfFunctions
          (obligatorySymbolOutcomeFn
            (Online.adaptiveRuntimeSymbols processingTime))
          (Online.adaptiveRuntimeProcessing processingTime)) =
      vectorOfflineCost .infinite processingTime := by
  rw [obligatoryOPTPairObjective_jobsOfFunctions]
  unfold vectorOfflineCost vectorEffectiveLengths
  congr 2
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_eq_getElem]
    simp [Online.adaptiveRuntimeProcessing]

end

end SchedulingPaper
