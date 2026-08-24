import SchedulingPaper.RevealingOptimizationLearnedPilot
import SchedulingPaper.RandomizedOperationalAnalytic
import Mathlib.Tactic

/-!
# Operational analysis of the learned revealing pilot

The input-dependent objects in this file occur only in theorem statements.
The executable policy still receives just its public transcript.  We first
identify its complete run with the fixed pilot/quota run selected by the
realized pilot prefix, and then identify that prefix's histogram with the
usual without-replacement sample histogram.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace LearnedPilotAnalysis

open Online
open QuotaStrategy
open PilotStrategy
open LearnedPilot
open QuotaFluid
open Randomized
open RandomizedOptional
open RandomizedObligatory

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Once the input is fixed for analysis, the transcript learner produces
exactly one fixed quota and selector.  This is equality of complete runs,
not merely equality of their terminal costs. -/
theorem runFuel_learnedPilotQuotaStrategy_eq_adaptive
    {processing : Online.Label n → ℝ} {Q k : ℕ}
    (hQ : Q ≤ n) (u : ℝ) (rule : PilotRule n)
    (hQdef : Q = max k
      (rule ((Online.fixedTestResults processing).take k)).1)
    (fuel : ℕ) (config : Online.Config n)
    (hgood : QuotaStrategy.Config.Invariant processing Q config) :
    Online.runFuel (.finite u) (Online.fixedOracle processing)
        (learnedPilotQuotaStrategy n k rule) fuel config =
      Online.runFuel (.finite u) (Online.fixedOracle processing)
        (adaptiveQuotaStrategy n Q
          (pilotPhaseSelector k
            (rule ((Online.fixedTestResults processing).take k)).2))
        fuel config := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      by_cases hzero : config.remainingWork = 0
      · have hlearned := learnedPilotQuotaStrategy_stop_of_zero
          hgood hQ hzero rule hQdef
        have hfixed := adaptiveQuotaStrategy_stop_of_zero hgood hzero
          (pilotPhaseSelector k
            (rule ((Online.fixedTestResults processing).take k)).2)
        simp [Online.runFuel, hlearned, hfixed]
      · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
        obtain ⟨action, next, hchosen, hlegal, hnextGood, _hdec⟩ :=
          learnedPilotQuotaStrategy_progress hgood hQ hpos u rule hQdef
        have heq := learnedPilotQuotaStrategy_eq_fixed_of_invariant
          hgood hQ rule hQdef
        have hfixed : adaptiveQuotaStrategy n Q
            (pilotPhaseSelector k
              (rule ((Online.fixedTestResults processing).take k)).2)
            config.transcript = some action := by
          rw [← heq]
          exact hchosen
        simp only [Online.runFuel, hchosen, hfixed, hlegal]
        exact ih next hnextGood

theorem run_learnedPilotQuotaStrategy_eq_pilotQuotaStrategy
    {n k : ℕ} (hk : k ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (rule : PilotRule n)
    (hrule : (rule ((Online.fixedTestResults processing).take k)).1 ≤ n) :
    Online.run (.finite u) (Online.fixedOracle processing)
        (learnedPilotQuotaStrategy n k rule) (2 * n + 1) =
      Online.run (.finite u) (Online.fixedOracle processing)
        (pilotQuotaStrategy n k
          (rule ((Online.fixedTestResults processing).take k)).1
          (rule ((Online.fixedTestResults processing).take k)).2)
        (2 * n + 1) := by
  let Q := max k (rule ((Online.fixedTestResults processing).take k)).1
  have hQ : Q ≤ n := max_le hk hrule
  unfold Online.run pilotQuotaStrategy
  exact runFuel_learnedPilotQuotaStrategy_eq_adaptive hQ u rule rfl _ _
    (QuotaStrategy.Config.initial_invariant processing Q)

/-- Private random placement of the literal transcript-learned policy. -/
def randomizedLearnedPilotQuotaStrategy
    (n k : ℕ) (rule : PilotRule n) (order : Equiv.Perm (Fin n)) :
    Online.Strategy n :=
  (learnedPilotQuotaStrategy n k rule).relabel order

theorem randomizedLearnedGridPilotQuotaStrategy_completes
    {n k : ℕ} (hk : k ≤ n) (u : ℝ)
    (processing : Fin n → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : ℝ → Option ι) (price : ι → ℝ)
    (order : Equiv.Perm (Fin n)) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (randomizedLearnedPilotQuotaStrategy n k
          (gridPilotRule k category price u) order)
        (2 * n + 1)).config.jobs job = .done := by
  rw [randomizedLearnedPilotQuotaStrategy, Online.run_relabel_config]
  intro job
  exact learnedGridPilotQuotaStrategy_completes hk u
    (fun virtual => processing (order virtual)) category price
      (order.symm job)

/-! ## The public transcript histogram is the sampling histogram -/

theorem resultHistogram_fixedTake_eq_sampleHistogram
    (k r : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (processing : Fin (k + r) → ℝ)
    (valueCategory : ℝ → Option ι)
    (category : Fin (k + r) → Option ι)
    (order : Equiv.Perm (Fin (k + r)))
    (hcategory : ∀ job,
      valueCategory (processing job) = category job) :
    resultHistogram k valueCategory
        ((Online.fixedTestResults
          (fun virtual => processing (order virtual))).take k) =
      sampleHistogram (firstBlockPositions k r) category order := by
  funext cell
  unfold resultHistogram sampleHistogram sampleCategoryFraction
  have hvalues := map_snd_fixedTestResults_take_add k r
    (fun virtual => processing (order virtual))
  have hfilter :
      (((Online.fixedTestResults
        (fun virtual => processing (order virtual))).take k).filter
          fun result => valueCategory result.2 = cell).length =
        ((((Online.fixedTestResults
          (fun virtual => processing (order virtual))).take k).map
            Prod.snd).filter fun value => valueCategory value = cell).length := by
    induction (Online.fixedTestResults
      (fun virtual => processing (order virtual))).take k with
    | nil => rfl
    | cons result results ih =>
        simp only [List.filter_cons, List.map_cons]
        split <;> simp_all
  rw [hfilter, hvalues]
  rw [length_filter_ofFn]
  rw [show (firstBlockPositions k r).card = k by simp]
  unfold permutationSampleSum categoryClass categoryIndicator
  apply congrArg (fun numerator : ℝ => numerator / k)
  norm_cast
  have hsum := Equiv.sum_comp (firstBlockEquiv k r)
    (fun position : ↥(firstBlockPositions k r) =>
      if order position.val ∈ categoryClass category cell
        then (1 : ℕ) else 0)
  simpa [firstBlockEquiv, categoryClass, hcategory] using hsum

theorem gridPilotRule_fixedTake
    (k r : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (processing : Fin (k + r) → ℝ)
    (valueCategory : ℝ → Option ι)
    (category : Fin (k + r) → Option ι)
    (price : ι → ℝ) (u : ℝ)
    (order : Equiv.Perm (Fin (k + r)))
    (hcategory : ∀ job,
      valueCategory (processing job) = category job) :
    gridPilotRule k valueCategory price u
        ((Online.fixedTestResults
          (fun virtual => processing (order virtual))).take k) =
      let T := InstanceLearning.minimizingTemplate (n := k + r)
        (sampleHistogram (firstBlockPositions k r) category order) price u
      (T.quota.val, templateLowSelector price T) := by
  unfold gridPilotRule
  rw [resultHistogram_fixedTake_eq_sampleHistogram k r processing
    valueCategory category order hcategory]

end

end LearnedPilotAnalysis
end RevealingOptimization
end SchedulingPaper
