import SchedulingPaper.TestProcessUTEWord
import SchedulingPaper.FinPairObjective
import SchedulingPaper.HiddenStoppingCostAccounting
import Mathlib.Tactic

/-!
# Exact finite-cap runtime bridge for a fixed UTE word

This module identifies both sides of the competitive excess of a concrete
ForcedPrefixUTE execution with the coordinatewise-convex fixed-word
functional used by the endpoint reduction.
-/

namespace SchedulingPaper

noncomputable section

open LowerBound

def uteFixedWordOPT {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : ℝ :=
  Finset.univ.sum
      (fun i : Fin n => uteEffectiveAt s (processing i)) +
    Finset.univ.sum (fun i : Fin n =>
      (Finset.univ.filter (fun j : Fin n => i < j)).sum
        (fun j =>
          uteFixedOPTPairCharge s (processing i) (processing j)))

theorem uteFixedWordExcess_eq_alg_sub_rho_mul_opt
    {n : ℕ} (s : ℝ) (word : UTEFixedSymbolicWord n)
    (processing : Fin n → ℝ) :
    uteFixedWordExcess s word processing =
      uteFixedWordALG word processing -
        uteRho s * uteFixedWordOPT s processing := by
  unfold uteFixedWordExcess uteFixedWordALG uteFixedWordOPT
    uteFixedSelfExcessAt uteFixedPairExcessAt
  simp only [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  ring

theorem vectorOfflineCost_finite_add_one_eq_uteFixedWordOPT
    {n : ℕ} (s : ℝ) (processing : Online.Label n → ℝ) :
    vectorOfflineCost (.finite (s + 1)) processing =
      uteFixedWordOPT s processing := by
  rw [vectorOfflineCost_eq_pairCost]
  unfold vectorEffectiveLengths
  rw [pairCost_ofFn_eq_finSelfPairSum]
  unfold uteFixedWordOPT uteFixedOPTPairCharge
  have heffective :
      ∀ i : Fin n,
        effectiveLength (.finite (s + 1)) (processing i) =
          uteEffectiveAt s (processing i) := by
    intro i
    simp [effectiveLength, uteEffectiveAt, min_comm]
  simp_rw [heffective]

namespace Online

/-- Exact operational excess of ForcedPrefixUTE as one fixed-word excess. -/
theorem run_forcedPrefixUTEStrategy_excess_eq_uteFixedWordExcess
    (n : ℕ) (s b : ℝ)
    (processingTime : Label n → ℝ) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
    runCompletionCost (.finite (s + 1)) processingTime result -
        uteRho s *
          vectorOfflineCost (.finite (s + 1)) processingTime =
      uteFixedWordExcess s
        (transcriptUTEFixedSymbolicWord processingTime
          result.config.transcript)
        processingTime := by
  dsimp only
  let result :=
    run (.finite (s + 1)) (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
  rw [run_forcedPrefixUTEStrategy_completionCost_eq_uteFixedWordALG,
    vectorOfflineCost_finite_add_one_eq_uteFixedWordOPT,
    uteFixedWordExcess_eq_alg_sub_rho_mul_opt]

end Online

end

end SchedulingPaper
