import SchedulingPaper.ObligatoryPaperAlgorithm
import SchedulingPaper.RandomizedRelabelRun
import Mathlib.Tactic

/-!
# The paper's obligatory algorithm for every input size

`ObligatoryPaperAlgorithm` analyzes the asymptotically relevant growing
branch.  This file packages it together with the literal `n < 16` branch
printed in Algorithm 2.  It therefore gives one total strategy family, with
no side condition hidden in its definition.
-/

namespace SchedulingPaper
namespace ObligatoryPaper

open RandomizedObligatory
open Online

noncomputable section

/-- Testing every job and then using the shortest revealed remaining job. -/
def testAllThenSPTStrategy (n : ℕ) : Online.Strategy n :=
  Online.testProcessStrategy fun _ => none

theorem testAllThenSPTStrategy_completes
    (n : ℕ) (processing : Fin n → ℝ) :
    ∀ job,
      (Online.run .infinite (Online.fixedOracle processing)
        (testAllThenSPTStrategy n) (2 * n + 1)).config.jobs job = .done := by
  have hselect : Online.SelectsLastTest (fun _ : Online.Transcript n => none) := by
    intro transcript job h
    simp at h
  simpa [testAllThenSPTStrategy] using
    (Online.runFuel_testProcessStrategy_completed .infinite
      (Online.fixedOracle processing) hselect 0).2

/-- The displayed mesh is positive as soon as Algorithm 2 leaves its
small-input branch. -/
theorem paperMesh_pos_of_sixteen_le (n : ℕ) (hn : 16 ≤ n) :
    0 < paperMesh n := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hrootNonneg := fourthRoot_nonneg n
  have hroot : 2 ≤ fourthRoot n := by
    by_contra h
    have hlt : fourthRoot n < 2 := lt_of_not_ge h
    have hsquare : (fourthRoot n) ^ 2 < 4 := by nlinarith
    have hfour : (fourthRoot n) ^ 4 < 16 := by
      nlinarith [sq_nonneg ((fourthRoot n) ^ 2)]
    rw [fourthRoot_pow_four] at hfour
    linarith
  have hd : 0 < paperBins n := by
    unfold paperBins concreteBins
    exact Nat.floor_pos.mpr (by linarith)
  have hdR : (0 : ℝ) < paperBins n := by exact_mod_cast hd
  have hgrowth : 0 ≤ paperGrowth n := by
    unfold paperGrowth
    exact Real.rpow_nonneg hrootNonneg _
  unfold paperMesh paperCutoff
  exact div_pos (by linarith) hdR

/-- Algorithm 2 exactly as printed: test-all/SPT for `n < 16`, and the
growing-cutoff learner otherwise.  The permutation is still an explicit
private seed in both branches. -/
def fullPaperStrategy (n : ℕ) :
    Equiv.Perm (Fin n) → Online.Strategy n :=
  if hsmall : n < 16 then
    fun order => (testAllThenSPTStrategy n).relabel order
  else
    Online.randomizedGrowingObligatoryStrategy n
      (paperPilotSize n) (paperBins n) (paperCutoff n) (paperMesh n)
      (paperMesh_pos_of_sixteen_le n (Nat.le_of_not_gt hsmall))

theorem fullPaperStrategy_completes
    (n : ℕ) (processing : Fin n → ℝ)
    (order : Equiv.Perm (Fin n)) :
    ∀ job,
      (Online.run .infinite (Online.fixedOracle processing)
        (fullPaperStrategy n order) (2 * n + 1)).config.jobs job = .done := by
  by_cases hsmall : n < 16
  · rw [fullPaperStrategy, dif_pos hsmall]
    rw [Online.run_relabel_config]
    intro job
    change (Online.run .infinite
      (Online.fixedOracle (fun virtual => processing (order virtual)))
      (testAllThenSPTStrategy n) (2 * n + 1)).config.jobs
        (order.symm job) = .done
    exact testAllThenSPTStrategy_completes n
      (fun virtual => processing (order virtual)) (order.symm job)
  · rw [fullPaperStrategy, dif_neg hsmall]
    unfold Online.randomizedGrowingObligatoryStrategy
    rw [Online.run_relabel_config]
    intro job
    change (Online.run .infinite
      (Online.fixedOracle (fun virtual => processing (order virtual)))
      (Online.growingObligatoryStrategy n (paperPilotSize n) (paperBins n)
        (paperCutoff n) (paperMesh n)
        (paperMesh_pos_of_sixteen_le n (Nat.le_of_not_gt hsmall)))
      (2 * n + 1)).config.jobs (order.symm job) = .done
    exact (Online.run_growingObligatoryStrategy_completed n
      (paperPilotSize n) (paperBins n) (paperCutoff n) (paperMesh n)
      (paperMesh_pos_of_sixteen_le n (Nat.le_of_not_gt hsmall))
      (Online.fixedOracle (fun virtual => processing (order virtual)))).2
      (order.symm job)

end
end ObligatoryPaper
end SchedulingPaper
