import SchedulingPaper.TestProcessPairShape
import Mathlib.Tactic

/-!
# Exact runtime accounting for completed test/process executions

This module combines the generic completion-label decomposition with the
canonical one- and two-label trace shapes.  The result is an exact
diagonal-plus-unordered-pairs formula for every concrete ForcedPrefixUTE
run, before any endpoint inequality is applied.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Exact operational cost formula for a completed ForcedPrefixUTE run.
The diagonal is already evaluated; each unordered-pair charge remains in
its literal transcript form for the strategy-specific symbolic reduction. -/
theorem run_forcedPrefixUTEStrategy_completionCost_eq_self_add_pairs
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    runCompletionCost cap processingTime result =
      Finset.univ.sum
          (fun job : Label n => (1 : ℝ) + processingTime job) +
        Finset.univ.sum (fun left : Label n =>
          (Finset.univ.filter
            (fun right : Label n => left < right)).sum
              (fun right =>
                tracePairCharge cap processingTime
                  result.config.transcript left right)) := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n u b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n u b cap processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hperm :
      (result.config.transcript.completionLabels processingTime).Perm
        (List.ofFn id) := by
    simpa [result] using
      run_forcedPrefixUTEStrategy_completionLabels_perm
        n u b cap processingTime
  have hdecomposition :=
    completionCost_eq_traceSelf_add_pairs cap processingTime
      result.config.transcript hperm
  have hself :
      ∀ job : Label n,
        traceSelfCharge cap processingTime
            result.config.transcript job =
          1 + processingTime job := by
    intro job
    apply traceSelfCharge_eq_one_add_of_projection
    · exact
        hrun.2.2.2.2.1.terminal_selfProjection
          hrun.2.2.1 hallTests hallProcessed job
    · rfl
  unfold runCompletionCost
  rw [hdecomposition]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro job _hjob
    exact hself job
  · rfl

/-- The corresponding exact three-shape classification for every pair in
the same concrete run. -/
theorem run_forcedPrefixUTEStrategy_pairProjection_shapes
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    result.config.transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .processed left,
          .testResult right (processingTime right),
          .processed right] ∨
      result.config.transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed right, .processed left] ∨
      result.config.transcript.pairProjection left right =
        [.testResult left (processingTime left),
          .testResult right (processingTime right),
          .processed left, .processed right] := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n u b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n u b cap processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  exact
    hrun.2.2.2.2.1.terminal_pairProjection_shapes
      hrun.2.2.1 hallTests hallProcessed horder

end

end SchedulingPaper.Online
