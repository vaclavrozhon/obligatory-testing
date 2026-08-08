import SchedulingPaper.RandomizedOptionalObservedTrace
import SchedulingPaper.RandomizedOptionalWorkInvariant
import Mathlib.Tactic

/-!
# Terminal work of a completed observed optional-testing run

The adaptive policy may interleave tests, known processing, and blind jobs,
but after completion its total elapsed work is exactly the number of tests
plus the sum of all processing times.  The occurrence-token permutation then
turns the latter into the empirical mean term used by the fluid envelope.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedTrace

open ObservedOnline
open TraceBijection
open Randomized

noncomputable section

theorem settled_elapsed_eq_test_sum_add_population_sum
    {n : ℕ} (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) :
    elapsed (placedProcessing p σ)
        (settledRun p policy.strategy σ).config.transcript =
      (∑ k, compiledTestSelector p policy k
        (revealOrder (touchTrace p policy) σ)) + ∑ occurrence, p occurrence := by
  let transcript := (settledRun p policy.strategy σ).config.transcript
  have hwork := run_processingWork_eq_sum_of_done
    (placedProcessing p σ) policy.strategy (2 * n + 1) (policy.completes σ)
  have hworkSettled :
      processedWork (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript +
        blindWork (settledRun p policy.strategy σ).config.transcript =
      ∑ job, placedProcessing p σ job := by
    simpa [settledRun] using hwork
  have htestRaw := compiled_test_class_sum_eq_operational
    p policy σ (fun _ => true)
  have htest :
      (∑ k, compiledTestSelector p policy k
        (revealOrder (touchTrace p policy) σ)) =
        (transcript.testResults.length : ℝ) := by
    simpa [transcript] using htestRaw
  have hsumPlaced :
      (∑ job, placedProcessing p σ job) = ∑ occurrence, p occurrence := by
    simpa [placedProcessing] using Equiv.sum_comp σ p
  rw [elapsed_eq_test_add_processed_add_blind]
  calc
    (transcript.testResults.length : ℝ) +
          processedWork (placedProcessing p σ) transcript + blindWork transcript =
        (transcript.testResults.length : ℝ) +
          (processedWork (placedProcessing p σ) transcript + blindWork transcript) := by
            ring
    _ = (transcript.testResults.length : ℝ) + ∑ occurrence, p occurrence := by
          rw [hworkSettled, hsumPlaced]
    _ = (∑ k, compiledTestSelector p policy k
          (revealOrder (touchTrace p policy) σ)) + ∑ occurrence, p occurrence := by
          rw [htest]

theorem settled_elapsed_div_eq_testFraction_add_mean
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) {μ : ℝ}
    (hμDef : μ = populationMean p) :
    elapsed (placedProcessing p σ)
        (settledRun p policy.strategy σ).config.transcript / n =
      ((∑ k, compiledTestSelector p policy k
        (revealOrder (touchTrace p policy) σ)) / n) + μ := by
  rw [settled_elapsed_eq_test_sum_add_population_sum]
  rw [hμDef]
  simp only [populationMean, Fintype.card_fin]
  have hnR : (0 : ℝ) ≠ n := by exact_mod_cast (Ne.symm hn.ne')
  field_simp [hnR]

end

end ObservedTrace
end RandomizedOptional
end SchedulingPaper
