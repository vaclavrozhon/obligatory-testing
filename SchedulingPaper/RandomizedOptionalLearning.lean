import SchedulingPaper.RandomizedOptionalKernel
import SchedulingPaper.RandomizedHistogramConcentration

/-!
# Optional testing: the pilot-learning wrapper

This file combines the finite histogram concentration theorem with the
empirical-minimizer sandwich.  It is the abstract statistical core of the
unknown-multiset upper bound; the scheduling implementation contributes a
separate `o(n^2)` pilot-placement term.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

/-- A uniform sample, a template family uniformly Lipschitz in histogram
`L¹`, and empirical minimization imply the usual `2 C sqrt(K/k)` excess on
the untouched target histogram. -/
theorem uniformSample_empirical_minimizer_le
    {α β Template : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (category : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    {sampleValue : Equiv.Perm α → Template → ℝ}
    {targetValue : Template → ℝ}
    {chosen : Equiv.Perm α → Template} {targetMin : Template}
    {C : ℝ} (hC : 0 ≤ C)
    (hstable : ∀ σ π,
      |sampleValue σ π - targetValue π| ≤
        C * Randomized.histogramL1Error S category σ)
    (hchosen : ∀ σ π,
      sampleValue σ (chosen σ) ≤ sampleValue σ π) :
    Randomized.uniformAverage (fun σ => targetValue (chosen σ)) ≤
      targetValue targetMin +
        2 * C * Real.sqrt ((Fintype.card β : ℝ) / S.card) := by
  have hlearn := uniformAverage_empirical_minimizer_transfer
    (targetMin := targetMin) hstable hchosen
  have hhist := Randomized.uniformAverage_histogramL1Error_le_sqrt
    S category hS hn
  have hscaled :
      2 * C * Randomized.uniformAverage
          (Randomized.histogramL1Error S category) ≤
        2 * C * Real.sqrt ((Fintype.card β : ℝ) / S.card) :=
    mul_le_mul_of_nonneg_left hhist (mul_nonneg (by norm_num) hC)
  linarith

end

end RandomizedOptional
end SchedulingPaper
