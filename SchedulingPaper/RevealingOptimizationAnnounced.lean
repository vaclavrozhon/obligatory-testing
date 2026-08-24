import SchedulingPaper.ObligatoryInstanceBenchmark
import Mathlib.Tactic

/-!
# Explicit finite announced endpoint for revealing optimization

The survival-function development identifies the exact finite formula of
the stationary-or-raw endpoint.  This file connects that formula to literal
finite operation words.  In the stationary branch, labels are discovered in
a uniformly random order, short jobs are completed immediately, and the
deferred tail is completed in SPT order.  In the raw branch, all jobs are
run as equal raw blocks.
-/

namespace SchedulingPaper
namespace RevealingOptimization

open Randomized
open RandomizedObligatory
open ObligatoryInstance

noncomputable section

/-- Uniform expected completion cost of the explicit announced endpoint
template chosen by the maximum-density threshold. -/
def empiricalAnnouncedTemplateAverage {n : ℕ}
    (p : Fin n → ℝ) (u τ : ℝ) : ℝ :=
  if τ ≤ u then empiricalStationaryTemplateAverage p τ
  else empiricalRawCost n u

/-- The explicit announced operation word has exactly the aggregate finite
cost used by the survival reduction. -/
theorem empiricalAnnouncedTemplateAverage_eq_finiteCost
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (u τ : ℝ) :
    empiricalAnnouncedTemplateAverage p u τ =
      if τ ≤ u then empiricalStationaryFiniteCost p τ
      else empiricalRawCost n u := by
  unfold empiricalAnnouncedTemplateAverage
  by_cases hτu : τ ≤ u
  · rw [if_pos hτu, if_pos hτu,
      empiricalStationaryTemplateAverage_eq_finiteCost hn p τ]
  · rw [if_neg hτu, if_neg hτu]

/-- Fully concrete finite announced endpoint.  For every nonempty bounded
input, Lean constructs the threshold and a literal stationary-or-raw
template whose uniform expected completion cost obeys the exact randomized
revealing curve up to the displayed linear diagonal term. -/
theorem announcedTemplate_curve_upper
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u : ℝ} (hu : 1 < u)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u) :
    ∃ τ, 1 ≤ τ ∧
      (∑ job, max (τ - p job) 0 = n) ∧
      empiricalAnnouncedTemplateAverage p u τ ≤
        randomizedCurve u * empiricalRevealingOfflineCost u p +
          (n : ℝ) * (1 + u) / 2 := by
  obtain ⟨τ, hτ, hthreshold, hcost⟩ :=
    exists_empiricalAnnouncedCost_le_curve_mul_offline_add_linear
      hn p hu hp0 hpu
  refine ⟨τ, hτ, hthreshold, ?_⟩
  rw [empiricalAnnouncedTemplateAverage_eq_finiteCost hn p u τ]
  exact hcost

end

end RevealingOptimization
end SchedulingPaper
