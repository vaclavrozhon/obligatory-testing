import SchedulingPaper.RandomizedAnnouncedFluid
import Mathlib.Tactic

/-!
# Algebra for a sample-first stationary discovery order

The unknown-multiset algorithm tests a random sample before running the
learned stationary policy on the remaining labels.  This file isolates the
exact cross-term created by forcing the sample blocks before the remainder.
-/

namespace SchedulingPaper
namespace Randomized

noncomputable section

/-- Expected early-job cost when the sample blocks are uniformly ordered
first and the remaining blocks are uniformly ordered second. -/
def sampleFirstEarlyCost
    (eSample eRest workSample workRest
      selfSample selfRest : ℝ) : ℝ :=
  (eSample * workSample + selfSample) / 2 +
    eRest * workSample +
    (eRest * workRest + selfRest) / 2

/-- Expected early-job cost under one fully uniform discovery order. -/
def uniformEarlyCost
    (eSample eRest workSample workRest
      selfSample selfRest : ℝ) : ℝ :=
  ((eSample + eRest) * (workSample + workRest) +
    selfSample + selfRest) / 2

/-- Forcing the sample first changes only one antisymmetric cross term. -/
theorem sampleFirstEarlyCost_sub_uniformEarlyCost
    (eSample eRest workSample workRest
      selfSample selfRest : ℝ) :
    sampleFirstEarlyCost eSample eRest workSample workRest
        selfSample selfRest -
      uniformEarlyCost eSample eRest workSample workRest
        selfSample selfRest =
      (eRest * workSample - eSample * workRest) / 2 := by
  unfold sampleFirstEarlyCost uniformEarlyCost
  ring

/-- Dropping the favorable sample-before-rest cross term gives the simple
upper bound used in the sampling theorem. -/
theorem sampleFirstEarlyCost_le_uniform_add
    {eSample eRest workSample workRest selfSample selfRest : ℝ}
    (heSample : 0 ≤ eSample)
    (hworkRest : 0 ≤ workRest) :
    sampleFirstEarlyCost eSample eRest workSample workRest
        selfSample selfRest ≤
      uniformEarlyCost eSample eRest workSample workRest
        selfSample selfRest + eRest * workSample / 2 := by
  have hidentity := sampleFirstEarlyCost_sub_uniformEarlyCost
    eSample eRest workSample workRest selfSample selfRest
  have hproduct : 0 ≤ eSample * workRest :=
    mul_nonneg heSample hworkRest
  linarith

end

end Randomized
end SchedulingPaper
