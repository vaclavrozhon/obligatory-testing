import SchedulingPaper.RandomizedOptionalGoodEventAverage
import SchedulingPaper.RandomizedOptionalFluid

/-!
# Model-independent fluid-to-finite transfer

This file contains the two pieces of bookkeeping shared by the revealing,
obligatory, and blind-execution instance-optimality arguments.  Model-specific
files only have to supply a completion-envelope comparison and a stability
metric.  Probability, edit losses, and empirical minimization are handled
here once.
-/

namespace SchedulingPaper
namespace FluidToFinite

open Randomized

noncomputable section

/-- Finite-probability form of the fluid-to-finite completion transfer.

`cost` is already normalized by `n²`.  On every good seed, the scheduling
and completion-envelope argument supplies the pathwise lower bound in
`hgood`.  The theorem performs exactly the last averaging step, including
the loss on the bad event. -/
theorem completion_transfer_uniform
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (cost : Ω → ℝ) (Bad : Ω → Prop) [DecidablePred Bad]
    {fluidValue editError horizontalError horizon verticalError
      failureProbability fluidUpper : ℝ}
    (hcost0 : ∀ ω, 0 ≤ cost ω)
    (hgood : ∀ ω, ¬ Bad ω →
      fluidValue - editError - horizontalError -
          horizon * verticalError ≤ cost ω)
    (hfluid0 : 0 ≤ fluidValue)
    (hfluidUpper : fluidValue ≤ fluidUpper)
    (herrors : 0 ≤ editError ∧ 0 ≤ horizontalError ∧
      0 ≤ horizon ∧ 0 ≤ verticalError)
    (hbad : uniformProbability Bad ≤ failureProbability) :
    fluidValue - editError - horizontalError - horizon * verticalError -
        fluidUpper * failureProbability ≤ uniformAverage cost := by
  have hupper0 : 0 ≤ fluidUpper := hfluid0.trans hfluidUpper
  have hpathUpper :
      fluidValue - editError - horizontalError - horizon * verticalError ≤
        fluidUpper := by
    have hproduct : 0 ≤ horizon * verticalError :=
      mul_nonneg herrors.2.2.1 herrors.2.2.2
    linarith [hfluidUpper, herrors.1, herrors.2.1]
  exact RandomizedOptional.uniformAverage_ge_of_good_event
    cost Bad hcost0 hgood hpathUpper hupper0 hbad

/-- Seedwise version of the empirical-minimization/pilot-learning transfer.

The sample and untouched population may both depend on the pilot seed.  The
chosen template minimizes the sample objective; `target` is any fixed
population comparator (in applications, a population minimizer).  The first
stability estimate is paid twice and the remaining-to-population estimate
once, exactly as in the paper's pilot-learning lemma. -/
theorem pilot_learning_pointwise
    {Ω Template : Type*}
    (sampleValue remainingValue : Ω → Template → ℝ)
    (populationValue : Template → ℝ)
    (chosen : Ω → Template) (target : Template)
    (sampleError remainingError finiteError : Ω → ℝ)
    {stability : ℝ}
    (hchosen : ∀ ω π,
      sampleValue ω (chosen ω) ≤ sampleValue ω π)
    (hsample : ∀ ω π,
      |sampleValue ω π - remainingValue ω π| ≤
        stability * sampleError ω)
    (hremaining : ∀ ω π,
      |remainingValue ω π - populationValue π| ≤
        stability * remainingError ω) :
    ∀ ω,
      finiteError ω + remainingValue ω (chosen ω) ≤
        populationValue target +
          2 * stability * sampleError ω +
          stability * remainingError ω + finiteError ω := by
  intro ω
  have hlearned :
      remainingValue ω (chosen ω) ≤
        remainingValue ω target + 2 * stability * sampleError ω := by
    simpa [mul_assoc] using
      RandomizedOptional.empirical_minimizer_transfer
        (hsample ω) (hchosen ω target)
  have htarget := (abs_le.mp (hremaining ω target)).2
  linarith

/-- Averaged pilot-learning transfer for a finite private seed.

`conditionalCost` can be the expectation over further independent main
schedule randomness.  No independence premise is needed here: all such
conditioning has already been absorbed into the pointwise finite-cost
bound. -/
theorem pilot_learning_transfer
    {Ω Template : Type*} [Fintype Ω] [Nonempty Ω]
    (sampleValue remainingValue : Ω → Template → ℝ)
    (populationValue : Template → ℝ)
    (chosen : Ω → Template) (target : Template)
    (conditionalCost sampleError remainingError finiteError : Ω → ℝ)
    {stability : ℝ}
    (hchosen : ∀ ω π,
      sampleValue ω (chosen ω) ≤ sampleValue ω π)
    (hsample : ∀ ω π,
      |sampleValue ω π - remainingValue ω π| ≤
        stability * sampleError ω)
    (hremaining : ∀ ω π,
      |remainingValue ω π - populationValue π| ≤
        stability * remainingError ω)
    (hcost : ∀ ω,
      conditionalCost ω ≤
        remainingValue ω (chosen ω) + finiteError ω) :
    uniformAverage conditionalCost ≤
      populationValue target +
        2 * stability * uniformAverage sampleError +
        stability * uniformAverage remainingError +
        uniformAverage finiteError := by
  have hpoint : ∀ ω,
      conditionalCost ω ≤
        populationValue target +
          2 * stability * sampleError ω +
          stability * remainingError ω + finiteError ω := by
    intro ω
    have hlearned :
        remainingValue ω (chosen ω) ≤
          remainingValue ω target + 2 * stability * sampleError ω :=
      by
        simpa [mul_assoc] using
          RandomizedOptional.empirical_minimizer_transfer
            (hsample ω) (hchosen ω target)
    have htarget := (abs_le.mp (hremaining ω target)).2
    linarith [hcost ω]
  have havg := uniformAverage_mono hpoint
  have hexpand :
      uniformAverage (fun ω =>
        populationValue target +
          2 * stability * sampleError ω +
          stability * remainingError ω + finiteError ω) =
      populationValue target +
        2 * stability * uniformAverage sampleError +
        stability * uniformAverage remainingError +
        uniformAverage finiteError := by
    calc
      uniformAverage (fun ω =>
          populationValue target +
            2 * stability * sampleError ω +
            stability * remainingError ω + finiteError ω) =
          uniformAverage (fun _ω : Ω => populationValue target) +
            uniformAverage (fun ω => (2 * stability) * sampleError ω) +
            uniformAverage (fun ω => stability * remainingError ω) +
            uniformAverage finiteError := by
              rw [← uniformAverage_add, ← uniformAverage_add,
                ← uniformAverage_add]
      _ = populationValue target +
            2 * stability * uniformAverage sampleError +
            stability * uniformAverage remainingError +
            uniformAverage finiteError := by
              rw [uniformAverage_const, uniformAverage_smul,
                uniformAverage_smul]
  rwa [hexpand] at havg

end

end FluidToFinite
end SchedulingPaper
