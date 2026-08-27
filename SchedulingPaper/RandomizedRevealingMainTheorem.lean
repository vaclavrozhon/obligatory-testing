import SchedulingPaper.RevealingOptimizationInstanceOptimal
import SchedulingPaper.RevealingOptimizationOperationalUpper
import SchedulingPaper.RevealingOptimizationOperationalCompiler

/-!
# Top-level randomized revealing-optimization curve statement

This file packages the three operational ingredients of the exact randomized
curve in one public conclusion: the announced finite curve upper bound, the
instance-comparison transfer to the literal unannounced pilot learner, and the
finite-seed Yao lower bound whose exact coefficient tends to the curve.
-/

namespace SchedulingPaper
namespace RevealingOptimization

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower
open InstanceOptimal
open ObservedAreaLower
open OperationalUpper
open OperationalCompiler

noncomputable section

/-- The announced operational endpoint used in the randomized curve upper
bound.  The threshold depends only on the announced multiset, while the
strategy itself remains transcript-only. -/
def AnnouncedRandomizedCurveUpper (u : ℝ) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ processing : Fin n → ℝ,
    1 < u →
    (∀ job, 0 ≤ processing job) →
    (∀ job, processing job ≤ u) →
    ∃ (τ : ℝ) (strategy : Equiv.Perm (Fin n) → Online.Strategy n),
      1 ≤ τ ∧
      (∑ job, max (τ - processing job) 0 = n) ∧
      (∀ seed job,
        (Online.run (.finite u) (Online.fixedOracle processing)
          (strategy seed) (2 * n + 1)).config.jobs job = .done) ∧
      uniformAverage (fun seed =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (strategy seed) (2 * n + 1))) ≤
        randomizedCurve u * empiricalRevealingOfflineCost u processing +
          (n : ℝ) * (1 + u) / 2

/-- Exact quantifier order of the operational finite-seed Yao lower bound.
The attaining binary family depends only on `u`; for every size and every
completing randomized strategy one fixed input is then selected outside the
seed average. -/
def OperationalRandomizedCurveLower (u : ℝ) : Prop :=
  (∃ τ ∈ Set.Icc (1 : ℝ) u,
    familyB u τ = randomizedCurve u ∧
    Filter.Tendsto (fun n : ℕ => familyBFiniteYaoRatio n u τ)
      Filter.atTop (nhds (randomizedCurve u)) ∧
    ∀ (n : ℕ) (Seeds : Type) [Fintype Seeds] [Nonempty Seeds],
      0 < n → ∀ strategy : Seeds → Online.Strategy n,
        (∀ seed, CompletesBinary u u (strategy seed)) →
        ∃ input : RandomizedYao.BinaryInput n,
          familyBFiniteYaoRatio n u τ *
              empiricalRevealingOfflineCost u
                (RandomizedYao.binaryProcessing u input) ≤
            uniformAverage fun seed =>
              binaryRunCost u u (strategy seed) input) ∨
  (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1),
    familyA τ = randomizedCurve u ∧
    Filter.Tendsto (fun n : ℕ => familyAFiniteYaoRatio n τ)
      Filter.atTop (nhds (randomizedCurve u)) ∧
    ∀ (n : ℕ) (Seeds : Type) [Fintype Seeds] [Nonempty Seeds],
      0 < n → ∀ strategy : Seeds → Online.Strategy n,
        (∀ seed, CompletesBinary u τ (strategy seed)) →
        ∃ input : RandomizedYao.BinaryInput n,
          familyAFiniteYaoRatio n τ *
              empiricalRevealingOfflineCost u
                (RandomizedYao.binaryProcessing τ input) ≤
            uniformAverage fun seed =>
              binaryRunCost u τ (strategy seed) input)

/-- The exact finite composition previously left to prose.  Any announced
finite-seed policy with a curve upper bound can be inserted into the checked
instance comparison.  The selected placement is internal to the proof, and
the result is a direct bound for the literal unannounced pilot learner. -/
theorem compiledExpectedNormalizedCost_le_curve_of_competitor
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ}
    (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Seeds → CompletePolicy p) (competitorError : ℝ)
    (hpolicy : ∀ σ : Placement n,
      uniformAverage (fun seed =>
        normalizedRawCost u p (policy seed) σ) ≤
          randomizedCurve u * empiricalRevealingOfflineCost u p /
              (n : ℝ) ^ 2 + competitorError) :
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    compiledExpectedNormalizedCost G pilot u ≤
      randomizedCurve u * empiricalRevealingOfflineCost u p /
          (n : ℝ) ^ 2 + competitorError +
        concreteRevealingComparisonError u n := by
  dsimp only
  obtain ⟨σ, hcomparison⟩ :=
    exists_fixedPlacement_compiled_le_randomizedCompetitor_concrete_rate
      hroot hu p hp0 hpu policy
  calc
    _ ≤ uniformAverage (fun seed =>
          normalizedRawCost u p (policy seed) σ) +
        concreteRevealingComparisonError u n := hcomparison
    _ ≤ (randomizedCurve u * empiricalRevealingOfflineCost u p /
          (n : ℝ) ^ 2 + competitorError) +
        concreteRevealingComparisonError u n :=
      by linarith [hpolicy σ]
    _ = randomizedCurve u * empiricalRevealingOfflineCost u p /
          (n : ℝ) ^ 2 + competitorError +
        concreteRevealingComparisonError u n := by ring

/-- Predicate form of the checked announced-to-unannounced composition, used
as a field of the public exact-curve package. -/
def UnannouncedRandomizedCurveTransfer (u : ℝ) : Prop :=
  ∀ {Seeds : Type} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ},
    ∀ (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n),
    ∀ (hu : 0 < u),
    ∀ (p : Fin n → ℝ)
      (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u)
      (policy : Seeds → CompletePolicy p) (competitorError : ℝ),
    (∀ σ : Placement n,
      uniformAverage (fun seed =>
        normalizedRawCost u p (policy seed) σ) ≤
          randomizedCurve u * empiricalRevealingOfflineCost u p /
              (n : ℝ) ^ 2 + competitorError) →
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    compiledExpectedNormalizedCost G pilot u ≤
      randomizedCurve u * empiricalRevealingOfflineCost u p /
          (n : ℝ) ^ 2 + competitorError +
        concreteRevealingComparisonError u n

theorem unannouncedRandomizedCurveTransfer
    (u : ℝ) : UnannouncedRandomizedCurveTransfer u := by
  unfold UnannouncedRandomizedCurveTransfer
  intro Seeds _ _ n hroot hu p hp0 hpu policy competitorError hpolicy
  exact compiledExpectedNormalizedCost_le_curve_of_competitor
    hroot hu p hp0 hpu policy competitorError hpolicy

/-- One public package for the randomized revealing curve above the trivial
cap-one regime.  It records the announced operational upper, the formal
unannouncement transfer, and the matching operational Yao lower. -/
structure RandomizedRevealingCurveConclusion (u : ℝ) : Prop where
  announcedUpper : AnnouncedRandomizedCurveUpper u
  unannouncedTransfer : UnannouncedRandomizedCurveTransfer u
  lower : OperationalRandomizedCurveLower u
  errorVanishing :
    Filter.Tendsto (concreteRevealingComparisonError u)
      Filter.atTop (nhds 0)

/-- Top-level randomized revealing-optimization exact-curve package. -/
theorem randomizedRevealingCurveExact
    {u : ℝ} (hu : 1 < u) :
    RandomizedRevealingCurveConclusion u := by
  refine {
    announcedUpper := ?_
    unannouncedTransfer := ?_
    lower := ?_
    errorVanishing := concreteRevealingComparisonError_tendsto_zero u }
  · intro n hn processing _hu hp0 hpu
    exact exists_announced_operational_curve_upper hn processing hu hp0 hpu
  · exact unannouncedRandomizedCurveTransfer u
  · exact exists_operational_binary_family_ratio_tendsto_curve hu

end

end RevealingOptimization
end SchedulingPaper
