import SchedulingPaper.RandomizedOptionalRoundingUpper
import Mathlib.Tactic

/-!
# Finite announced instance-optimal sandwich for optional testing

This module joins the adaptive-policy lower bound and the executable
canonical-policy upper bound around the same empirical rounded benchmark.
All errors are explicit.  No asymptotic notation and no conditioning on the
adaptive stopping fraction occur in the statement.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every complete announced policy is lower-bounded by an empirical grid
benchmark, and the same benchmark is implemented on the original processing
times by one canonical threshold/medium/blind/high policy. -/
theorem boundedUniform_announced_instance_optimal_sandwich
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let roundedScale := L + L / K
    let scale := max 1 roundedScale
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let badBound :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ (B : BenchmarkData p G) (q : ℕ), q ≤ n ∧
      B.value - (roundedScale * γ + L / K) -
          (K + 1) * γ * (1 + B.mean) -
          (1 + roundedScale) * ((K + 2) * badBound) ≤
        uniformAverage (normalizedCost p policy) ∧
      uniformAverage (canonicalPlacedRunCost (q := q) p
        (pullbackRoundedSelector G (benchmarkLowSelector B))
        (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
          (n : ℝ) ^ 2 ≤
        B.value + (17 + 63 * scale) / n +
          12 * (scale + 1) * (L / K) := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  let roundedScale : ℝ := L + L / K
  let scale : ℝ := max 1 roundedScale
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let badBound : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  obtain ⟨B, hlower⟩ := exists_boundedUniformBenchmark_uniformAverage_lower
    hn hK hL p hp0 hpL hmean policy cutoff
      hMartingaleStep hSuffixStep he hr
  obtain ⟨q, hq, hupper⟩ :=
    exists_boundedUniform_actualCanonicalPlacedRunCost_le_benchmark
      hn hK hL p hp0 hpL B
  refine ⟨B, q, hq, ?_, ?_⟩
  · simpa [G, roundedScale, threshold, γ, badBound] using hlower
  · simpa [G, roundedScale, scale] using hupper

/-- Direct comparison form: the canonical policy is within the sum of the
explicit upper and lower errors of every announced complete policy. -/
theorem boundedUniform_canonical_le_every_announced_policy
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let roundedScale := L + L / K
    let scale := max 1 roundedScale
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let badBound :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ (B : BenchmarkData p G) (q : ℕ), q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) p
        (pullbackRoundedSelector G (benchmarkLowSelector B))
        (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
          (n : ℝ) ^ 2 ≤
        uniformAverage (normalizedCost p policy) +
          (roundedScale * γ + L / K) +
          (K + 1) * γ * (1 + B.mean) +
          (1 + roundedScale) * ((K + 2) * badBound) +
          (17 + 63 * scale) / n +
          12 * (scale + 1) * (L / K) := by
  dsimp
  obtain ⟨B, q, hq, hlower, hupper⟩ :=
    boundedUniform_announced_instance_optimal_sandwich
      hn hK hL p hp0 hpL hmean policy cutoff
        hMartingaleStep hSuffixStep he hr
  refine ⟨B, q, hq, ?_⟩
  linarith

end

end RandomizedOptional
end SchedulingPaper
