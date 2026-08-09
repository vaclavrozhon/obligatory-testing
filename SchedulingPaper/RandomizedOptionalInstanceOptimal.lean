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

/-- Rate-ready form of the sandwich.  Once the five displayed scalar error
quantities are at most `δ`, the canonical policy is within
`(32+77*scale)δ` of every announced policy.  This theorem isolates all
remaining asymptotic arithmetic from the scheduling proof. -/
theorem boundedUniform_canonical_le_every_policy_of_error_bounds
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r δ : ℝ} (he : 0 < e) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hDiscovery :
      (L + L / K) *
          ((e + martingaleStep +
            (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) + L / K ≤ δ)
    (hCounts :
      (K + 1) *
        ((e + martingaleStep +
          (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card) / n) ≤ δ)
    (hBad :
      (K + 2) *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) ≤ δ)
    (hInverse : 1 / (n : ℝ) ≤ δ)
    (hMesh : L / (K : ℝ) ≤ δ) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let scale := max 1 (L + L / K)
    ∃ (B : BenchmarkData p G) (q : ℕ), q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) p
        (pullbackRoundedSelector G (benchmarkLowSelector B))
        (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
          (n : ℝ) ^ 2 ≤
        uniformAverage (normalizedCost p policy) +
          (32 + 77 * scale) * δ := by
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
  obtain ⟨B, q, hq, hlower, hupper⟩ :=
    boundedUniform_announced_instance_optimal_sandwich
      hn hK hL p hp0 hpL hmean policy cutoff
        hMartingaleStep hSuffixStep he hr
  refine ⟨B, q, hq, ?_⟩
  have hrounded0 : 0 ≤ roundedScale := by
    dsimp [roundedScale]
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  have hscale1 : 1 ≤ scale := le_max_left _ _
  have hmeanLe : B.mean ≤ roundedScale := by
    rw [B.mean_def]
    exact populationMean_le_scale (show 0 < n by omega)
      G.roundedProcessing (fun job => by
        dsimp [G, roundedScale]
        exact boundedUniformRoundedGrid_roundedProcessing_le
          hK hL p hp0 hpL job)
  have hDiscovery' : roundedScale * γ + L / K ≤ δ := by
    simpa [roundedScale, threshold, γ] using hDiscovery
  have hCounts' : (K + 1 : ℝ) * γ ≤ δ := by
    simpa [threshold, γ] using hCounts
  have hBad' : (K + 2 : ℝ) * badBound ≤ δ := by
    simpa [badBound] using hBad
  have hcountTerm : (K + 1 : ℝ) * γ * (1 + B.mean) ≤
      δ * (1 + roundedScale) := by
    exact mul_le_mul hCounts' (by linarith) (by linarith [B.mean_pos]) hδ
  have hbadTerm : (1 + roundedScale) * ((K + 2 : ℝ) * badBound) ≤
      (1 + roundedScale) * δ :=
    mul_le_mul_of_nonneg_left hBad' (by linarith)
  have hfiniteTerm : (17 + 63 * scale) / (n : ℝ) ≤
      (17 + 63 * scale) * δ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hInverse)
      (by linarith)
  have hmeshTerm : 12 * (scale + 1) * (L / (K : ℝ)) ≤
      12 * (scale + 1) * δ :=
    mul_le_mul_of_nonneg_left hMesh (by positivity)
  change uniformAverage (canonicalPlacedRunCost (q := q) p
      (pullbackRoundedSelector G (benchmarkLowSelector B))
      (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
        (n : ℝ) ^ 2 ≤ _
  have hconstant :
      δ + δ * (1 + roundedScale) + (1 + roundedScale) * δ +
          (17 + 63 * scale) * δ + 12 * (scale + 1) * δ ≤
        (32 + 77 * scale) * δ := by
    have hroundScale : roundedScale ≤ scale := le_max_right _ _
    nlinarith
  linarith

end

end RandomizedOptional
end SchedulingPaper
