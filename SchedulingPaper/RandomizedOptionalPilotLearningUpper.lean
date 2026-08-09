import SchedulingPaper.RandomizedOptionalPilotKernel
import Mathlib.Tactic

/-!
# The learned canonical main schedule

The pilot permutation chooses a finite template from its category histogram;
an independent fresh permutation executes that fixed template.  This module
combines histogram learning, the finite kernel, rounding, and the announced
benchmark into one explicit double-average upper bound.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

def learnedPositiveGridTemplate
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (S : Finset (Fin n)) (pilotOrder : Equiv.Perm (Fin n)) :
    GridTemplate ι n :=
  minimizingPositiveGridTemplate
    (sampleHistogram S (roundedGridCell G) pilotOrder) G.price

def learnedCanonicalPlacedCost
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (S : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) : ℝ :=
  let T := learnedPositiveGridTemplate G S pilotOrder
  canonicalPlacedRunCost (q := T.1.quota.val) p
    (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
    (pullbackRoundedSelector G (gridTemplateRoundedMedium G.price T))
    mainOrder

/-- Pilot learning against an arbitrary fixed member of the common finite
template family.  Unlike the benchmark wrapper below, this statement remains
available when the rounded population mean is zero. -/
theorem learnedCanonicalPlacedCost_le_target
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (target : GridTemplate ι n)
    {scale : ℝ} (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, p job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale)
    (hpriceScale : ∀ i, G.price i ≤ scale) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (learnedCanonicalPlacedCost G S pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price target +
        24 * (scale + 1) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hlearn := uniformSample_minimizingPositiveGridTemplate_le
    (N := n) (show 0 < n by omega) S (roundedGridCell G) hS
      (by simpa using hn) G.price (show 0 ≤ scale by linarith)
      (fun i => (hprice0 i).le) hpriceScale target
  have hpoint : ∀ pilotOrder : Equiv.Perm (Fin n),
      uniformAverage (learnedCanonicalPlacedCost G S pilotOrder) /
          (n : ℝ) ^ 2 ≤
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh := by
    intro pilotOrder
    exact canonicalPlacedRunCost_le_positiveGridTemplateValue hn G
      hprice0 hprice (learnedPositiveGridTemplate G S pilotOrder)
      hscaleOne hpScale hroundedScale
  have havg := uniformAverage_mono hpoint
  have hdivide :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
          uniformAverage (learnedCanonicalPlacedCost G S pilotOrder) /
            (n : ℝ) ^ 2) =
        uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
          uniformAverage (learnedCanonicalPlacedCost G S pilotOrder)) /
            (n : ℝ) ^ 2 := by
    simp only [uniformAverage, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro pilotOrder _
    apply Finset.sum_congr rfl
    intro mainOrder _
    ring
  rw [hdivide] at havg
  have hright :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh) =
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder)) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh := by
    rw [uniformAverage_add, uniformAverage_add,
      uniformAverage_const, uniformAverage_const]
  rw [hright] at havg
  dsimp [learnedPositiveGridTemplate] at hlearn havg ⊢
  linarith

/-- Explicit upper bound for the canonical full-population schedule selected
by a uniform pilot histogram.  The physical cost of placing the pilot before
the main schedule is handled separately; this theorem closes all statistical
and finite-kernel terms. -/
theorem learnedCanonicalPlacedCost_le_benchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (B : BenchmarkData p G)
    {scale : ℝ} (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, p job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale)
    (hpriceScale : ∀ i, G.price i ≤ scale) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (learnedCanonicalPlacedCost G S pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      B.value +
        24 * (scale + 1) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) +
        (17 + 63 * scale) / n +
        12 * (scale + 1) * G.mesh := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨target, htarget⟩ :=
    exists_gridTemplateValue_le_benchmark hn B hprice hroundedScale
  have hlearn := uniformSample_minimizingPositiveGridTemplate_le
    (N := n) (show 0 < n by omega) S (roundedGridCell G) hS
      (by simpa using hn) G.price (show 0 ≤ scale by linarith)
      (fun i => (hprice0 i).le) hpriceScale target
  have hpoint : ∀ pilotOrder : Equiv.Perm (Fin n),
      uniformAverage (learnedCanonicalPlacedCost G S pilotOrder) /
          (n : ℝ) ^ 2 ≤
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh := by
    intro pilotOrder
    exact canonicalPlacedRunCost_le_positiveGridTemplateValue hn G
      hprice0 hprice (learnedPositiveGridTemplate G S pilotOrder)
      hscaleOne hpScale hroundedScale
  have havg := uniformAverage_mono hpoint
  have hdivide :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
          uniformAverage (learnedCanonicalPlacedCost G S pilotOrder) /
            (n : ℝ) ^ 2) =
        uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
          uniformAverage (learnedCanonicalPlacedCost G S pilotOrder)) /
            (n : ℝ) ^ 2 := by
    simp only [uniformAverage, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro pilotOrder _
    apply Finset.sum_congr rfl
    intro mainOrder _
    ring
  rw [hdivide] at havg
  have hright :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh) =
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price
          (learnedPositiveGridTemplate G S pilotOrder)) +
        (5 + 18 * scale) / n +
        12 * (scale + 1) * G.mesh := by
    rw [uniformAverage_add, uniformAverage_add,
      uniformAverage_const, uniformAverage_const]
  rw [hright] at havg
  dsimp [learnedPositiveGridTemplate] at hlearn havg ⊢
  have htargetCombined :
      positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price target +
          24 * (scale + 1) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) ≤
        B.value + (12 + 45 * scale) / n +
          24 * (scale + 1) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) := by
    linarith
  have herr : (12 + 45 * scale) / (n : ℝ) +
      (5 + 18 * scale) / n = (17 + 63 * scale) / n := by ring
  linarith

end

end RandomizedOptional
end SchedulingPaper
