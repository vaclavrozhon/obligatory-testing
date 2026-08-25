import SchedulingPaper.RevealingOptimizationRawObserved
import SchedulingPaper.ObligatoryGrowingCutoffBenchmark
import Mathlib.Tactic

/-!
# The bounded revealing-optimization instance benchmark

The maximum-density test module is shared with obligatory testing.  The only
new item is a raw block of capacity `1-q` and public cost `u`.  We package the
attained minimum over the final tested fraction so the operational lower and
learned upper can meet at one concrete finite-grid value.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace InstanceBenchmark

open RandomizedOptional
open Randomized
open RandomizedOptional.ObservedEnvelope
open RandomizedOptional.AnnouncedRoundedLower
open ObligatoryInstance

noncomputable section

def rawBenchmarkBlocks
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u q : ℝ) : List FluidBlock :=
  optionalSortedBlocks q
    (RandomizedAnnounced.discoveryMass B.zeroMass
      (selectedPart B.selected B.mass))
    B.tau u G.price (residualPart B.selected B.mass)

def rawBenchmarkAt
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u q : ℝ) : ℝ :=
  fluidBlocksArea (rawBenchmarkBlocks B u q)

structure RawBenchmarkData
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u : ℝ) where
  qStar : ℝ
  qStar_nonneg : 0 ≤ qStar
  qStar_le_one : qStar ≤ 1
  minimizes : ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
    rawBenchmarkAt B u qStar ≤ rawBenchmarkAt B u q

def RawBenchmarkData.value
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    {B : BenchmarkData p G} {u : ℝ}
    (R : RawBenchmarkData B u) : ℝ :=
  rawBenchmarkAt B u R.qStar

theorem exists_rawBenchmarkData
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u : ℝ) :
    Nonempty (RawBenchmarkData B u) := by
  let a := RandomizedAnnounced.discoveryMass B.zeroMass
    (selectedPart B.selected B.mass)
  let residual := residualPart B.selected B.mass
  obtain ⟨qStar, hq0, hq1, hmin⟩ :=
    exists_optionalSortedBlocks_area_minimizer
      a B.tau u G.price residual
  exact ⟨{
    qStar := qStar
    qStar_nonneg := hq0
    qStar_le_one := hq1
    minimizes := by
      intro q hq0' hq1'
      simpa [rawBenchmarkAt, rawBenchmarkBlocks, a, residual] using
        hmin q hq0' hq1' }⟩

theorem rawBenchmarkBlocks_mass_eq_one
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u q : ℝ) :
    fluidBlocksMass (rawBenchmarkBlocks B u q) = 1 := by
  apply optionalSortedBlocks_mass_eq_one
  dsimp [RandomizedAnnounced.discoveryMass]
  have hsplit := sum_selectedPart_add_sum_residualPart B.selected B.mass
  linarith [B.population_mass]

theorem rawBenchmarkBlocks_cost_pos
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u q : ℝ} (hu : 0 < u) :
    ∀ block ∈ rawBenchmarkBlocks B u q, 0 < block.cost := by
  exact optionalSortedBlocks_cost_pos B.tau_pos hu B.price_pos

theorem rawBenchmarkBlocks_mass_nonneg
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ block ∈ rawBenchmarkBlocks B u q, 0 ≤ block.mass := by
  apply optionalSortedBlocks_mass_nonneg hq0 hq1
  · exact B.module_pos.le
  · exact residualPart_nonneg fun i => by
      rw [B.mass_def i]
      unfold populationMean
      exact div_nonneg
        (Finset.sum_nonneg fun occurrence _ => by
          by_cases h : G.category i (p occurrence) = true <;> simp [h])
        (Nat.cast_nonneg _)

theorem rawBenchmarkAt_nonneg
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u q : ℝ} (hu : 0 < u)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ rawBenchmarkAt B u q := by
  unfold rawBenchmarkAt
  exact fluidBlocksArea_nonneg _
    (fun block hblock => (rawBenchmarkBlocks_cost_pos B hu block hblock).le)
    (rawBenchmarkBlocks_mass_nonneg B hq0 hq1)

theorem rawBenchmarkAt_zero
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u : ℝ) :
    rawBenchmarkAt B u 0 = u / 2 := by
  rw [rawBenchmarkAt, rawBenchmarkBlocks,
    optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype]
  simp [optionalItemCapacity, optionalItemCost]

theorem RawBenchmarkData.value_nonneg
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    {B : BenchmarkData p G} {u : ℝ}
    (R : RawBenchmarkData B u) (hu : 0 < u) :
    0 ≤ R.value :=
  rawBenchmarkAt_nonneg B hu R.qStar_nonneg R.qStar_le_one

theorem RawBenchmarkData.value_le_half_raw
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    {B : BenchmarkData p G} {u : ℝ}
    (R : RawBenchmarkData B u) :
    R.value ≤ u / 2 := by
  calc
    R.value ≤ rawBenchmarkAt B u 0 := R.minimizes 0 (by norm_num) (by norm_num)
    _ = u / 2 := rawBenchmarkAt_zero B u

end

end InstanceBenchmark
end RevealingOptimization
end SchedulingPaper
