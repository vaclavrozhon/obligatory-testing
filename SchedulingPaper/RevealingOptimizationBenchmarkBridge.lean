import SchedulingPaper.RevealingOptimizationObservedAreaLower
import SchedulingPaper.RevealingOptimizationCompiledRun
import Mathlib.Tactic

/-!
# Matching the raw block benchmark to learnable revealing templates

The completion lower bound is a sorted block area, whereas the compiled
upper bound uses a symmetric two-draw pair kernel.  This file proves the
algebraic identity between those presentations and supplies the finite
quota approximation.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace BenchmarkBridge

open Randomized
open RandomizedOptional
open RandomizedOptional.AnnouncedRoundedLower
open RandomizedOptional.ObservedEnvelope
open ObligatoryInstance
open InstanceBenchmark
open InstanceLearning

noncomputable section
attribute [local instance] Classical.propDecidable

theorem finiteProductExpectation_add
    {β : Type*} [Fintype β] (D : β → ℝ) (f g : β → β → ℝ) :
    finiteProductExpectation D (fun i j => f i j + g i j) =
      finiteProductExpectation D f + finiteProductExpectation D g := by
  unfold finiteProductExpectation
  simp_rw [mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]

theorem finiteProductExpectation_const
    {β : Type*} [Fintype β] (D : β → ℝ)
    (hmass : ∑ i, D i = 1) (c : ℝ) :
    finiteProductExpectation D (fun _ _ => c) = c := by
  unfold finiteProductExpectation
  have hinner : ∀ i,
      (∑ j, D i * D j * c) = D i * (∑ j, D j) * c := by
    intro i
    calc
      (∑ j, D i * D j * c) = (∑ j, D i * D j) * c := by
        rw [Finset.sum_mul]
      _ = D i * (∑ j, D j) * c := by rw [Finset.mul_sum]
  simp_rw [hinner, hmass]
  rw [← Finset.sum_mul]
  simp [hmass]

theorem finiteProductExpectation_separable
    {β : Type*} [Fintype β] (D f g : β → ℝ) :
    finiteProductExpectation D (fun i j => f i * g j) =
      RandomizedOptional.finiteExpectation D f *
        RandomizedOptional.finiteExpectation D g := by
  unfold finiteProductExpectation RandomizedOptional.finiteExpectation
  have hinner : ∀ i,
      (∑ j, D i * D j * (f i * g j)) =
        (D i * f i) * ∑ j, D j * g j := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hinner]
  rw [← Finset.sum_mul]

theorem finiteProductExpectation_smul
    {β : Type*} [Fintype β] (D : β → ℝ) (c : ℝ)
    (f : β → β → ℝ) :
    finiteProductExpectation D (fun i j => c * f i j) =
      c * finiteProductExpectation D f := by
  unfold finiteProductExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def boolReal (b : Bool) : ℝ := if b then 1 else 0

/-- Multilinear expansion of the four tested/tested cases. -/
theorem testedPairChargeFlags_decomposition
    (leftLow rightLow : Bool) (p q : ℝ) :
    testedPairChargeFlags leftLow rightLow p q =
      2 + (p - 1 / 2) * boolReal leftLow +
        (q - 1 / 2) * boolReal rightLow -
        ((p * boolReal leftLow) * boolReal rightLow +
          boolReal leftLow * (q * boolReal rightLow)) / 2 +
        (1 - boolReal leftLow) * (1 - boolReal rightLow) * min p q := by
  cases leftLow <;> cases rightLow <;>
    simp [testedPairChargeFlags, boolReal] <;> ring

/-- The expected tested-pair charge is twice the obligatory stationary
template value. -/
theorem finiteProductExpectation_testedPairCharge_eq_two_mul_obligatory
    {β : Type*} [Fintype β]
    (D price : β → ℝ) (early : β → Bool)
    (hmass : ∑ i, D i = 1) :
    finiteProductExpectation D (fun i j =>
        testedPairChargeFlags (early i) (early j) (price i) (price j)) =
      2 * obligatoryTemplateValue D price early := by
  let e : β → ℝ := fun i => boolReal (early i)
  let late : β → ℝ := fun i => 1 - e i
  let a := RandomizedOptional.finiteExpectation D e
  let m := RandomizedOptional.finiteExpectation D fun i => price i * e i
  let k := finiteProductExpectation D fun i j =>
    late i * late j * min (price i) (price j)
  have hea : templateEarlyMass D early = a := by
    unfold templateEarlyMass a e boolReal RandomizedOptional.finiteExpectation
    rfl
  have hem : templateEarlyMoment D price early = m := by
    unfold templateEarlyMoment m e boolReal RandomizedOptional.finiteExpectation
    rfl
  have hek : templateLatePair D price early = k := by
    unfold templateLatePair k late e boolReal finiteProductExpectation
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    cases hi : early i <;> cases hj : early j <;> simp [hi, hj]
  have hpoint : (fun i j =>
      testedPairChargeFlags (early i) (early j) (price i) (price j)) =
      fun i j =>
        2 + ((price i - 1 / 2) * e i) +
          ((price j - 1 / 2) * e j) +
          (-((price i * e i) * e j) / 2) +
          (-(e i * (price j * e j)) / 2) +
          late i * late j * min (price i) (price j) := by
    funext i j
    rw [testedPairChargeFlags_decomposition]
    dsimp [e, late]
    ring
  rw [hpoint]
  simp_rw [finiteProductExpectation_add]
  have hconst := finiteProductExpectation_const D hmass 2
  have hleft := finiteProductExpectation_separable D
    (fun i => (price i - 1 / 2) * e i) (fun _ => 1)
  have hright := finiteProductExpectation_separable D
    (fun _ => 1) (fun j => (price j - 1 / 2) * e j)
  have hcrossLeft := finiteProductExpectation_separable D
    (fun i => -(price i * e i) / 2) e
  have hcrossRight := finiteProductExpectation_separable D
    (fun i => -(e i) / 2) (fun j => price j * e j)
  have hone : RandomizedOptional.finiteExpectation D (fun _ => (1 : ℝ)) = 1 := by
    unfold RandomizedOptional.finiteExpectation
    simpa using hmass
  have hleftMoment :
      RandomizedOptional.finiteExpectation D
        (fun i => (price i - 1 / 2) * e i) = m - a / 2 := by
    dsimp [m, a]
    unfold RandomizedOptional.finiteExpectation
    calc
      (∑ i, D i * ((price i - 1 / 2) * e i)) =
          ∑ i, (D i * (price i * e i) - (D i * e i) / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, D i * (price i * e i)) -
          ∑ i, (D i * e i) / 2 := by rw [Finset.sum_sub_distrib]
      _ = (∑ i, D i * (price i * e i)) -
          (∑ i, D i * e i) / 2 := by rw [Finset.sum_div]
  have hcrossMoment :
      RandomizedOptional.finiteExpectation D
        (fun i => -(price i * e i) / 2) = -m / 2 := by
    dsimp [m]
    unfold RandomizedOptional.finiteExpectation
    calc
      (∑ i, D i * (-(price i * e i) / 2)) =
          ∑ i, -(D i * (price i * e i)) / 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, -(D i * (price i * e i))) / 2 := by
        rw [Finset.sum_div]
      _ = -(∑ i, D i * (price i * e i)) / 2 := by
        rw [Finset.sum_neg_distrib]
  have hcrossMass :
      RandomizedOptional.finiteExpectation D (fun i => -e i / 2) = -a / 2 := by
    dsimp [a]
    unfold RandomizedOptional.finiteExpectation
    calc
      (∑ i, D i * (-e i / 2)) = ∑ i, -(D i * e i) / 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, -(D i * e i)) / 2 := by rw [Finset.sum_div]
      _ = -(∑ i, D i * e i) / 2 := by rw [Finset.sum_neg_distrib]
  have hleft' : finiteProductExpectation D
      (fun i _j => (price i - 1 / 2) * e i) = m - a / 2 := by
    rw [show (fun i _j => (price i - 1 / 2) * e i) =
      (fun i j => ((price i - 1 / 2) * e i) * (1 : ℝ)) by
        funext i j; ring]
    rw [hleft, hleftMoment, hone]
    ring
  have hright' : finiteProductExpectation D
      (fun _i j => (price j - 1 / 2) * e j) = m - a / 2 := by
    rw [show (fun _i j => (price j - 1 / 2) * e j) =
      (fun i j => (1 : ℝ) * ((price j - 1 / 2) * e j)) by
        funext i j; ring]
    rw [hright, hleftMoment, hone]
    ring
  have hcrossLeft' : finiteProductExpectation D
      (fun i j => -(price i * e i * e j) / 2) = (-m / 2) * a := by
    rw [show (fun i j => -(price i * e i * e j) / 2) =
      (fun i j => (-(price i * e i) / 2) * e j) by
        funext i j; ring]
    rw [hcrossLeft, hcrossMoment]
  have hcrossRight' : finiteProductExpectation D
      (fun i j => -(e i * (price j * e j)) / 2) = (-a / 2) * m := by
    rw [show (fun i j => -(e i * (price j * e j)) / 2) =
      (fun i j => (-e i / 2) * (price j * e j)) by
        funext i j; ring]
    rw [hcrossRight, hcrossMass]
  rw [hconst, hleft', hright', hcrossLeft', hcrossRight']
  change 2 + (m - a / 2) + (m - a / 2) +
      (-m / 2) * a + (-a / 2) * m + k =
    2 * obligatoryTemplateValue D price early
  rw [obligatoryTemplateValue, hea, hem, hek]
  ring

/-- Closed form of the revealing pair kernel at a real tested fraction. -/
theorem fluidPairValue_eq_raw_quadratic
    {β : Type*} [Fintype β]
    (D price : β → ℝ) (early : β → Bool)
    (u x : ℝ) (hmass : ∑ i, D i = 1) :
    finiteProductExpectation D (fun i j =>
        fluidPairChargeFlags u x (early i) (early j) (price i) (price j)) / 2 =
      x ^ 2 * obligatoryTemplateValue D price early +
        x * (1 - x) *
          (1 + RandomizedOptional.finiteExpectation D price) +
        (1 - x) ^ 2 * u / 2 := by
  let tested : β → β → ℝ := fun i j =>
    testedPairChargeFlags (early i) (early j) (price i) (price j)
  let left : β → ℝ := fun i => 1 + price i
  have htested := finiteProductExpectation_testedPairCharge_eq_two_mul_obligatory
    D price early hmass
  have hone : RandomizedOptional.finiteExpectation D (fun _ => (1 : ℝ)) = 1 := by
    unfold RandomizedOptional.finiteExpectation
    simpa using hmass
  have hleftMean : RandomizedOptional.finiteExpectation D left =
      1 + RandomizedOptional.finiteExpectation D price := by
    dsimp [left]
    unfold RandomizedOptional.finiteExpectation
    calc
      (∑ x_1, D x_1 * (1 + price x_1)) =
          ∑ x_1, (D x_1 + D x_1 * price x_1) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ =
          (∑ x_1, D x_1) + ∑ x_1, D x_1 * price x_1 := by
        rw [Finset.sum_add_distrib]
      _ = 1 + ∑ x_1, D x_1 * price x_1 := by rw [hmass]
  have hpair : (fun i j =>
      fluidPairChargeFlags u x (early i) (early j) (price i) (price j)) =
      fun i j =>
        x ^ 2 * tested i j +
          x * (1 - x) * left i +
          x * (1 - x) * left j +
          (1 - x) ^ 2 * u := by
    funext i j
    rfl
  rw [hpair]
  simp_rw [finiteProductExpectation_add]
  have htt := finiteProductExpectation_smul D (x ^ 2) tested
  have hleftPair := finiteProductExpectation_separable D
    (fun i => x * (1 - x) * left i) (fun _ => 1)
  have hrightPair := finiteProductExpectation_separable D
    (fun _ => 1) (fun j => x * (1 - x) * left j)
  have hraw := finiteProductExpectation_const D hmass ((1 - x) ^ 2 * u)
  have hleftScaled : RandomizedOptional.finiteExpectation D
      (fun i => x * (1 - x) * left i) =
        x * (1 - x) * RandomizedOptional.finiteExpectation D left := by
    unfold RandomizedOptional.finiteExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htt' : finiteProductExpectation D (fun i j => x ^ 2 * tested i j) =
      x ^ 2 * (2 * obligatoryTemplateValue D price early) := by
    rw [htt, htested]
  have hleftPair' : finiteProductExpectation D
      (fun i _j => x * (1 - x) * left i) =
        x * (1 - x) * (1 + RandomizedOptional.finiteExpectation D price) := by
    rw [show (fun i _j => x * (1 - x) * left i) =
      (fun i j => (x * (1 - x) * left i) * (1 : ℝ)) by
        funext i j; ring]
    rw [hleftPair, hleftScaled, hone, hleftMean]
    ring
  have hrightPair' : finiteProductExpectation D
      (fun _i j => x * (1 - x) * left j) =
        x * (1 - x) * (1 + RandomizedOptional.finiteExpectation D price) := by
    rw [show (fun _i j => x * (1 - x) * left j) =
      (fun i j => (1 : ℝ) * (x * (1 - x) * left j)) by
        funext i j; ring]
    rw [hrightPair, hleftScaled, hone, hleftMean]
    ring
  rw [htt', hleftPair', hrightPair', hraw]
  ring

/-- Closed form of the executable grid-template objective. -/
theorem gridTemplateValue_eq_raw_quadratic
    {ι : Type*} [Fintype ι] {n : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (u : ℝ)
    (T : Template ι n) (hmass : ∑ cell, D cell = 1) :
    InstanceLearning.gridTemplateValue D price u T =
      T.fraction ^ 2 *
          obligatoryTemplateValue D (positiveGridPrice price) T.lowWithZero +
        T.fraction * (1 - T.fraction) *
          (1 + RandomizedOptional.finiteExpectation D
            (positiveGridPrice price)) +
        (1 - T.fraction) ^ 2 * u / 2 := by
  unfold InstanceLearning.gridTemplateValue gridPairCharge
  exact fluidPairValue_eq_raw_quadratic D (positiveGridPrice price)
    T.lowWithZero u T.fraction hmass

def benchmarkRawTemplate
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (quota : Fin (n + 1)) : Template ι n where
  low := B.selected
  quota := quota

theorem benchmarkCellHistogram_mass_one
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    ∑ cell, benchmarkCellHistogram B cell = 1 := by
  rw [Fintype.sum_option]
  exact B.population_mass

theorem benchmarkCellHistogram_mean
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    RandomizedOptional.finiteExpectation (benchmarkCellHistogram B)
        (positiveGridPrice G.price) = B.mean := by
  unfold RandomizedOptional.finiteExpectation benchmarkCellHistogram
    positiveGridPrice
  rw [Fintype.sum_option]
  simp only [mul_zero, zero_add]
  have hsplit :
      (∑ i, G.price i * B.mass i) =
        (∑ i, G.price i * selectedPart B.selected B.mass i) +
          ∑ i, G.price i * residualPart B.selected B.mass i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add, selectedPart_add_residualPart]
  calc
    (∑ i, B.mass i * G.price i) = ∑ i, G.price i * B.mass i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := hsplit.trans B.mean_partition

@[simp] theorem benchmarkRawTemplate_lowWithZero
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (quota : Fin (n + 1)) :
    (benchmarkRawTemplate B quota).lowWithZero = benchmarkCellEarly B := by
  funext cell
  cases cell <;> rfl

theorem benchmarkRawTemplate_value_eq_quadratic
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u : ℝ) (quota : Fin (n + 1)) :
    InstanceLearning.gridTemplateValue (benchmarkCellHistogram B)
        G.price u (benchmarkRawTemplate B quota) =
      (benchmarkRawTemplate B quota).fraction ^ 2 * roundedObligatoryValue B +
        (benchmarkRawTemplate B quota).fraction *
          (1 - (benchmarkRawTemplate B quota).fraction) * (1 + B.mean) +
        (1 - (benchmarkRawTemplate B quota).fraction) ^ 2 * u / 2 := by
  rw [gridTemplateValue_eq_raw_quadratic _ _ _ _
    (benchmarkCellHistogram_mass_one B),
    benchmarkRawTemplate_lowWithZero,
    benchmarkCellHistogram_mean,
    ← roundedObligatoryValue_eq_benchmarkCellTemplate hn B]

theorem rawBenchmarkAt_one_eq_roundedObligatoryValue
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (u : ℝ) :
    rawBenchmarkAt B u 1 = roundedObligatoryValue B := by
  unfold rawBenchmarkAt rawBenchmarkBlocks roundedObligatoryValue
  rw [optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype,
    optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype]
  simp only [Fintype.sum_option, optionalItemCapacity, optionalItemCost]
  simp

theorem rawBenchmarkAt_eq_quadratic_of_test_cost_le_raw
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u q : ℝ}
    (htau : B.tau ≤ u) (hpriceu : ∀ i, G.price i ≤ u) :
    rawBenchmarkAt B u q =
      q ^ 2 * roundedObligatoryValue B +
        q * (1 - q) * (1 + B.mean) + (1 - q) ^ 2 * u / 2 := by
  let a := RandomizedAnnounced.discoveryMass B.zeroMass
    (selectedPart B.selected B.mass)
  let residual := residualPart B.selected B.mass
  let testedPair : ℝ :=
    B.tau * a * a +
      ∑ i, min B.tau (G.price i) * a * residual i +
      ∑ i, (min (G.price i) B.tau * residual i * a +
        ∑ j, min (G.price i) (G.price j) * residual i * residual j)
  have htestArea : testedPair / 2 = roundedObligatoryValue B := by
    rw [← rawBenchmarkAt_one_eq_roundedObligatoryValue B u]
    unfold rawBenchmarkAt rawBenchmarkBlocks
    rw [optionalSortedBlocks_area_eq_half_minPair,
      optionalSortedBlocks_minPair_eq_fintype]
    simp only [Fintype.sum_option, optionalItemCapacity, optionalItemCost]
    simp [testedPair, a, residual]
  have htestWork : B.tau * a + ∑ i, G.price i * residual i = 1 + B.mean := by
    have hmodule := B.module_density
    have hmean := B.mean_partition
    dsimp [a, residual]
    unfold RandomizedAnnounced.discoveryWork at hmodule
    linarith
  unfold rawBenchmarkAt rawBenchmarkBlocks
  rw [optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype]
  simp only [Fintype.sum_option, optionalItemCapacity, optionalItemCost]
  simp_rw [min_eq_left htau, min_eq_right htau]
  simp_rw [min_eq_left (hpriceu _), min_eq_right (hpriceu _)]
  simp [min_self]
  ring_nf
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs1 :
      (∑ i, a * q ^ 2 * min B.tau (G.price i) * residual i) =
        a * q ^ 2 * ∑ i, min B.tau (G.price i) * residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hwq : (∑ i, q * G.price i * residual i) =
      q * ∑ i, G.price i * residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hwq2 : (∑ i, q ^ 2 * G.price i * residual i) =
      q ^ 2 * ∑ i, G.price i * residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hwq2rev : (∑ i, q ^ 2 * residual i * G.price i) =
      q ^ 2 * ∑ i, G.price i * residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcombined :
      (∑ i, (a * q ^ 2 * min (G.price i) B.tau * residual i +
          q * residual i * G.price i)) =
        a * q ^ 2 * ∑ i, min (G.price i) B.tau * residual i +
          q * ∑ i, G.price i * residual i := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have hnested :
      (∑ i, ∑ j, q ^ 2 * residual i * min (G.price i) (G.price j) * residual j) =
        q ^ 2 * ∑ i, ∑ j,
          min (G.price i) (G.price j) * residual i * residual j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs1, hwq, hwq2, hwq2rev, hcombined, hnested]
  have htestPairExpanded : testedPair =
      B.tau * a ^ 2 +
        a * ∑ i, min B.tau (G.price i) * residual i +
        a * ∑ i, min (G.price i) B.tau * residual i +
        ∑ i, ∑ j, min (G.price i) (G.price j) * residual i * residual j := by
    dsimp [testedPair]
    have hright :
        (∑ i, min B.tau (G.price i) * a * residual i) =
          a * ∑ i, min B.tau (G.price i) * residual i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hleft :
        (∑ i, min (G.price i) B.tau * residual i * a) =
          a * ∑ i, min (G.price i) B.tau * residual i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_add_distrib, hright, hleft]
    ring
  have htestArea' :
      (B.tau * a ^ 2 +
        a * ∑ i, min B.tau (G.price i) * residual i +
        a * ∑ i, min (G.price i) B.tau * residual i +
        ∑ i, ∑ j, min (G.price i) (G.price j) * residual i * residual j) / 2 =
          roundedObligatoryValue B := by
    rw [← htestPairExpanded]
    exact htestArea
  linear_combination q ^ 2 * htestArea' + q * (1 - q) * htestWork

def rawTemplateQuadratic (testedValue mean u x : ℝ) : ℝ :=
  x ^ 2 * testedValue + x * (1 - x) * (1 + mean) +
    (1 - x) ^ 2 * u / 2

/-- The raw/test mixture objective is uniformly Lipschitz in its tested
fraction when both the fully-tested value and the processing mean obey the
public raw-time bound. -/
theorem rawTemplateQuadratic_lipschitz
    {testedValue mean u x y : ℝ}
    (hu0 : 0 ≤ u)
    (htested0 : 0 ≤ testedValue) (htestedU : testedValue ≤ 1 + u)
    (hmean0 : 0 ≤ mean) (hmeanU : mean ≤ u)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |rawTemplateQuadratic testedValue mean u x -
        rawTemplateQuadratic testedValue mean u y| ≤
      4 * (u + 1) * |x - y| := by
  have hsum0 : 0 ≤ x + y := add_nonneg hx0 hy0
  have hsum2 : x + y ≤ 2 := by linarith
  have hsumAbs : |x + y| ≤ 2 := by
    rw [abs_of_nonneg hsum0]
    exact hsum2
  have honeAbs : |1 - x - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have htwoAbs : |2 - x - y| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have htestedAbs : |testedValue| ≤ 1 + u := by
    rw [abs_of_nonneg htested0]
    exact htestedU
  have hmeanAbs : |1 + mean| ≤ 1 + u := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have huAbs : |u| ≤ u := by
    rw [abs_of_nonneg hu0]
  have htestedTerm : |(x + y) * testedValue| ≤ 2 * (1 + u) := by
    rw [abs_mul]
    exact mul_le_mul hsumAbs htestedAbs (abs_nonneg _) (by norm_num)
  have hmeanTerm : |(1 - x - y) * (1 + mean)| ≤ 1 + u := by
    calc
      |(1 - x - y) * (1 + mean)| =
          |1 - x - y| * |1 + mean| := abs_mul _ _
      _ ≤ 1 * (1 + u) :=
        mul_le_mul honeAbs hmeanAbs (abs_nonneg _) (by norm_num)
      _ = 1 + u := one_mul _
  have hrawTerm : |(2 - x - y) * u / 2| ≤ u := by
    have hproduct : |2 - x - y| * |u| ≤ 2 * u :=
      mul_le_mul htwoAbs huAbs (abs_nonneg _) (by norm_num)
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hslope :
      |(x + y) * testedValue + (1 - x - y) * (1 + mean) -
          (2 - x - y) * u / 2| ≤ 4 * (u + 1) := by
    calc
      |(x + y) * testedValue + (1 - x - y) * (1 + mean) -
          (2 - x - y) * u / 2| ≤
          |(x + y) * testedValue + (1 - x - y) * (1 + mean)| +
            |(2 - x - y) * u / 2| := abs_sub _ _
      _ ≤ (|(x + y) * testedValue| +
            |(1 - x - y) * (1 + mean)|) +
          |(2 - x - y) * u / 2| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (2 * (1 + u) + (1 + u)) + u := by
        gcongr
      _ ≤ 4 * (u + 1) := by linarith
  have hfactor :
      rawTemplateQuadratic testedValue mean u x -
          rawTemplateQuadratic testedValue mean u y =
        (x - y) *
          ((x + y) * testedValue + (1 - x - y) * (1 + mean) -
            (2 - x - y) * u / 2) := by
    unfold rawTemplateQuadratic
    ring
  rw [hfactor, abs_mul]
  have hmul := mul_le_mul_of_nonneg_left hslope (abs_nonneg (x - y))
  nlinarith

theorem benchmark_mean_le_raw
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u : ℝ} (hu0 : 0 ≤ u)
    (hpriceu : ∀ i, G.price i ≤ u) :
    B.mean ≤ u := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [← benchmarkCellHistogram_mean B]
  apply finiteExpectation_le_bound
  · rw [benchmarkCellHistogram_eq_populationHistogram hn B]
    exact populationHistogram_nonneg _
  · exact benchmarkCellHistogram_mass_one B
  · intro cell
    cases cell <;> simp [positiveGridPrice, hu0, hpriceu]

/-- Every real tested fraction in `[0,1]` has a legal integral quota whose
fractional displacement is at most one job. -/
theorem exists_integralQuota_close
    {n : ℕ} (hn : 0 < n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ quota : Fin (n + 1), |(quota : ℝ) / n - q| ≤ 1 / n := by
  let k : ℕ := ⌊q * (n : ℝ)⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale0 : 0 ≤ q * (n : ℝ) := mul_nonneg hq0 hnR.le
  have hkCastLe : (k : ℝ) ≤ q * (n : ℝ) := by
    dsimp [k]
    exact Nat.floor_le hscale0
  have hkCastN : (k : ℝ) ≤ n := by
    calc
      (k : ℝ) ≤ q * (n : ℝ) := hkCastLe
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hq1 hnR.le
      _ = n := one_mul _
  have hk : k ≤ n := by exact_mod_cast hkCastN
  let quota : Fin (n + 1) := ⟨k, by omega⟩
  have hfracLe : (k : ℝ) / n ≤ q := by
    exact (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hkCastLe)
  have hscaleLt : q * (n : ℝ) < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one _
  have hqLt : q < (k : ℝ) / n + 1 / n := by
    have hdiv : q < ((k : ℝ) + 1) / n :=
      (lt_div_iff₀ hnR).2 (by simpa [mul_comm] using hscaleLt)
    convert hdiv using 1 <;> field_simp
  refine ⟨quota, ?_⟩
  change |(k : ℝ) / n - q| ≤ 1 / n
  rw [abs_of_nonpos (sub_nonpos.mpr hfracLe)]
  linarith

theorem benchmarkRawTemplate_value_close_rawBenchmarkAt_of_tau_le_raw
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u q : ℝ} (hu : 0 < u)
    (hpriceu : ∀ i, G.price i ≤ u) (htau : B.tau ≤ u)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (quota : Fin (n + 1)) :
    |InstanceLearning.gridTemplateValue (benchmarkCellHistogram B)
          G.price u (benchmarkRawTemplate B quota) -
        rawBenchmarkAt B u q| ≤
      4 * (u + 1) * |(benchmarkRawTemplate B quota).fraction - q| := by
  have hmeanU := benchmark_mean_le_raw hn B hu.le hpriceu
  have htested0 : 0 ≤ roundedObligatoryValue B := by
    rw [← rawBenchmarkAt_one_eq_roundedObligatoryValue B u]
    exact rawBenchmarkAt_nonneg B hu (by norm_num) (by norm_num)
  have htestedU : roundedObligatoryValue B ≤ 1 + u := by
    exact (roundedObligatoryValue_le_one_add_mean hn B).trans
      (by linarith)
  rw [benchmarkRawTemplate_value_eq_quadratic hn B u quota,
    rawBenchmarkAt_eq_quadratic_of_test_cost_le_raw B htau hpriceu]
  change |rawTemplateQuadratic (roundedObligatoryValue B) B.mean u
      (benchmarkRawTemplate B quota).fraction -
    rawTemplateQuadratic (roundedObligatoryValue B) B.mean u q| ≤ _
  exact rawTemplateQuadratic_lipschitz hu.le htested0 htestedU
    B.mean_pos.le hmeanU
    (benchmarkRawTemplate B quota).fraction_nonneg
    ((benchmarkRawTemplate B quota).fraction_le_one hn) hq0 hq1

/-- If raw execution is no slower than the maximum-density test module,
every positive-mass tested residual is also no cheaper than raw execution.
Thus the raw block is optimal and the revealing benchmark is exactly the
all-raw area. -/
theorem RawBenchmarkData.value_eq_half_raw_of_raw_le_tau
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hutau : u ≤ B.tau) :
    R.value = u / 2 := by
  let blocks := rawBenchmarkBlocks B u R.qStar
  have hblockMass0 : ∀ b ∈ blocks, 0 ≤ b.mass := by
    dsimp [blocks]
    exact rawBenchmarkBlocks_mass_nonneg B R.qStar_nonneg R.qStar_le_one
  have hblockCost : ∀ b ∈ blocks, b.mass = 0 ∨ u ≤ b.cost := by
    intro b hb
    dsimp [blocks, rawBenchmarkBlocks] at hb
    unfold optionalSortedBlocks knapsackBlocks at hb
    obtain ⟨item, _hitem, rfl⟩ := List.mem_map.mp hb
    rcases item with _ | (_ | i)
    · exact Or.inr hutau
    · exact Or.inr le_rfl
    · rcases benchmarkData_residual_eq_zero_or_tau_le_price hn B i with
        hzero | hprice
      · left
        simp [optionalItemCapacity, hzero]
      · exact Or.inr (hutau.trans hprice)
  have hlower : u / 2 ≤ R.value := by
    have harea := fluidBlocksArea_ge_base_half_sq blocks hu.le
      hblockMass0 hblockCost
    have hmass : fluidBlocksMass blocks = 1 := by
      dsimp [blocks]
      exact rawBenchmarkBlocks_mass_eq_one B u R.qStar
    rw [hmass] at harea
    simpa [RawBenchmarkData.value, rawBenchmarkAt, blocks] using harea
  exact le_antisymm R.value_le_half_raw hlower

/-- The benchmark selector together with one integral quota realizes the
continuous raw-block optimum up to one-job rounding.  The proof covers both
the genuine test/raw mixture and the all-raw long-test branch. -/
theorem exists_benchmarkRawTemplate_value_le_rawBenchmark
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {u : ℝ} (hu : 0 < u)
    (hpriceu : ∀ i, G.price i ≤ u) (R : RawBenchmarkData B u) :
    ∃ quota : Fin (n + 1),
      InstanceLearning.gridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price u
          (benchmarkRawTemplate B quota) ≤
        R.value + 4 * (u + 1) / n := by
  by_cases htau : B.tau ≤ u
  · obtain ⟨quota, hquota⟩ := exists_integralQuota_close hn
      R.qStar_nonneg R.qStar_le_one
    have hclose :=
      benchmarkRawTemplate_value_close_rawBenchmarkAt_of_tau_le_raw
        hn B hu hpriceu htau R.qStar_nonneg R.qStar_le_one quota
    change |InstanceLearning.gridTemplateValue (benchmarkCellHistogram B)
          G.price u (benchmarkRawTemplate B quota) -
        rawBenchmarkAt B u R.qStar| ≤
      4 * (u + 1) * |(quota : ℝ) / n - R.qStar| at hclose
    have hupper := (abs_le.mp hclose).2
    have hscaled := mul_le_mul_of_nonneg_left hquota (by positivity :
      0 ≤ 4 * (u + 1))
    have herror : 4 * (u + 1) * (1 / (n : ℝ)) =
        4 * (u + 1) / n := by ring
    rw [herror] at hscaled
    refine ⟨quota, ?_⟩
    rw [← benchmarkCellHistogram_eq_populationHistogram hn B]
    change InstanceLearning.gridTemplateValue (benchmarkCellHistogram B)
        G.price u (benchmarkRawTemplate B quota) ≤
      rawBenchmarkAt B u R.qStar + 4 * (u + 1) / n
    nlinarith
  · have hutau : u ≤ B.tau := le_of_not_ge htau
    let quota : Fin (n + 1) := ⟨0, by omega⟩
    have htarget :
        InstanceLearning.gridTemplateValue (benchmarkCellHistogram B)
            G.price u (benchmarkRawTemplate B quota) = u / 2 := by
      rw [benchmarkRawTemplate_value_eq_quadratic hn B u quota]
      simp [benchmarkRawTemplate, quota, InstanceLearning.Template.fraction]
    have hvalue :=
      BenchmarkBridge.RawBenchmarkData.value_eq_half_raw_of_raw_le_tau
        hn B R hu hutau
    refine ⟨quota, ?_⟩
    rw [← benchmarkCellHistogram_eq_populationHistogram hn B, htarget,
      hvalue]
    have herror0 : 0 ≤ 4 * (u + 1) / (n : ℝ) := by positivity
    linarith

/-- End-to-end finite upper theorem against the same raw-block benchmark as
the completion-envelope lower bound.  The left side is the literal fixed-
fuel transcript-only strategy; every approximation term is explicit. -/
theorem compiledLearnedStrategy_expectedCost_le_rawBenchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (u : ℝ) (hu : 0 < u)
    (hpriceU : ∀ cell, G.price cell ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u)
    (B : BenchmarkData processing G) (R : RawBenchmarkData B u) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (CompiledStrategy.compiledLearnedStrategy n G.category G.price u
              positions pilotOrder mainOrder) (4 * n + 2)) /
          (n : ℝ) ^ 2)) ≤
      R.value + 4 * (u + 1) / n +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
        (5 * u + 8) / (2 * n) +
        2 * positions.card * (u + 1) / n := by
  obtain ⟨quota, htarget⟩ :=
    exists_benchmarkRawTemplate_value_le_rawBenchmark
      (show 0 < n by omega) B hu hpriceU R
  have hrun := CompiledRun.compiledLearnedStrategy_expectedCost_le
    hn G hprice0 hprice positions hpositions u hu.le hpriceU hroundedU
      (benchmarkRawTemplate B quota)
  calc
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (CompiledStrategy.compiledLearnedStrategy n G.category G.price u
              positions pilotOrder mainOrder) (4 * n + 2)) /
          (n : ℝ) ^ 2)) ≤
        InstanceLearning.gridTemplateValue
            (populationHistogram (roundedGridCell G)) G.price u
            (benchmarkRawTemplate B quota) +
          2 * (u + 2) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
          (5 * u + 8) / (2 * n) +
          2 * positions.card * (u + 1) / n := hrun
    _ ≤ R.value + 4 * (u + 1) / n +
          2 * (u + 2) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
          (5 * u + 8) / (2 * n) +
          2 * positions.card * (u + 1) / n := by
      linarith

end

end BenchmarkBridge
end RevealingOptimization
end SchedulingPaper
