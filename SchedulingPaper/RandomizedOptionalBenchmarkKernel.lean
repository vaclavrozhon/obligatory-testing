import SchedulingPaper.RandomizedOptionalRoundedBenchmark
import SchedulingPaper.RandomizedOptionalCanonicalKernel
import SchedulingPaper.RandomizedOptionalGridBlocks
import Mathlib.Tactic

/-!
# From the announced optional benchmark to the canonical finite kernel

The announced lower bound defines its value as the area of a sorted
fractional-knapsack block list.  The finite upper bound is expressed by the
five moments used by `canonicalFluidCost`.  This file identifies the two
descriptions without committing to a tie-breaking order among equal-cost
blocks.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedEnvelope
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The sorted optional block list has the symmetric minimum-pair area. -/
theorem optionalSortedBlocks_area_eq_half_minPair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (price residual : ι → ℝ) :
    fluidBlocksArea (optionalSortedBlocks q a τ μ price residual) =
      fluidBlocksMinPair
        (optionalSortedBlocks q a τ μ price residual) / 2 := by
  apply fluidBlocksArea_eq_half_minPair
  unfold optionalSortedBlocks knapsackBlocks optionalSortedItems
  rw [List.pairwise_map]
  exact sortedKnapsackItems_pairwise (optionalItemCost τ μ price)

/-- On a duplicate-free enumeration of a finite item type the symmetric
minimum-pair expression is the corresponding double finite sum. -/
theorem knapsackBlocks_minPair_fintype
    {α : Type*} [Fintype α] [DecidableEq α]
    (items : List α) (capacity cost : α → ℝ)
    (hnodup : items.Nodup) (hcomplete : items.toFinset = Finset.univ) :
    fluidBlocksMinPair (knapsackBlocks items capacity cost) =
      ∑ i, ∑ j, min (cost i) (cost j) * capacity i * capacity j := by
  unfold fluidBlocksMinPair knapsackBlocks
  simp only [List.map_map]
  change (items.map fun i =>
      (items.map fun j =>
        min (cost i) (cost j) * capacity i * capacity j).sum).sum = _
  rw [← List.sum_toFinset _ hnodup, hcomplete]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← List.sum_toFinset _ hnodup, hcomplete]

theorem optionalSortedBlocks_minPair_eq_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (price residual : ι → ℝ) :
    fluidBlocksMinPair (optionalSortedBlocks q a τ μ price residual) =
      ∑ i : OptionalKnapsackItem ι, ∑ j : OptionalKnapsackItem ι,
        min (optionalItemCost τ μ price i)
            (optionalItemCost τ μ price j) *
          optionalItemCapacity q a residual i *
          optionalItemCapacity q a residual j := by
  exact knapsackBlocks_minPair_fintype
    (sortedKnapsackItems (optionalItemCost τ μ price))
    (optionalItemCapacity q a residual) (optionalItemCost τ μ price)
    (sortedKnapsackItems_nodup _) (sortedKnapsackItems_complete _)

/-- Residual mass whose rounded class price lies before the blind block. -/
def benchmarkMediumMass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) : ℝ :=
  if G.price i < B.mean then residualPart B.selected B.mass i else 0

/-- Residual mass whose rounded class price lies after the blind block. -/
def benchmarkHighMass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) : ℝ :=
  if G.price i < B.mean then 0 else residualPart B.selected B.mass i

def benchmarkGridFluidData
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : GridFluidData ι where
  zeroMass := B.zeroMass
  mass := B.mass
  price := G.price
  selectedMass := selectedPart B.selected B.mass
  mediumMass := benchmarkMediumMass B
  highMass := benchmarkHighMass B

theorem sum_min_mean_split
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ) (μ : ℝ) :
    (∑ i, min μ (price i) * residual i) =
      (∑ i, price i * (if price i < μ then residual i else 0)) +
        μ * ∑ i, (if price i < μ then 0 else residual i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : price i < μ
  · rw [min_eq_right h.le]
    simp [h]
  · rw [min_eq_left (le_of_not_gt h)]
    simp [h]

theorem sum_min_mean_split_left
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ) (μ : ℝ) :
    (∑ i, min (price i) μ * residual i) =
      (∑ i, price i * (if price i < μ then residual i else 0)) +
        μ * ∑ i, (if price i < μ then 0 else residual i) := by
  simpa [min_comm] using sum_min_mean_split price residual μ

theorem sum_minPair_split
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ) (μ : ℝ) :
    (∑ i, ∑ j, min (price i) (price j) * residual i * residual j) =
      (∑ i, ∑ j,
          min (price i) (price j) *
            (if price i < μ then residual i else 0) *
            (if price j < μ then residual j else 0)) +
      2 * (∑ i, price i * (if price i < μ then residual i else 0)) *
        (∑ i, if price i < μ then 0 else residual i) +
      (∑ i, ∑ j,
          min (price i) (price j) *
            (if price i < μ then 0 else residual i) *
            (if price j < μ then 0 else residual j)) := by
  have hpoint : ∀ i j,
      min (price i) (price j) * residual i * residual j =
        min (price i) (price j) *
            (if price i < μ then residual i else 0) *
            (if price j < μ then residual j else 0) +
          price i * (if price i < μ then residual i else 0) *
            (if price j < μ then 0 else residual j) +
          price j * (if price i < μ then 0 else residual i) *
            (if price j < μ then residual j else 0) +
          min (price i) (price j) *
            (if price i < μ then 0 else residual i) *
            (if price j < μ then 0 else residual j) := by
    intro i j
    by_cases hi : price i < μ <;> by_cases hj : price j < μ
    · simp [hi, hj]
    · have hij : price i ≤ price j := hi.le.trans (le_of_not_gt hj)
      simp [hi, hj, min_eq_left hij]
    · have hji : price j ≤ price i := hj.le.trans (le_of_not_gt hi)
      simp [hi, hj, min_eq_right hji]
    · simp [hi, hj]
  simp_rw [hpoint]
  simp_rw [Finset.sum_add_distrib]
  have hcrossOne :
      (∑ i, ∑ j,
        price i * (if price i < μ then residual i else 0) *
          (if price j < μ then 0 else residual j)) =
        (∑ i, price i * (if price i < μ then residual i else 0)) *
          (∑ j, if price j < μ then 0 else residual j) := by
    rw [Fintype.sum_mul_sum]
  have hcrossTwo :
      (∑ i, ∑ j,
        price j * (if price i < μ then 0 else residual i) *
          (if price j < μ then residual j else 0)) =
        (∑ i, price i * (if price i < μ then residual i else 0)) *
          (∑ j, if price j < μ then 0 else residual j) := by
    calc
      (∑ i, ∑ j,
          price j * (if price i < μ then 0 else residual i) *
            (if price j < μ then residual j else 0)) =
          ∑ i, (if price i < μ then 0 else residual i) *
            (∑ j, price j * (if price j < μ then residual j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [hcrossOne, hcrossTwo]
  ring

theorem sum_scaled_min_mean_split
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ)
    (μ left right : ℝ) :
    (∑ i, min μ (price i) * left * (right * residual i)) =
      left * right *
        ((∑ i, price i * (if price i < μ then residual i else 0)) +
          μ * ∑ i, (if price i < μ then 0 else residual i)) := by
  calc
    (∑ i, min μ (price i) * left * (right * residual i)) =
        left * right * ∑ i, min μ (price i) * residual i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [sum_min_mean_split]

theorem sum_scaled_min_mean_split_left
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ)
    (μ left right : ℝ) :
    (∑ i, min (price i) μ * (left * residual i) * right) =
      left * right *
        ((∑ i, price i * (if price i < μ then residual i else 0)) +
          μ * ∑ i, (if price i < μ then 0 else residual i)) := by
  calc
    (∑ i, min (price i) μ * (left * residual i) * right) =
        left * right * ∑ i, min (price i) μ * residual i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [sum_min_mean_split_left]

theorem sum_scaled_minPair_split
    {ι : Type*} [Fintype ι] (price residual : ι → ℝ)
    (μ q : ℝ) :
    (∑ i, ∑ j,
      min (price i) (price j) * (q * residual i) * (q * residual j)) =
      q ^ 2 *
        ((∑ i, ∑ j,
            min (price i) (price j) *
              (if price i < μ then residual i else 0) *
              (if price j < μ then residual j else 0)) +
          2 * (∑ i, price i * (if price i < μ then residual i else 0)) *
            (∑ i, if price i < μ then 0 else residual i) +
          (∑ i, ∑ j,
            min (price i) (price j) *
              (if price i < μ then 0 else residual i) *
              (if price j < μ then 0 else residual j))) := by
  calc
    (∑ i, ∑ j,
        min (price i) (price j) * (q * residual i) * (q * residual j)) =
        q ^ 2 *
          ∑ i, ∑ j, min (price i) (price j) * residual i * residual j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [sum_minPair_split]

@[simp] theorem benchmarkMediumMass_add_highMass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) :
    benchmarkMediumMass B i + benchmarkHighMass B i =
      residualPart B.selected B.mass i := by
  by_cases h : G.price i < B.mean <;>
    simp [benchmarkMediumMass, benchmarkHighMass, h]

theorem benchmarkGridFluidData_valid
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : (benchmarkGridFluidData B).Valid := by
  let mass0 : ∀ i, 0 ≤ B.mass i := fun i => by
    rw [B.mass_def i]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hzero0 : 0 ≤ B.zeroMass := by
    rw [B.zeroMass_def]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])).1
  refine {
    zero_nonneg := hzero0
    mass_nonneg := mass0
    price_pos := B.price_pos
    selected_nonneg := selectedPart_nonneg mass0
    medium_nonneg := ?_
    high_nonneg := ?_
    partition := ?_
    total_mass := B.population_mass }
  · intro i
    by_cases h : G.price i < B.mean <;>
      simp [benchmarkGridFluidData, benchmarkMediumMass, h,
        residualPart_nonneg mass0 i]
  · intro i
    by_cases h : G.price i < B.mean <;>
      simp [benchmarkGridFluidData, benchmarkHighMass, h,
        residualPart_nonneg mass0 i]
  · intro i
    change selectedPart B.selected B.mass i +
        benchmarkMediumMass B i + benchmarkHighMass B i = B.mass i
    rw [add_assoc, benchmarkMediumMass_add_highMass,
      selectedPart_add_residualPart]

/-- A maximum-density module leaves positive residual mass only at prices at
least its reciprocal density.  This is the pointwise ordering fact needed by
the canonical four-block schedule. -/
theorem benchmarkData_residual_eq_zero_or_tau_le_price
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) :
    residualPart B.selected B.mass i = 0 ∨ B.tau ≤ G.price i := by
  have hmass0 : ∀ j, 0 ≤ B.mass j := by
    intro j
    rw [B.mass_def j]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category j (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category j (p occurrence) = true <;> simp [h])).1
  cases hs : B.selected i with
  | true =>
      exact Or.inl (by simp [residualPart, hs])
  | false =>
      by_cases hm : B.mass i = 0
      · exact Or.inl (by simp [residualPart, hs, hm])
      · right
        have hmi : 0 < B.mass i := lt_of_le_of_ne (hmass0 i) (Ne.symm hm)
        let selectedMass := selectedPart B.selected B.mass
        let x : ι → ℝ := fun j => selectedMass j +
          if j = i then B.mass i else 0
        have hx0 : ∀ j, 0 ≤ x j := by
          intro j
          exact add_nonneg (selectedPart_nonneg hmass0 j) (by
            split <;> positivity)
        have hxcap : ∀ j, x j ≤ B.mass j := by
          intro j
          by_cases hji : j = i
          · subst j
            simp [x, selectedMass, selectedPart, hs]
          · cases hsj : B.selected j <;>
              simp [x, selectedMass, selectedPart, hji, hsj, hmass0 j]
        have hsumX : (∑ j, x j) =
            (∑ j, selectedMass j) + B.mass i := by
          dsimp [x]
          rw [Finset.sum_add_distrib]
          simp
        have hworkX : (∑ j, G.price j * x j) =
            (∑ j, G.price j * selectedMass j) +
              G.price i * B.mass i := by
          dsimp [x]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp
        have hmax := B.density_max x hx0 hxcap
        have hmodule := B.module_density
        unfold RandomizedAnnounced.discoveryMass
          RandomizedAnnounced.discoveryWork at hmax hmodule
        rw [hsumX, hworkX] at hmax
        dsimp [selectedMass] at hmax hmodule
        nlinarith

/-- Algebraic comparison between the sorted-knapsack benchmark and the
canonical four-block moments.  The only ordering hypothesis needed is that
every residual class of positive mass costs at least the test module. -/
theorem benchmarkValue_eq_canonicalFluidCost_of_residual
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G)
    (htauMean : B.tau ≤ B.mean)
    (hresidual : ∀ i,
      residualPart B.selected B.mass i = 0 ∨ B.tau ≤ G.price i) :
    B.value =
      canonicalFluidCost (benchmarkGridFluidData B).moments B.qStar := by
  rw [BenchmarkData.value, optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype]
  simp only [Fintype.sum_option]
  simp only [optionalItemCost, optionalItemCapacity]
  unfold canonicalFluidCost testLowArea mediumArea blindArea highArea
  simp only [GridFluidData.moments, benchmarkGridFluidData,
    benchmarkMediumMass, benchmarkHighMass]
  let a := RandomizedAnnounced.discoveryMass B.zeroMass
    (selectedPart B.selected B.mass)
  let lowMoment := ∑ i, G.price i * selectedPart B.selected B.mass i
  let residual := residualPart B.selected B.mass
  let mediumMoment := ∑ i,
    G.price i * (if G.price i < B.mean then residual i else 0)
  let highMass := ∑ i, if G.price i < B.mean then 0 else residual i
  let mediumPair := ∑ i, ∑ j,
    min (G.price i) (G.price j) *
      (if G.price i < B.mean then residual i else 0) *
      (if G.price j < B.mean then residual j else 0)
  let highPair := ∑ i, ∑ j,
    min (G.price i) (G.price j) *
      (if G.price i < B.mean then 0 else residual i) *
      (if G.price j < B.mean then 0 else residual j)
  have hmodule : B.tau * a = 1 + lowMoment := by
    simpa [a, lowMoment, RandomizedAnnounced.discoveryWork] using
      B.module_density
  have hmass : a + ∑ i, residual i = 1 := by
    dsimp [a, residual, RandomizedAnnounced.discoveryMass]
    have hsplit := sum_selectedPart_add_sum_residualPart B.selected B.mass
    linarith [B.population_mass]
  have hmean : lowMoment + ∑ i, G.price i * residual i = B.mean := by
    simpa [lowMoment, residual] using B.mean_partition
  have hmeanAll : ∑ i, G.price i * B.mass i = B.mean := by
    calc
      (∑ i, G.price i * B.mass i) =
          (∑ i, G.price i * selectedPart B.selected B.mass i) +
            ∑ i, G.price i * residualPart B.selected B.mass i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_add, selectedPart_add_residualPart]
      _ = B.mean := B.mean_partition
  have hminTauRight :
      (∑ i, min B.tau (G.price i) * (a * B.qStar) *
          (B.qStar * residual i)) =
        ∑ i, B.tau * (a * B.qStar) * (B.qStar * residual i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hresidual i with hz | hle
    · have hz' : residual i = 0 := by simpa [residual] using hz
      rw [hz']
      ring
    · rw [min_eq_left hle]
  have hminTauLeft :
      (∑ i, min (G.price i) B.tau * (B.qStar * residual i) *
          (a * B.qStar)) =
        ∑ i, B.tau * (B.qStar * residual i) * (a * B.qStar) := by
    apply Finset.sum_congr rfl
    intro i hi
    rcases hresidual i with hz | hle
    · have hz' : residual i = 0 := by simpa [residual] using hz
      rw [hz']
      ring
    · rw [min_eq_right hle]
  have hmediumHighMass :
      (∑ i, residual i) =
        (∑ i, if G.price i < B.mean then residual i else 0) + highMass := by
    dsimp [highMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : G.price i < B.mean <;> simp [h]
  have hresidualMoment :
      (∑ i, G.price i * residual i) = mediumMoment +
        ∑ i, G.price i * (if G.price i < B.mean then 0 else residual i) := by
    dsimp [mediumMoment]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : G.price i < B.mean <;> simp [h]
  simp only [min_self, min_eq_left htauMean, min_eq_right htauMean]
  rw [show RandomizedAnnounced.discoveryMass B.zeroMass
      (selectedPart B.selected B.mass) = a by rfl]
  rw [show residualPart B.selected B.mass = residual by rfl]
  simp_rw [Finset.sum_add_distrib]
  rw [hminTauRight, hminTauLeft]
  rw [sum_scaled_min_mean_split G.price residual B.mean
    (1 - B.qStar) B.qStar]
  rw [sum_scaled_min_mean_split_left G.price residual B.mean
    B.qStar (1 - B.qStar)]
  rw [sum_scaled_minPair_split G.price residual B.mean B.qStar]
  rw [hmeanAll]
  change _ =
    (1 + lowMoment) *
          (B.qStar - (B.zeroMass + ∑ x, selectedPart B.selected B.mass x) *
            B.qStar ^ 2 / 2) +
        ((B.qStar * mediumMoment) *
            (1 - B.qStar + B.qStar * highMass) +
          B.qStar ^ 2 * mediumPair / 2) +
      B.mean * ((1 - B.qStar) * B.qStar * highMass +
        (1 - B.qStar) ^ 2 / 2) +
      B.qStar ^ 2 * highPair / 2
  have haExpanded : B.zeroMass +
      ∑ x, selectedPart B.selected B.mass x = a := rfl
  rw [haExpanded]
  dsimp [mediumMoment, highMass, mediumPair, highPair] at *
  have hsumTauResidualRight :
      (∑ i, B.tau * (a * B.qStar) * (B.qStar * residual i)) =
        B.tau * a * B.qStar ^ 2 * ∑ i, residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsumTauResidualLeft :
      (∑ i, B.tau * (B.qStar * residual i) * (a * B.qStar)) =
        B.tau * a * B.qStar ^ 2 * ∑ i, residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsumTauResidualRight, hsumTauResidualLeft]
  ring_nf at hmodule hmass hmean hmediumHighMass hresidualMoment ⊢
  linear_combination
    (B.qStar - a * B.qStar ^ 2 / 2) * hmodule +
    (B.tau * a * B.qStar ^ 2) * hmass

theorem benchmarkData_value_eq_canonicalFluidCost
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (htauMean : B.tau ≤ B.mean) :
    B.value =
      canonicalFluidCost (benchmarkGridFluidData B).moments B.qStar := by
  exact benchmarkValue_eq_canonicalFluidCost_of_residual B htauMean
    (benchmarkData_residual_eq_zero_or_tau_le_price hn B)

/-- Once the empirical moments and tested fraction match the announced
benchmark, the already-proved finite kernel theorem gives its complete
`O_L(n)` implementation estimate. -/
theorem canonicalKernelCost_le_benchmark
    {n q : ℕ} (hn : 1 < n) (hq : q ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (htauMean : B.tau ≤ B.mean)
    (processing : Fin n → ℝ) (low medium high : ℝ → Bool)
    {L : ℝ} (hp0 : ∀ x, 0 ≤ processing x)
    (hpL : ∀ x, processing x ≤ L)
    (hmoments : canonicalEmpiricalMoments processing low medium high =
      (benchmarkGridFluidData B).moments)
    (hfraction : (q : ℝ) / n = B.qStar) :
    uniformAverage (canonicalKernelCost q processing low medium high) /
        (n : ℝ) ^ 2 ≤
      B.value + (5 + 18 * L) / n := by
  have hkernel := canonicalKernelCost_fluid_normalized hn hq processing
    low medium high hp0 hpL
  rw [hmoments, hfraction, ← benchmarkData_value_eq_canonicalFluidCost
    (show 0 < n by omega) B htauMean] at hkernel
  linarith [(abs_le.mp hkernel).2]

end

end RandomizedOptional
end SchedulingPaper
