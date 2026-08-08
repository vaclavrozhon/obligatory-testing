import SchedulingPaper.RandomizedOptionalRoundedObservedAreaLower
import SchedulingPaper.RandomizedOptionalBenchmarkOptimizer
import Mathlib.Tactic

/-!
# The empirical optional-testing benchmark after upward rounding

This is the rounded analogue of `BenchmarkData`.  Its mean and all block
prices are computed from the zero-preserving upward-rounded population, while
the online transcript continues to run with the original processing times.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedRoundedLower

open Randomized
open ObservedEnvelope
open AnnouncedExactLower

noncomputable section
attribute [local instance] Classical.propDecidable

structure BenchmarkData {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : RoundedPositiveGrid ι p) where
  selected : ι → Bool
  mass : ι → ℝ
  zeroMass : ℝ
  tau : ℝ
  mean : ℝ
  qStar : ℝ
  qStar_nonneg : 0 ≤ qStar
  qStar_le_one : qStar ≤ 1
  mass_def : ∀ i, mass i = populationMean
    (fun occurrence => if G.category i (p occurrence) then 1 else 0)
  zeroMass_def : zeroMass = populationMean
    (fun occurrence => if zeroCategory (p occurrence) then 1 else 0)
  mean_def : mean = populationMean G.roundedProcessing
  tau_pos : 0 < tau
  mean_pos : 0 < mean
  price_pos : ∀ i, 0 < G.price i
  population_mass : zeroMass + ∑ i, mass i = 1
  mean_partition :
    (∑ i, G.price i * selectedPart selected mass i) +
      ∑ i, G.price i * residualPart selected mass i = mean
  density_max : ∀ x : ι → ℝ,
    (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
    tau * RandomizedAnnounced.discoveryMass zeroMass x ≤
      RandomizedAnnounced.discoveryWork G.price x
  module_pos : 0 < RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  module_density :
    tau * RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass) =
      RandomizedAnnounced.discoveryWork G.price
        (selectedPart selected mass)
  minimizes : ∀ q, 0 ≤ q → q ≤ 1 →
    fluidBlocksArea (optionalSortedBlocks qStar
        (RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass)) tau mean G.price
        (residualPart selected mass)) ≤
      fluidBlocksArea (optionalSortedBlocks q
        (RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass)) tau mean G.price
        (residualPart selected mass))

def BenchmarkData.value {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : ℝ :=
  fluidBlocksArea (optionalSortedBlocks B.qStar
    (RandomizedAnnounced.discoveryMass B.zeroMass
      (selectedPart B.selected B.mass)) B.tau B.mean G.price
    (residualPart B.selected B.mass))

theorem exists_benchmarkData_of_module
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : RoundedPositiveGrid ι p)
    (selected : ι → Bool) (mass : ι → ℝ)
    (zeroMass tau mean : ℝ)
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hmeanDef : mean = populationMean G.roundedProcessing)
    (htau : 0 < tau) (hmean : 0 < mean)
    (hprice : ∀ i, 0 < G.price i)
    (hpopulation : zeroMass + ∑ i, mass i = 1)
    (hpartition :
      (∑ i, G.price i * selectedPart selected mass i) +
        ∑ i, G.price i * residualPart selected mass i = mean)
    (hmax : ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
      tau * RandomizedAnnounced.discoveryMass zeroMass x ≤
        RandomizedAnnounced.discoveryWork G.price x)
    (hmodulePos : 0 < RandomizedAnnounced.discoveryMass zeroMass
      (selectedPart selected mass))
    (hmoduleDensity :
      tau * RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass) =
        RandomizedAnnounced.discoveryWork G.price
          (selectedPart selected mass)) :
    ∃ B : BenchmarkData p G,
      B.selected = selected ∧ B.mass = mass ∧ B.zeroMass = zeroMass ∧
        B.tau = tau ∧ B.mean = mean := by
  obtain ⟨qStar, hq0, hq1, hqMin⟩ :=
    exists_optionalSortedBlocks_area_minimizer
      (RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass)) tau mean G.price
      (residualPart selected mass)
  let B : BenchmarkData p G := {
    selected := selected
    mass := mass
    zeroMass := zeroMass
    tau := tau
    mean := mean
    qStar := qStar
    qStar_nonneg := hq0
    qStar_le_one := hq1
    mass_def := hmassDef
    zeroMass_def := hzeroMassDef
    mean_def := hmeanDef
    tau_pos := htau
    mean_pos := hmean
    price_pos := hprice
    population_mass := hpopulation
    mean_partition := hpartition
    density_max := hmax
    module_pos := hmodulePos
    module_density := hmoduleDensity
    minimizes := hqMin }
  exact ⟨B, rfl, rfl, rfl, rfl, rfl⟩

theorem BenchmarkData.value_le_one_add_mean
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : B.value ≤ 1 + B.mean := by
  let low := selectedPart B.selected B.mass
  let residual := residualPart B.selected B.mass
  let a := RandomizedAnnounced.discoveryMass B.zeroMass low
  let blocks := optionalSortedBlocks B.qStar a B.tau B.mean G.price residual
  have hmass0 : ∀ i, 0 ≤ B.mass i := by
    intro i
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
  have hlow0 : ∀ i, 0 ≤ low i := selectedPart_nonneg hmass0
  have hresidual0 : ∀ i, 0 ≤ residual i := residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := by
    unfold a RandomizedAnnounced.discoveryMass
    exact add_nonneg hzero0 (Finset.sum_nonneg fun i _ => hlow0 i)
  have hmassPartition : a + ∑ i, residual i = 1 := by
    unfold a RandomizedAnnounced.discoveryMass low residual
    have hsplit := sum_selectedPart_add_sum_residualPart B.selected B.mass
    linarith [B.population_mass]
  let lowWork := ∑ i, G.price i * low i
  have hmeanPartition : lowWork + ∑ i, G.price i * residual i = B.mean := by
    simpa [lowWork, low, residual] using B.mean_partition
  have hmodule : B.tau * a = 1 + lowWork := by
    simpa [a, lowWork, low, RandomizedAnnounced.discoveryWork] using
      B.module_density
  have hmassOne : fluidBlocksMass blocks = 1 := by
    dsimp [blocks]
    exact optionalSortedBlocks_mass_eq_one B.qStar a B.tau B.mean G.price
      residual hmassPartition
  have hwork : fluidBlocksWork blocks = B.qStar + B.mean := by
    dsimp [blocks]
    exact optionalSortedBlocks_work_eq_q_add_mean B.qStar a B.tau B.mean
      lowWork G.price residual hmodule hmeanPartition
  have hcost : ∀ b ∈ blocks, 0 ≤ b.cost := by
    intro b hb
    exact (optionalSortedBlocks_cost_pos B.tau_pos B.mean_pos B.price_pos
      b (by simpa [blocks] using hb)).le
  have hblockMass : ∀ b ∈ blocks, 0 ≤ b.mass := by
    intro b hb
    exact optionalSortedBlocks_mass_nonneg B.qStar_nonneg B.qStar_le_one
      ha0 hresidual0 b (by simpa [blocks] using hb)
  have harea := fluidBlocksArea_le_work_mul_mass blocks hcost hblockMass
  unfold BenchmarkData.value
  change fluidBlocksArea blocks ≤ 1 + B.mean
  rw [hwork, hmassOne] at harea
  nlinarith [B.qStar_le_one]

/-- Every positive empirical population and upward grid canonically supplies
the maximum-density module and a minimizing test fraction. -/
theorem exists_empiricalBenchmarkData
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : RoundedPositiveGrid ι p)
    (hprice : ∀ i, 0 < G.price i)
    (hmeanPos : 0 < populationMean G.roundedProcessing) :
    Nonempty (BenchmarkData p G) := by
  classical
  let mass : ι → ℝ := fun i => populationMean
    (fun occurrence => if G.category i (p occurrence) then 1 else 0)
  let zeroMass : ℝ := populationMean
    (fun occurrence => if zeroCategory (p occurrence) then 1 else 0)
  let mean : ℝ := populationMean G.roundedProcessing
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    dsimp [mass]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hzero0 : 0 ≤ zeroMass := by
    dsimp [zeroMass]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])).1
  have hpointMass : ∀ occurrence,
      (if zeroCategory (p occurrence) then (1 : ℝ) else 0) +
          ∑ i, (if G.category i (p occurrence) then (1 : ℝ) else 0) = 1 := by
    intro occurrence
    rw [G.sum_category_indicator occurrence]
    by_cases hz : p occurrence = 0 <;> simp [zeroCategory, hz]
  have hpopulation : zeroMass + ∑ i, mass i = 1 := by
    dsimp [zeroMass, mass]
    unfold populationMean
    simp only [Fintype.card_fin]
    rw [← Finset.sum_div]
    field_simp [hnR.ne']
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ occurrence,
          ((if zeroCategory (p occurrence) then (1 : ℝ) else 0) +
            ∑ i, (if G.category i (p occurrence) then (1 : ℝ) else 0))) =
          ∑ _occurrence : Fin n, (1 : ℝ) :=
        Finset.sum_congr rfl fun occurrence _ => hpointMass occurrence
      _ = n := by simp
  have hmeanPartitionAll : ∑ i, G.price i * mass i = mean := by
    dsimp [mass, mean]
    unfold populationMean RoundedPositiveGrid.roundedProcessing
    simp only [Fintype.card_fin]
    have hleft :
        (∑ i, G.price i *
            ((∑ occurrence,
              (if G.category i (p occurrence) then (1 : ℝ) else 0)) / n)) =
          (∑ i, G.price i *
            ∑ occurrence,
              (if G.category i (p occurrence) then (1 : ℝ) else 0)) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hleft]
    field_simp [hnR.ne']
    have hdistribute :
        (∑ i, G.price i *
            ∑ occurrence,
              (if G.category i (p occurrence) then (1 : ℝ) else 0)) =
          ∑ i, ∑ occurrence,
            G.price i *
              (if G.category i (p occurrence) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    rw [hdistribute, Finset.sum_comm]
  obtain ⟨D⟩ := AnnouncedExactLower.exists_densityModule zeroMass mass G.price
    hzero0 hmass0 hprice hpopulation
  have hpartition :
      (∑ i, G.price i * selectedPart D.selected mass i) +
        ∑ i, G.price i * residualPart D.selected mass i = mean := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i, (G.price i * selectedPart D.selected mass i +
        G.price i * residualPart D.selected mass i)) =
          ∑ i, G.price i * mass i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← mul_add, selectedPart_add_residualPart]
      _ = mean := hmeanPartitionAll
  obtain ⟨B, _⟩ := exists_benchmarkData_of_module p G D.selected mass
    zeroMass D.tau mean (fun _ => rfl) rfl rfl D.tau_pos hmeanPos hprice
    hpopulation hpartition D.density_max D.module_pos D.module_density
  exact ⟨B⟩

end

end AnnouncedRoundedLower
end RandomizedOptional
end SchedulingPaper
