import SchedulingPaper.RandomizedOptionalObservedAreaLower
import SchedulingPaper.RandomizedOptionalGoodEventAverage
import Mathlib.Tactic

/-!
# Finite announced lower bound on an exact support

This file packages the deterministic pathwise theorem and the finite
good/bad averaging lemma.  It deliberately leaves the numerical urn
probability as an input; the next layer instantiates it from the global
checkpoint bounds.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedExactLower

open Randomized
open ObservedOnline
open ObservedTrace
open TraceBijection
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

structure BenchmarkData {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : ExactPositiveGrid ι p) where
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
  mean_def : mean = populationMean p
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

/-- Once a maximum-density module has been supplied, compactness of the
one-dimensional fluid objective supplies the optimizing tested fraction.
Thus `qStar` is never an additional existence assumption. -/
theorem exists_benchmarkData_of_module
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : ExactPositiveGrid ι p)
    (selected : ι → Bool) (mass : ι → ℝ)
    (zeroMass tau mean : ℝ)
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hmeanDef : mean = populationMean p)
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

def BenchmarkData.value {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : ExactPositiveGrid ι p}
    (B : BenchmarkData p G) : ℝ :=
  fluidBlocksArea (optionalSortedBlocks B.qStar
    (RandomizedAnnounced.discoveryMass B.zeroMass
      (selectedPart B.selected B.mass)) B.tau B.mean G.price
    (residualPart B.selected B.mass))

/-- Uniform coarse bound on the benchmark area.  It is used only to pay for
the bad concentration event, so no sharp constant is needed. -/
theorem BenchmarkData.value_le_one_add_mean
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : ExactPositiveGrid ι p}
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

structure PlacementGood {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : ExactPositiveGrid ι p}
    (B : BenchmarkData p G) (policy : CompletePolicy p)
    (γ blindError : ℝ) (σ : ObservedTrace.Placement n) : Prop where
  class_good : ∀ cutoff i,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if G.category i
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.mass i *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n
  zero_good : ∀ cutoff,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if zeroCategory
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.zeroMass *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n
  blind_good : ∀ cutoff,
    |(∑ k ∈ positionsThrough cutoff,
        compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          p (revealOrder (touchTrace p policy) σ k)) -
      B.mean *
        ∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ blindError * n

def normalizedCost {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : ObservedTrace.Placement n) : ℝ :=
  completionCost (placedProcessing p σ)
      (settledRun p policy.strategy σ).config.transcript / (n : ℝ) ^ 2

/-- Finite exact-support announced lower bound after averaging the pathwise
envelope inequality over uniform hidden placements. -/
theorem uniformAverage_normalizedCost_ge
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (G : ExactPositiveGrid ι p) (B : BenchmarkData p G)
    {γ blindError δ U : ℝ}
    (hγ : 0 ≤ γ) (hblindError : 0 ≤ blindError)
    (hU0 : 0 ≤ U) (hvalueU : B.value ≤ U)
    (hbad : uniformProbability
      (fun σ => ¬ PlacementGood B policy γ blindError σ) ≤ δ) :
    B.value - blindError - (Fintype.card ι + 1) * γ * (1 + B.mean) -
        U * δ ≤
      uniformAverage (normalizedCost p policy) := by
  classical
  let Bad : ObservedTrace.Placement n → Prop := fun σ =>
    ¬ PlacementGood B policy γ blindError σ
  let repaired := B.value - blindError -
    (Fintype.card ι + 1) * γ * (1 + B.mean)
  have hprocessing : ∀ σ job, 0 ≤ placedProcessing p σ job := by
    intro σ job
    exact G.processing_nonneg (σ job)
  have hcost0 : ∀ σ, 0 ≤ normalizedCost p policy σ := by
    intro σ
    unfold normalizedCost
    apply div_nonneg
    · apply completionCost_nonneg_of_revealsMatch (hprocessing σ)
      dsimp [settledRun]
      exact (run_historyInvariant (placedProcessing p σ) policy.strategy
        (2 * n + 1)).revealsMatch
    · positivity
  have hgood : ∀ σ, ¬ Bad σ → repaired ≤ normalizedCost p policy σ := by
    intro σ hnotBad
    have hplacement : PlacementGood B policy γ blindError σ := by
      simpa [Bad] using hnotBad
    have hpath := settled_cost_ge_fixedFluidMinimum hn p policy σ G
      B.selected B.mass_def B.zeroMass_def B.mean_def hγ hblindError
      B.tau_pos B.mean_pos B.price_pos B.population_mass B.mean_partition
      hplacement.class_good hplacement.zero_good hplacement.blind_good
      B.density_max B.module_pos B.module_density B.minimizes
    simpa [repaired, BenchmarkData.value, normalizedCost] using hpath
  have hrepairedU : repaired ≤ U := by
    dsimp [repaired]
    have hrepair0 : 0 ≤ blindError +
        (Fintype.card ι + 1 : ℝ) * γ * (1 + B.mean) := by
      have hmean0 : 0 ≤ B.mean := B.mean_pos.le
      positivity
    linarith
  have haverage := uniformAverage_ge_of_good_event
    (normalizedCost p policy) Bad hcost0 hgood hrepairedU hU0
    (by simpa [Bad] using hbad)
  simpa [repaired, Bad, sub_eq_add_neg, add_assoc] using haverage

end

end AnnouncedExactLower
end RandomizedOptional
end SchedulingPaper
