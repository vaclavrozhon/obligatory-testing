import SchedulingPaper.RandomizedOptionalAnnouncedExactLower
import Mathlib.Tactic

/-!
# Constructing the optional-testing fluid benchmark

For a finite empirical histogram, this file constructs the maximum-density
test module and combines it with compactness of `[0,1]` to produce the full
`BenchmarkData` used by the announced lower bound.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedExactLower

open Randomized
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

def moduleSubsetMass {ι : Type*} [Fintype ι]
    (zeroMass : ℝ) (mass : ι → ℝ) (S : Finset ι) : ℝ :=
  zeroMass + ∑ i ∈ S, mass i

def moduleSubsetWork {ι : Type*} [Fintype ι]
    (price mass : ι → ℝ) (S : Finset ι) : ℝ :=
  1 + ∑ i ∈ S, price i * mass i

def moduleSubsetDensity {ι : Type*} [Fintype ι]
    (zeroMass : ℝ) (mass price : ι → ℝ) (S : Finset ι) : ℝ :=
  moduleSubsetMass zeroMass mass S / moduleSubsetWork price mass S

def IsMaximumModuleSubset {ι : Type*} [Fintype ι]
    (zeroMass : ℝ) (mass price : ι → ℝ) (S : Finset ι) : Prop :=
  ∀ T, moduleSubsetDensity zeroMass mass price T ≤
    moduleSubsetDensity zeroMass mass price S

theorem exists_maximumModuleSubset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (zeroMass : ℝ) (mass price : ι → ℝ) :
    ∃ S : Finset ι, IsMaximumModuleSubset zeroMass mass price S := by
  classical
  obtain ⟨S, _hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset : Finset (Finset ι))
    (moduleSubsetDensity zeroMass mass price) (by simp)
  refine ⟨S, ?_⟩
  intro T
  exact hmax T (by simp)

structure DensityModule {ι : Type*} [Fintype ι]
    (zeroMass : ℝ) (mass price : ι → ℝ) where
  selected : ι → Bool
  tau : ℝ
  tau_pos : 0 < tau
  density_max : ∀ x : ι → ℝ,
    (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
    tau * RandomizedAnnounced.discoveryMass zeroMass x ≤
      RandomizedAnnounced.discoveryWork price x
  module_pos : 0 < RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  module_density :
    tau * RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass) =
      RandomizedAnnounced.discoveryWork price
        (selectedPart selected mass)

theorem moduleSubsetWork_pos
    {ι : Type*} [Fintype ι] {mass price : ι → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hprice : ∀ i, 0 ≤ price i)
    (S : Finset ι) : 0 < moduleSubsetWork price mass S := by
  unfold moduleSubsetWork
  have hsum : 0 ≤ ∑ i ∈ S, price i * mass i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hprice i) (hmass i)
  linarith

theorem maximumModuleSubset_contains_below
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {zeroMass : ℝ} {mass price : ι → ℝ} {S : Finset ι} {tau : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hprice : ∀ i, 0 ≤ price i)
    (hmax : IsMaximumModuleSubset zeroMass mass price S)
    (hmodulePos : 0 < moduleSubsetMass zeroMass mass S)
    (hdensity : moduleSubsetWork price mass S =
      moduleSubsetMass zeroMass mass S * tau)
    {i : ι} (hmi : 0 < mass i) (hbelow : price i < tau) :
    i ∈ S := by
  classical
  by_contra hi
  have hiNot : i ∉ S := hi
  have hworkS := moduleSubsetWork_pos hmass hprice S
  have hworkInsert := moduleSubsetWork_pos hmass hprice (insert i S)
  have hmassInsert : moduleSubsetMass zeroMass mass (insert i S) =
      moduleSubsetMass zeroMass mass S + mass i := by
    unfold moduleSubsetMass
    rw [Finset.sum_insert hiNot]
    ring
  have hworkInsertEq : moduleSubsetWork price mass (insert i S) =
      moduleSubsetWork price mass S + price i * mass i := by
    unfold moduleSubsetWork
    rw [Finset.sum_insert hiNot]
    ring
  have himprove :
      moduleSubsetDensity zeroMass mass price S <
        moduleSubsetDensity zeroMass mass price (insert i S) := by
    unfold moduleSubsetDensity
    rw [div_lt_div_iff₀ hworkS hworkInsert]
    rw [hmassInsert, hworkInsertEq]
    nlinarith [mul_pos hmi hmodulePos]
  exact (not_lt_of_ge (hmax (insert i S))) himprove

theorem maximumModuleSubset_excludes_above
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {zeroMass : ℝ} {mass price : ι → ℝ} {S : Finset ι} {tau : ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hprice : ∀ i, 0 ≤ price i)
    (hmax : IsMaximumModuleSubset zeroMass mass price S)
    (hmodulePos : 0 < moduleSubsetMass zeroMass mass S)
    (hdensity : moduleSubsetWork price mass S =
      moduleSubsetMass zeroMass mass S * tau)
    {i : ι} (hmi : 0 < mass i) (habove : tau < price i) :
    i ∉ S := by
  classical
  intro hi
  let T := S.erase i
  have hworkS := moduleSubsetWork_pos hmass hprice S
  have hworkT := moduleSubsetWork_pos hmass hprice T
  have hmassErase : moduleSubsetMass zeroMass mass T + mass i =
      moduleSubsetMass zeroMass mass S := by
    dsimp [T]
    unfold moduleSubsetMass
    have hsum := Finset.sum_erase_add S mass hi
    linarith
  have hworkErase : moduleSubsetWork price mass T + price i * mass i =
      moduleSubsetWork price mass S := by
    dsimp [T]
    unfold moduleSubsetWork
    have hsum := Finset.sum_erase_add S (fun j => price j * mass j) hi
    linarith
  have himprove :
      moduleSubsetDensity zeroMass mass price S <
        moduleSubsetDensity zeroMass mass price T := by
    unfold moduleSubsetDensity
    rw [div_lt_div_iff₀ hworkS hworkT]
    nlinarith [mul_pos hmi hmodulePos]
  exact (not_lt_of_ge (hmax T)) himprove

/-- Every nonnegative finite probability histogram has a maximum-density
test module.  The zero atom is automatically part of every module and is
therefore represented outside the selected positive classes. -/
theorem exists_densityModule
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (zeroMass : ℝ) (mass price : ι → ℝ)
    (hzero : 0 ≤ zeroMass) (hmass : ∀ i, 0 ≤ mass i)
    (hprice : ∀ i, 0 < price i)
    (htotal : zeroMass + ∑ i, mass i = 1) :
    Nonempty (DensityModule zeroMass mass price) := by
  classical
  obtain ⟨S, hmax⟩ := exists_maximumModuleSubset zeroMass mass price
  have hprice0 : ∀ i, 0 ≤ price i := fun i => (hprice i).le
  have hworkS := moduleSubsetWork_pos hmass hprice0 S
  have hworkUniv := moduleSubsetWork_pos hmass hprice0 (Finset.univ : Finset ι)
  have hmassUniv : moduleSubsetMass zeroMass mass (Finset.univ : Finset ι) = 1 := by
    simpa [moduleSubsetMass] using htotal
  have hunivDensity : 0 < moduleSubsetDensity zeroMass mass price
      (Finset.univ : Finset ι) := by
    unfold moduleSubsetDensity
    rw [hmassUniv]
    positivity
  have hselectedDensity : 0 < moduleSubsetDensity zeroMass mass price S :=
    lt_of_lt_of_le hunivDensity (hmax Finset.univ)
  have hmodulePos : 0 < moduleSubsetMass zeroMass mass S := by
    unfold moduleSubsetDensity at hselectedDensity
    rcases div_pos_iff.mp hselectedDensity with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hworkS.le) hneg.2)
  let tau := moduleSubsetWork price mass S /
    moduleSubsetMass zeroMass mass S
  have htau : 0 < tau := div_pos hworkS hmodulePos
  have hdensity : moduleSubsetWork price mass S =
      moduleSubsetMass zeroMass mass S * tau := by
    dsimp [tau]
    field_simp [hmodulePos.ne']
  let selected : ι → Bool := fun i => decide (i ∈ S)
  have hselectedPart : selectedPart selected mass = fun i =>
      if i ∈ S then mass i else 0 := by
    funext i
    by_cases hi : i ∈ S <;> simp [selected, selectedPart, hi]
  have hmoduleMass :
      RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass) =
        moduleSubsetMass zeroMass mass S := by
    unfold RandomizedAnnounced.discoveryMass moduleSubsetMass
    rw [hselectedPart]
    simp
  have hmoduleWork :
      RandomizedAnnounced.discoveryWork price
          (selectedPart selected mass) =
        moduleSubsetWork price mass S := by
    unfold RandomizedAnnounced.discoveryWork moduleSubsetWork
    rw [hselectedPart]
    simp
  have hstarLow : ∀ i, price i < tau →
      selectedPart selected mass i = mass i := by
    intro i hi
    by_cases hmi : mass i = 0
    · simp [selectedPart, hmi]
    · have hmiPos : 0 < mass i := lt_of_le_of_ne (hmass i) (Ne.symm hmi)
      have hiS := maximumModuleSubset_contains_below hmass hprice0 hmax
        hmodulePos hdensity hmiPos hi
      simp [selectedPart, selected, hiS]
  have hstarHigh : ∀ i, tau < price i →
      selectedPart selected mass i = 0 := by
    intro i hi
    by_cases hmi : mass i = 0
    · simp [selectedPart, hmi]
    · have hmiPos : 0 < mass i := lt_of_le_of_ne (hmass i) (Ne.symm hmi)
      have hiS := maximumModuleSubset_excludes_above hmass hprice0 hmax
        hmodulePos hdensity hmiPos hi
      simp [selectedPart, selected, hiS]
  let D : DensityModule zeroMass mass price := {
    selected := selected
    tau := tau
    tau_pos := htau
    density_max := fun x hx0 hxcap =>
      RandomizedAnnounced.threshold_maximizes_discovery_density
        hx0 hxcap hstarLow hstarHigh (by
          rw [hmoduleMass, hmoduleWork, hdensity]
          ring)
    module_pos := by simpa [hmoduleMass] using hmodulePos
    module_density := by
      rw [hmoduleMass, hmoduleWork, hdensity]
      ring }
  exact ⟨D⟩

/-- An exact positive empirical grid with positive mean canonically supplies
all data required by the finite announced benchmark: empirical masses, a
maximum-density threshold module, and a minimizing tested fraction. -/
theorem exists_empiricalBenchmarkData
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (G : ExactPositiveGrid ι p)
    (hprice : ∀ i, 0 < G.price i)
    (hmeanPos : 0 < populationMean p) :
    ∃ B : BenchmarkData p G, True := by
  classical
  let mass : ι → ℝ := fun i => populationMean
    (fun occurrence => if G.category i (p occurrence) then 1 else 0)
  let zeroMass : ℝ := populationMean
    (fun occurrence => if zeroCategory (p occurrence) then 1 else 0)
  let mean : ℝ := populationMean p
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
    by_cases hz : p occurrence = 0
    · simp [zeroCategory, hz]
    · simp [zeroCategory, hz]
  have hpopulation : zeroMass + ∑ i, mass i = 1 := by
    dsimp [zeroMass, mass]
    unfold populationMean
    simp only [Fintype.card_fin]
    have hrest :
        (∑ i, (∑ occurrence,
            (if G.category i (p occurrence) then (1 : ℝ) else 0)) / n) =
          (∑ i, ∑ occurrence,
            (if G.category i (p occurrence) then (1 : ℝ) else 0)) / n := by
      exact (Finset.sum_div _ _ (n : ℝ)).symm
    rw [hrest]
    field_simp [hnR.ne']
    rw [Finset.sum_comm]
    have hcombined :
        (∑ occurrence,
            (if zeroCategory (p occurrence) then (1 : ℝ) else 0)) +
          (∑ occurrence, ∑ i,
            (if G.category i (p occurrence) then (1 : ℝ) else 0)) = n := by
      rw [← Finset.sum_add_distrib]
      calc
        (∑ occurrence,
            ((if zeroCategory (p occurrence) then (1 : ℝ) else 0) +
              ∑ i, (if G.category i (p occurrence) then (1 : ℝ) else 0))) =
            ∑ _occurrence : Fin n, (1 : ℝ) :=
          Finset.sum_congr rfl fun occurrence _ => hpointMass occurrence
        _ = n := by simp
    exact hcombined
  have hmeanPartitionAll : ∑ i, G.price i * mass i = mean := by
    dsimp [mass, mean]
    unfold populationMean
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
    apply Finset.sum_congr rfl
    intro occurrence ho
    exact G.sum_price_indicator occurrence
  obtain ⟨D⟩ := exists_densityModule zeroMass mass G.price hzero0 hmass0
    hprice hpopulation
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
  exact ⟨B, trivial⟩

end

end AnnouncedExactLower
end RandomizedOptional
end SchedulingPaper
