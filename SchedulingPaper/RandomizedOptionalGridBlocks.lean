import SchedulingPaper.RandomizedOptionalBlockEnvelope
import Mathlib.Tactic

/-!
# Canonical block lists for a finite positive grid

Zero mass is kept outside the positive-class type.  The selected positive
mass joins zero in the test module; residual medium and high masses become
SPT-sorted class blocks.  This file identifies their aggregate work, mass,
and ordered minimum-pair moments with `FluidMoments`.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

structure GridFluidData (ι : Type*) [Fintype ι] where
  zeroMass : ℝ
  mass : ι → ℝ
  price : ι → ℝ
  selectedMass : ι → ℝ
  mediumMass : ι → ℝ
  highMass : ι → ℝ

def GridFluidData.moments {ι : Type*} [Fintype ι]
    (G : GridFluidData ι) : FluidMoments where
  lowMass := G.zeroMass + ∑ i, G.selectedMass i
  lowMoment := ∑ i, G.price i * G.selectedMass i
  mediumMoment := ∑ i, G.price i * G.mediumMass i
  highMass := ∑ i, G.highMass i
  mean := ∑ i, G.price i * G.mass i
  mediumMinPair := ∑ i, ∑ j,
    min (G.price i) (G.price j) * G.mediumMass i * G.mediumMass j
  highMinPair := ∑ i, ∑ j,
    min (G.price i) (G.price j) * G.highMass i * G.highMass j

structure GridFluidData.Valid {ι : Type*} [Fintype ι]
    (G : GridFluidData ι) : Prop where
  zero_nonneg : 0 ≤ G.zeroMass
  mass_nonneg : ∀ i, 0 ≤ G.mass i
  price_pos : ∀ i, 0 < G.price i
  selected_nonneg : ∀ i, 0 ≤ G.selectedMass i
  medium_nonneg : ∀ i, 0 ≤ G.mediumMass i
  high_nonneg : ∀ i, 0 ≤ G.highMass i
  partition : ∀ i,
    G.selectedMass i + G.mediumMass i + G.highMass i = G.mass i
  total_mass : G.zeroMass + ∑ i, G.mass i = 1

structure GridClassOrder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (price : ι → ℝ) where
  items : List ι
  nodup : items.Nodup
  complete : items.toFinset = Finset.univ
  sorted : items.Pairwise fun i j => price i ≤ price j

theorem GridClassOrder.sum_eq_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {price : ι → ℝ} (order : GridClassOrder price) (f : ι → ℝ) :
    (order.items.map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset f order.nodup, order.complete]

theorem GridClassOrder.double_sum_eq_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {price : ι → ℝ} (order : GridClassOrder price)
    (f : ι → ι → ℝ) :
    (order.items.map fun i => (order.items.map fun j => f i j).sum).sum =
      ∑ i, ∑ j, f i j := by
  calc
    (order.items.map fun i => (order.items.map fun j => f i j).sum).sum =
        ∑ i, (order.items.map fun j => f i j).sum :=
      order.sum_eq_fintype _
    _ = ∑ i, ∑ j, f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact order.sum_eq_fintype (f i)

def gridMediumBlocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    List FluidBlock :=
  scaledClassBlocks q G.price G.mediumMass order.items

def gridHighBlocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    List FluidBlock :=
  scaledClassBlocks q G.price G.highMass order.items

theorem gridMediumBlocks_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    fluidBlocksMass (gridMediumBlocks G order q) =
      q * ∑ i, G.mediumMass i := by
  unfold gridMediumBlocks
  rw [scaledClassBlocks_mass, order.sum_eq_fintype]

theorem gridHighBlocks_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    fluidBlocksMass (gridHighBlocks G order q) =
      q * ∑ i, G.highMass i := by
  unfold gridHighBlocks
  rw [scaledClassBlocks_mass, order.sum_eq_fintype]

theorem gridMediumBlocks_work
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    fluidBlocksWork (gridMediumBlocks G order q) =
      q * (G.moments.mediumMoment) := by
  unfold gridMediumBlocks GridFluidData.moments
  rw [scaledClassBlocks_work, order.sum_eq_fintype]

theorem gridHighBlocks_work
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ)
    (hvalid : G.Valid) :
    fluidBlocksWork (gridHighBlocks G order q) =
      q * (G.moments.mean - G.moments.lowMoment -
        G.moments.mediumMoment) := by
  unfold gridHighBlocks
  rw [scaledClassBlocks_work, order.sum_eq_fintype]
  unfold GridFluidData.moments
  have hpoint : ∀ i,
      G.price i * G.mass i - G.price i * G.selectedMass i -
          G.price i * G.mediumMass i = G.price i * G.highMass i := by
    intro i
    rw [← hvalid.partition i]
    ring
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply congrArg (fun x => q * x)
  apply Finset.sum_congr rfl
  intro i hi
  exact (hpoint i).symm

theorem gridMediumBlocks_area
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    fluidBlocksArea (gridMediumBlocks G order q) =
      q ^ 2 * G.moments.mediumMinPair / 2 := by
  unfold gridMediumBlocks
  rw [scaledClassBlocks_area q G.price G.mediumMass order.items order.sorted]
  unfold GridFluidData.moments
  rw [order.double_sum_eq_fintype]

theorem gridHighBlocks_area
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price) (q : ℝ) :
    fluidBlocksArea (gridHighBlocks G order q) =
      q ^ 2 * G.moments.highMinPair / 2 := by
  unfold gridHighBlocks
  rw [scaledClassBlocks_area q G.price G.highMass order.items order.sorted]
  unfold GridFluidData.moments
  rw [order.double_sum_eq_fintype]

theorem gridCanonical_mass_relation
    {ι : Type*} [Fintype ι]
    (G : GridFluidData ι) (hvalid : G.Valid) (q : ℝ) :
    q * (∑ i, G.mediumMass i) + (1 - q) +
        q * (∑ i, G.highMass i) =
      1 - G.moments.lowMass * q := by
  unfold GridFluidData.moments
  have hsumPartition :
      (∑ i, G.selectedMass i) + (∑ i, G.mediumMass i) +
          ∑ i, G.highMass i = ∑ i, G.mass i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hvalid.partition i
  have hresidual :
      (∑ i, G.mediumMass i) + ∑ i, G.highMass i =
        1 - G.zeroMass - ∑ i, G.selectedMass i := by
    linarith [hvalid.total_mass, hsumPartition]
  rw [show q * (∑ i, G.mediumMass i) + (1 - q) +
      q * (∑ i, G.highMass i) =
      1 - q + q * ((∑ i, G.mediumMass i) + ∑ i, G.highMass i) by ring,
    hresidual]
  ring

/-- The concrete positive-grid canonical block list has unit mass, total
work `q+μ`, and area exactly `canonicalFluidCost`. -/
theorem gridCanonical_blocks_certificates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price)
    (hvalid : G.Valid) (q τ : ℝ)
    (hmodule : τ * G.moments.lowMass = 1 + G.moments.lowMoment) :
    let medium := gridMediumBlocks G order q
    let high := gridHighBlocks G order q
    let blocks := canonicalFluidBlocks G.moments q τ medium high
    fluidBlocksMass blocks = 1 ∧
      fluidBlocksWork blocks = q + G.moments.mean ∧
      fluidBlocksArea blocks = canonicalFluidCost G.moments q := by
  dsimp
  have hmassRelation := gridCanonical_mass_relation G hvalid q
  have hmediumMass := gridMediumBlocks_mass G order q
  have hhighMass := gridHighBlocks_mass G order q
  have hmass :
      fluidBlocksMass (gridMediumBlocks G order q) + (1 - q) +
          fluidBlocksMass (gridHighBlocks G order q) =
        1 - G.moments.lowMass * q := by
    rw [hmediumMass, hhighMass]
    exact hmassRelation
  refine ⟨canonicalFluidBlocks_mass_eq_one G.moments q τ _ _ hmass,
    canonicalFluidBlocks_work_eq_q_add_mean G.moments q τ _ _ hmodule
      (gridMediumBlocks_work G order q)
      (gridHighBlocks_work G order q hvalid), ?_⟩
  exact canonicalFluidBlocks_area_eq_cost G.moments q τ _ _ hmodule hmass
    (gridMediumBlocks_work G order q) (gridMediumBlocks_area G order q)
    (gridHighBlocks_mass G order q) (gridHighBlocks_area G order q)

/-- Literal remaining-mass integral of the finite-grid canonical envelope. -/
theorem gridCanonical_remaining_integral_eq_cost
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : GridFluidData ι) (order : GridClassOrder G.price)
    (hvalid : G.Valid) {q τ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 < τ)
    (hmean : 0 < G.moments.mean)
    (hmodule : τ * G.moments.lowMass = 1 + G.moments.lowMoment) :
    let medium := gridMediumBlocks G order q
    let high := gridHighBlocks G order q
    let blocks := canonicalFluidBlocks G.moments q τ medium high
    (∫ x in 0..q + G.moments.mean,
      (1 - fluidBlocksCompleted blocks x)) =
        canonicalFluidCost G.moments q := by
  dsimp
  let medium := gridMediumBlocks G order q
  let high := gridHighBlocks G order q
  let blocks := canonicalFluidBlocks G.moments q τ medium high
  have hlowMass0 : 0 ≤ G.moments.lowMass := by
    unfold GridFluidData.moments
    exact add_nonneg hvalid.zero_nonneg
      (Finset.sum_nonneg fun i _ => hvalid.selected_nonneg i)
  have hcost : ∀ b ∈ blocks, 0 < b.cost := by
    intro b hb
    dsimp [blocks, medium, high, canonicalFluidBlocks,
      gridMediumBlocks, gridHighBlocks, scaledClassBlocks] at hb
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hb
    rcases hb with rfl | hmedium | rfl | hhigh
    · exact hτ
    · obtain ⟨i, hi, rfl⟩ := hmedium
      exact hvalid.price_pos i
    · exact hmean
    · obtain ⟨i, hi, rfl⟩ := hhigh
      exact hvalid.price_pos i
  have hmass : ∀ b ∈ blocks, 0 ≤ b.mass := by
    intro b hb
    dsimp [blocks, medium, high, canonicalFluidBlocks,
      gridMediumBlocks, gridHighBlocks, scaledClassBlocks] at hb
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hb
    rcases hb with rfl | hmedium | rfl | hhigh
    · exact mul_nonneg hlowMass0 hq0
    · obtain ⟨i, hi, rfl⟩ := hmedium
      exact mul_nonneg hq0 (hvalid.medium_nonneg i)
    · linarith
    · obtain ⟨i, hi, rfl⟩ := hhigh
      exact mul_nonneg hq0 (hvalid.high_nonneg i)
  have hcert := gridCanonical_blocks_certificates G order hvalid q τ hmodule
  have hmassOne : fluidBlocksMass blocks = 1 := by
    simpa [blocks, medium, high] using hcert.1
  have hwork : fluidBlocksWork blocks = q + G.moments.mean := by
    simpa [blocks, medium, high] using hcert.2.1
  have hmassRelation := gridCanonical_mass_relation G hvalid q
  have hmediumMass :
      fluidBlocksMass medium + (1 - q) + fluidBlocksMass high =
        1 - G.moments.lowMass * q := by
    dsimp [medium, high]
    rw [gridMediumBlocks_mass, gridHighBlocks_mass]
    exact hmassRelation
  have hintegral := canonicalFluidBlocks_remaining_integral_eq_cost
    G.moments q τ medium high hcost hmass hmodule hmediumMass
      (gridMediumBlocks_work G order q)
      (gridMediumBlocks_area G order q)
      (gridHighBlocks_mass G order q)
      (gridHighBlocks_area G order q)
  rw [hmassOne, hwork] at hintegral
  exact hintegral

end

end RandomizedOptional
end SchedulingPaper
