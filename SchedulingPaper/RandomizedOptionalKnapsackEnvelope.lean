import SchedulingPaper.RandomizedOptionalBlockEnvelope
import SchedulingPaper.RandomizedOptionalGridBridge
import Mathlib.Tactic

/-!
# The literal sorted optional-knapsack envelope

This file specializes the generic ordered block construction to the three
families used by optional testing: the full test module, the blind module,
and one residual item for every positive grid class.  It supplies the greedy
allocation and supporting pivot required by the operational prefix bridge,
instead of leaving those objects as hypotheses.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

def optionalSortedItems {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ μ : ℝ) (p : ι → ℝ) : List (OptionalKnapsackItem ι) :=
  sortedKnapsackItems (optionalItemCost τ μ p)

def optionalSortedBlocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (p residualMass : ι → ℝ) : List FluidBlock :=
  knapsackBlocks (optionalSortedItems τ μ p)
    (optionalItemCapacity q a residualMass) (optionalItemCost τ μ p)

def optionalSortedAllocation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ x : ℝ) (p residualMass : ι → ℝ) :
    OptionalKnapsackItem ι → ℝ :=
  orderedGreedyAllocation (optionalItemCapacity q a residualMass)
    (optionalItemCost τ μ p) (optionalSortedItems τ μ p) x

def optionalSortedModule {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ x : ℝ) (p residualMass : ι → ℝ) : ℝ :=
  optionalSortedAllocation q a τ μ x p residualMass none

def optionalSortedBlind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ x : ℝ) (p residualMass : ι → ℝ) : ℝ :=
  optionalSortedAllocation q a τ μ x p residualMass (some none)

def optionalSortedResidual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ x : ℝ) (p residualMass : ι → ℝ) (i : ι) : ℝ :=
  optionalSortedAllocation q a τ μ x p residualMass (some (some i))

/-- For fixed class data, the exact greedy-envelope area depends
continuously on the tested fraction. -/
theorem continuous_optionalSortedBlocks_area
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a τ μ : ℝ) (p residualMass : ι → ℝ) :
    Continuous (fun q =>
      fluidBlocksArea (optionalSortedBlocks q a τ μ p residualMass)) := by
  change Continuous (fun q => fluidBlocksArea
    ((optionalSortedItems τ μ p).map fun item =>
      ⟨optionalItemCost τ μ p item,
        optionalItemCapacity q a residualMass item⟩))
  apply continuous_fluidBlocksArea_map
  intro item hitem
  rcases item with _ | (_ | i) <;>
    simp only [optionalItemCapacity] <;> fun_prop

/-- The one-dimensional fluid optimization always attains its minimum on
`[0,1]`.  This removes the formerly implicit `argmin` assumption from the
finite announced benchmark. -/
theorem exists_optionalSortedBlocks_area_minimizer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a τ μ : ℝ) (p residualMass : ι → ℝ) :
    ∃ qStar : ℝ, 0 ≤ qStar ∧ qStar ≤ 1 ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
        fluidBlocksArea (optionalSortedBlocks qStar a τ μ p residualMass) ≤
          fluidBlocksArea (optionalSortedBlocks q a τ μ p residualMass) := by
  let f : ℝ → ℝ := fun q =>
    fluidBlocksArea (optionalSortedBlocks q a τ μ p residualMass)
  have hf : Continuous f := continuous_optionalSortedBlocks_area a τ μ p residualMass
  obtain ⟨qStar, hqStar, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hf.continuousOn
  exact ⟨qStar, hqStar.1, hqStar.2, fun q hq0 hq1 => hmin ⟨hq0, hq1⟩⟩

theorem optionalItemAllocation_sorted_components
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ x : ℝ) (p residualMass : ι → ℝ) :
    optionalItemAllocation
        (optionalSortedModule q a τ μ x p residualMass)
        (optionalSortedBlind q a τ μ x p residualMass)
        (optionalSortedResidual q a τ μ x p residualMass) =
      optionalSortedAllocation q a τ μ x p residualMass := by
  funext item
  rcases item with _ | (_ | i) <;>
    rfl

theorem optionalSortedBlocks_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (p residualMass : ι → ℝ) :
    fluidBlocksMass (optionalSortedBlocks q a τ μ p residualMass) =
      a * q + (1 - q) + q * ∑ i, residualMass i := by
  let capacity := optionalItemCapacity q a residualMass
  let cost := optionalItemCost τ μ p
  have hsum : fluidBlocksMass
      (knapsackBlocks (sortedKnapsackItems cost) capacity cost) =
        fractionalMass capacity := by
    rw [knapsackBlocks_mass]
    unfold fractionalMass
    rw [← sortedKnapsackItems_complete cost,
      List.sum_toFinset _ (sortedKnapsackItems_nodup cost)]
  rw [show optionalSortedBlocks q a τ μ p residualMass =
      knapsackBlocks (sortedKnapsackItems cost) capacity cost by rfl,
    hsum]
  simp [capacity, optionalItemCapacity, fractionalMass]
  rw [Finset.mul_sum]
  ring

theorem optionalSortedBlocks_work
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (p residualMass : ι → ℝ) :
    fluidBlocksWork (optionalSortedBlocks q a τ μ p residualMass) =
      τ * (a * q) + μ * (1 - q) +
        q * ∑ i, p i * residualMass i := by
  let capacity := optionalItemCapacity q a residualMass
  let cost := optionalItemCost τ μ p
  have hsum : fluidBlocksWork
      (knapsackBlocks (sortedKnapsackItems cost) capacity cost) =
        fractionalWork cost capacity := by
    rw [knapsackBlocks_work]
    unfold fractionalWork
    rw [← sortedKnapsackItems_complete cost,
      List.sum_toFinset _ (sortedKnapsackItems_nodup cost)]
  rw [show optionalSortedBlocks q a τ μ p residualMass =
      knapsackBlocks (sortedKnapsackItems cost) capacity cost by rfl,
    hsum]
  simp [capacity, cost, optionalItemCapacity, optionalItemCost,
    fractionalWork]
  rw [Finset.mul_sum]
  ring

theorem optionalSortedBlocks_mass_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ : ℝ) (p residualMass : ι → ℝ)
    (hpartition : a + ∑ i, residualMass i = 1) :
    fluidBlocksMass (optionalSortedBlocks q a τ μ p residualMass) = 1 := by
  rw [optionalSortedBlocks_mass]
  linear_combination q * hpartition

theorem optionalSortedBlocks_work_eq_q_add_mean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a τ μ lowWork : ℝ) (p residualMass : ι → ℝ)
    (hmodule : τ * a = 1 + lowWork)
    (hmean : lowWork + ∑ i, p i * residualMass i = μ) :
    fluidBlocksWork (optionalSortedBlocks q a τ μ p residualMass) = q + μ := by
  rw [optionalSortedBlocks_work]
  linear_combination q * hmodule + q * hmean

theorem optionalSortedBlocks_cost_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q a τ μ : ℝ} {p residualMass : ι → ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hp : ∀ i, 0 < p i) :
    ∀ b ∈ optionalSortedBlocks q a τ μ p residualMass, 0 < b.cost := by
  intro b hb
  unfold optionalSortedBlocks knapsackBlocks at hb
  obtain ⟨item, _hitem, rfl⟩ := List.mem_map.mp hb
  rcases item with _ | (_ | i)
  · exact hτ
  · exact hμ
  · exact hp i

theorem optionalSortedBlocks_mass_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q a τ μ : ℝ} {p residualMass : ι → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (hresidual0 : ∀ i, 0 ≤ residualMass i) :
    ∀ b ∈ optionalSortedBlocks q a τ μ p residualMass, 0 ≤ b.mass := by
  intro b hb
  unfold optionalSortedBlocks knapsackBlocks at hb
  obtain ⟨item, _hitem, rfl⟩ := List.mem_map.mp hb
  rcases item with _ | (_ | i)
  · exact mul_nonneg ha0 hq0
  · dsimp [optionalItemCapacity]
    linarith
  · exact mul_nonneg hq0 (hresidual0 i)

/-- Executable greedy certificate for the optional item family at every
work budget within the terminal work of the envelope. -/
theorem optionalSortedAllocation_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q a τ μ x : ℝ} {p residualMass : ι → ℝ}
    (hτ : 0 < τ) (hμ : 0 < μ) (hp : ∀ i, 0 < p i)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (hresidual0 : ∀ i, 0 ≤ residualMass i)
    (hx0 : 0 ≤ x)
    (hxWork : x ≤ fluidBlocksWork
      (optionalSortedBlocks q a τ μ p residualMass)) :
    optionalKnapsackWork τ μ
        (optionalSortedModule q a τ μ x p residualMass)
        (optionalSortedBlind q a τ μ x p residualMass) p
        (optionalSortedResidual q a τ μ x p residualMass) = x ∧
      optionalKnapsackMass
        (optionalSortedModule q a τ μ x p residualMass)
        (optionalSortedBlind q a τ μ x p residualMass)
        (optionalSortedResidual q a τ μ x p residualMass) =
          fluidBlocksCompleted
            (optionalSortedBlocks q a τ μ p residualMass) x ∧
      ∃ pivotCost, 0 < pivotCost ∧
        (∀ item, optionalItemCost τ μ p item < pivotCost →
          optionalItemAllocation
              (optionalSortedModule q a τ μ x p residualMass)
              (optionalSortedBlind q a τ μ x p residualMass)
              (optionalSortedResidual q a τ μ x p residualMass) item =
            optionalItemCapacity q a residualMass item) ∧
        (∀ item, pivotCost < optionalItemCost τ μ p item →
          optionalItemAllocation
              (optionalSortedModule q a τ μ x p residualMass)
              (optionalSortedBlind q a τ μ x p residualMass)
              (optionalSortedResidual q a τ μ x p residualMass) item = 0) := by
  let capacity := optionalItemCapacity q a residualMass
  let cost := optionalItemCost τ μ p
  have hcost : ∀ item, 0 < cost item := by
    intro item
    rcases item with _ | (_ | i)
    · exact hτ
    · exact hμ
    · exact hp i
  have hcapacity : ∀ item, 0 ≤ capacity item := by
    intro item
    rcases item with _ | (_ | i)
    · dsimp [capacity, optionalItemCapacity]
      exact mul_nonneg ha0 hq0
    · dsimp [capacity, optionalItemCapacity]
      linarith
    · dsimp [capacity, optionalItemCapacity]
      exact mul_nonneg hq0 (hresidual0 i)
  have hcert := sortedKnapsackAllocation_certificate capacity cost hcost
    hcapacity hx0 (by simpa [optionalSortedBlocks, capacity, cost] using hxWork)
  obtain ⟨_hfeasible, hwork, hmass, pivotCost, hpivot,
      hpivotLow, hpivotHigh⟩ := hcert
  have hallocation := optionalItemAllocation_sorted_components
    q a τ μ x p residualMass
  refine ⟨?_, ?_, pivotCost, hpivot, ?_, ?_⟩
  · rw [← optionalItemAllocation_work, hallocation]
    exact hwork
  · rw [← optionalItemAllocation_mass, hallocation]
    exact hmass
  · intro item hitem
    rw [hallocation]
    exact hpivotLow item hitem
  · intro item hitem
    rw [hallocation]
    exact hpivotHigh item hitem

end

end RandomizedOptional
end SchedulingPaper
