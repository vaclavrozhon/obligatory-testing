import SchedulingPaper.RandomizedAnnouncedFluid
import Mathlib

/-!
# Optional testing: deterministic fluid algebra

This file contains the deterministic fluid layer of the non-obligatory,
oblivious-adversary structure theorem.  It checks the algebra which is
independent of the later predictable-urn concentration argument:

* replacement of an arbitrary partial low discovery state by a fractional
  full test module;
* the pointwise fractional-knapsack completion envelope and long-test branch;
* finite-grid revelation repair and the horizontal/vertical area transfer;
* the five area terms of the canonical threshold / medium / YOLO / high
  policy;
* the fact that its fixed-distribution objective is a quadratic in the tested
  fraction.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

/-- Amount of a full discovery module needed to reproduce completed mass `y`
when one full module completes mass `a`. -/
def moduleAmount (y a : ℝ) : ℝ := y / a

/-- The exact replacement calculation in the completion-envelope proof.

`y ≤ a*t` is the revelation-capacity constraint.  `w*y ≤ a*x` is the
cross-multiplied assertion that the partial low state has density at most the
full module's density `a/w`. -/
theorem module_replacement
    {a w t q y x : ℝ}
    (ha : 0 < a)
    (htq : t ≤ q)
    (hy : 0 ≤ y)
    (hcapacity : y ≤ a * t)
    (hdensity : w * y ≤ a * x) :
    0 ≤ moduleAmount y a ∧
      moduleAmount y a ≤ q ∧
      moduleAmount y a * w ≤ x := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hnonneg : 0 ≤ moduleAmount y a := by
    exact div_nonneg hy ha.le
  have hle_t : moduleAmount y a ≤ t := by
    rw [moduleAmount, div_le_iff₀ ha]
    simpa [mul_comm] using hcapacity
  have hwork : moduleAmount y a * w ≤ x := by
    rw [moduleAmount, div_mul_eq_mul_div, div_le_iff₀ ha]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdensity
  exact ⟨hnonneg, hle_t.trans htq, hwork⟩

/-- The finite maximum-density threshold supplies exactly the cross-multiplied
density premise used by `module_replacement` for every partial low state. -/
theorem threshold_partial_low_density
    {ι : Type*} [Fintype ι]
    {μ0 τ T : ℝ} {μ p xStar x : ι → ℝ}
    (hT : 0 ≤ T)
    (hmassStar : 0 ≤ RandomizedAnnounced.discoveryMass μ0 xStar)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_cap : ∀ i, x i ≤ μ i)
    (hstar_low : ∀ i, p i < τ → xStar i = μ i)
    (hstar_high : ∀ i, τ < p i → xStar i = 0)
    (hstar_density :
      τ * RandomizedAnnounced.discoveryMass μ0 xStar =
        RandomizedAnnounced.discoveryWork p xStar) :
    RandomizedAnnounced.discoveryWork p xStar *
        (T * RandomizedAnnounced.discoveryMass μ0 x) ≤
      RandomizedAnnounced.discoveryMass μ0 xStar *
        (T * RandomizedAnnounced.discoveryWork p x) := by
  have hmax := RandomizedAnnounced.threshold_maximizes_discovery_density
    hx_nonneg hx_cap hstar_low hstar_high hstar_density
  have hscaled := mul_le_mul_of_nonneg_left hmax hT
  have hmul := mul_le_mul_of_nonneg_left hscaled hmassStar
  calc
    RandomizedAnnounced.discoveryWork p xStar *
        (T * RandomizedAnnounced.discoveryMass μ0 x) =
      RandomizedAnnounced.discoveryMass μ0 xStar *
        (T * (τ * RandomizedAnnounced.discoveryMass μ0 x)) := by
          rw [← hstar_density]
          ring
    _ ≤ RandomizedAnnounced.discoveryMass μ0 xStar *
        (T * RandomizedAnnounced.discoveryWork p x) := hmul

/-- Full test-module density identity. -/
theorem module_cost_eq_threshold
    {a w τ : ℝ} (ha : 0 < a) (hτ : τ * a = w) :
    w / a = τ := by
  rw [div_eq_iff (ne_of_gt ha)]
  simpa [mul_comm] using hτ.symm

/-- The testing-threshold equation in aggregate notation. -/
theorem threshold_gap_eq_one
    {a lowMoment τ : ℝ}
    (hdensity : τ * a = 1 + lowMoment) :
    τ * a - lowMoment = 1 := by
  linarith

/-- Area contributed by a homogeneous fluid block of mass `m` and work per
completion `cost`, when mass `later` remains throughout the block. -/
def homogeneousBlockArea (cost m later : ℝ) : ℝ :=
  cost * (m * later + m ^ 2 / 2)

/-- Exact adjacent-interchange identity for two fluid blocks. -/
theorem two_block_swap_identity
    (costA massA costB massB later : ℝ) :
    (homogeneousBlockArea costA massA (massB + later) +
        homogeneousBlockArea costB massB later) -
      (homogeneousBlockArea costB massB (massA + later) +
        homogeneousBlockArea costA massA later) =
      massA * massB * (costA - costB) := by
  unfold homogeneousBlockArea
  ring

/-- Fractional SPT/knapsack exchange: lower work per completion goes first. -/
theorem lower_cost_block_first
    {costA massA costB massB later : ℝ}
    (hmassA : 0 ≤ massA) (hmassB : 0 ≤ massB)
    (hcost : costA ≤ costB) :
    homogeneousBlockArea costA massA (massB + later) +
        homogeneousBlockArea costB massB later ≤
      homogeneousBlockArea costB massB (massA + later) +
        homogeneousBlockArea costA massA later := by
  have hprod : massA * massB * (costA - costB) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hmassA hmassB) (sub_nonpos.mpr hcost)
  linarith [two_block_swap_identity costA massA costB massB later]

/-! ## Fractional-knapsack completion envelopes -/

/-- Total completion mass of a fractional allocation. -/
def fractionalMass {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, x i

/-- Work used by a fractional allocation with per-completion costs `cost`. -/
def fractionalWork {ι : Type*} [Fintype ι]
    (cost x : ι → ℝ) : ℝ :=
  ∑ i, cost i * x i

/-- Coordinatewise capacity constraints for a fractional allocation. -/
def FractionalFeasible {ι : Type*} [Fintype ι]
    (capacity x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ capacity i

/-- Supporting-hyperplane certificate for a greedy fractional-knapsack
prefix.  Every item strictly cheaper than the pivot is full and every item
strictly more expensive is empty; ties may be split arbitrarily.

This form avoids choosing an ordering of equal-cost atoms and is the exact
pointwise inequality needed for a completion envelope. -/
theorem fractional_greedy_cut_supporting
    {ι : Type*} [Fintype ι]
    {capacity cost x greedy : ι → ℝ} {pivotCost : ℝ}
    (hx : FractionalFeasible capacity x)
    (hgreedyLow : ∀ i, cost i < pivotCost → greedy i = capacity i)
    (hgreedyHigh : ∀ i, pivotCost < cost i → greedy i = 0) :
    pivotCost * (fractionalMass x - fractionalMass greedy) ≤
      fractionalWork cost x - fractionalWork cost greedy := by
  have hcoordinate : ∀ i,
      (pivotCost - cost i) * (x i - greedy i) ≤ 0 := by
    intro i
    rcases lt_trichotomy (cost i) pivotCost with hlow | heq | hhigh
    · rw [hgreedyLow i hlow]
      exact mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hlow.le) (sub_nonpos.mpr (hx.2 i))
    · simp [heq]
    · rw [hgreedyHigh i hhigh]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hhigh.le) (by simpa using hx.1 i)
  have hsum :
      ∑ i, (pivotCost - cost i) * (x i - greedy i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hcoordinate i
  have hidentity :
      pivotCost * (fractionalMass x - fractionalMass greedy) -
          (fractionalWork cost x - fractionalWork cost greedy) =
        ∑ i, (pivotCost - cost i) * (x i - greedy i) := by
    unfold fractionalMass fractionalWork
    rw [← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hidentity] at hsum
  linarith

/-- A greedy prefix with the same or greater work completes at least as much
mass as every feasible allocation. -/
theorem fractional_greedy_cut_dominates
    {ι : Type*} [Fintype ι]
    {capacity cost x greedy : ι → ℝ} {pivotCost : ℝ}
    (hpivot : 0 < pivotCost)
    (hx : FractionalFeasible capacity x)
    (hgreedyLow : ∀ i, cost i < pivotCost → greedy i = capacity i)
    (hgreedyHigh : ∀ i, pivotCost < cost i → greedy i = 0)
    (hwork : fractionalWork cost x ≤ fractionalWork cost greedy) :
    fractionalMass x ≤ fractionalMass greedy := by
  have hsupport := fractional_greedy_cut_supporting
    hx hgreedyLow hgreedyHigh
  by_contra hnot
  have hmass : fractionalMass greedy < fractionalMass x :=
    lt_of_not_ge hnot
  have hpositive :
      0 < pivotCost * (fractionalMass x - fractionalMass greedy) :=
    mul_pos hpivot (sub_pos.mpr hmass)
  linarith

/-- If every completion item costs at least `base`, completed mass times
`base` is bounded by work.  This is the one-line envelope certificate for the
long-test regime. -/
theorem fractional_mass_mul_minCost_le_work
    {ι : Type*} [Fintype ι]
    {base : ℝ} {cost x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hcost : ∀ i, base ≤ cost i) :
    base * fractionalMass x ≤ fractionalWork cost x := by
  unfold fractionalMass fractionalWork
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hcost i) (hx i)

/-- Completion mass represented by the optional test-module / residual /
blind relaxation. -/
def optionalKnapsackMass {ι : Type*} [Fintype ι]
    (moduleCompletion blindCompletion : ℝ)
    (residualCompletion : ι → ℝ) : ℝ :=
  moduleCompletion + blindCompletion + ∑ i, residualCompletion i

/-- Work of the same three-part fractional allocation. -/
def optionalKnapsackWork {ι : Type*} [Fintype ι]
    (τ μ moduleCompletion blindCompletion : ℝ)
    (p residualCompletion : ι → ℝ) : ℝ :=
  τ * moduleCompletion + μ * blindCompletion +
    ∑ i, p i * residualCompletion i

/-- Capacities after a total fraction `q` of jobs has been tested. -/
def OptionalKnapsackFeasible {ι : Type*} [Fintype ι]
    (q a moduleCompletion blindCompletion : ℝ)
    (residualMass residualCompletion : ι → ℝ) : Prop :=
  0 ≤ moduleCompletion ∧ moduleCompletion ≤ a * q ∧
    0 ≤ blindCompletion ∧ blindCompletion ≤ 1 - q ∧
    (∀ i, 0 ≤ residualCompletion i) ∧
    ∀ i, residualCompletion i ≤ q * residualMass i

/-- A uniform finite item type for the test module, the residual classes,
and the blind module.  `none` is the test item, `some none` is blind, and
`some (some i)` is residual class `i`. -/
abbrev OptionalKnapsackItem (ι : Type*) := Option (Option ι)

def optionalItemCapacity {ι : Type*}
    (q a : ℝ) (residualMass : ι → ℝ) :
    OptionalKnapsackItem ι → ℝ
  | none => a * q
  | some none => 1 - q
  | some (some i) => q * residualMass i

def optionalItemCost {ι : Type*}
    (τ μ : ℝ) (p : ι → ℝ) : OptionalKnapsackItem ι → ℝ
  | none => τ
  | some none => μ
  | some (some i) => p i

def optionalItemAllocation {ι : Type*}
    (moduleCompletion blindCompletion : ℝ)
    (residualCompletion : ι → ℝ) : OptionalKnapsackItem ι → ℝ
  | none => moduleCompletion
  | some none => blindCompletion
  | some (some i) => residualCompletion i

theorem optionalItemCost_ge_mean
    {ι : Type*} {τ μ : ℝ} {p : ι → ℝ}
    (hτμ : μ ≤ τ) (hresidual : ∀ i, τ ≤ p i) :
    ∀ item : OptionalKnapsackItem ι, μ ≤ optionalItemCost τ μ p item := by
  intro item
  rcases item with _ | (_ | i)
  · exact hτμ
  · exact le_rfl
  · exact hτμ.trans (hresidual i)

theorem optionalItemAllocation_mass
    {ι : Type*} [Fintype ι]
    (moduleCompletion blindCompletion : ℝ)
    (residualCompletion : ι → ℝ) :
    fractionalMass
        (optionalItemAllocation moduleCompletion blindCompletion
          residualCompletion) =
      optionalKnapsackMass moduleCompletion blindCompletion
        residualCompletion := by
  simp [fractionalMass, optionalKnapsackMass, optionalItemAllocation,
    add_comm, add_left_comm]

theorem optionalItemAllocation_work
    {ι : Type*} [Fintype ι]
    (τ μ moduleCompletion blindCompletion : ℝ)
    (p residualCompletion : ι → ℝ) :
    fractionalWork (optionalItemCost τ μ p)
        (optionalItemAllocation moduleCompletion blindCompletion
          residualCompletion) =
      optionalKnapsackWork τ μ moduleCompletion blindCompletion p
        residualCompletion := by
  simp [fractionalWork, optionalKnapsackWork, optionalItemCost,
    optionalItemAllocation, add_assoc]

theorem optionalItemAllocation_feasible
    {ι : Type*} [Fintype ι]
    {q a moduleCompletion blindCompletion : ℝ}
    {residualMass residualCompletion : ι → ℝ}
    (h : OptionalKnapsackFeasible q a moduleCompletion blindCompletion
      residualMass residualCompletion) :
    FractionalFeasible (optionalItemCapacity q a residualMass)
      (optionalItemAllocation moduleCompletion blindCompletion
        residualCompletion) := by
  constructor
  · intro item
    rcases item with _ | (_ | i)
    · exact h.1
    · exact h.2.2.1
    · exact h.2.2.2.2.1 i
  · intro item
    rcases item with _ | (_ | i)
    · exact h.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.2 i

/-- Exact embedding of an arbitrary optional-testing prefix into the ordinary
fractional knapsack used by the completion-envelope proof.

`yLow,xLow` are respectively the completion mass and work of tests together
with already processed selected-low outcomes.  Residual known classes are
only constrained by revelation, and `blindCompletion` is bounded by the
untested stock.  The resulting knapsack point has exactly the same completed
mass and weakly less idealized work. -/
theorem optional_prefix_embeds_knapsack
    {ι : Type*} [Fintype ι]
    {a w τ t q yLow xLow blindCompletion μ : ℝ}
    {residualMass p residualCompletion : ι → ℝ}
    (ha : 0 < a)
    (hτ : τ * a = w)
    (ht0 : 0 ≤ t) (htq : t ≤ q)
    (hy0 : 0 ≤ yLow) (hyCapacity : yLow ≤ a * t)
    (hyDensity : w * yLow ≤ a * xLow)
    (hb0 : 0 ≤ blindCompletion) (hbCap : blindCompletion ≤ 1 - q)
    (hD0 : ∀ i, 0 ≤ residualMass i)
    (hc0 : ∀ i, 0 ≤ residualCompletion i)
    (hcReveal : ∀ i, residualCompletion i ≤ residualMass i * t) :
    OptionalKnapsackFeasible q a yLow blindCompletion
        residualMass residualCompletion ∧
      optionalKnapsackWork τ μ yLow blindCompletion p residualCompletion ≤
        xLow + μ * blindCompletion +
          ∑ i, p i * residualCompletion i := by
  have hq0 : 0 ≤ q := ht0.trans htq
  have hmodule := module_replacement ha htq hy0 hyCapacity hyDensity
  have hyCapQ : yLow ≤ a * q := by
    exact hyCapacity.trans
      (mul_le_mul_of_nonneg_left htq ha.le)
  have hcCapQ : ∀ i, residualCompletion i ≤ q * residualMass i := by
    intro i
    calc
      residualCompletion i ≤ residualMass i * t := hcReveal i
      _ ≤ residualMass i * q :=
        mul_le_mul_of_nonneg_left htq (hD0 i)
      _ = q * residualMass i := by ring
  have hmoduleWork : τ * yLow ≤ xLow := by
    have hτdiv : w / a = τ := module_cost_eq_threshold ha hτ
    have hrewrite :
        τ * yLow = moduleAmount yLow a * w := by
      unfold moduleAmount
      rw [← hτdiv]
      field_simp [ne_of_gt ha]
    rw [hrewrite]
    exact hmodule.2.2
  constructor
  · exact ⟨hy0, hyCapQ, hb0, hbCap, hc0, hcCapQ⟩
  · unfold optionalKnapsackWork
    linarith

/-- Pointwise completion-envelope theorem for an optional prefix.  Once a
canonical allocation is known to be a greedy cut of the three-item-family
knapsack and to use at least the prefix's physical work, it has completed at
least as much mass.  No interchange of adaptive policy-tree nodes appears in
the statement or proof. -/
theorem optional_prefix_completion_le_greedy
    {ι : Type*} [Fintype ι]
    {a w τ t q yLow xLow blindCompletion μ physicalWork : ℝ}
    {residualMass p residualCompletion : ι → ℝ}
    {greedyModule greedyBlind pivotCost : ℝ}
    {greedyResidual : ι → ℝ}
    (ha : 0 < a)
    (hτ : τ * a = w)
    (ht0 : 0 ≤ t) (htq : t ≤ q)
    (hy0 : 0 ≤ yLow) (hyCapacity : yLow ≤ a * t)
    (hyDensity : w * yLow ≤ a * xLow)
    (hb0 : 0 ≤ blindCompletion) (hbCap : blindCompletion ≤ 1 - q)
    (hD0 : ∀ i, 0 ≤ residualMass i)
    (hc0 : ∀ i, 0 ≤ residualCompletion i)
    (hcReveal : ∀ i, residualCompletion i ≤ residualMass i * t)
    (hpivot : 0 < pivotCost)
    (hphysical :
      xLow + μ * blindCompletion +
          ∑ i, p i * residualCompletion i ≤ physicalWork)
    (hgreedyWork :
      physicalWork ≤ optionalKnapsackWork τ μ greedyModule greedyBlind
        p greedyResidual)
    (hgreedyLow : ∀ item,
      optionalItemCost τ μ p item < pivotCost →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item =
          optionalItemCapacity q a residualMass item)
    (hgreedyHigh : ∀ item,
      pivotCost < optionalItemCost τ μ p item →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item = 0) :
    optionalKnapsackMass yLow blindCompletion residualCompletion ≤
      optionalKnapsackMass greedyModule greedyBlind greedyResidual := by
  obtain ⟨hfeasible, hrelaxedWork⟩ := optional_prefix_embeds_knapsack
    ha hτ ht0 htq hy0 hyCapacity hyDensity hb0 hbCap hD0 hc0 hcReveal
  let x := optionalItemAllocation yLow blindCompletion residualCompletion
  let greedy := optionalItemAllocation greedyModule greedyBlind greedyResidual
  let capacity := optionalItemCapacity q a residualMass
  let cost := optionalItemCost τ μ p
  have hx : FractionalFeasible capacity x := by
    exact optionalItemAllocation_feasible hfeasible
  have hwork : fractionalWork cost x ≤ fractionalWork cost greedy := by
    rw [optionalItemAllocation_work, optionalItemAllocation_work]
    exact hrelaxedWork.trans (hphysical.trans hgreedyWork)
  have hdom := fractional_greedy_cut_dominates hpivot hx
    (by simpa [cost, capacity, greedy] using hgreedyLow)
    (by simpa [cost, greedy] using hgreedyHigh) hwork
  simpa [x, greedy, optionalItemAllocation_mass] using hdom

/-- In the long-test regime every item in the optional relaxation has work
per completion at least the blind mean. -/
theorem optional_long_regime_completion_density
    {ι : Type*} [Fintype ι]
    {τ μ moduleCompletion blindCompletion : ℝ}
    {p residualCompletion : ι → ℝ}
    (hτμ : μ ≤ τ) (hresidual : ∀ i, τ ≤ p i)
    (hmodule : 0 ≤ moduleCompletion)
    (hblind : 0 ≤ blindCompletion)
    (hknown : ∀ i, 0 ≤ residualCompletion i) :
    μ * optionalKnapsackMass moduleCompletion blindCompletion
        residualCompletion ≤
      optionalKnapsackWork τ μ moduleCompletion blindCompletion p
        residualCompletion := by
  let x := optionalItemAllocation moduleCompletion blindCompletion
    residualCompletion
  have hx : ∀ item, 0 ≤ x item := by
    intro item
    rcases item with _ | (_ | i)
    · exact hmodule
    · exact hblind
    · exact hknown i
  have h := fractional_mass_mul_minCost_le_work hx
    (optionalItemCost_ge_mean hτμ hresidual)
  simpa [x, optionalItemAllocation_mass, optionalItemAllocation_work] using h

/-- Area consequence of the long-regime density bound.  If at normalized
work time `x` no more than `x/μ` mass can have completed, then the completion
time area is at least the all-blind value `μ/2`. -/
theorem long_regime_area_ge_blind
    {completed : ℝ → ℝ} {μ : ℝ}
    (hμ : 0 < μ)
    (hCompletedInt :
      IntervalIntegrable completed MeasureTheory.volume 0 μ)
    (hCompletionDensity :
      ∀ x ∈ Set.Icc (0 : ℝ) μ, μ * completed x ≤ x) :
    μ / 2 ≤ ∫ x in 0..μ, (1 - completed x) := by
  have hIdDivContinuous : Continuous (fun x : ℝ => x / μ) :=
    continuous_id.div_const μ
  have hIdDivInt :
      IntervalIntegrable (fun x : ℝ => x / μ)
        MeasureTheory.volume 0 μ :=
    hIdDivContinuous.intervalIntegrable 0 μ
  have hLinearInt :
      IntervalIntegrable (fun x : ℝ => 1 - x / μ)
        MeasureTheory.volume 0 μ :=
    IntervalIntegrable.sub intervalIntegrable_const hIdDivInt
  have hRemainingInt :
      IntervalIntegrable (fun x => 1 - completed x)
        MeasureTheory.volume 0 μ :=
    IntervalIntegrable.sub intervalIntegrable_const hCompletedInt
  have hmono :
      (∫ x in 0..μ, (1 - x / μ)) ≤
        ∫ x in 0..μ, (1 - completed x) :=
    intervalIntegral.integral_mono_on hμ.le hLinearInt hRemainingInt (by
      intro x hx
      have hc : completed x ≤ x / μ := by
        rw [le_div_iff₀ hμ]
        simpa [mul_comm] using hCompletionDensity x hx
      linarith)
  have hcalc : (∫ x in 0..μ, (1 - x / μ)) = μ / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIdDivInt]
    simp [intervalIntegral.integral_div]
    field_simp [hμ.ne']
    ring
  rwa [hcalc] at hmono

/-! ## Uniform grid-error repair -/

/-- Remove one discrepancy allowance from a revealed class count. -/
def repairedCompletion (γ c : ℝ) : ℝ := max (c - γ) 0

theorem repairedCompletion_nonneg (γ c : ℝ) :
    0 ≤ repairedCompletion γ c := by
  unfold repairedCompletion
  exact le_max_right _ _

theorem repairedCompletion_le
    {γ c cap : ℝ} (hcap0 : 0 ≤ cap)
    (hcap : c ≤ cap + γ) :
    repairedCompletion γ c ≤ cap := by
  unfold repairedCompletion
  rw [max_le_iff]
  exact ⟨by linarith, hcap0⟩

theorem le_repairedCompletion_add
    {γ c : ℝ} :
    c ≤ repairedCompletion γ c + γ := by
  unfold repairedCompletion
  linarith [le_max_left (c - γ) 0]

theorem repairedCompletion_le_original
    {γ c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) :
    repairedCompletion γ c ≤ c := by
  unfold repairedCompletion
  rw [max_le_iff]
  exact ⟨by linarith, hc⟩

/-- Simultaneous repair of all approximate revelation constraints.

Subtracting `γ` from every positive class restores the exact constraints,
loses at most `card ι * γ` completed mass, and cannot increase processing
work when class lengths are nonnegative.  This is the deterministic core of
the finite-support and growing-grid transfers. -/
theorem grid_revelation_repair
    {ι : Type*} [Fintype ι]
    {γ t : ℝ} {mass length completion : ι → ℝ}
    (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hmass : ∀ i, 0 ≤ mass i)
    (hlength : ∀ i, 0 ≤ length i)
    (hcompletion : ∀ i, 0 ≤ completion i)
    (happrox : ∀ i, completion i ≤ mass i * t + γ) :
    (∀ i, 0 ≤ repairedCompletion γ (completion i)) ∧
    (∀ i, repairedCompletion γ (completion i) ≤ mass i * t) ∧
    (∑ i, completion i) ≤
      (∑ i, repairedCompletion γ (completion i)) +
        Fintype.card ι * γ ∧
    (∑ i, length i * repairedCompletion γ (completion i)) ≤
      ∑ i, length i * completion i := by
  have hcap0 : ∀ i, 0 ≤ mass i * t := fun i => mul_nonneg (hmass i) ht
  have hnonneg : ∀ i, 0 ≤ repairedCompletion γ (completion i) :=
    fun i => repairedCompletion_nonneg _ _
  have hcap : ∀ i,
      repairedCompletion γ (completion i) ≤ mass i * t := by
    intro i
    unfold repairedCompletion
    rw [max_le_iff]
    exact ⟨by linarith [happrox i], hcap0 i⟩
  have hmassPoint : ∀ i,
      completion i ≤ repairedCompletion γ (completion i) + γ :=
    fun i => le_repairedCompletion_add
  have hmassSum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) =>
    hmassPoint i
  have hworkPoint : ∀ i,
      length i * repairedCompletion γ (completion i) ≤
        length i * completion i := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (repairedCompletion_le_original hγ (hcompletion i)) (hlength i)
  refine ⟨hnonneg, hcap, ?_, Finset.sum_le_sum fun i _ => hworkPoint i⟩
  simpa [Finset.sum_add_distrib] using hmassSum

/-- Pointwise finite-grid transfer to the canonical fractional-knapsack
envelope.  Approximate revelation constraints are repaired class by class;
the resulting loss is exactly `card ι * γ`, and nonnegative processing
lengths ensure that the repair never increases work.

This is the deterministic scheduling core of display (36).  A predictable
urn theorem supplies `happrox` and `hphysicalOriginal`; no probabilistic
assumption is hidden here. -/
theorem optional_grid_prefix_completion_le_greedy
    {ι : Type*} [Fintype ι]
    {γ a w τ t q yLow xLow blindCompletion μ physicalWork
      actualCompleted : ℝ}
    {residualMass p residualCompletion : ι → ℝ}
    {greedyModule greedyBlind pivotCost : ℝ}
    {greedyResidual : ι → ℝ}
    (hγ : 0 ≤ γ)
    (ha : 0 < a)
    (hτ : τ * a = w)
    (ht0 : 0 ≤ t) (htq : t ≤ q)
    (hy0 : 0 ≤ yLow) (hyCapacity : yLow ≤ a * t)
    (hyDensity : w * yLow ≤ a * xLow)
    (hb0 : 0 ≤ blindCompletion) (hbCap : blindCompletion ≤ 1 - q)
    (hD0 : ∀ i, 0 ≤ residualMass i)
    (hp0 : ∀ i, 0 ≤ p i)
    (hc0 : ∀ i, 0 ≤ residualCompletion i)
    (happrox : ∀ i,
      residualCompletion i ≤ residualMass i * t + γ)
    (hactual : actualCompleted ≤
      optionalKnapsackMass yLow blindCompletion residualCompletion)
    (hpivot : 0 < pivotCost)
    (hphysicalOriginal :
      xLow + μ * blindCompletion +
          ∑ i, p i * residualCompletion i ≤ physicalWork)
    (hgreedyWork :
      physicalWork ≤ optionalKnapsackWork τ μ greedyModule greedyBlind
        p greedyResidual)
    (hgreedyLow : ∀ item,
      optionalItemCost τ μ p item < pivotCost →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item =
          optionalItemCapacity q a residualMass item)
    (hgreedyHigh : ∀ item,
      pivotCost < optionalItemCost τ μ p item →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item = 0) :
    actualCompleted ≤
      optionalKnapsackMass greedyModule greedyBlind greedyResidual +
        Fintype.card ι * γ := by
  let repaired : ι → ℝ := fun i =>
    repairedCompletion γ (residualCompletion i)
  obtain ⟨hrepaired0, hrepairedCap, hmassRepair, hworkRepair⟩ :=
    grid_revelation_repair hγ ht0 hD0 hp0 hc0 happrox
  have hphysicalRepaired :
      xLow + μ * blindCompletion + ∑ i, p i * repaired i ≤
        physicalWork := by
    dsimp [repaired]
    linarith
  have henvelope :
      optionalKnapsackMass yLow blindCompletion repaired ≤
        optionalKnapsackMass greedyModule greedyBlind greedyResidual := by
    exact optional_prefix_completion_le_greedy
      ha hτ ht0 htq hy0 hyCapacity hyDensity hb0 hbCap hD0
      (by simpa [repaired] using hrepaired0)
      (by simpa [repaired] using hrepairedCap)
      hpivot hphysicalRepaired hgreedyWork hgreedyLow hgreedyHigh
  unfold optionalKnapsackMass at hactual henvelope ⊢
  linarith

/-! ## Integrating a horizontally shifted completion envelope -/

/-- Shifting a normalized remaining-mass curve to the left by `ζ` can lose
at most `ζ` area.  This is the analytic step used after the grid repair:
the completion envelope is evaluated at `x + ζ`, and no slope bound near a
possibly tiny positive processing-time bin is needed.

The statement only uses that the curve takes values in `[0,1]`. -/
theorem remainingMass_integral_shift
    {f : ℝ → ℝ} {T ζ : ℝ}
    (hT : 0 ≤ T) (hζ : 0 ≤ ζ)
    (hInt : IntervalIntegrable f MeasureTheory.volume 0 (T + ζ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x in 0..T, f x) - ζ ≤ ∫ x in 0..T, f (x + ζ) := by
  have hTend : T ≤ T + ζ := by linarith
  have hInt0T : IntervalIntegrable f MeasureTheory.volume 0 T :=
    hInt.mono_set (by grind [Set.uIcc])
  have hIntTend : IntervalIntegrable f MeasureTheory.volume T (T + ζ) :=
    hInt.mono_set (by grind [Set.uIcc])
  have hInt0ζ : IntervalIntegrable f MeasureTheory.volume 0 ζ :=
    hInt.mono_set (by grind [Set.uIcc])
  have hIntζend : IntervalIntegrable f MeasureTheory.volume ζ (T + ζ) :=
    hInt.mono_set (by grind [Set.uIcc])
  have hfirst : (∫ x in 0..ζ, f x) ≤ ζ := by
    calc
      (∫ x in 0..ζ, f x) ≤ ∫ _x in 0..ζ, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hζ hInt0ζ (by simp) (by
          intro x _hx
          exact hf1 x)
      _ = ζ := by simp
  have hlast : 0 ≤ ∫ x in T..T + ζ, f x :=
    intervalIntegral.integral_nonneg_of_forall hTend hf0
  have hsplitT :
      (∫ x in 0..T, f x) + (∫ x in T..T + ζ, f x) =
        ∫ x in 0..T + ζ, f x :=
    intervalIntegral.integral_add_adjacent_intervals hInt0T hIntTend
  have hsplitζ :
      (∫ x in 0..ζ, f x) + (∫ x in ζ..T + ζ, f x) =
        ∫ x in 0..T + ζ, f x :=
    intervalIntegral.integral_add_adjacent_intervals hInt0ζ hIntζend
  have hshift :
      (∫ x in 0..T, f (x + ζ)) = ∫ x in ζ..T + ζ, f x := by
    simp
  rw [hshift]
  linarith

/-- Integrated form of an approximate completion-envelope comparison.

If an actual completion curve `completed` is everywhere at most the ideal
envelope evaluated `ζ` work units later, plus vertical slack `ε`, then the
actual remaining-mass area loses at most `ζ + ε*T`.  This packages the
horizontal and vertical estimates used in displays (36)--(38) of the
analytic proof. -/
theorem completionEnvelope_area_transfer
    {completed envelope : ℝ → ℝ} {T ζ ε : ℝ}
    (hT : 0 ≤ T) (hζ : 0 ≤ ζ)
    (hCompletedInt :
      IntervalIntegrable completed MeasureTheory.volume 0 T)
    (hEnvelopeInt :
      IntervalIntegrable envelope MeasureTheory.volume 0 (T + ζ))
    (hEnvelope0 : ∀ x, 0 ≤ envelope x)
    (hEnvelope1 : ∀ x, envelope x ≤ 1)
    (hComparison : ∀ x, completed x ≤ envelope (x + ζ) + ε) :
    (∫ x in 0..T, (1 - envelope x)) - ζ - ε * T ≤
      ∫ x in 0..T, (1 - completed x) := by
  have hRemainingInt :
      IntervalIntegrable (fun x => 1 - envelope x)
        MeasureTheory.volume 0 (T + ζ) :=
    IntervalIntegrable.sub intervalIntegrable_const hEnvelopeInt
  have hHorizontal := remainingMass_integral_shift hT hζ hRemainingInt
    (fun x => by linarith [hEnvelope1 x])
    (fun x => by linarith [hEnvelope0 x])
  have hEnvelopeShiftInt :
      IntervalIntegrable (fun x => envelope (x + ζ))
        MeasureTheory.volume 0 T := by
    have hsub :
        IntervalIntegrable envelope MeasureTheory.volume ζ (T + ζ) :=
      hEnvelopeInt.mono_set (by grind [Set.uIcc])
    simpa using hsub.comp_add_right ζ
  have hLeftInt :
      IntervalIntegrable (fun x => 1 - envelope (x + ζ) - ε)
        MeasureTheory.volume 0 T :=
    (IntervalIntegrable.sub intervalIntegrable_const hEnvelopeShiftInt).sub
      intervalIntegrable_const
  have hRightInt :
      IntervalIntegrable (fun x => 1 - completed x)
        MeasureTheory.volume 0 T :=
    IntervalIntegrable.sub intervalIntegrable_const hCompletedInt
  have hVertical :
      (∫ x in 0..T, (1 - envelope (x + ζ) - ε)) ≤
        ∫ x in 0..T, (1 - completed x) :=
    intervalIntegral.integral_mono_on hT hLeftInt hRightInt (by
      intro x _hx
      linarith [hComparison x])
  have hVertical' :
      (∫ x in 0..T, (1 - envelope (x + ζ))) - ε * T ≤
        ∫ x in 0..T, (1 - completed x) := by
    have hBaseInt :
        IntervalIntegrable (fun x => 1 - envelope (x + ζ))
          MeasureTheory.volume 0 T :=
      IntervalIntegrable.sub intervalIntegrable_const hEnvelopeShiftInt
    rw [intervalIntegral.integral_sub hBaseInt intervalIntegrable_const] at hVertical
    simpa [mul_comm] using hVertical
  linarith

/-- Statistics entering the canonical optional-testing fluid cost.

`lowMass` and `lowMoment` refer to outcomes completed during discovery;
`mediumMoment` and `highMass` describe the residual classes around the blind
block; `mediumMinPair` and `highMinPair` are their two-draw SPT moments. -/
structure FluidMoments where
  lowMass : ℝ
  lowMoment : ℝ
  mediumMoment : ℝ
  highMass : ℝ
  mean : ℝ
  mediumMinPair : ℝ
  highMinPair : ℝ

/-- Area accumulated during test modules and immediate low completions. -/
def testLowArea (M : FluidMoments) (q : ℝ) : ℝ :=
  (1 + M.lowMoment) * (q - M.lowMass * q ^ 2 / 2)

/-- Area of the known-medium SPT block, including its delay to later blocks. -/
def mediumArea (M : FluidMoments) (q : ℝ) : ℝ :=
  q * M.mediumMoment * ((1 - q) + q * M.highMass) +
    q ^ 2 * M.mediumMinPair / 2

/-- Area of the blind (YOLO) block. -/
def blindArea (M : FluidMoments) (q : ℝ) : ℝ :=
  M.mean * ((1 - q) * q * M.highMass + (1 - q) ^ 2 / 2)

/-- Area internal to the known-high SPT tail. -/
def highArea (M : FluidMoments) (q : ℝ) : ℝ :=
  q ^ 2 * M.highMinPair / 2

/-- Normalized leading cost of the canonical policy testing fraction `q`. -/
def canonicalFluidCost (M : FluidMoments) (q : ℝ) : ℝ :=
  testLowArea M q + mediumArea M q + blindArea M q + highArea M q

/-- The four area blocks partition the canonical completion-time objective.
This named expansion mirrors equation (28) of the analytic proof. -/
theorem canonicalFluidCost_eq_five_terms (M : FluidMoments) (q : ℝ) :
    canonicalFluidCost M q =
      (1 + M.lowMoment) * (q - M.lowMass * q ^ 2 / 2) +
      q * M.mediumMoment * ((1 - q) + q * M.highMass) +
      q ^ 2 * M.mediumMinPair / 2 +
      M.mean * ((1 - q) * q * M.highMass + (1 - q) ^ 2 / 2) +
      q ^ 2 * M.highMinPair / 2 := by
  unfold canonicalFluidCost testLowArea mediumArea blindArea highArea
  ring

/-- Linear coefficient of the tested fraction. -/
def canonicalLinearCoeff (M : FluidMoments) : ℝ :=
  1 + M.lowMoment + M.mediumMoment + M.mean * (M.highMass - 1)

/-- Aggregate form of `E[(μ-P)⁺]` when low and medium are precisely the
classes below the blind-job mean `μ`. -/
def meanShortfall (M : FluidMoments) : ℝ :=
  M.mean * (1 - M.highMass) -
    (M.lowMoment + M.mediumMoment)

/-- The linear coefficient is `1-E[(μ-P)⁺]`. -/
theorem canonicalLinearCoeff_eq_one_sub_meanShortfall (M : FluidMoments) :
    canonicalLinearCoeff M = 1 - meanShortfall M := by
  unfold canonicalLinearCoeff meanShortfall
  ring

/-- In the genuine testing regime, where the mean shortfall exceeds the unit
test time, testing a positive initial fraction strictly improves over YOLO. -/
theorem canonicalLinearCoeff_neg_of_one_lt_meanShortfall
    (M : FluidMoments) (h : 1 < meanShortfall M) :
    canonicalLinearCoeff M < 0 := by
  rw [canonicalLinearCoeff_eq_one_sub_meanShortfall]
  linarith

/-- Quadratic coefficient of the tested fraction. -/
def canonicalQuadraticCoeff (M : FluidMoments) : ℝ :=
  -(1 + M.lowMoment) * M.lowMass / 2 +
    M.mediumMoment * (M.highMass - 1) +
    M.mediumMinPair / 2 +
    M.mean * (1 / 2 - M.highMass) +
    M.highMinPair / 2

/-- For a fixed empirical distribution, optimizing the canonical policy is a
one-dimensional quadratic optimization in `q`. -/
theorem canonicalFluidCost_quadratic (M : FluidMoments) (q : ℝ) :
    canonicalFluidCost M q =
      M.mean / 2 + canonicalLinearCoeff M * q +
        canonicalQuadraticCoeff M * q ^ 2 := by
  unfold canonicalFluidCost testLowArea mediumArea blindArea highArea
    canonicalLinearCoeff canonicalQuadraticCoeff
  ring

/-- If the quadratic coefficient is positive, its unconstrained vertex is a
global minimizer.  The constrained optimizer on `[0,1]` is therefore this
vertex when it lies in the interval, and otherwise the appropriate endpoint. -/
theorem canonicalFluidCost_minimized_at_vertex
    (M : FluidMoments)
    (hA : 0 < canonicalQuadraticCoeff M)
    (q : ℝ) :
    canonicalFluidCost M
        (-canonicalLinearCoeff M / (2 * canonicalQuadraticCoeff M)) ≤
      canonicalFluidCost M q := by
  let A := canonicalQuadraticCoeff M
  let B := canonicalLinearCoeff M
  let qStar := -B / (2 * A)
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hsquare : 0 ≤ A * (q - qStar) ^ 2 :=
    mul_nonneg hA.le (sq_nonneg _)
  rw [canonicalFluidCost_quadratic, canonicalFluidCost_quadratic]
  dsimp [A, B, qStar] at hA0 hsquare ⊢
  field_simp [hA0] at hsquare ⊢
  nlinarith

/-- If the quadratic's derivative is still nonpositive at `q=1`, the
constrained minimizer on `[0,1]` is the clipped vertex `q=1`. -/
theorem canonicalFluidCost_minimized_at_one
    (M : FluidMoments)
    (hquad : 0 ≤ canonicalQuadraticCoeff M)
    (hderiv : canonicalLinearCoeff M +
      2 * canonicalQuadraticCoeff M ≤ 0)
    {q : ℝ} (hq1 : q ≤ 1) :
    canonicalFluidCost M 1 ≤ canonicalFluidCost M q := by
  have hqplus : q + 1 ≤ 2 := by linarith
  have hscaled :
      canonicalQuadraticCoeff M * (q + 1) ≤
        canonicalQuadraticCoeff M * 2 :=
    mul_le_mul_of_nonneg_left hqplus hquad
  have hbracket :
      canonicalLinearCoeff M +
          canonicalQuadraticCoeff M * (q + 1) ≤ 0 := by
    linarith
  have hproduct :
      (1 - q) *
          (canonicalLinearCoeff M +
            canonicalQuadraticCoeff M * (q + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hbracket
  rw [canonicalFluidCost_quadratic, canonicalFluidCost_quadratic]
  nlinarith

/-- Moments of the analytic three-point witness
`Pr[P=0]=1/5`, `Pr[P=9]=1/5`, `Pr[P=16]=3/5`. -/
def threePointMoments : FluidMoments where
  lowMass := 1 / 5
  lowMoment := 0
  mediumMoment := 9 / 5
  highMass := 3 / 5
  mean := 57 / 5
  mediumMinPair := 9 / 25
  highMinPair := 144 / 25

/-- The three-point witness has the claimed quadratic objective. -/
theorem threePoint_canonicalFluidCost (q : ℝ) :
    canonicalFluidCost threePointMoments q =
      57 / 10 - (44 / 25) * q + (11 / 10) * q ^ 2 := by
  rw [canonicalFluidCost_quadratic]
  norm_num [threePointMoments, canonicalLinearCoeff,
    canonicalQuadraticCoeff]
  ring

/-- Its optimal tested fraction is `q=4/5`. -/
theorem threePoint_minimized_at_four_fifths (q : ℝ) :
    canonicalFluidCost threePointMoments (4 / 5) ≤
      canonicalFluidCost threePointMoments q := by
  rw [threePoint_canonicalFluidCost, threePoint_canonicalFluidCost]
  nlinarith [sq_nonneg (q - 4 / 5)]

/-- The normalized optimum of the three-point witness is `4.996`. -/
theorem threePoint_optimal_value :
    canonicalFluidCost threePointMoments (4 / 5) = 2498 / 500 := by
  rw [threePoint_canonicalFluidCost]
  norm_num

end

end RandomizedOptional
end SchedulingPaper
