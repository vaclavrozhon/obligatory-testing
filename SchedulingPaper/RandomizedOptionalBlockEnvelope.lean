import SchedulingPaper.RandomizedOptionalFluid
import Mathlib.Tactic

/-!
# Integrating a finite greedy fluid-block envelope

The optional knapsack is a finite sequence of homogeneous completion blocks
ordered by increasing work per completion.  This file constructs its literal
continuous completion curve and proves that the remaining-mass area is the
usual block formula.  It is the global analytic companion to the pointwise
supporting-hyperplane theorem in `RandomizedOptionalFluid`.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

structure FluidBlock where
  cost : ℝ
  mass : ℝ

def FluidBlock.work (b : FluidBlock) : ℝ := b.cost * b.mass

def fluidBlocksMass : List FluidBlock → ℝ
  | [] => 0
  | b :: rest => b.mass + fluidBlocksMass rest

def fluidBlocksWork : List FluidBlock → ℝ
  | [] => 0
  | b :: rest => b.work + fluidBlocksWork rest

/-- Mass completed inside one homogeneous block after local work `x`, with
the value clamped outside the block's work interval. -/
def FluidBlock.completed (b : FluidBlock) (x : ℝ) : ℝ :=
  min b.mass (max 0 (x / b.cost))

/-- Cumulative completion curve obtained by executing the blocks in list
order. -/
def fluidBlocksCompleted : List FluidBlock → ℝ → ℝ
  | [], _ => 0
  | b :: rest, x => b.completed x +
      fluidBlocksCompleted rest (x - b.work)

/-- Exact remaining-mass area of an ordered homogeneous block list. -/
def fluidBlocksArea : List FluidBlock → ℝ
  | [] => 0
  | b :: rest =>
      homogeneousBlockArea b.cost b.mass (fluidBlocksMass rest) +
        fluidBlocksArea rest

def fluidBlocksMinPair (blocks : List FluidBlock) : ℝ :=
  (blocks.map fun b =>
    (blocks.map fun c => min b.cost c.cost * b.mass * c.mass).sum).sum

theorem fluidBlocksMinPair_cons (b : FluidBlock) (rest : List FluidBlock) :
    fluidBlocksMinPair (b :: rest) =
      b.cost * b.mass ^ 2 +
      (rest.map fun c => min b.cost c.cost * b.mass * c.mass).sum +
      (rest.map fun c => min c.cost b.cost * c.mass * b.mass).sum +
      fluidBlocksMinPair rest := by
  unfold fluidBlocksMinPair
  simp only [List.map_cons, List.sum_cons, min_self]
  rw [List.sum_map_add]
  ring

theorem map_min_left_sum_of_forall_le
    (b : FluidBlock) (rest : List FluidBlock)
    (hle : ∀ c ∈ rest, b.cost ≤ c.cost) :
    (rest.map fun c => min b.cost c.cost * b.mass * c.mass).sum =
      b.cost * b.mass * fluidBlocksMass rest := by
  induction rest with
  | nil => simp [fluidBlocksMass]
  | cons c tail ih =>
      have hbc := hle c (by simp)
      have htail : ∀ d ∈ tail, b.cost ≤ d.cost := by
        intro d hd; exact hle d (by simp [hd])
      simp [fluidBlocksMass, min_eq_left hbc, ih htail]
      ring

theorem map_min_right_sum_of_forall_le
    (b : FluidBlock) (rest : List FluidBlock)
    (hle : ∀ c ∈ rest, b.cost ≤ c.cost) :
    (rest.map fun c => min c.cost b.cost * c.mass * b.mass).sum =
      b.cost * b.mass * fluidBlocksMass rest := by
  induction rest with
  | nil => simp [fluidBlocksMass]
  | cons c tail ih =>
      have hbc := hle c (by simp)
      have htail : ∀ d ∈ tail, b.cost ≤ d.cost := by
        intro d hd; exact hle d (by simp [hd])
      simp [fluidBlocksMass, min_eq_right hbc, ih htail]
      ring

/-- Internal SPT block area is one half of the full ordered minimum-pair
moment. -/
theorem fluidBlocksArea_eq_half_minPair
    (blocks : List FluidBlock)
    (hsorted : blocks.Pairwise fun a b => a.cost ≤ b.cost) :
    fluidBlocksArea blocks = fluidBlocksMinPair blocks / 2 := by
  induction blocks with
  | nil => simp [fluidBlocksArea, fluidBlocksMinPair]
  | cons b rest ih =>
      have hhead : ∀ c ∈ rest, b.cost ≤ c.cost :=
        (List.pairwise_cons.mp hsorted).1
      have hrestSorted : rest.Pairwise fun a b => a.cost ≤ b.cost :=
        (List.pairwise_cons.mp hsorted).2
      rw [fluidBlocksArea, ih hrestSorted, fluidBlocksMinPair_cons,
        map_min_left_sum_of_forall_le b rest hhead,
        map_min_right_sum_of_forall_le b rest hhead]
      unfold homogeneousBlockArea
      ring

def scaledClassBlocks {ι : Type*} (q : ℝ) (p D : ι → ℝ)
    (items : List ι) : List FluidBlock :=
  items.map fun i => ⟨p i, q * D i⟩

@[simp] theorem scaledClassBlocks_mass {ι : Type*}
    (q : ℝ) (p D : ι → ℝ) (items : List ι) :
    fluidBlocksMass (scaledClassBlocks q p D items) =
      q * (items.map D).sum := by
  induction items with
  | nil => simp [scaledClassBlocks, fluidBlocksMass]
  | cons i rest ih =>
      change q * D i + fluidBlocksMass (scaledClassBlocks q p D rest) = _
      rw [ih]
      simp
      ring

@[simp] theorem scaledClassBlocks_work {ι : Type*}
    (q : ℝ) (p D : ι → ℝ) (items : List ι) :
    fluidBlocksWork (scaledClassBlocks q p D items) =
      q * (items.map fun i => p i * D i).sum := by
  induction items with
  | nil => simp [scaledClassBlocks, fluidBlocksWork]
  | cons i rest ih =>
      change p i * (q * D i) +
        fluidBlocksWork (scaledClassBlocks q p D rest) = _
      rw [ih]
      simp
      ring

@[simp] theorem scaledClassBlocks_minPair {ι : Type*}
    (q : ℝ) (p D : ι → ℝ) (items : List ι) :
    fluidBlocksMinPair (scaledClassBlocks q p D items) =
      q ^ 2 *
        (items.map fun i =>
          (items.map fun j => min (p i) (p j) * D i * D j).sum).sum := by
  unfold fluidBlocksMinPair scaledClassBlocks
  simp only [List.map_map, Function.comp_apply]
  change (items.map fun i =>
      (items.map fun j =>
        min (p i) (p j) * (q * D i) * (q * D j)).sum).sum = _
  let base : ι → ℝ := fun i =>
    (items.map fun j => min (p i) (p j) * D i * D j).sum
  have houter :
      (items.map fun i =>
        (items.map fun j =>
          min (p i) (p j) * (q * D i) * (q * D j)).sum) =
      items.map fun i => q ^ 2 * base i := by
    apply List.map_congr_left
    intro i hi
    have hinner :
        (items.map fun j =>
          min (p i) (p j) * (q * D i) * (q * D j)) =
        items.map fun j => q ^ 2 *
          (min (p i) (p j) * D i * D j) := by
      apply List.map_congr_left
      intro j hj
      ring
    rw [hinner, List.sum_map_mul_left]
  rw [houter, List.sum_map_mul_left]

theorem scaledClassBlocks_pairwise
    {ι : Type*} {q : ℝ} {p D : ι → ℝ} {items : List ι}
    (hsorted : items.Pairwise fun i j => p i ≤ p j) :
    (scaledClassBlocks q p D items).Pairwise fun a b => a.cost ≤ b.cost := by
  induction items with
  | nil => simp [scaledClassBlocks]
  | cons i rest ih =>
      have hs := List.pairwise_cons.mp hsorted
      rw [show scaledClassBlocks q p D (i :: rest) =
        ({ cost := p i, mass := q * D i } : FluidBlock) ::
          scaledClassBlocks q p D rest by rfl]
      rw [List.pairwise_cons]
      constructor
      · intro block hblock
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hblock
        exact hs.1 j hj
      · exact ih hs.2

theorem scaledClassBlocks_area
    {ι : Type*} (q : ℝ) (p D : ι → ℝ) (items : List ι)
    (hsorted : items.Pairwise fun i j => p i ≤ p j) :
    fluidBlocksArea (scaledClassBlocks q p D items) =
      q ^ 2 *
        (items.map fun i =>
          (items.map fun j => min (p i) (p j) * D i * D j).sum).sum / 2 := by
  rw [fluidBlocksArea_eq_half_minPair _
    (scaledClassBlocks_pairwise hsorted), scaledClassBlocks_minPair]

/-! ## Greedy allocations carried by an ordered item list -/

def knapsackBlocks {α : Type*} (items : List α)
    (capacity cost : α → ℝ) : List FluidBlock :=
  items.map fun i => ⟨cost i, capacity i⟩

@[simp] theorem knapsackBlocks_mass {α : Type*}
    (items : List α) (capacity cost : α → ℝ) :
    fluidBlocksMass (knapsackBlocks items capacity cost) =
      (items.map capacity).sum := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
      simp only [knapsackBlocks, List.map_cons, fluidBlocksMass,
        List.sum_cons]
      exact congrArg (fun z => capacity i + z) ih

@[simp] theorem knapsackBlocks_work {α : Type*}
    (items : List α) (capacity cost : α → ℝ) :
    fluidBlocksWork (knapsackBlocks items capacity cost) =
      (items.map fun i => cost i * capacity i).sum := by
  induction items with
  | nil => rfl
  | cons i rest ih =>
      simp only [knapsackBlocks, List.map_cons, fluidBlocksWork,
        FluidBlock.work, List.sum_cons]
      exact congrArg (fun z => cost i * capacity i + z) ih

def orderedGreedyAllocation {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) : List α → ℝ → α → ℝ
  | [], _, _ => 0
  | i :: rest, x, j =>
      if j = i then
        (⟨cost i, capacity i⟩ : FluidBlock).completed x
      else
        orderedGreedyAllocation capacity cost rest
          (x - cost i * capacity i) j

/-- Canonical increasing-cost enumeration of a finite item type. -/
def sortedKnapsackItems {α : Type*} [Fintype α] [DecidableEq α]
    (cost : α → ℝ) : List α :=
  (Finset.univ.toList : List α).insertionSort
    (fun i j => cost i ≤ cost j)

theorem sortedKnapsackItems_nodup
    {α : Type*} [Fintype α] [DecidableEq α] (cost : α → ℝ) :
    (sortedKnapsackItems cost).Nodup := by
  have hp := List.perm_insertionSort (fun i j : α => cost i ≤ cost j)
    (Finset.univ.toList : List α)
  exact hp.nodup_iff.mpr (Finset.nodup_toList (Finset.univ : Finset α))

theorem sortedKnapsackItems_complete
    {α : Type*} [Fintype α] [DecidableEq α] (cost : α → ℝ) :
    (sortedKnapsackItems cost).toFinset = Finset.univ := by
  apply Finset.ext
  intro i
  simp [sortedKnapsackItems]

theorem sortedKnapsackItems_pairwise
    {α : Type*} [Fintype α] [DecidableEq α] (cost : α → ℝ) :
    (sortedKnapsackItems cost).Pairwise fun i j => cost i ≤ cost j := by
  let r : α → α → Prop := fun i j => cost i ≤ cost j
  letI : Std.Total r := ⟨fun i j => le_total (cost i) (cost j)⟩
  letI : IsTrans α r := ⟨fun _ _ _ hij hjk => hij.trans hjk⟩
  exact List.pairwise_insertionSort r (Finset.univ.toList : List α)

theorem sortedKnapsackItems_nonempty
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (cost : α → ℝ) : sortedKnapsackItems cost ≠ [] := by
  intro hnil
  let i : α := Classical.choice (inferInstance : Nonempty α)
  have hi : i ∈ (sortedKnapsackItems cost).toFinset := by
    rw [sortedKnapsackItems_complete]
    simp
  rw [hnil] at hi
  simp at hi

theorem FluidBlock.completed_nonneg {b : FluidBlock}
    (hmass : 0 ≤ b.mass) (x : ℝ) : 0 ≤ b.completed x := by
  unfold FluidBlock.completed
  exact le_min hmass (le_max_left _ _)

theorem FluidBlock.completed_le_mass {b : FluidBlock} (x : ℝ) :
    b.completed x ≤ b.mass := by
  unfold FluidBlock.completed
  exact min_le_left _ _

theorem greedyBlock_completed_eq_zero {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass) {x : ℝ} (hx : x ≤ 0) :
    b.completed x = 0 := by
  have hdiv : x / b.cost ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hx hcost.le
  unfold FluidBlock.completed
  rw [max_eq_left hdiv, min_eq_right hmass]

theorem greedyBlock_completed_eq_div {b : FluidBlock}
    (hcost : 0 < b.cost) {x : ℝ} (hx0 : 0 ≤ x)
    (hxw : x ≤ b.work) :
    b.completed x = x / b.cost := by
  have hdiv0 : 0 ≤ x / b.cost := div_nonneg hx0 hcost.le
  have hdivMass : x / b.cost ≤ b.mass := by
    rw [div_le_iff₀ hcost]
    simpa [FluidBlock.work, mul_comm] using hxw
  unfold FluidBlock.completed
  rw [max_eq_right hdiv0, min_eq_right hdivMass]

theorem greedyBlock_completed_eq_mass {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass)
    {x : ℝ} (hxw : b.work ≤ x) :
    b.completed x = b.mass := by
  have hdiv0 : 0 ≤ x / b.cost :=
    div_nonneg ((mul_nonneg hcost.le hmass).trans hxw) hcost.le
  have hmassDiv : b.mass ≤ x / b.cost := by
    rw [le_div_iff₀ hcost]
    simpa [FluidBlock.work, mul_comm] using hxw
  unfold FluidBlock.completed
  rw [max_eq_right hdiv0, min_eq_left hmassDiv]

theorem orderedGreedyAllocation_zero_of_not_mem
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α) (x : ℝ) {j : α}
    (hj : j ∉ items) :
    orderedGreedyAllocation capacity cost items x j = 0 := by
  induction items generalizing x with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.mem_cons, not_or] at hj
      simp [orderedGreedyAllocation, hj.1, ih _ hj.2]

theorem orderedGreedyAllocation_eq_zero_of_nonpos
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hcost : ∀ i ∈ items, 0 < cost i)
    (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    {x : ℝ} (hx : x ≤ 0) (j : α) :
    orderedGreedyAllocation capacity cost items x j = 0 := by
  induction items generalizing x with
  | nil => rfl
  | cons i rest ih =>
      have hiCost := hcost i (by simp)
      have hiCapacity := hcapacity i (by simp)
      have hrestCost : ∀ k ∈ rest, 0 < cost k := by
        intro k hk; exact hcost k (by simp [hk])
      have hrestCapacity : ∀ k ∈ rest, 0 ≤ capacity k := by
        intro k hk; exact hcapacity k (by simp [hk])
      by_cases hji : j = i
      · subst j
        simp [orderedGreedyAllocation]
        exact greedyBlock_completed_eq_zero
          (b := ⟨cost i, capacity i⟩) hiCost hiCapacity hx
      · have hshift : x - cost i * capacity i ≤ 0 := by
          linarith [mul_nonneg hiCost.le hiCapacity]
        simp [orderedGreedyAllocation, hji,
          ih hrestCost hrestCapacity hshift]

theorem orderedGreedyAllocation_nonneg
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    (x : ℝ) (j : α) :
    0 ≤ orderedGreedyAllocation capacity cost items x j := by
  induction items generalizing x with
  | nil => simp [orderedGreedyAllocation]
  | cons i rest ih =>
      by_cases hji : j = i
      · subst j
        simp [orderedGreedyAllocation,
          FluidBlock.completed_nonneg
            (b := ⟨cost i, capacity i⟩) (hcapacity i (by simp))]
      · simp [orderedGreedyAllocation, hji,
          ih (fun k hk => hcapacity k (by simp [hk]))]

theorem orderedGreedyAllocation_le_capacity
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnodup : items.Nodup) (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    (x : ℝ) {j : α} (hj : j ∈ items) :
    orderedGreedyAllocation capacity cost items x j ≤ capacity j := by
  induction items generalizing x j with
  | nil => simp at hj
  | cons i rest ih =>
      have hnot : i ∉ rest := List.nodup_cons.mp hnodup |>.1
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      rcases List.mem_cons.mp hj with rfl | hjrest
      · simp [orderedGreedyAllocation]
        exact FluidBlock.completed_le_mass x
      · have hji : j ≠ i := by
          intro h; subst j; exact hnot hjrest
        simp [orderedGreedyAllocation, hji]
        exact ih hrestNodup (fun k hk => hcapacity k (by simp [hk]))
          (x - cost i * capacity i) hjrest

theorem orderedGreedyAllocation_list_sum
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnodup : items.Nodup) (x : ℝ) :
    (items.map (orderedGreedyAllocation capacity cost items x)).sum =
      fluidBlocksCompleted (knapsackBlocks items capacity cost) x := by
  induction items generalizing x with
  | nil => simp [orderedGreedyAllocation, knapsackBlocks,
      fluidBlocksCompleted]
  | cons i rest ih =>
      have hnot : i ∉ rest := List.nodup_cons.mp hnodup |>.1
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      simp only [List.map_cons, List.sum_cons, knapsackBlocks,
        fluidBlocksCompleted]
      rw [show orderedGreedyAllocation capacity cost (i :: rest) x i =
          (⟨cost i, capacity i⟩ : FluidBlock).completed x by
        simp [orderedGreedyAllocation]]
      have htail :
          rest.map (orderedGreedyAllocation capacity cost (i :: rest) x) =
            rest.map (orderedGreedyAllocation capacity cost rest
              (x - cost i * capacity i)) := by
        apply List.map_congr_left
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hnot hj
        simp [orderedGreedyAllocation, hji]
      rw [htail, ih hrestNodup]
      rfl

theorem orderedGreedyAllocation_fintype_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnodup : items.Nodup) (hcomplete : items.toFinset = Finset.univ)
    (x : ℝ) :
    fractionalMass (orderedGreedyAllocation capacity cost items x) =
      fluidBlocksCompleted (knapsackBlocks items capacity cost) x := by
  unfold fractionalMass
  rw [← hcomplete, List.sum_toFinset _ hnodup]
  exact orderedGreedyAllocation_list_sum capacity cost items hnodup x

theorem orderedGreedyAllocation_work_eq
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnodup : items.Nodup)
    (hcost : ∀ i ∈ items, 0 < cost i)
    (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    {x : ℝ} (hx0 : 0 ≤ x)
    (hxWork : x ≤ fluidBlocksWork (knapsackBlocks items capacity cost)) :
    (items.map fun j =>
      cost j * orderedGreedyAllocation capacity cost items x j).sum = x := by
  induction items generalizing x with
  | nil =>
      simp [knapsackBlocks, fluidBlocksWork] at hxWork
      simp [orderedGreedyAllocation]
      linarith
  | cons i rest ih =>
      have hiCost := hcost i (by simp)
      have hiCapacity := hcapacity i (by simp)
      have hnot : i ∉ rest := List.nodup_cons.mp hnodup |>.1
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      have hrestCost : ∀ j ∈ rest, 0 < cost j := by
        intro j hj; exact hcost j (by simp [hj])
      have hrestCapacity : ∀ j ∈ rest, 0 ≤ capacity j := by
        intro j hj; exact hcapacity j (by simp [hj])
      let block : FluidBlock := ⟨cost i, capacity i⟩
      have hworkShape : fluidBlocksWork
          (knapsackBlocks (i :: rest) capacity cost) =
          block.work + fluidBlocksWork (knapsackBlocks rest capacity cost) := rfl
      by_cases hxFirst : x ≤ block.work
      · have hshift : x - block.work ≤ 0 := sub_nonpos.mpr hxFirst
        have htailZero : ∀ j ∈ rest,
            orderedGreedyAllocation capacity cost rest
              (x - block.work) j = 0 := by
          intro j hj
          exact orderedGreedyAllocation_eq_zero_of_nonpos capacity cost rest
            hrestCost hrestCapacity hshift j
        simp only [List.map_cons, List.sum_cons]
        rw [show orderedGreedyAllocation capacity cost (i :: rest) x i =
            block.completed x by simp [orderedGreedyAllocation, block]]
        rw [greedyBlock_completed_eq_div hiCost hx0 hxFirst]
        have htail :
            (rest.map fun j => cost j *
              orderedGreedyAllocation capacity cost (i :: rest) x j).sum = 0 := by
          apply List.sum_eq_zero
          intro term hterm
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hterm
          have hji : j ≠ i := by intro h; subst j; exact hnot hj
          have hz := htailZero j hj
          dsimp [block, FluidBlock.work] at hz
          rw [show orderedGreedyAllocation capacity cost (i :: rest) x j =
            orderedGreedyAllocation capacity cost rest
              (x - cost i * capacity i) j by
              simp [orderedGreedyAllocation, hji]]
          simp [hz]
        rw [htail]
        dsimp [block] at *
        field_simp [hiCost.ne']
        ring
      · have hxPast : block.work < x := lt_of_not_ge hxFirst
        have hxRest0 : 0 ≤ x - block.work := by linarith
        have hxRestWork : x - block.work ≤
            fluidBlocksWork (knapsackBlocks rest capacity cost) := by
          rw [hworkShape] at hxWork
          linarith
        have htailEq := ih hrestNodup hrestCost hrestCapacity
          hxRest0 hxRestWork
        simp only [List.map_cons, List.sum_cons]
        rw [show orderedGreedyAllocation capacity cost (i :: rest) x i =
            block.completed x by simp [orderedGreedyAllocation, block]]
        rw [greedyBlock_completed_eq_mass hiCost hiCapacity hxPast.le]
        have htail :
            (rest.map fun j => cost j *
              orderedGreedyAllocation capacity cost (i :: rest) x j).sum =
            (rest.map fun j => cost j *
              orderedGreedyAllocation capacity cost rest
                (x - block.work) j).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro j hj
          have hji : j ≠ i := by intro h; subst j; exact hnot hj
          rw [show orderedGreedyAllocation capacity cost (i :: rest) x j =
            orderedGreedyAllocation capacity cost rest
              (x - cost i * capacity i) j by
              simp [orderedGreedyAllocation, hji]]
          rfl
        rw [htail, htailEq]
        dsimp [block, FluidBlock.work]
        ring

/-- At every work budget inside a sorted finite knapsack there is a positive
pivot cost for which the ordered allocation is full below the pivot and zero
above it. -/
theorem orderedGreedyAllocation_exists_pivot
    {α : Type*} [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnonempty : items ≠ []) (hnodup : items.Nodup)
    (hsorted : items.Pairwise fun i j => cost i ≤ cost j)
    (hcost : ∀ i ∈ items, 0 < cost i)
    (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    {x : ℝ} (hx0 : 0 ≤ x)
    (hxWork : x ≤ fluidBlocksWork (knapsackBlocks items capacity cost)) :
    ∃ pivot ∈ items, 0 < cost pivot ∧
      (∀ j ∈ items, cost j < cost pivot →
        orderedGreedyAllocation capacity cost items x j = capacity j) ∧
      (∀ j ∈ items, cost pivot < cost j →
        orderedGreedyAllocation capacity cost items x j = 0) := by
  induction items generalizing x with
  | nil => contradiction
  | cons i rest ih =>
      have hiCost := hcost i (by simp)
      have hiCapacity := hcapacity i (by simp)
      have hnot : i ∉ rest := List.nodup_cons.mp hnodup |>.1
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      have hpair := List.pairwise_cons.mp hsorted
      have hrestCost : ∀ j ∈ rest, 0 < cost j := by
        intro j hj; exact hcost j (by simp [hj])
      have hrestCapacity : ∀ j ∈ rest, 0 ≤ capacity j := by
        intro j hj; exact hcapacity j (by simp [hj])
      let block : FluidBlock := ⟨cost i, capacity i⟩
      by_cases hxFirst : x ≤ block.work
      · refine ⟨i, by simp, hiCost, ?_, ?_⟩
        · intro j hj hjlow
          rcases List.mem_cons.mp hj with rfl | hjrest
          · exact False.elim (lt_irrefl _ hjlow)
          · exact False.elim (not_lt_of_ge (hpair.1 j hjrest) hjlow)
        · intro j hj hjhigh
          rcases List.mem_cons.mp hj with rfl | hjrest
          · exact False.elim (lt_irrefl _ hjhigh)
          · have hji : j ≠ i := by intro h; subst j; exact hnot hjrest
            have hshift : x - block.work ≤ 0 := sub_nonpos.mpr hxFirst
            rw [show orderedGreedyAllocation capacity cost (i :: rest) x j =
              orderedGreedyAllocation capacity cost rest
                (x - cost i * capacity i) j by
                simp [orderedGreedyAllocation, hji]]
            simpa [block] using
              orderedGreedyAllocation_eq_zero_of_nonpos capacity cost rest
                hrestCost hrestCapacity hshift j
      · have hxPast : block.work < x := lt_of_not_ge hxFirst
        have hxRest0 : 0 ≤ x - block.work := by linarith
        have hxRestWork : x - block.work ≤
            fluidBlocksWork (knapsackBlocks rest capacity cost) := by
          change x ≤ block.work +
            fluidBlocksWork (knapsackBlocks rest capacity cost) at hxWork
          linarith
        have hrestNonempty : rest ≠ [] := by
          intro hnil
          subst rest
          simp [knapsackBlocks, fluidBlocksWork] at hxRestWork
          linarith
        obtain ⟨pivot, hpivotMem, hpivotCost, hpivotLow, hpivotHigh⟩ :=
          ih hrestNonempty hrestNodup hpair.2 hrestCost hrestCapacity
            hxRest0 hxRestWork
        refine ⟨pivot, by simp [hpivotMem], hpivotCost, ?_, ?_⟩
        · intro j hj hjlow
          rcases List.mem_cons.mp hj with rfl | hjrest
          · have hfull := greedyBlock_completed_eq_mass
              (b := block) hiCost hiCapacity hxPast.le
            simpa [orderedGreedyAllocation, block] using hfull
          · have hji : j ≠ i := by intro h; subst j; exact hnot hjrest
            simpa [orderedGreedyAllocation, hji, block] using
              hpivotLow j hjrest hjlow
        · intro j hj hjhigh
          rcases List.mem_cons.mp hj with rfl | hjrest
          · have hipivot := hpair.1 pivot hpivotMem
            exact False.elim (not_lt_of_ge hipivot hjhigh)
          · have hji : j ≠ i := by intro h; subst j; exact hnot hjrest
            simpa [orderedGreedyAllocation, hji, block] using
              hpivotHigh j hjrest hjhigh

/-- A complete sorted list turns the executable ordered allocation into the
ordinary finite fractional-knapsack certificate used by the optional
completion-envelope theorem.  In particular, this theorem packages the
coordinatewise capacity bounds, exact work and completion mass, and the
supporting pivot in one statement. -/
theorem orderedGreedyAllocation_fintype_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (capacity cost : α → ℝ) (items : List α)
    (hnonempty : items ≠ []) (hnodup : items.Nodup)
    (hcomplete : items.toFinset = Finset.univ)
    (hsorted : items.Pairwise fun i j => cost i ≤ cost j)
    (hcost : ∀ i ∈ items, 0 < cost i)
    (hcapacity : ∀ i ∈ items, 0 ≤ capacity i)
    {x : ℝ} (hx0 : 0 ≤ x)
    (hxWork : x ≤ fluidBlocksWork (knapsackBlocks items capacity cost)) :
    let greedy := orderedGreedyAllocation capacity cost items x
    FractionalFeasible capacity greedy ∧
      fractionalWork cost greedy = x ∧
      fractionalMass greedy =
        fluidBlocksCompleted (knapsackBlocks items capacity cost) x ∧
      ∃ pivotCost, 0 < pivotCost ∧
        (∀ j, cost j < pivotCost → greedy j = capacity j) ∧
        (∀ j, pivotCost < cost j → greedy j = 0) := by
  dsimp
  have hmem : ∀ j : α, j ∈ items := by
    intro j
    have hj : j ∈ items.toFinset := by
      rw [hcomplete]
      simp
    simpa using hj
  have hfeasible : FractionalFeasible capacity
      (orderedGreedyAllocation capacity cost items x) := by
    constructor
    · intro j
      exact orderedGreedyAllocation_nonneg capacity cost items hcapacity x j
    · intro j
      exact orderedGreedyAllocation_le_capacity capacity cost items hnodup
        hcapacity x (hmem j)
  have hwork : fractionalWork cost
      (orderedGreedyAllocation capacity cost items x) = x := by
    unfold fractionalWork
    rw [← hcomplete, List.sum_toFinset _ hnodup]
    exact orderedGreedyAllocation_work_eq capacity cost items hnodup hcost
      hcapacity hx0 hxWork
  have hmass : fractionalMass
      (orderedGreedyAllocation capacity cost items x) =
        fluidBlocksCompleted (knapsackBlocks items capacity cost) x :=
    orderedGreedyAllocation_fintype_mass capacity cost items hnodup hcomplete x
  obtain ⟨pivot, hpivotMem, hpivotCost, hpivotLow, hpivotHigh⟩ :=
    orderedGreedyAllocation_exists_pivot capacity cost items hnonempty hnodup
      hsorted hcost hcapacity hx0 hxWork
  refine ⟨hfeasible, hwork, hmass, cost pivot, hpivotCost, ?_, ?_⟩
  · intro j hj
    exact hpivotLow j (hmem j) hj
  · intro j hj
    exact hpivotHigh j (hmem j) hj

/-- The preceding certificate specialized to the canonical increasing-cost
enumeration of all items. -/
theorem sortedKnapsackAllocation_certificate
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (capacity cost : α → ℝ)
    (hcost : ∀ i, 0 < cost i)
    (hcapacity : ∀ i, 0 ≤ capacity i)
    {x : ℝ} (hx0 : 0 ≤ x)
    (hxWork : x ≤ fluidBlocksWork
      (knapsackBlocks (sortedKnapsackItems cost) capacity cost)) :
    let items := sortedKnapsackItems cost
    let greedy := orderedGreedyAllocation capacity cost items x
    FractionalFeasible capacity greedy ∧
      fractionalWork cost greedy = x ∧
      fractionalMass greedy =
        fluidBlocksCompleted (knapsackBlocks items capacity cost) x ∧
      ∃ pivotCost, 0 < pivotCost ∧
        (∀ j, cost j < pivotCost → greedy j = capacity j) ∧
        (∀ j, pivotCost < cost j → greedy j = 0) := by
  dsimp
  exact orderedGreedyAllocation_fintype_certificate capacity cost
    (sortedKnapsackItems cost) (sortedKnapsackItems_nonempty cost)
      (sortedKnapsackItems_nodup cost) (sortedKnapsackItems_complete cost)
      (sortedKnapsackItems_pairwise cost)
      (fun i _ => hcost i) (fun i _ => hcapacity i) hx0 hxWork

@[simp] theorem fluidBlocksMass_append (left right : List FluidBlock) :
    fluidBlocksMass (left ++ right) =
      fluidBlocksMass left + fluidBlocksMass right := by
  induction left with
  | nil => simp [fluidBlocksMass]
  | cons b rest ih => simp [fluidBlocksMass, ih, add_assoc]

@[simp] theorem fluidBlocksWork_append (left right : List FluidBlock) :
    fluidBlocksWork (left ++ right) =
      fluidBlocksWork left + fluidBlocksWork right := by
  induction left with
  | nil => simp [fluidBlocksWork]
  | cons b rest ih => simp [fluidBlocksWork, ih, add_assoc]

theorem fluidBlocksArea_append (left right : List FluidBlock) :
    fluidBlocksArea (left ++ right) =
      fluidBlocksArea left + fluidBlocksArea right +
        fluidBlocksWork left * fluidBlocksMass right := by
  induction left with
  | nil => simp [fluidBlocksArea, fluidBlocksWork]
  | cons b rest ih =>
      simp only [List.cons_append, fluidBlocksArea, fluidBlocksMass_append,
        fluidBlocksWork]
      rw [ih]
      unfold homogeneousBlockArea FluidBlock.work
      ring

theorem FluidBlock.work_nonneg {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass) :
    0 ≤ b.work := mul_nonneg hcost.le hmass

theorem FluidBlock.completed_continuous (b : FluidBlock) :
    Continuous b.completed := by
  unfold FluidBlock.completed
  exact continuous_const.min
    (continuous_const.max (continuous_id.div_const b.cost))

theorem FluidBlock.completed_monotone {b : FluidBlock}
    (hcost : 0 < b.cost) : Monotone b.completed := by
  intro x y hxy
  have hdiv : x / b.cost ≤ y / b.cost :=
    div_le_div_of_nonneg_right hxy hcost.le
  unfold FluidBlock.completed
  exact min_le_min le_rfl (max_le_max le_rfl hdiv)

theorem fluidBlocksCompleted_monotone
    {blocks : List FluidBlock}
    (hcost : ∀ b ∈ blocks, 0 < b.cost) :
    Monotone (fluidBlocksCompleted blocks) := by
  induction blocks with
  | nil => exact monotone_const
  | cons b rest ih =>
      intro x y hxy
      exact add_le_add
        (FluidBlock.completed_monotone (hcost b (by simp)) hxy)
        (ih (fun c hc => hcost c (by simp [hc])) (sub_le_sub_right hxy b.work))

theorem fluidBlocksCompleted_continuous (blocks : List FluidBlock) :
    Continuous (fluidBlocksCompleted blocks) := by
  induction blocks with
  | nil => exact continuous_const
  | cons b rest ih =>
      exact b.completed_continuous.add
        (ih.comp (continuous_id.sub continuous_const))

theorem FluidBlock.completed_eq_zero {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass) {x : ℝ} (hx : x ≤ 0) :
    b.completed x = 0 := by
  have hdiv : x / b.cost ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hx hcost.le
  unfold FluidBlock.completed
  rw [max_eq_left hdiv, min_eq_right hmass]

theorem FluidBlock.completed_eq_div {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass)
    {x : ℝ} (hx0 : 0 ≤ x) (hxw : x ≤ b.work) :
    b.completed x = x / b.cost := by
  have hdiv0 : 0 ≤ x / b.cost := div_nonneg hx0 hcost.le
  have hdivMass : x / b.cost ≤ b.mass := by
    rw [div_le_iff₀ hcost]
    simpa [FluidBlock.work, mul_comm] using hxw
  unfold FluidBlock.completed
  rw [max_eq_right hdiv0, min_eq_right hdivMass]

theorem FluidBlock.completed_eq_mass {b : FluidBlock}
    (hcost : 0 < b.cost) (hmass : 0 ≤ b.mass)
    {x : ℝ} (hxw : b.work ≤ x) :
    b.completed x = b.mass := by
  have hdiv0 : 0 ≤ x / b.cost := by
    exact div_nonneg (b.work_nonneg hcost hmass |>.trans hxw) hcost.le
  have hmassDiv : b.mass ≤ x / b.cost := by
    rw [le_div_iff₀ hcost]
    simpa [FluidBlock.work, mul_comm] using hxw
  unfold FluidBlock.completed
  rw [max_eq_right hdiv0, min_eq_left hmassDiv]

theorem fluidBlocksCompleted_eq_zero_of_nonpos
    {blocks : List FluidBlock}
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass)
    {x : ℝ} (hx : x ≤ 0) :
    fluidBlocksCompleted blocks x = 0 := by
  induction blocks generalizing x with
  | nil => rfl
  | cons b rest ih =>
      have hbCost : 0 < b.cost := hcost b (by simp)
      have hbMass : 0 ≤ b.mass := hmass b (by simp)
      have hrestCost : ∀ c ∈ rest, 0 < c.cost := by
        intro c hc; exact hcost c (by simp [hc])
      have hrestMass : ∀ c ∈ rest, 0 ≤ c.mass := by
        intro c hc; exact hmass c (by simp [hc])
      have hshift : x - b.work ≤ 0 := by
        linarith [b.work_nonneg hbCost hbMass]
      simp [fluidBlocksCompleted, b.completed_eq_zero hbCost hbMass hx,
        ih hrestCost hrestMass hshift]

theorem fluidBlocksCompleted_nonneg
    {blocks : List FluidBlock}
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass) (x : ℝ) :
    0 ≤ fluidBlocksCompleted blocks x := by
  induction blocks generalizing x with
  | nil => rfl
  | cons b rest ih =>
      exact add_nonneg
        (FluidBlock.completed_nonneg (hmass b (by simp)) x)
        (ih (fun c hc => hmass c (by simp [hc])) (x - b.work))

theorem fluidBlocksCompleted_le_mass
    {blocks : List FluidBlock}
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass) (x : ℝ) :
    fluidBlocksCompleted blocks x ≤ fluidBlocksMass blocks := by
  induction blocks generalizing x with
  | nil => exact le_rfl
  | cons b rest ih =>
      change b.completed x + fluidBlocksCompleted rest (x - b.work) ≤
        b.mass + fluidBlocksMass rest
      exact add_le_add (FluidBlock.completed_le_mass x)
        (ih (fun c hc => hmass c (by simp [hc])) (x - b.work))

theorem fluidBlocksMass_nonneg {blocks : List FluidBlock}
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass) :
    0 ≤ fluidBlocksMass blocks := by
  induction blocks with
  | nil => simp [fluidBlocksMass]
  | cons b rest ih =>
      simp only [fluidBlocksMass]
      exact add_nonneg (hmass b (by simp))
        (ih (fun c hc => hmass c (by simp [hc])))

theorem fluidBlocksWork_nonneg {blocks : List FluidBlock}
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass) :
    0 ≤ fluidBlocksWork blocks := by
  induction blocks with
  | nil => simp [fluidBlocksWork]
  | cons b rest ih =>
      simp only [fluidBlocksWork]
      exact add_nonneg
        (FluidBlock.work_nonneg (hcost b (by simp)) (hmass b (by simp)))
        (ih (fun c hc => hcost c (by simp [hc]))
          (fun c hc => hmass c (by simp [hc])))

/-- Once the whole ordered block list has received its terminal work, its
clamped completion curve stays equal to total mass. -/
theorem fluidBlocksCompleted_eq_mass_of_work_le
    {blocks : List FluidBlock}
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass)
    {x : ℝ} (hx : fluidBlocksWork blocks ≤ x) :
    fluidBlocksCompleted blocks x = fluidBlocksMass blocks := by
  induction blocks generalizing x with
  | nil => rfl
  | cons b rest ih =>
      have hbCost : 0 < b.cost := hcost b (by simp)
      have hbMass : 0 ≤ b.mass := hmass b (by simp)
      have hrestCost : ∀ c ∈ rest, 0 < c.cost := by
        intro c hc
        exact hcost c (by simp [hc])
      have hrestMass : ∀ c ∈ rest, 0 ≤ c.mass := by
        intro c hc
        exact hmass c (by simp [hc])
      have hrestWork0 : 0 ≤ fluidBlocksWork rest :=
        fluidBlocksWork_nonneg hrestCost hrestMass
      have hbx : b.work ≤ x := by
        change b.work + fluidBlocksWork rest ≤ x at hx
        linarith
      change b.completed x + fluidBlocksCompleted rest (x - b.work) =
        b.mass + fluidBlocksMass rest
      rw [FluidBlock.completed_eq_mass hbCost hbMass hbx]
      rw [ih hrestCost hrestMass (by
        change b.work + fluidBlocksWork rest ≤ x at hx
        linarith)]

theorem fluidBlocksCompleted_on_first
    {b : FluidBlock} {rest : List FluidBlock}
    (hbCost : 0 < b.cost) (hbMass : 0 ≤ b.mass)
    (hrestCost : ∀ c ∈ rest, 0 < c.cost)
    (hrestMass : ∀ c ∈ rest, 0 ≤ c.mass)
    {x : ℝ} (hx0 : 0 ≤ x) (hxw : x ≤ b.work) :
    fluidBlocksCompleted (b :: rest) x = x / b.cost := by
  unfold fluidBlocksCompleted
  rw [b.completed_eq_div hbCost hbMass hx0 hxw]
  have hshift : x - b.work ≤ 0 := sub_nonpos.mpr hxw
  rw [fluidBlocksCompleted_eq_zero_of_nonpos hrestCost hrestMass hshift]
  ring

theorem fluidBlocksCompleted_after_first
    {b : FluidBlock} {rest : List FluidBlock}
    (hbCost : 0 < b.cost) (hbMass : 0 ≤ b.mass)
    {x : ℝ} (hxw : b.work ≤ x) :
    fluidBlocksCompleted (b :: rest) x =
      b.mass + fluidBlocksCompleted rest (x - b.work) := by
  change b.completed x + fluidBlocksCompleted rest (x - b.work) = _
  rw [b.completed_eq_mass hbCost hbMass hxw]

/-- The integral under the remaining-mass curve of a finite ordered block
schedule is exactly the homogeneous-block area sum. -/
theorem fluidBlocks_remaining_integral_eq_area
    (blocks : List FluidBlock)
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass) :
    (∫ x in 0..fluidBlocksWork blocks,
      (fluidBlocksMass blocks - fluidBlocksCompleted blocks x)) =
        fluidBlocksArea blocks := by
  induction blocks with
  | nil => simp [fluidBlocksWork, fluidBlocksMass, fluidBlocksCompleted,
      fluidBlocksArea]
  | cons b rest ih =>
      have hbCost : 0 < b.cost := hcost b (by simp)
      have hbMass : 0 ≤ b.mass := hmass b (by simp)
      have hrestCost : ∀ c ∈ rest, 0 < c.cost := by
        intro c hc; exact hcost c (by simp [hc])
      have hrestMass : ∀ c ∈ rest, 0 ≤ c.mass := by
        intro c hc; exact hmass c (by simp [hc])
      have hWb : 0 ≤ b.work := b.work_nonneg hbCost hbMass
      have hWr : 0 ≤ fluidBlocksWork rest :=
        fluidBlocksWork_nonneg hrestCost hrestMass
      let remaining : ℝ → ℝ := fun x =>
        fluidBlocksMass (b :: rest) - fluidBlocksCompleted (b :: rest) x
      have hremainingContinuous : Continuous remaining :=
        continuous_const.sub (fluidBlocksCompleted_continuous (b :: rest))
      have hleftInt : IntervalIntegrable remaining MeasureTheory.volume
          0 b.work := hremainingContinuous.intervalIntegrable 0 b.work
      have hrightInt : IntervalIntegrable remaining MeasureTheory.volume
          b.work (b.work + fluidBlocksWork rest) :=
        hremainingContinuous.intervalIntegrable b.work
          (b.work + fluidBlocksWork rest)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        hleftInt hrightInt
      have hfirst :
          (∫ x in 0..b.work, remaining x) =
            homogeneousBlockArea b.cost b.mass (fluidBlocksMass rest) := by
        rw [intervalIntegral.integral_congr (by
          intro x hx
          have hx' : x ∈ Set.Icc (0 : ℝ) b.work := by
            simpa [Set.uIcc_of_le hWb] using hx
          change b.mass + fluidBlocksMass rest -
              fluidBlocksCompleted (b :: rest) x = _
          rw [fluidBlocksCompleted_on_first hbCost hbMass hrestCost
            hrestMass hx'.1 hx'.2])]
        simp [FluidBlock.work, homogeneousBlockArea,
          intervalIntegral.integral_sub, intervalIntegral.integral_div]
        field_simp [hbCost.ne']
        ring
      have hsecond :
          (∫ x in b.work..b.work + fluidBlocksWork rest, remaining x) =
            fluidBlocksArea rest := by
        rw [intervalIntegral.integral_congr (by
          intro x hx
          have hx' : x ∈ Set.Icc b.work
              (b.work + fluidBlocksWork rest) := by
            rw [Set.uIcc_of_le (by linarith)] at hx
            exact hx
          change b.mass + fluidBlocksMass rest -
              fluidBlocksCompleted (b :: rest) x = _
          rw [fluidBlocksCompleted_after_first hbCost hbMass hx'.1])]
        simp only [add_sub_add_left_eq_sub]
        rw [intervalIntegral.integral_comp_sub_right
          (fun y => fluidBlocksMass rest - fluidBlocksCompleted rest y)
          b.work]
        convert ih hrestCost hrestMass using 1 <;> ring
      simp only [fluidBlocksWork, fluidBlocksArea]
      change (∫ x in 0..b.work + fluidBlocksWork rest, remaining x) = _
      rw [← hsplit, hfirst, hsecond]

/-! ## Canonical optional four-block specialization -/

def canonicalFluidBlocks (M : FluidMoments) (q τ : ℝ)
    (medium high : List FluidBlock) : List FluidBlock :=
  ⟨τ, M.lowMass * q⟩ ::
    (medium ++ ⟨M.mean, 1 - q⟩ :: high)

/-- Aggregate block identities imply that the greedy block area is exactly
the five-term canonical optional objective.  The medium and high internal
identities are supplied by their SPT class lists. -/
theorem canonicalFluidBlocks_area_eq_cost
    (M : FluidMoments) (q τ : ℝ)
    (medium high : List FluidBlock)
    (hmodule : τ * M.lowMass = 1 + M.lowMoment)
    (hmediumMass : fluidBlocksMass medium + (1 - q) +
        fluidBlocksMass high = 1 - M.lowMass * q)
    (hmediumWork : fluidBlocksWork medium = q * M.mediumMoment)
    (hmediumArea : fluidBlocksArea medium =
      q ^ 2 * M.mediumMinPair / 2)
    (hhighMass : fluidBlocksMass high = q * M.highMass)
    (hhighArea : fluidBlocksArea high =
      q ^ 2 * M.highMinPair / 2) :
    fluidBlocksArea (canonicalFluidBlocks M q τ medium high) =
      canonicalFluidCost M q := by
  have hmediumMass' : fluidBlocksMass medium +
      (1 - q + fluidBlocksMass high) = 1 - M.lowMass * q := by
    linarith
  unfold canonicalFluidBlocks
  simp only [fluidBlocksArea]
  rw [fluidBlocksArea_append]
  simp only [fluidBlocksMass_append, fluidBlocksMass, fluidBlocksArea,
    fluidBlocksWork]
  rw [hmediumMass', hmediumWork,
    hmediumArea, hhighMass, hhighArea]
  unfold homogeneousBlockArea canonicalFluidCost testLowArea mediumArea
    blindArea highArea
  linear_combination (q - M.lowMass * q ^ 2 / 2) * hmodule

theorem canonicalFluidBlocks_mass_eq_one
    (M : FluidMoments) (q τ : ℝ)
    (medium high : List FluidBlock)
    (hmediumMass : fluidBlocksMass medium + (1 - q) +
      fluidBlocksMass high = 1 - M.lowMass * q) :
    fluidBlocksMass (canonicalFluidBlocks M q τ medium high) = 1 := by
  unfold canonicalFluidBlocks
  simp only [fluidBlocksMass, fluidBlocksMass_append]
  linarith

theorem canonicalFluidBlocks_work_eq_q_add_mean
    (M : FluidMoments) (q τ : ℝ)
    (medium high : List FluidBlock)
    (hmodule : τ * M.lowMass = 1 + M.lowMoment)
    (hmediumWork : fluidBlocksWork medium = q * M.mediumMoment)
    (hhighWork : fluidBlocksWork high =
      q * (M.mean - M.lowMoment - M.mediumMoment)) :
    fluidBlocksWork (canonicalFluidBlocks M q τ medium high) = q + M.mean := by
  unfold canonicalFluidBlocks
  simp only [fluidBlocksWork, fluidBlocksWork_append, FluidBlock.work]
  rw [hmediumWork, hhighWork]
  linear_combination q * hmodule

/-- Integral form of the preceding identity. -/
theorem canonicalFluidBlocks_remaining_integral_eq_cost
    (M : FluidMoments) (q τ : ℝ)
    (medium high : List FluidBlock)
    (hcost : ∀ b ∈ canonicalFluidBlocks M q τ medium high, 0 < b.cost)
    (hmass : ∀ b ∈ canonicalFluidBlocks M q τ medium high, 0 ≤ b.mass)
    (hmodule : τ * M.lowMass = 1 + M.lowMoment)
    (hmediumMass : fluidBlocksMass medium + (1 - q) +
        fluidBlocksMass high = 1 - M.lowMass * q)
    (hmediumWork : fluidBlocksWork medium = q * M.mediumMoment)
    (hmediumArea : fluidBlocksArea medium =
      q ^ 2 * M.mediumMinPair / 2)
    (hhighMass : fluidBlocksMass high = q * M.highMass)
    (hhighArea : fluidBlocksArea high =
      q ^ 2 * M.highMinPair / 2) :
    (∫ x in 0..fluidBlocksWork (canonicalFluidBlocks M q τ medium high),
      (fluidBlocksMass (canonicalFluidBlocks M q τ medium high) -
        fluidBlocksCompleted (canonicalFluidBlocks M q τ medium high) x)) =
      canonicalFluidCost M q := by
  rw [fluidBlocks_remaining_integral_eq_area _ hcost hmass]
  exact canonicalFluidBlocks_area_eq_cost M q τ medium high hmodule
    hmediumMass hmediumWork hmediumArea hhighMass hhighArea

end

end RandomizedOptional
end SchedulingPaper
