import SchedulingPaper.RandomizedStationaryCost
import Mathlib.Tactic

/-!
# Conditional averaging for a sample-first discovery order

Condition on the unordered sample.  The sampled labels and the remaining
labels are then ordered independently and uniformly.  This file proves that
the resulting early-completion contribution is exactly the scalar
`sampleFirstEarlyCost` used in the analytic proof.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

/-- The canonical enumeration hidden inside `Fintype.equivFin`, converted
to a permutation of `Fin k`. -/
def canonicalFinOrder (k : ℕ) : Equiv.Perm (Fin k) :=
  (Fintype.equivFin (Fin k)).trans (finCongr (Fintype.card_fin k))

/-- If `order` permutes the jobs of a block, this is the corresponding map
from literal positions `0,...,k-1` to jobs. -/
def linearizedFinOrder (k : ℕ) (order : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin k) :=
  (canonicalFinOrder k).symm.trans order

@[simp] theorem linearizedFinOrder_apply
    (k : ℕ) (order : Equiv.Perm (Fin k)) (i : Fin k) :
    linearizedFinOrder k order i = order ((canonicalFinOrder k).symm i) :=
  rfl

theorem precedes_linearizedFinOrder_iff
    (k : ℕ) (order : Equiv.Perm (Fin k)) (i j : Fin k) :
    Precedes order (linearizedFinOrder k order i)
        (linearizedFinOrder k order j) ↔ i < j := by
  unfold Precedes linearizedFinOrder canonicalFinOrder
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change
    (Fintype.equivFin (Fin k) ((Fintype.equivFin (Fin k)).symm
      ((finCongr (Fintype.card_fin k)).symm i)) <
    Fintype.equivFin (Fin k) ((Fintype.equivFin (Fin k)).symm
      ((finCongr (Fintype.card_fin k)).symm j))) ↔ _
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Early completion cost when the discovery blocks are written in literal
position order. -/
def positionEarlyCost
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) : ℝ :=
  ∑ i, if early i then
    discoveryBlock p early i +
      ∑ j, if j < i then discoveryBlock p early j else 0
  else 0

/-- Reindexing physical jobs by a random order turns the literal positional
cost into the stationary cost used by the expectation lemma. -/
theorem positionEarlyCost_comp_linearized_eq_stationary
    (k : ℕ) (p : Fin k → ℝ) (early : Fin k → Bool)
    (order : Equiv.Perm (Fin k)) :
    positionEarlyCost
        (p ∘ linearizedFinOrder k order)
        (early ∘ linearizedFinOrder k order) =
      stationaryEarlyCost p early order := by
  let linear := linearizedFinOrder k order
  let positional : Fin k → ℝ := fun i =>
    if early (linear i) then
      discoveryBlock p early (linear i) +
        ∑ j, if j < i then discoveryBlock p early (linear j) else 0
    else 0
  let physical : Fin k → ℝ := fun i =>
    if early i then discoveryCompletion p early order i else 0
  have hpoint : ∀ i, positional i = physical (linear i) := by
    intro i
    dsimp [positional, physical]
    congr 1
    unfold discoveryCompletion
    apply congrArg (fun z => discoveryBlock p early (linear i) + z)
    let f : Fin k → ℝ := fun z =>
      if z = linear i then 0
      else if Precedes order z (linear i) then
        discoveryBlock p early z else 0
    calc
      (∑ j, if j < i then discoveryBlock p early (linear j) else 0) =
          ∑ j, f (linear j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [f, Precedes]
        · have hlin : linear j ≠ linear i := fun h =>
            hji (linear.injective h)
          simp only [f, hlin, if_false]
          have hiff := precedes_linearizedFinOrder_iff k order j i
          by_cases hlt : j < i
          · have hp : Precedes order (linear j) (linear i) := hiff.mpr hlt
            simp [hlt, hp]
          · have hp : ¬Precedes order (linear j) (linear i) :=
              fun h => hlt (hiff.mp h)
            simp [hlt, hp]
      _ = ∑ z, f z := Equiv.sum_comp linear f
      _ = ∑ j, if j = linear i then 0
          else if Precedes order j (linear i) then
            discoveryBlock p early j else 0 := by
        rfl
  calc
    positionEarlyCost (p ∘ linear) (early ∘ linear) =
        ∑ i, positional i := by
      unfold positionEarlyCost positional linear
      rfl
    _ = ∑ i, physical (linear i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = ∑ i, physical i := Equiv.sum_comp linear physical
    _ = stationaryEarlyCost p early order := by
      rfl

theorem uniformAverage_prod
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℝ) :
    uniformAverage (fun z : A × B => f z.1 z.2) =
      uniformAverage (fun a : A => uniformAverage (f a)) := by
  unfold uniformAverage
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_div]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hB : (Fintype.card B : ℝ) ≠ 0 := by positivity
  field_simp [hA, hB]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp [hA, hB]

/-- Early-completion cost for two consecutive discovery blocks.  The first
block is the sample and the second block is the remaining population. -/
def blockOrderedEarlyCost
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (pSample : A → ℝ) (earlySample : A → Bool)
    (pRest : B → ℝ) (earlyRest : B → Bool)
    (sampleOrder : Equiv.Perm A) (restOrder : Equiv.Perm B) : ℝ :=
  stationaryEarlyCost pSample earlySample sampleOrder +
    earlyMassCount earlyRest *
      (∑ i, discoveryBlock pSample earlySample i) +
    stationaryEarlyCost pRest earlyRest restOrder

/-- Exact conditional expectation of the early-completion part. -/
theorem uniformAverage_blockOrderedEarlyCost
    {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (pSample : A → ℝ) (earlySample : A → Bool)
    (pRest : B → ℝ) (earlyRest : B → Bool) :
    uniformAverage (fun orders : Equiv.Perm A × Equiv.Perm B =>
      blockOrderedEarlyCost pSample earlySample pRest earlyRest
        orders.1 orders.2) =
      Randomized.sampleFirstEarlyCost
        (earlyMassCount earlySample) (earlyMassCount earlyRest)
        (∑ i, discoveryBlock pSample earlySample i)
        (∑ i, discoveryBlock pRest earlyRest i)
        (earlySelfWork pSample earlySample)
        (earlySelfWork pRest earlyRest) := by
  rw [uniformAverage_prod]
  rw [show (fun sampleOrder : Equiv.Perm A =>
      uniformAverage (fun restOrder : Equiv.Perm B =>
        blockOrderedEarlyCost pSample earlySample pRest earlyRest
          sampleOrder restOrder)) =
      (fun sampleOrder =>
        stationaryEarlyCost pSample earlySample sampleOrder +
          earlyMassCount earlyRest *
            (∑ i, discoveryBlock pSample earlySample i) +
          (earlyMassCount earlyRest *
              (∑ i, discoveryBlock pRest earlyRest i) / 2 +
            earlySelfWork pRest earlyRest / 2)) by
    funext sampleOrder
    rw [show (fun restOrder : Equiv.Perm B =>
        blockOrderedEarlyCost pSample earlySample pRest earlyRest
          sampleOrder restOrder) =
      (fun restOrder =>
        (stationaryEarlyCost pSample earlySample sampleOrder +
          earlyMassCount earlyRest *
            (∑ i, discoveryBlock pSample earlySample i)) +
          stationaryEarlyCost pRest earlyRest restOrder) by
            funext restOrder
            unfold blockOrderedEarlyCost
            rfl,
      uniformAverage_add, uniformAverage_const,
      uniformAverage_stationaryEarlyCost]
    ]
  rw [show (fun sampleOrder : Equiv.Perm A =>
      stationaryEarlyCost pSample earlySample sampleOrder +
        earlyMassCount earlyRest *
          (∑ i, discoveryBlock pSample earlySample i) +
        (earlyMassCount earlyRest *
            (∑ i, discoveryBlock pRest earlyRest i) / 2 +
          earlySelfWork pRest earlyRest / 2)) =
      (fun sampleOrder =>
        stationaryEarlyCost pSample earlySample sampleOrder +
          (earlyMassCount earlyRest *
              (∑ i, discoveryBlock pSample earlySample i) +
            (earlyMassCount earlyRest *
                (∑ i, discoveryBlock pRest earlyRest i) / 2 +
              earlySelfWork pRest earlyRest / 2))) by
    funext sampleOrder
    ring,
    uniformAverage_add, uniformAverage_const,
    uniformAverage_stationaryEarlyCost]
  unfold Randomized.sampleFirstEarlyCost
  ring

/-- Adding a deterministic late-tail contribution commutes with the same
conditional average. -/
theorem uniformAverage_blockOrderedEarlyCost_add_late
    {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (pSample : A → ℝ) (earlySample : A → Bool)
    (pRest : B → ℝ) (earlyRest : B → Bool)
    (lateCost : ℝ) :
    uniformAverage (fun orders : Equiv.Perm A × Equiv.Perm B =>
      blockOrderedEarlyCost pSample earlySample pRest earlyRest
        orders.1 orders.2 + lateCost) =
      sampleFirstScalarCost
        (earlyMassCount earlySample) (earlyMassCount earlyRest)
        (∑ i, discoveryBlock pSample earlySample i)
        (∑ i, discoveryBlock pRest earlyRest i)
        (earlySelfWork pSample earlySample)
        (earlySelfWork pRest earlyRest) lateCost := by
  rw [uniformAverage_add, uniformAverage_const,
    uniformAverage_blockOrderedEarlyCost]
  rfl

end

end RandomizedObligatory
end SchedulingPaper
