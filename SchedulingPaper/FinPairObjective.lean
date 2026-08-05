import SchedulingPaper.OfflineOptimal
import Mathlib.Tactic

/-!
# Conversion between finite-index and recursive pair objectives

Several runtime reductions use a `Fin n` diagonal plus an `i<j` sum, while
the offline and endpoint games use a recursive list objective.  This file
provides the common exact conversion.
-/

namespace SchedulingPaper

noncomputable section

def listPairObjective {α : Type*}
    (self : α → ℝ) (pair : α → α → ℝ) : List α → ℝ
  | [] => 0
  | value :: values =>
      self value +
        (values.map (pair value)).sum +
        listPairObjective self pair values

private theorem generic_pair_rows_ofFn
    {n : ℕ} (pair : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1),
      ∑ j ∈ Finset.univ.filter (fun j => i < j),
        pair i j) =
      (∑ j : Fin n, pair 0 j.succ) +
      ∑ i : Fin n, ∑ j ∈
        Finset.univ.filter (fun j => i < j),
          pair i.succ j.succ := by
  rw [Fin.sum_univ_succ]
  congr 1
  · classical
    simp_rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp
  · apply Finset.sum_congr rfl
    intro i _hi
    classical
    simp_rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp

/-- A diagonal plus one charge for every `i<j` is the recursive pair
objective of the corresponding `List.ofFn`. -/
theorem finSelfPairSum_eq_listPairObjective
    {n : ℕ} {α : Type*}
    (self : α → ℝ) (pair : α → α → ℝ)
    (values : Fin n → α) :
    (∑ i, self (values i)) +
        ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            pair (values i) (values j) =
      listPairObjective self pair (List.ofFn values) := by
  induction n with
  | zero =>
      simp [listPairObjective]
  | succ n ih =>
      let tailValues : Fin n → α :=
        fun i => values i.succ
      have htail := ih tailValues
      rw [Fin.sum_univ_succ]
      rw [generic_pair_rows_ofFn
        (fun i j => pair (values i) (values j))]
      rw [show List.ofFn values =
          values 0 :: List.ofFn tailValues by
        simp [tailValues, List.ofFn_succ]]
      simp only [listPairObjective]
      have hrow :
          ((List.ofFn tailValues).map
            (pair (values 0))).sum =
            ∑ j : Fin n,
              pair (values 0) (tailValues j) := by
        rw [List.map_ofFn, List.sum_ofFn]
        simp [Function.comp_apply]
      rw [hrow, ← htail]
      dsimp [tailValues]
      ring

theorem pairCost_eq_listPairObjective (values : List ℝ) :
    pairCost values =
      listPairObjective id min values := by
  induction values with
  | nil =>
      simp [pairCost, listPairObjective]
  | cons value values ih =>
      simp only [pairCost, List.sum_cons, pairMinCost_cons]
      rw [show
        listPairObjective id min (value :: values) =
          value + (values.map (min value)).sum +
            listPairObjective id min values by
        rfl]
      rw [← ih]
      unfold pairCost
      ring

/-- Finite-index normal form of the unordered shortest-first objective. -/
theorem pairCost_ofFn_eq_finSelfPairSum
    {n : ℕ} (values : Fin n → ℝ) :
    pairCost (List.ofFn values) =
      (∑ i, values i) +
        ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            min (values i) (values j) := by
  calc
    pairCost (List.ofFn values) =
        listPairObjective id min (List.ofFn values) :=
      pairCost_eq_listPairObjective _
    _ =
        (∑ i, values i) +
          ∑ i, ∑ j ∈
            Finset.univ.filter (fun j => i < j),
              min (values i) (values j) :=
      (finSelfPairSum_eq_listPairObjective
        (self := id) (pair := min) values).symm

end

end SchedulingPaper
