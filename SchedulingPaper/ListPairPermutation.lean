import SchedulingPaper.FinPairObjective
import Mathlib.Tactic

/-!
# Generic lemmas for finite pair objectives

The endpoint reductions below produce a diagonal term and one charge for
each unordered pair.  This file records the elementary list facts used to
sort endpoint classes and to compare the exact `k (k-1) / 2` finite count
with its homogeneous `k² / 2` limit.
-/

namespace SchedulingPaper

noncomputable section

theorem listPairObjective_mono
    {α : Type*} {self₁ self₂ : α → ℝ}
    {pair₁ pair₂ : α → α → ℝ}
    (hself : ∀ x, self₁ x ≤ self₂ x)
    (hpair : ∀ x y, pair₁ x y ≤ pair₂ x y) :
    ∀ values : List α,
      listPairObjective self₁ pair₁ values ≤
        listPairObjective self₂ pair₂ values := by
  intro values
  induction values with
  | nil =>
      simp [listPairObjective]
  | cons value values ih =>
      simp only [listPairObjective]
      have hrow :
          (values.map (pair₁ value)).sum ≤
            (values.map (pair₂ value)).sum := by
        apply List.sum_le_sum
        intro tail _htail
        exact hpair value tail
      linarith [hself value]

theorem listPairObjective_mono_of_pairwise
    {α : Type*} {self₁ self₂ : α → ℝ}
    {pair₁ pair₂ : α → α → ℝ}
    {values : List α}
    (hself : ∀ x ∈ values, self₁ x ≤ self₂ x)
    (hpair :
      values.Pairwise (fun x y => pair₁ x y ≤ pair₂ x y)) :
    listPairObjective self₁ pair₁ values ≤
      listPairObjective self₂ pair₂ values := by
  induction values with
  | nil =>
      simp [listPairObjective]
  | cons value values ih =>
      rw [List.pairwise_cons] at hpair
      simp only [listPairObjective]
      have hrow :
          (values.map (pair₁ value)).sum ≤
            (values.map (pair₂ value)).sum := by
        apply List.sum_le_sum
        intro tail htail
        exact hpair.1 tail htail
      have htail :
          listPairObjective self₁ pair₁ values ≤
            listPairObjective self₂ pair₂ values := by
        apply ih
        · intro tail htail
          exact hself tail (by simp [htail])
        · exact hpair.2
      linarith [hself value (by simp)]

theorem listPairObjective_perm
    {α : Type*} (self : α → ℝ) (pair : α → α → ℝ)
    (hsymm : ∀ x y, pair x y = pair y x)
    {left right : List α} (hperm : left.Perm right) :
    listPairObjective self pair left =
      listPairObjective self pair right := by
  induction hperm using List.Perm.recOnSwap' with
  | nil =>
      rfl
  | cons value hperm ih =>
      simp only [listPairObjective]
      have hmap :
          (List.map (pair value) _).Perm
            (List.map (pair value) _) :=
        hperm.map _
      rw [ih, hmap.sum_eq]
  | swap' first second hperm ih =>
      have hfirst :
          (List.map (pair first) _).sum =
            (List.map (pair first) _).sum :=
        (hperm.map _).sum_eq
      have hsecond :
          (List.map (pair second) _).sum =
            (List.map (pair second) _).sum :=
        (hperm.map _).sum_eq
      simp only [listPairObjective, List.map_cons, List.sum_cons]
      rw [ih, hfirst, hsecond, hsymm first second]
      ring
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

@[simp] theorem listPairObjective_replicate
    {α : Type*} (pair : α → α → ℝ) (value : α) :
    ∀ count : ℕ,
      listPairObjective (fun _ => 0) pair
          (List.replicate count value) =
        (count : ℝ) * (count - 1) / 2 *
          pair value value := by
  intro count
  induction count with
  | zero =>
      simp [listPairObjective]
  | succ count ih =>
      simp only [List.replicate_succ, listPairObjective,
        List.map_replicate, List.sum_replicate, ih,
        Nat.cast_add, Nat.cast_one]
      push_cast
      ring

theorem listPairObjective_replicate_append
    {α : Type*} (pair : α → α → ℝ)
    (value : α) (count : ℕ) (tail : List α) :
    listPairObjective (fun _ => 0) pair
        (List.replicate count value ++ tail) =
      (count : ℝ) * (count - 1) / 2 *
          pair value value +
        count * (tail.map (pair value)).sum +
        listPairObjective (fun _ => 0) pair tail := by
  induction count with
  | zero =>
      simp [listPairObjective]
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        listPairObjective, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, ih,
        Nat.cast_add, Nat.cast_one]
      push_cast
      ring

theorem sum_map_replicate_append
    {α : Type*} (f : α → ℝ)
    (value : α) (count : ℕ) (tail : List α) :
    ((List.replicate count value ++ tail).map f).sum =
      count * f value + (tail.map f).sum := by
  simp

end

end SchedulingPaper
