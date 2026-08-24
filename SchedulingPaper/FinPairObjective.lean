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

private theorem sum_row_split_lt
    {n : ℕ} (f : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j, f i j) =
      f i i +
        ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j +
        ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), f i j := by
  classical
  let upper := Finset.univ.filter (fun j : Fin n ↦ i < j)
  let lower := Finset.univ.filter (fun j : Fin n ↦ j < i)
  have hdisjoint : Disjoint upper lower := by
    apply Finset.disjoint_left.mpr
    intro j hjUpper hjLower
    simp only [upper, lower, Finset.mem_filter, Finset.mem_univ,
      true_and] at hjUpper hjLower
    exact (not_lt_of_ge hjUpper.le hjLower)
  have hunion : upper ∪ lower = Finset.univ.erase i := by
    ext j
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro (hij | hji)
      · exact ⟨ne_of_gt hij, trivial⟩
      · exact ⟨ne_of_lt hji, trivial⟩
    · rintro ⟨hji, _⟩
      rcases lt_trichotomy i j with hij | heq | hji'
      · exact Or.inl hij
      · exact (hji heq.symm).elim
      · exact Or.inr hji'
  calc
    (∑ j, f i j) = f i i + ∑ j ∈ Finset.univ.erase i, f i j :=
      (Finset.add_sum_erase Finset.univ (fun j ↦ f i j)
        (Finset.mem_univ i)).symm
    _ = f i i + ((∑ j ∈ upper, f i j) +
        ∑ j ∈ lower, f i j) := by
      rw [← Finset.sum_union hdisjoint, hunion]
    _ = _ := by dsimp [upper, lower]; ring

private theorem sum_lower_triangle_transpose
    {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), f i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f j i := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Split a symmetric ordered double sum into its diagonal and twice its
strict upper triangle. -/
theorem symmetric_double_sum
    {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + 2 *
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j := by
  simp_rw [sum_row_split_lt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_lower_triangle_transpose]
  have htranspose :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f j i) =
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    exact hsymm j i
  rw [htranspose]
  ring

/-- Ordered-pair form of the shortest-first objective on a finite vector. -/
theorem two_mul_pairCost_ofFn {n : ℕ} (values : Fin n → ℝ) :
    2 * pairCost (List.ofFn values) =
      (∑ i, ∑ j, min (values i) (values j)) + ∑ i, values i := by
  rw [pairCost_ofFn_eq_finSelfPairSum]
  have hdouble := symmetric_double_sum
    (fun i j ↦ min (values i) (values j))
    (fun i j ↦ min_comm _ _)
  simp only [min_self] at hdouble
  linarith

end

end SchedulingPaper
