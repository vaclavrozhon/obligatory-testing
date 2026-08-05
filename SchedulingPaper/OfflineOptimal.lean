import SchedulingPaper.Model
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# The unified offline order

This file formalizes the combinatorial core of the paper's Lemma 3.1. A list
records effective job lengths in execution order. Its cost is the sum of the
completion times. The order-independent pair expression is the diagonal sum
plus one minimum for every unordered pair.

The proof does not assume that job lengths are distinct.
-/

namespace SchedulingPaper

/-- Sum of completion times for jobs executed as contiguous blocks in the
given order. The recursive coefficient says that the first block contributes
to every job's completion time. -/
def prefixCost : List ℝ → ℝ
  | [] => 0
  | x :: xs => (xs.length + 1 : ℝ) * x + prefixCost xs

/-- The actual list of nonempty prefix sums (the jobs' completion times). -/
def completionTimes (xs : List ℝ) : List ℝ :=
  xs.inits.tail.map List.sum

/-- For every pair of positions, charge the earlier job's length. -/
def orderedPairCost : List ℝ → ℝ
  | [] => 0
  | x :: xs => (xs.length : ℝ) * x + orderedPairCost xs

/-- For every unordered pair of jobs, charge the shorter length. -/
def pairMinCost : List ℝ → ℝ
  | [] => 0
  | x :: xs => (xs.map (min x)).sum + pairMinCost xs

/-- The full diagonal-plus-unordered-pairs expression from the paper. -/
def pairCost (xs : List ℝ) : ℝ := xs.sum + pairMinCost xs

@[simp] theorem prefixCost_nil : prefixCost [] = 0 := rfl

@[simp] theorem prefixCost_cons (x : ℝ) (xs : List ℝ) :
    prefixCost (x :: xs) = (xs.length + 1 : ℝ) * x + prefixCost xs := rfl

@[simp] theorem completionTimes_nil : completionTimes [] = [] := rfl

@[simp] theorem orderedPairCost_nil : orderedPairCost [] = 0 := rfl

@[simp] theorem orderedPairCost_cons (x : ℝ) (xs : List ℝ) :
    orderedPairCost (x :: xs) = (xs.length : ℝ) * x + orderedPairCost xs := rfl

@[simp] theorem pairMinCost_nil : pairMinCost [] = 0 := rfl

@[simp] theorem pairMinCost_cons (x : ℝ) (xs : List ℝ) :
    pairMinCost (x :: xs) = (xs.map (min x)).sum + pairMinCost xs := rfl

@[simp] theorem pairCost_nil : pairCost [] = 0 := by simp [pairCost]

/-- The recursive objective really is the sum of all nonempty prefix sums. -/
theorem prefixCost_eq_sum_prefixes (xs : List ℝ) :
    prefixCost xs = (xs.inits.tail.map List.sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [prefixCost_cons, List.inits_cons]
      simp only [List.tail_cons, List.map_map]
      change (xs.length + 1 : ℝ) * x + prefixCost xs =
        (xs.inits.map fun t => x + t.sum).sum
      have hzero : (xs.inits.map List.sum).sum =
          (xs.inits.tail.map List.sum).sum := by
        cases xs <;> simp
      rw [ih, ← hzero, List.sum_map_add]
      rw [List.map_const', List.sum_replicate, nsmul_eq_mul, List.length_inits]
      push_cast
      ring

theorem prefixCost_eq_sum_completionTimes (xs : List ℝ) :
    prefixCost xs = (completionTimes xs).sum := by
  exact prefixCost_eq_sum_prefixes xs

/-- Diagonal-plus-ordered-pairs identity for an arbitrary order. -/
theorem prefixCost_eq_sum_add_orderedPairCost (xs : List ℝ) :
    prefixCost xs = xs.sum + orderedPairCost xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [prefixCost_cons, List.sum_cons, orderedPairCost_cons, ih]
      ring

/-- Splitting a schedule into an initial block and a suffix. -/
theorem prefixCost_append (l r : List ℝ) :
    prefixCost (l ++ r) =
      prefixCost l + (r.length : ℝ) * l.sum + prefixCost r := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.cons_append, prefixCost_cons, List.length_append, List.sum_cons, ih]
      push_cast
      ring

/-- Exact effect of interchanging two adjacent jobs. -/
theorem prefixCost_adjacent_swap_eq (l r : List ℝ) (a b : ℝ) :
    prefixCost (l ++ a :: b :: r) - prefixCost (l ++ b :: a :: r) = a - b := by
  rw [prefixCost_append, prefixCost_append]
  simp only [List.length_cons, prefixCost_cons]
  push_cast
  ring

/-- Swapping an inversion cannot increase total completion time. -/
theorem prefixCost_adjacent_swap_le (l r : List ℝ) {a b : ℝ} (h : b ≤ a) :
    prefixCost (l ++ b :: a :: r) ≤ prefixCost (l ++ a :: b :: r) := by
  have hdiff := prefixCost_adjacent_swap_eq l r a b
  linarith

/-- The unordered-pair expression is invariant under reordering. -/
theorem pairMinCost_perm {xs ys : List ℝ} (h : xs.Perm ys) :
    pairMinCost xs = pairMinCost ys := by
  induction h with
  | nil => rfl
  | cons x h ih =>
      simp only [pairMinCost_cons]
      rw [ih]
      congr 1
      exact (h.map (min x)).sum_eq
  | swap x y l =>
      simp only [pairMinCost_cons, List.map_cons, List.sum_cons]
      rw [min_comm x y]
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pairCost_perm {xs ys : List ℝ} (h : xs.Perm ys) :
    pairCost xs = pairCost ys := by
  unfold pairCost
  rw [h.sum_eq, pairMinCost_perm h]

/-- Any order pays at least the sum of diagonals and unordered pair minima. -/
theorem pairCost_le_prefixCost (xs : List ℝ) :
    pairCost xs ≤ prefixCost xs := by
  unfold pairCost
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [prefixCost_eq_sum_add_orderedPairCost]
      simp only [List.sum_cons, pairMinCost_cons, orderedPairCost_cons]
      have hmin : (xs.map (min x)).sum ≤ (xs.length : ℝ) * x := by
        calc
          (xs.map (min x)).sum ≤ (xs.map fun _ => x).sum := by
            exact List.sum_le_sum fun y hy => min_le_left x y
          _ = (xs.length : ℝ) * x := by simp
      have ih' : xs.sum + pairMinCost xs ≤
          xs.sum + orderedPairCost xs := by
        rw [← prefixCost_eq_sum_add_orderedPairCost]
        exact ih
      linarith

/-- On a nondecreasing list, every earlier member is the minimum of its pair. -/
theorem prefixCost_eq_pairCost_of_pairwise
    {xs : List ℝ} (hs : xs.Pairwise (· ≤ ·)) :
    prefixCost xs = pairCost xs := by
  unfold pairCost
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [prefixCost_eq_sum_add_orderedPairCost]
      simp only [List.sum_cons, orderedPairCost_cons, pairMinCost_cons]
      have hsHead : ∀ y ∈ xs, x ≤ y := (List.pairwise_cons.mp hs).1
      have hmap : xs.map (min x) = xs.map fun _ => x := by
        apply List.map_congr_left
        intro y hy
        exact min_eq_left (hsHead y hy)
      rw [hmap]
      rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
      have ih' := ih hs.tail
      rw [prefixCost_eq_sum_add_orderedPairCost] at ih'
      linarith

/-- Smith/SPT rule: every nondecreasing permutation minimizes prefix cost. -/
theorem pairwise_prefixCost_minimal
    {sorted candidate : List ℝ}
    (hs : sorted.Pairwise (· ≤ ·)) (hp : sorted.Perm candidate) :
    prefixCost sorted ≤ prefixCost candidate := by
  rw [prefixCost_eq_pairCost_of_pairwise hs]
  rw [pairCost_perm hp]
  exact pairCost_le_prefixCost candidate

noncomputable section

/-- Canonical shortest-processing-time schedule. -/
def shortestFirst (xs : List ℝ) : List ℝ := xs.insertionSort (· ≤ ·)

theorem shortestFirst_perm (xs : List ℝ) : (shortestFirst xs).Perm xs :=
  List.perm_insertionSort (· ≤ ·) xs

@[simp] theorem length_shortestFirst (xs : List ℝ) :
    (shortestFirst xs).length = xs.length :=
  (shortestFirst_perm xs).length_eq

theorem shortestFirst_pairwise (xs : List ℝ) :
    (shortestFirst xs).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort (· ≤ ·) xs

/-- Formal version of the offline-order assertion in Lemma 3.1. -/
theorem shortestFirst_optimal {xs ys : List ℝ} (hperm : ys.Perm xs) :
    prefixCost (shortestFirst xs) ≤ prefixCost ys := by
  apply pairwise_prefixCost_minimal (shortestFirst_pairwise xs)
  exact (shortestFirst_perm xs).trans hperm.symm

/-- Formal version of the paper's pair formula for the offline optimum. -/
theorem shortestFirst_pair_formula (xs : List ℝ) :
    prefixCost (shortestFirst xs) = pairCost xs := by
  rw [prefixCost_eq_pairCost_of_pairwise (shortestFirst_pairwise xs)]
  exact pairCost_perm (shortestFirst_perm xs)

end

end SchedulingPaper
