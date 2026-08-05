import SchedulingPaper.OfflineOptimal

/-!
# Application to uniform testing instances

This file instantiates the abstract shortest-processing-time result with the
paper's clairvoyant effective lengths.  It gives the ordering and pair
formulas of Lemma 3.1 and the quadratic lower bounds (3.6) and (3.7).
-/

namespace SchedulingPaper

noncomputable section

/-- Effective lengths of the labelled jobs, before choosing a schedule. -/
def Instance.effectiveLengths (I : Instance) : List ℝ :=
  I.jobs.map fun job => effectiveLength I.cap job.processingTime

/-- The value achieved by the clairvoyant shortest-processing-time schedule. -/
def offlineValue (I : Instance) : ℝ :=
  prefixCost (shortestFirst I.effectiveLengths)

/-- Every job's effective length is nonnegative. -/
theorem Instance.effectiveLengths_nonneg (I : Instance) :
    ∀ q ∈ I.effectiveLengths, 0 ≤ q := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨job, _hj, rfl⟩
  exact effectiveLength_nonneg I.cap I.cap_valid
    job.processingTime job.processingTime_nonneg

/-- The shortest-processing-time schedule is optimal among all schedules
with the same multiset of effective job lengths. -/
theorem offlineValue_minimal (I : Instance) {schedule : List ℝ}
    (hperm : schedule.Perm I.effectiveLengths) :
    offlineValue I ≤ prefixCost schedule := by
  exact shortestFirst_optimal hperm

/-- The prefix-sum form of the offline optimum (paper equation (3.2)). -/
theorem offlineValue_prefix_formula (I : Instance) :
    offlineValue I =
      ((shortestFirst I.effectiveLengths).inits.tail.map List.sum).sum := by
  exact prefixCost_eq_sum_prefixes _

/-- The diagonal-plus-pairs form of the offline optimum (paper equation
(3.3)).  `pairMinCost` recursively enumerates each unordered pair once. -/
theorem offlineValue_pair_formula (I : Instance) :
    offlineValue I = I.effectiveLengths.sum + pairMinCost I.effectiveLengths := by
  exact shortestFirst_pair_formula I.effectiveLengths

/-- The real triangular number `n(n+1)/2`. -/
def triangular (n : ℕ) : ℝ := (n : ℝ) * (n + 1) / 2

@[simp] theorem triangular_zero : triangular 0 = 0 := by simp [triangular]

theorem triangular_succ (n : ℕ) :
    triangular (n + 1) = (n + 1 : ℕ) + triangular n := by
  unfold triangular
  push_cast
  ring

/-- Closed form for `n` equal-length jobs. -/
theorem prefixCost_replicate (n : ℕ) (x : ℝ) :
    prefixCost (List.replicate n x) = x * triangular n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, prefixCost_cons, List.length_replicate,
        ih, triangular_succ]
      push_cast
      ring

/-- If every block has length at least `a`, every order has total
completion time at least `a n(n+1)/2`. -/
theorem prefixCost_quadratic_lower {a : ℝ}
    (xs : List ℝ) (hxs : ∀ x ∈ xs, a ≤ x) :
    a * triangular xs.length ≤ prefixCost xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : a ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, a ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      have hcoeff : 0 ≤ (xs.length + 1 : ℝ) := by positivity
      calc
        a * triangular (x :: xs).length =
            (xs.length + 1 : ℝ) * a + a * triangular xs.length := by
              simp only [List.length_cons, triangular_succ]
              push_cast
              ring
        _ ≤ (xs.length + 1 : ℝ) * x + prefixCost xs := by
              exact add_le_add (mul_le_mul_of_nonneg_left hx hcoeff) (ih htail)
        _ = prefixCost (x :: xs) := by rw [prefixCost_cons]

/-- All effective lengths have the common lower bound used in the paper. -/
theorem Instance.baseLength_le_effectiveLengths (I : Instance) :
    ∀ q ∈ I.effectiveLengths, I.cap.baseLength ≤ q := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨job, _hj, rfl⟩
  exact baseLength_le_effectiveLength I.cap
    job.processingTime job.processingTime_nonneg

/-- Unified quadratic lower bound on the offline optimum. -/
theorem offlineValue_quadratic_lower (I : Instance) :
    I.cap.baseLength * triangular I.jobs.length ≤ offlineValue I := by
  have hq : ∀ q ∈ shortestFirst I.effectiveLengths, I.cap.baseLength ≤ q := by
    intro q hq
    exact I.baseLength_le_effectiveLengths q
      ((shortestFirst_perm I.effectiveLengths).mem_iff.mp hq)
  have hbound := prefixCost_quadratic_lower
    (a := I.cap.baseLength) (shortestFirst I.effectiveLengths) hq
  simpa [offlineValue, Instance.effectiveLengths] using hbound

/-- Equation (3.7): for a finite common cap `u`,
`OPT ≥ min u 1 · n(n+1)/2`. -/
theorem finite_offlineValue_quadratic_lower (I : Instance) (u : ℝ)
    (hcap : I.cap = .finite u) :
    min u 1 * triangular I.jobs.length ≤ offlineValue I := by
  simpa [hcap, Cap.baseLength] using offlineValue_quadratic_lower I

/-- Equation (3.6): at the obligatory endpoint,
`OPT ≥ n(n+1)/2`. -/
theorem obligatory_offlineValue_quadratic_lower (I : Instance)
    (hcap : I.cap = .infinite) :
    triangular I.jobs.length ≤ offlineValue I := by
  simpa [hcap, Cap.baseLength] using offlineValue_quadratic_lower I

end

end SchedulingPaper
