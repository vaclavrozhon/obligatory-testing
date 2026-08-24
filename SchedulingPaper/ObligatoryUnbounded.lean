import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Unbounded obligatory-testing instance optimality is impossible

This is the finite private-seed averaging argument from part (ii) of the
obligatory-testing impossibility theorem.  On the all-`H` execution,
`completedBefore seed rank` records how many jobs have completed before the
test of rank `rank`.  Either the accumulated all-`H` delay is already
quadratic, or a uniformly chosen exceptional zero is forced behind many
length-`H` completions.  Averaging then fixes one oblivious zero label.
-/

namespace SchedulingPaper
namespace ObligatoryUnbounded

noncomputable section

open SchedulingPaper.Randomized

def rankValue {n : ℕ} (rank : Fin n) : ℝ := rank.val

def rankGap {n : ℕ} (completedBefore : Fin n → ℕ)
    (rank : Fin n) : ℝ :=
  rankValue rank - completedBefore rank

def allHighExcess {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (completedBefore : Ω → Fin n → ℕ) : ℝ :=
  uniformAverage fun seed ↦
    ∑ rank, rankGap (completedBefore seed) rank

def exceptionalZeroCharge {n : ℕ}
    (order : Equiv.Perm (Fin n)) (completedBefore : Fin n → ℕ)
    (H : ℝ) (label : Fin n) : ℝ :=
  H * completedBefore (order.symm label)

@[simp] theorem rankValue_zero (n : ℕ) :
    rankValue (0 : Fin (n + 1)) = 0 := by simp [rankValue]

@[simp] theorem rankValue_succ {n : ℕ} (rank : Fin n) :
    rankValue rank.succ = rankValue rank + 1 := by simp [rankValue]

@[simp] theorem sum_rankValues (n : ℕ) :
    (∑ rank : Fin n, rankValue rank) = (n : ℝ) * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [rankValue_zero, zero_add, rankValue_succ,
        Finset.sum_add_distrib, ih]
      simp
      push_cast
      ring

theorem exceptionalZeroCharge_sum_labels {n : ℕ}
    (order : Equiv.Perm (Fin n)) (completedBefore : Fin n → ℕ)
    (H : ℝ) :
    (∑ label, exceptionalZeroCharge order completedBefore H label) =
      H * ∑ rank, (completedBefore rank : ℝ) := by
  unfold exceptionalZeroCharge
  rw [← Finset.mul_sum]
  have hperm := Equiv.sum_comp order.symm
    (fun rank : Fin n ↦ (completedBefore rank : ℝ))
  exact congrArg (fun x : ℝ ↦ H * x) hperm

theorem uniformAverage_exceptionalZeroCharge_sum_labels
    {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (completedBefore : Ω → Fin n → ℕ) (H : ℝ) :
    (∑ label, uniformAverage (fun seed ↦
        exceptionalZeroCharge (order seed) (completedBefore seed) H label)) =
      H * uniformAverage (fun seed ↦
        ∑ rank, (completedBefore seed rank : ℝ)) := by
  rw [← uniformAverage_fintype_sum, ← uniformAverage_smul]
  unfold uniformAverage
  congr 1
  apply Finset.sum_congr rfl
  intro seed hseed
  exact exceptionalZeroCharge_sum_labels
    (order seed) (completedBefore seed) H

theorem allHighExcess_add_completed
    {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (completedBefore : Ω → Fin n → ℕ) :
    allHighExcess completedBefore +
        uniformAverage (fun seed ↦
          ∑ rank, (completedBefore seed rank : ℝ)) =
      (n : ℝ) * (n - 1) / 2 := by
  unfold allHighExcess
  rw [← uniformAverage_add]
  calc
    uniformAverage (fun seed ↦
        (∑ rank, rankGap (completedBefore seed) rank) +
          ∑ rank, (completedBefore seed rank : ℝ)) =
        uniformAverage (fun _ : Ω ↦ ∑ rank : Fin n, rankValue rank) := by
      unfold uniformAverage
      congr 1
      apply Finset.sum_congr rfl
      intro seed hseed
      dsimp only
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro rank hrank
      simp [rankGap]
    _ = ∑ rank : Fin n, rankValue rank := uniformAverage_const _
    _ = (n : ℝ) * (n - 1) / 2 := sum_rankValues n

/-- Exact finite dichotomy in the unbounded OT lower bound.  `oneZeroGap`
is the online cost minus the announced comparison-policy cost on the input
with one exceptional zero.  The `n²` subtraction is the comparison policy's
worst possible displacement of its unit tests. -/
theorem allHigh_or_exists_oblivious_zero
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (completedBefore : Ω → Fin n → ℕ)
    (H : ℝ) (oneZeroGap : Fin n → ℝ)
    (hH : 0 < H)
    (hone : ∀ label,
      uniformAverage (fun seed ↦ exceptionalZeroCharge (order seed)
          (completedBefore seed) H label) - n ^ 2 ≤ oneZeroGap label) :
    (n : ℝ) ^ 2 / 8 ≤ allHighExcess completedBefore ∨
      ∃ label, H * ((n - 1 : ℝ) / 2 - n / 8) - n ^ 2 <
        oneZeroGap label := by
  by_cases hhigh : (n : ℝ) ^ 2 / 8 ≤ allHighExcess completedBefore
  · exact Or.inl hhigh
  · right
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hcompleted :
        (n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8 <
          uniformAverage (fun seed ↦
            ∑ rank, (completedBefore seed rank : ℝ)) := by
      have hidentity := allHighExcess_add_completed completedBefore
      linarith
    have hsumCharge :
        H * ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) <
          ∑ label, uniformAverage (fun seed ↦
            exceptionalZeroCharge (order seed) (completedBefore seed)
              H label) := by
      rw [uniformAverage_exceptionalZeroCharge_sum_labels]
      exact mul_lt_mul_of_pos_left hcompleted hH
    have hsumGap :
        H * ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) -
            (n : ℝ) * n ^ 2 < ∑ label, oneZeroGap label := by
      have honeSum :
          (∑ label : Fin n,
              (uniformAverage (fun seed ↦ exceptionalZeroCharge
                (order seed) (completedBefore seed) H label) - n ^ 2)) ≤
            ∑ label : Fin n, oneZeroGap label :=
        Finset.sum_le_sum fun label hlabel ↦ hone label
      have hrewrite :
          (∑ label : Fin n,
              (uniformAverage (fun seed ↦ exceptionalZeroCharge
                (order seed) (completedBefore seed) H label) - n ^ 2)) =
            (∑ label, uniformAverage (fun seed ↦ exceptionalZeroCharge
                (order seed) (completedBefore seed) H label)) -
              (n : ℝ) * n ^ 2 := by simp [Finset.sum_sub_distrib]
      rw [hrewrite] at honeSum
      linarith
    by_contra hexists
    push_neg at hexists
    have hsumUpper :
        (∑ label, oneZeroGap label) ≤
          ∑ _label : Fin n,
            (H * ((n - 1 : ℝ) / 2 - n / 8) - n ^ 2) :=
      Finset.sum_le_sum fun label hlabel ↦ hexists label
    have htarget :
        (∑ _label : Fin n,
            (H * ((n - 1 : ℝ) / 2 - n / 8) - n ^ 2)) =
          H * ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) -
            (n : ℝ) * n ^ 2 := by
      simp
      ring
    rw [htarget] at hsumUpper
    linarith

/-- At `H=n²`, one of the two fixed oblivious instances beats its announced
comparison policy by at least `n²/8` for every `n≥5`. -/
theorem exists_quadratic_instance_gap
    {n : ℕ} (hn : 5 ≤ n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (completedBefore : Ω → Fin n → ℕ)
    (oneZeroGap : Fin n → ℝ)
    (hone : ∀ label,
      uniformAverage (fun seed ↦ exceptionalZeroCharge (order seed)
          (completedBefore seed) ((n : ℝ) ^ 2) label) - n ^ 2 ≤
        oneZeroGap label) :
    (n : ℝ) ^ 2 / 8 ≤ allHighExcess completedBefore ∨
      ∃ label, (n : ℝ) ^ 2 / 8 < oneZeroGap label := by
  have hnpos : 0 < n := by omega
  rcases allHigh_or_exists_oblivious_zero hnpos order completedBefore
      ((n : ℝ) ^ 2) oneZeroGap (sq_pos_of_pos (by exact_mod_cast hnpos)) hone
      with hhigh | ⟨label, hlabel⟩
  · exact Or.inl hhigh
  · right
    refine ⟨label, ?_⟩
    have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hscale :
        (n : ℝ) ^ 2 / 8 ≤
          (n : ℝ) ^ 2 * ((n - 1 : ℝ) / 2 - n / 8) - n ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 5), sq_nonneg (n : ℝ)]
    exact lt_of_le_of_lt hscale hlabel

end

end ObligatoryUnbounded
end SchedulingPaper
