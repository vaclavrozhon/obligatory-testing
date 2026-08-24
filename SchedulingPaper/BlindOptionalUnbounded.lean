import SchedulingPaper.RandomizedOptionalOnline
import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# The unbounded blind-execution obstruction

This file formalizes the finite averaging argument behind the theorem that
blind execution admits no finite competitive ratio on unbounded inputs.
For each private seed, `order` is the first-touch permutation on the all-zero
input and `tested` records the mode of that first touch.  The two hypotheses
of the main theorem are exactly the two operational charging inequalities:

* a tested zero at rank `h` charges every job not touched yet;
* if the label at rank `h` is made exceptionally long and was touched
  blindly, its nonpreemptive execution charges the same unfinished suffix.

The conclusion chooses one fixed (oblivious) exceptional label after
averaging over labels and private seeds.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace Unbounded

noncomputable section

open SchedulingPaper.Randomized

/-- Number of jobs not yet first-touched at a zero-indexed rank. -/
def rankWeight (n : ℕ) (rank : Fin n) : ℝ :=
  (n : ℝ) - (rank.val : ℝ)

/-- Area paid by first touches that test on the all-zero input. -/
def testedArea {n : ℕ} (tested : Fin n → Bool) : ℝ :=
  ∑ rank, if tested rank then rankWeight n rank else 0

/-- Area exposed by first touches that execute blindly. -/
def blindArea {n : ℕ} (tested : Fin n → Bool) : ℝ :=
  ∑ rank, if tested rank then 0 else rankWeight n rank

/-- Charge caused by making one physical label long.  The first-touch
permutation is written from ranks to labels. -/
def exceptionalCharge {n : ℕ}
    (order : Equiv.Perm (Fin n)) (tested : Fin n → Bool)
    (H : ℝ) (label : Fin n) : ℝ :=
  H * if tested (order.symm label) then 0
    else rankWeight n (order.symm label)

theorem rankWeight_nonneg {n : ℕ} (rank : Fin n) :
    0 ≤ rankWeight n rank := by
  simp only [rankWeight, sub_nonneg]
  exact_mod_cast Nat.le_of_lt rank.isLt

@[simp] theorem rankWeight_succ_zero (n : ℕ) :
    rankWeight (n + 1) 0 = n + 1 := by
  simp [rankWeight]

@[simp] theorem rankWeight_succ_succ (n : ℕ) (rank : Fin n) :
    rankWeight (n + 1) rank.succ = rankWeight n rank := by
  simp [rankWeight]

theorem sum_rankWeight (n : ℕ) :
    (∑ rank : Fin n, rankWeight n rank) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [rankWeight_succ_zero, rankWeight_succ_succ, ih]
      push_cast
      ring

theorem testedArea_add_blindArea {n : ℕ} (tested : Fin n → Bool) :
    testedArea tested + blindArea tested = ∑ rank, rankWeight n rank := by
  unfold testedArea blindArea
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rank hrank
  cases h : tested rank <;>
    simp [testedArea, blindArea, h]

theorem exceptionalCharge_sum_labels {n : ℕ}
    (order : Equiv.Perm (Fin n)) (tested : Fin n → Bool) (H : ℝ) :
    (∑ label, exceptionalCharge order tested H label) =
      H * blindArea tested := by
  unfold exceptionalCharge blindArea
  rw [← Finset.mul_sum]
  have hperm := Equiv.sum_comp order.symm
    (fun rank : Fin n ↦ if tested rank then 0 else rankWeight n rank)
  exact congrArg (fun x : ℝ ↦ H * x) hperm

theorem uniformAverage_exceptionalCharge_sum_labels
    {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool) (H : ℝ) :
    (∑ label, uniformAverage (fun seed ↦
        exceptionalCharge (order seed) (tested seed) H label)) =
      H * uniformAverage (fun seed ↦ blindArea (tested seed)) := by
  rw [← uniformAverage_fintype_sum]
  rw [← uniformAverage_smul]
  unfold uniformAverage
  congr 1
  apply Finset.sum_congr rfl
  intro seed hseed
  exact exceptionalCharge_sum_labels (order seed) (tested seed) H

/-- Finite, quantitative form of the one-long-job adversary.  `zeroCost`
is the expected cost on the all-zero vector and `longCost label` is the
expected cost after only `label` is changed to length `H`. -/
theorem exists_oblivious_long_label
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool)
    (H zeroCost : ℝ) (longCost : Fin n → ℝ)
    (hH : 0 ≤ H)
    (hzero : uniformAverage (fun seed ↦ testedArea (tested seed)) ≤ zeroCost)
    (hlong : ∀ label,
      uniformAverage (fun seed ↦
          exceptionalCharge (order seed) (tested seed) H label) ≤
        longCost label) :
    ∃ label, H / n * ((n : ℝ) * (n + 1) / 2 - zeroCost) ≤
      longCost label := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let target := H / n * ((n : ℝ) * (n + 1) / 2 - zeroCost)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hblind :
      (n : ℝ) * (n + 1) / 2 - zeroCost ≤
        uniformAverage (fun seed ↦ blindArea (tested seed)) := by
    have hpartition :
        uniformAverage (fun seed ↦ testedArea (tested seed)) +
          uniformAverage (fun seed ↦ blindArea (tested seed)) =
            (n : ℝ) * (n + 1) / 2 := by
      rw [← uniformAverage_add]
      calc
        uniformAverage (fun seed ↦
            testedArea (tested seed) + blindArea (tested seed)) =
            uniformAverage (fun _ : Ω ↦ ∑ rank, rankWeight n rank) := by
              unfold uniformAverage
              congr 1
              apply Finset.sum_congr rfl
              intro seed hseed
              exact testedArea_add_blindArea (tested seed)
        _ = ∑ rank, rankWeight n rank := uniformAverage_const _
        _ = (n : ℝ) * (n + 1) / 2 := sum_rankWeight n
    linarith
  have hsumLower :
      (n : ℝ) * target ≤ ∑ label, longCost label := by
    have hcharges :
        H * uniformAverage (fun seed ↦ blindArea (tested seed)) ≤
          ∑ label, longCost label := by
      rw [← uniformAverage_exceptionalCharge_sum_labels order tested H]
      exact Finset.sum_le_sum fun label hlabel ↦ hlong label
    have htarget :
        (n : ℝ) * target =
          H * ((n : ℝ) * (n + 1) / 2 - zeroCost) := by
      dsimp [target]
      field_simp
    rw [htarget]
    exact (mul_le_mul_of_nonneg_left hblind hH).trans hcharges
  by_contra hexists
  push_neg at hexists
  have hsumUpper : (∑ label, longCost label) < (n : ℝ) * target := by
    calc
      (∑ label, longCost label) < ∑ _label : Fin n, target :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun label hlabel ↦ hexists label)
      _ = (n : ℝ) * target := by simp
  linarith

/-- If the all-zero expected cost is at most `η n²`, one fixed long label
forces the explicit lower bound used in the asymptotic contradiction. -/
theorem exists_oblivious_long_label_of_zero_bound
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool)
    (H η zeroCost : ℝ) (longCost : Fin n → ℝ)
    (hH : 0 ≤ H)
    (hzeroArea : uniformAverage (fun seed ↦ testedArea (tested seed)) ≤
      zeroCost)
    (hzeroCost : zeroCost ≤ η * n ^ 2)
    (hlong : ∀ label,
      uniformAverage (fun seed ↦
          exceptionalCharge (order seed) (tested seed) H label) ≤
        longCost label) :
    ∃ label, H * ((n + 1 : ℝ) / 2 - η * n) ≤ longCost label := by
  obtain ⟨label, hlabel⟩ := exists_oblivious_long_label hn order tested
    H zeroCost longCost hH hzeroArea hlong
  refine ⟨label, ?_⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    H * ((n + 1 : ℝ) / 2 - η * n) =
        H / n * ((n : ℝ) * (n + 1) / 2 - η * n ^ 2) := by
          field_simp
    _ ≤ H / n * ((n : ℝ) * (n + 1) / 2 - zeroCost) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hH (le_of_lt hnreal))
      linarith
    _ ≤ longCost label := hlabel

/-- A finite-scale contradiction to a putative competitive guarantee.  Once
`n` is larger than the fixed ratio and the zero-input error is at most
`n²/8`, the all-zero and one-`n²` inputs cannot both satisfy that guarantee.
This is the direct quantitative form of `thm:blind-unbounded-impossible`. -/
theorem no_finite_ratio_at_quadratic_scale
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool)
    (R η zeroCost : ℝ) (longCost : Fin n → ℝ)
    (hR : 0 ≤ R) (hη : η ≤ 1 / 8)
    (hnlarge : 8 * R + 1 < 3 * n)
    (hzeroArea : uniformAverage (fun seed ↦ testedArea (tested seed)) ≤
      zeroCost)
    (hzeroCost : zeroCost ≤ η * n ^ 2)
    (hlong : ∀ label,
      uniformAverage (fun seed ↦ exceptionalCharge (order seed)
        (tested seed) ((n : ℝ) ^ 2) label) ≤ longCost label)
    (hcompetitive : ∀ label,
      longCost label ≤ R * (n : ℝ) ^ 2 + η * n ^ 2) : False := by
  obtain ⟨label, hlower⟩ := exists_oblivious_long_label_of_zero_bound
    hn order tested ((n : ℝ) ^ 2) η zeroCost longCost (sq_nonneg _)
    hzeroArea hzeroCost hlong
  have hupper := hcompetitive label
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlargeReal : 8 * R + 1 < 3 * (n : ℝ) := by
    exact hnlarge
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
  have hcombined :
      (n : ℝ) ^ 2 * ((n + 1 : ℝ) / 2 - η * n) ≤
        R * (n : ℝ) ^ 2 + η * n ^ 2 := hlower.trans hupper
  have hcombined' :
      (n : ℝ) ^ 2 * ((n + 1 : ℝ) / 2 - η * n) ≤
        (n : ℝ) ^ 2 * (R + η) := by
    calc
      _ ≤ R * (n : ℝ) ^ 2 + η * n ^ 2 := hcombined
      _ = (n : ℝ) ^ 2 * (R + η) := by ring
  have hdivided :
      (n + 1 : ℝ) / 2 - η * n ≤ R + η :=
    le_of_mul_le_mul_left hcombined' hn2
  have hηscaled : η * (n : ℝ) ≤ (n : ℝ) / 8 :=
    by
      simpa [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right hη (le_of_lt hnreal)
  linarith

end

end Unbounded
end RandomizedOptional
end SchedulingPaper
