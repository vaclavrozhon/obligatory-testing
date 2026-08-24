import SchedulingPaper.RevealingOptimizationQuotaStrategy
import SchedulingPaper.RandomizedOptionalFiniteKernel
import Mathlib.Tactic

/-!
# Finite position kernel for revealing-optimization quota policies

This is the exact diagonal-and-pair cost of the canonical quota operation
word.  It keeps the finite without-replacement placement separate from the
fluid template in `RevealingOptimizationInstanceLearning`.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace QuotaKernel

open Randomized
open RandomizedOptional
open InstanceLearning

noncomputable section

/-- Charge of two tested jobs when `p` is discovered before `q`.  A low
first job completes before the second test; a low second job has already
waited through the first test; otherwise the residual pair is drained SPT. -/
def testedPairChargeOrdered
    (firstLow secondLow : Bool) (p q : ℝ) : ℝ :=
  if firstLow then 1 + p
  else if secondLow then 2 + q
  else 2 + min p q

theorem testedPairChargeOrdered_symmetrized
    (leftLow rightLow : Bool) (p q : ℝ) :
    (testedPairChargeOrdered leftLow rightLow p q +
        testedPairChargeOrdered rightLow leftLow q p) / 2 =
      testedPairChargeFlags leftLow rightLow p q := by
  cases leftLow <;> cases rightLow <;>
    simp [testedPairChargeOrdered, testedPairChargeFlags, min_comm] <;> ring

theorem testedPairChargeOrdered_nonneg
    {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (firstLow secondLow : Bool) :
    0 ≤ testedPairChargeOrdered firstLow secondLow p q := by
  cases firstLow <;> cases secondLow <;>
    simp [testedPairChargeOrdered] <;>
    have hmin : 0 ≤ min p q := le_min hp0 hq0 <;> linarith

theorem testedPairChargeOrdered_le
    {u p q : ℝ} (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u)
    (firstLow secondLow : Bool) :
    testedPairChargeOrdered firstLow secondLow p q ≤ u + 2 := by
  cases firstLow <;> cases secondLow <;>
    simp [testedPairChargeOrdered] <;>
    have hmin := min_le_left p q <;> linarith

/-- Symmetric unordered-pair charge at two fixed virtual positions. -/
def quotaPairCharge
    {n : ℕ} (q : ℕ) (u : ℝ) (low : ℝ → Bool)
    (i j : Fin n) (p r : ℝ) : ℝ :=
  if i.val < q then
    if j.val < q then
      if i.val < j.val then
        testedPairChargeOrdered (low p) (low r) p r
      else testedPairChargeOrdered (low r) (low p) r p
    else 1 + p
  else if j.val < q then 1 + r else u

theorem quotaPairCharge_comm
    {n q : ℕ} (u : ℝ) (low : ℝ → Bool)
    {i j : Fin n} (hij : i ≠ j) (p r : ℝ) :
    quotaPairCharge q u low i j p r =
      quotaPairCharge q u low j i r p := by
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · by_cases hi : i.val < q <;> by_cases hj : j.val < q <;>
      simp [quotaPairCharge, hi, hj, hlt, not_lt_of_ge hlt.le]
  · by_cases hi : i.val < q <;> by_cases hj : j.val < q <;>
      simp [quotaPairCharge, hi, hj, hgt, not_lt_of_ge hgt.le]

theorem quotaPairCharge_nonneg
    {n q : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (low : ℝ → Bool) (i j : Fin n) {p r : ℝ}
    (hp0 : 0 ≤ p) (hr0 : 0 ≤ r) :
    0 ≤ quotaPairCharge q u low i j p r := by
  unfold quotaPairCharge
  split <;> split <;> try split
  all_goals first
    | exact testedPairChargeOrdered_nonneg hp0 hr0 _ _
    | exact testedPairChargeOrdered_nonneg hr0 hp0 _ _
    | linarith

theorem quotaPairCharge_le
    {n q : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (low : ℝ → Bool) (i j : Fin n) {p r : ℝ}
    (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hr0 : 0 ≤ r) (hru : r ≤ u) :
    quotaPairCharge q u low i j p r ≤ u + 2 := by
  unfold quotaPairCharge
  split <;> split <;> try split
  all_goals first
    | exact testedPairChargeOrdered_le hp0 hpu hr0 hru _ _
    | exact testedPairChargeOrdered_le hr0 hru hp0 hpu _ _
    | linarith

/-- Diagonal charge of the job occupying a virtual position. -/
def quotaSingleKernel
    {n : ℕ} (q : ℕ) (u : ℝ) (processing : Fin n → ℝ)
    (i actual : Fin n) : ℝ :=
  if i.val < q then 1 + processing actual else u

/-- Half of the symmetric pair charge; summing over ordered distinct
positions therefore counts every unordered interaction once. -/
def quotaPairKernel
    {n : ℕ} (q : ℕ) (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) (z : OrderedDistinct (Fin n))
    (left right : Fin n) : ℝ :=
  quotaPairCharge q u low z.val.1 z.val.2
    (processing left) (processing right) / 2

def quotaKernelCost
    {n : ℕ} (q : ℕ) (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) (order : Equiv.Perm (Fin n)) : ℝ :=
  positionKernelCost (quotaSingleKernel q u processing)
    (quotaPairKernel q u processing low) order

theorem abs_quotaPairKernel_le
    {n q : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) (z : OrderedDistinct (Fin n))
    (left right : Fin n) :
    |quotaPairKernel q u processing low z left right| ≤ (u + 2) / 2 := by
  have hnonneg := quotaPairCharge_nonneg (q := q) hu0 low z.val.1 z.val.2
    (hp0 left) (hp0 right)
  have hupper := quotaPairCharge_le (q := q) hu0 low z.val.1 z.val.2
    (hp0 left) (hpu left) (hp0 right) (hpu right)
  unfold quotaPairKernel
  rw [abs_of_nonneg (div_nonneg hnonneg (by norm_num))]
  exact div_le_div_of_nonneg_right hupper (by norm_num)

/-- Random relabeling may be replaced by independent empirical draws in the
finite position kernel with a uniform normalized `O((u+1)/n)` loss. -/
theorem quotaKernelCost_product_normalized
    {n q : ℕ} (hn : 1 < n) (u : ℝ) (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u)
    (low : ℝ → Bool) :
    |uniformAverage (quotaKernelCost q u processing low) / (n : ℝ) ^ 2 -
        positionKernelProductValue (quotaSingleKernel q u processing)
          (quotaPairKernel q u processing low) / (n : ℝ) ^ 2| ≤
      (u + 2) / n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hB0 : 0 ≤ (u + 2) / 2 := by linarith
  have hreplace := positionKernel_product_replacement_normalized_with_single
    (by simpa using hn) (quotaSingleKernel q u processing)
      (quotaPairKernel q u processing low) hB0
      (abs_quotaPairKernel_le hu0 processing hp0 hpu low)
  calc
    |uniformAverage (quotaKernelCost q u processing low) / (n : ℝ) ^ 2 -
        positionKernelProductValue (quotaSingleKernel q u processing)
          (quotaPairKernel q u processing low) / (n : ℝ) ^ 2| ≤
        2 * ((u + 2) / 2) / n := by
          simpa [quotaKernelCost] using hreplace
    _ = (u + 2) / n := by ring

end

end QuotaKernel
end RevealingOptimization
end SchedulingPaper
