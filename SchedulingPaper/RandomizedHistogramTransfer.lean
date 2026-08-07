import SchedulingPaper.RandomizedHistogramConcentration
import SchedulingPaper.RandomizedThresholdClosure
import Mathlib.Tactic

/-!
# Transferring histogram error to a learned threshold

The `L¹` histogram error simultaneously controls the mass of every category
set and, when representatives are bounded by `B`, its rounded first moment.
These deterministic inequalities are what allow the threshold itself to be
chosen from the sample without a union bound over candidate prefixes.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

theorem selectedMass_sub_le_l1
    {β : Type*} [Fintype β]
    (μ μHat : β → ℝ) (selected : β → Prop) [DecidablePred selected] :
    |selectedMass μ selected - selectedMass μHat selected| ≤
      ∑ b, |μHat b - μ b| := by
  unfold selectedMass
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ b, (μ b * (if selected b then 1 else 0) -
        μHat b * (if selected b then 1 else 0))| ≤
        ∑ b, |μ b * (if selected b then 1 else 0) -
          μHat b * (if selected b then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |μHat b - μ b| := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : selected b
      · simp [hb, abs_sub_comm]
      · simp [hb]

theorem selectedMoment_sub_le_B_mul_l1
    {β : Type*} [Fintype β]
    {B : ℝ} (μ μHat q : β → ℝ)
    (selected : β → Prop) [DecidablePred selected]
    (hB : 0 ≤ B) (hq0 : ∀ b, 0 ≤ q b)
    (hqB : ∀ b, selected b → q b ≤ B) :
    |selectedMoment μ q selected - selectedMoment μHat q selected| ≤
      B * ∑ b, |μHat b - μ b| := by
  unfold selectedMoment
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ b, (μ b * q b * (if selected b then 1 else 0) -
        μHat b * q b * (if selected b then 1 else 0))| ≤
        ∑ b, |μ b * q b * (if selected b then 1 else 0) -
          μHat b * q b * (if selected b then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, B * |μHat b - μ b| := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : selected b
      · simp only [if_pos hb, mul_one]
        rw [show μ b * q b - μHat b * q b =
            (μ b - μHat b) * q b by ring,
          abs_mul, abs_of_nonneg (hq0 b), abs_sub_comm]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_right (hqB b hb) (abs_nonneg (μHat b - μ b)))
      · simp [hb, mul_nonneg hB (abs_nonneg _)]
    _ = B * ∑ b, |μHat b - μ b| := by
      rw [Finset.mul_sum]

/-- Category form of the mass-transfer estimate used in the proof. -/
theorem selectedMass_population_sample_le_histogramL1Error
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (c : α → β) (σ : Equiv.Perm α)
    (selected : β → Prop) [DecidablePred selected] :
    |selectedMass
        (fun b => ((categoryClass c b).card : ℝ) / Fintype.card α)
        selected -
      selectedMass
        (fun b => sampleCategoryFraction S (categoryClass c b) σ)
        selected| ≤ histogramL1Error S c σ := by
  exact selectedMass_sub_le_l1 _ _ selected

/-- Category form of the bounded first-moment transfer estimate. -/
theorem selectedMoment_population_sample_le_histogramL1Error
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {B : ℝ} (S : Finset α) (c : α → β) (σ : Equiv.Perm α)
    (q : β → ℝ) (selected : β → Prop) [DecidablePred selected]
    (hB : 0 ≤ B) (hq0 : ∀ b, 0 ≤ q b)
    (hqB : ∀ b, selected b → q b ≤ B) :
    |selectedMoment
        (fun b => ((categoryClass c b).card : ℝ) / Fintype.card α)
        q selected -
      selectedMoment
        (fun b => sampleCategoryFraction S (categoryClass c b) σ)
        q selected| ≤ B * histogramL1Error S c σ := by
  exact selectedMoment_sub_le_B_mul_l1 _ _ q selected hB hq0 hqB

/-- Combining rounded-moment histogram error with a deterministic rounding
loss. -/
theorem selectedMoment_actual_sample_le
    {actual rounded sample Δ η B : ℝ}
    (hround : |actual - rounded| ≤ η)
    (hhist : |rounded - sample| ≤ B * Δ) :
    |actual - sample| ≤ B * Δ + η := by
  calc
    |actual - sample| = |(actual - rounded) + (rounded - sample)| := by ring_nf
    _ ≤ |actual - rounded| + |rounded - sample| := abs_add_le _ _
    _ ≤ η + B * Δ := add_le_add hround hhist
    _ = B * Δ + η := by ring

/-- Regrouping a rounded job sum by histogram category. -/
theorem sum_category_representative
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (c : α → β) (q : β → ℝ)
    (selected : β → Prop) [DecidablePred selected] :
    (∑ b, ((categoryClass c b).card : ℝ) * q b *
        (if selected b then 1 else 0)) =
      ∑ a, q (c a) * (if selected (c a) then 1 else 0) := by
  calc
    (∑ b, ((categoryClass c b).card : ℝ) * q b *
        (if selected b then 1 else 0)) =
      ∑ b, ∑ a ∈ categoryClass c b,
        q b * (if selected b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ = ∑ a, q (c a) * (if selected (c a) then 1 else 0) := by
      simp_rw [categoryClass, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp

/-- Population rounded moment equals the average rounded value over jobs. -/
theorem selectedMoment_population_eq_jobAverage
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (c : α → β) (q : β → ℝ)
    (selected : β → Prop) [DecidablePred selected] :
    selectedMoment
        (fun b => ((categoryClass c b).card : ℝ) / Fintype.card α)
        q selected =
      (∑ a, q (c a) * (if selected (c a) then 1 else 0)) /
        Fintype.card α := by
  unfold selectedMoment
  calc
    (∑ b, (((categoryClass c b).card : ℝ) / Fintype.card α) * q b *
        (if selected b then 1 else 0)) =
      (∑ b, ((categoryClass c b).card : ℝ) * q b *
        (if selected b then 1 else 0)) / Fintype.card α := by
      rw [show (fun b => (((categoryClass c b).card : ℝ) /
          Fintype.card α) * q b * (if selected b then 1 else 0)) =
        (fun b => (((categoryClass c b).card : ℝ) * q b *
          (if selected b then 1 else 0)) / Fintype.card α) by
            funext b
            ring]
      rw [Finset.sum_div]
    _ = (∑ a, q (c a) * (if selected (c a) then 1 else 0)) /
        Fintype.card α := by
      rw [sum_category_representative c q selected]

theorem selectedMass_population_eq_jobAverage
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (c : α → β) (selected : β → Prop) [DecidablePred selected] :
    selectedMass
        (fun b => ((categoryClass c b).card : ℝ) / Fintype.card α)
        selected =
      (∑ a, if selected (c a) then 1 else 0) / Fintype.card α := by
  have hmoment := selectedMoment_population_eq_jobAverage c
    (fun _b => (1 : ℝ)) selected
  unfold selectedMoment at hmoment
  unfold selectedMass
  simpa using hmoment

/-- If every selected job is rounded by at most `η`, the selected population
first moment changes by at most `η`. -/
theorem jobAverage_rounding_error_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    {η : ℝ} (p : α → ℝ) (c : α → β) (q : β → ℝ)
    (selected : β → Prop) [DecidablePred selected]
    (hη : 0 ≤ η)
    (hround : ∀ a, selected (c a) → |p a - q (c a)| ≤ η) :
    |(∑ a, p a * (if selected (c a) then 1 else 0)) /
          Fintype.card α -
        selectedMoment
          (fun b => ((categoryClass c b).card : ℝ) / Fintype.card α)
          q selected| ≤ η := by
  rw [selectedMoment_population_eq_jobAverage c q selected]
  have hn : 0 < (Fintype.card α : ℝ) := by positivity
  rw [← sub_div, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).2
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a, (p a * (if selected (c a) then 1 else 0) -
        q (c a) * (if selected (c a) then 1 else 0))| ≤
      ∑ a, |p a * (if selected (c a) then 1 else 0) -
        q (c a) * (if selected (c a) then 1 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, η := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : selected (c a)
      · simpa [ha] using hround a ha
      · simp [ha, hη]
    _ = η * Fintype.card α := by simp [mul_comm]

end

end RandomizedObligatory
end SchedulingPaper
