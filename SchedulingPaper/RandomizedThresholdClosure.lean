import SchedulingPaper.RandomizedAnnouncedFluid
import Mathlib.Tactic

/-!
# Threshold closure for sample-empty histogram bins

An arbitrary maximizing category prefix need not classify bins with zero
sample mass.  The algorithm therefore closes the optimizer by its inverse
density threshold.  This file proves that the closure preserves the density
identity even when equality bins have positive mass, and makes the global
early/late separation tautological.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

noncomputable section

/-- Mass selected by a predicate on finitely many histogram categories. -/
def selectedMass {β : Type*} [Fintype β]
    (μ : β → ℝ) (selected : β → Prop) [DecidablePred selected] : ℝ :=
  ∑ b, μ b * if selected b then 1 else 0

/-- Rounded first moment selected by a category predicate. -/
def selectedMoment {β : Type*} [Fintype β]
    (μ q : β → ℝ) (selected : β → Prop) [DecidablePred selected] : ℝ :=
  ∑ b, μ b * q b * if selected b then 1 else 0

/-- Full threshold closure, including every sample-empty category whose
representative is below the learned inverse density. -/
def thresholdClosure {β : Type*} (q : β → ℝ) (θ : ℝ) (b : β) : Prop :=
  q b ≤ θ

instance {β : Type*} (q : β → ℝ) (θ : ℝ) :
    DecidablePred (thresholdClosure q θ) := fun b => by
      unfold thresholdClosure
      infer_instance

/-- Closing a sample optimizer by `q ≤ θ` preserves its density identity.

The hypotheses are exactly the local optimality consequences for categories
of positive sample mass.  Categories of zero mass do not affect either
statistic, and a category at equality contributes work `θ` per unit mass, so
it can be added without changing inverse density. -/
theorem thresholdClosure_preserves_density
    {β : Type*} [Fintype β]
    {μ q : β → ℝ} {selected : β → Prop} [DecidablePred selected]
    {θ : ℝ}
    (hμ : ∀ b, 0 ≤ μ b)
    (hbelow : ∀ b, 0 < μ b → q b < θ → selected b)
    (habove : ∀ b, 0 < μ b → θ < q b → ¬ selected b)
    (hdensity :
      1 + selectedMoment μ q selected = θ * selectedMass μ selected) :
    1 + selectedMoment μ q (thresholdClosure q θ) =
      θ * selectedMass μ (thresholdClosure q θ) := by
  have hterm : ∀ b,
      μ b * (q b - θ) *
          (if thresholdClosure q θ b then 1 else 0) =
        μ b * (q b - θ) * (if selected b then 1 else 0) := by
    intro b
    rcases lt_trichotomy (q b) θ with hlt | heq | hgt
    · have hclosed : thresholdClosure q θ b := hlt.le
      by_cases hzero : μ b = 0
      · simp [hzero]
      · have hpos : 0 < μ b := lt_of_le_of_ne (hμ b) (Ne.symm hzero)
        have hsel := hbelow b hpos hlt
        simp [hclosed, hsel]
    · subst heq
      ring
    · have hclosed : ¬ thresholdClosure q θ b := not_le.mpr hgt
      by_cases hzero : μ b = 0
      · simp [hzero]
      · have hpos : 0 < μ b := lt_of_le_of_ne (hμ b) (Ne.symm hzero)
        have hsel := habove b hpos hgt
        simp [hclosed, hsel]
  have hsum :
      (∑ b, μ b * (q b - θ) *
          (if thresholdClosure q θ b then 1 else 0)) =
        ∑ b, μ b * (q b - θ) * (if selected b then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    exact hterm b
  have hgap :
      selectedMoment μ q (thresholdClosure q θ) -
          θ * selectedMass μ (thresholdClosure q θ) =
        selectedMoment μ q selected - θ * selectedMass μ selected := by
    unfold selectedMoment selectedMass
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    calc
      (∑ b, (μ b * q b * (if thresholdClosure q θ b then 1 else 0) -
          θ * (μ b * if thresholdClosure q θ b then 1 else 0))) =
        ∑ b, μ b * (q b - θ) *
          (if thresholdClosure q θ b then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = ∑ b, μ b * (q b - θ) * (if selected b then 1 else 0) := hsum
      _ = ∑ b, (μ b * q b * (if selected b then 1 else 0) -
          θ * (μ b * if selected b then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro b _
            ring
  linarith

theorem thresholdClosure_early_le
    {β : Type*} {q : β → ℝ} {θ : ℝ} {b : β}
    (hb : thresholdClosure q θ b) :
    q b ≤ θ := hb

theorem thresholdClosure_late_gt
    {β : Type*} {q : β → ℝ} {θ : ℝ} {b : β}
    (hb : ¬ thresholdClosure q θ b) :
    θ < q b := lt_of_not_ge hb

theorem zero_category_in_thresholdClosure
    {β : Type*} {q : β → ℝ} {θ : ℝ} {zeroBin : β}
    (hq : q zeroBin = 0) (hθ : 0 ≤ θ) :
    thresholdClosure q θ zeroBin := by
  simpa [thresholdClosure, hq] using hθ

end

end RandomizedObligatory
end SchedulingPaper
