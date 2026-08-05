import SchedulingPaper.ReachableCappedBankRemainder
import Mathlib.Tactic

/-!
# Geometry of a capped reserve step

The normalized cap coordinate is monotone along a unit step.  When it crosses
the reserve cutoff, this module gives the explicit crossing time and proves
the corresponding before/after inequalities.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedVariables false

open Set

theorem cappedStepRate_mem_zero_one (outcome : CappedBoundaryOutcome) :
    ParameterizedAnalysisState.cappedStepRate outcome ∈
      ({0, 1} : Set ℝ) := by
  cases outcome <;>
    simp [ParameterizedAnalysisState.cappedStepRate]

theorem normalizedAffinePath_nonneg_of_capRate
    {x q κ t : ℝ} (hx : 2 ≤ x) (hq : 0 ≤ q)
    (hκ : κ ∈ ({0, 1} : Set ℝ)) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ normalizedAffinePath x q κ t := by
  rcases hκ with (rfl | rfl)
  · unfold normalizedAffinePath
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (by linarith : 0 ≤ x) hq)
        (mul_nonneg (by norm_num) ht.1))
      (by linarith [ht.2])
  · unfold normalizedAffinePath
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (by linarith : 0 ≤ x) hq)
        (mul_nonneg (by norm_num) ht.1))
      (by linarith [ht.2])

theorem normalizedAffinePath_monotoneOn_of_capRate
    {x q κ : ℝ} (hx : 2 ≤ x) (hq : 0 ≤ q)
    (hκ : κ ∈ ({0, 1} : Set ℝ)) :
    MonotoneOn (normalizedAffinePath x q κ) (Icc (0 : ℝ) 1) := by
  have hκ0 : 0 ≤ κ := by
    rcases hκ with (rfl | rfl) <;> norm_num
  intro t ht u hu htu
  have hxt : 0 < x - t := by linarith [ht.2]
  have hxu : 0 < x - u := by linarith [hu.2]
  have hprod :
      0 ≤ x * (q + κ) * (u - t) :=
    mul_nonneg
      (mul_nonneg (by linarith : 0 ≤ x) (add_nonneg hq hκ0))
      (sub_nonneg.mpr htu)
  unfold normalizedAffinePath
  apply (div_le_div_iff₀ hxt hxu).2
  nlinarith

@[simp]
theorem normalizedAffinePath_zero_of_pos
    {x q κ : ℝ} (hx : 0 < x) :
    normalizedAffinePath x q κ 0 = q := by
  simp [normalizedAffinePath, hx.ne']

def capReserveCutoffCrossingTime
    (x q κ qStar : ℝ) : ℝ :=
  x * (qStar - q) / (qStar + κ)

theorem capReserveCutoffCrossingTime_mem_and_eq
    {x q κ qStar : ℝ}
    (hx : 2 ≤ x) (hq : 0 ≤ q)
    (hκ : κ ∈ ({0, 1} : Set ℝ))
    (hqStar : 0 ≤ qStar)
    (hstart : q ≤ qStar)
    (hend : qStar < normalizedAffinePath x q κ 1) :
    capReserveCutoffCrossingTime x q κ qStar ∈ Ico (0 : ℝ) 1 ∧
      normalizedAffinePath x q κ
        (capReserveCutoffCrossingTime x q κ qStar) = qStar := by
  have hκ0 : 0 ≤ κ := by
    rcases hκ with (rfl | rfl) <;> norm_num
  have hx1 : 0 < x - 1 := by linarith
  have hcrossRaw : x * (qStar - q) < qStar + κ := by
    unfold normalizedAffinePath at hend
    have hmul := (lt_div_iff₀ hx1).mp hend
    nlinarith
  have hden : 0 < qStar + κ := by
    have hnum : 0 ≤ x * (qStar - q) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hstart)
    linarith
  have ht0 :
      0 ≤ capReserveCutoffCrossingTime x q κ qStar := by
    unfold capReserveCutoffCrossingTime
    exact div_nonneg
      (mul_nonneg (by linarith) (sub_nonneg.mpr hstart))
      hden.le
  have ht1 :
      capReserveCutoffCrossingTime x q κ qStar < 1 := by
    unfold capReserveCutoffCrossingTime
    exact (div_lt_one hden).2 hcrossRaw
  constructor
  · exact ⟨ht0, ht1⟩
  · have hxt :
        x - capReserveCutoffCrossingTime x q κ qStar ≠ 0 :=
      ne_of_gt (by linarith)
    unfold normalizedAffinePath
    apply (div_eq_iff hxt).2
    unfold capReserveCutoffCrossingTime
    field_simp [hden.ne']
    ring

theorem normalizedAffinePath_le_cutoff_before_crossing
    {x q κ qStar t : ℝ}
    (hx : 2 ≤ x) (hq : 0 ≤ q)
    (hκ : κ ∈ ({0, 1} : Set ℝ))
    (hqStar : 0 ≤ qStar)
    (hstart : q ≤ qStar)
    (hend : qStar < normalizedAffinePath x q κ 1)
    (ht0 : 0 ≤ t)
    (htCross :
      t ≤ capReserveCutoffCrossingTime x q κ qStar) :
    normalizedAffinePath x q κ t ≤ qStar := by
  have hcross :=
    capReserveCutoffCrossingTime_mem_and_eq
      hx hq hκ hqStar hstart hend
  have ht1 : t ≤ 1 := htCross.trans hcross.1.2.le
  have hmono :=
    normalizedAffinePath_monotoneOn_of_capRate hx hq hκ
      ⟨ht0, ht1⟩
      ⟨hcross.1.1, hcross.1.2.le⟩
      htCross
  simpa [hcross.2] using hmono

theorem cutoff_le_normalizedAffinePath_after_crossing
    {x q κ qStar t : ℝ}
    (hx : 2 ≤ x) (hq : 0 ≤ q)
    (hκ : κ ∈ ({0, 1} : Set ℝ))
    (hqStar : 0 ≤ qStar)
    (hstart : q ≤ qStar)
    (hend : qStar < normalizedAffinePath x q κ 1)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (htCross :
      capReserveCutoffCrossingTime x q κ qStar ≤ t) :
    qStar ≤ normalizedAffinePath x q κ t := by
  have hcross :=
    capReserveCutoffCrossingTime_mem_and_eq
      hx hq hκ hqStar hstart hend
  have hmono :=
    normalizedAffinePath_monotoneOn_of_capRate hx hq hκ
      ⟨hcross.1.1, hcross.1.2.le⟩ ht htCross
  simpa [hcross.2] using hmono

end

end SchedulingPaper
