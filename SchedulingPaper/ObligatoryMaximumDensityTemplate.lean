import SchedulingPaper.ObligatoryTemplateLearning
import SchedulingPaper.ObligatoryGrowingCutoffStrategy
import SchedulingPaper.RandomizedDensityOptimizer
import Mathlib.Tactic

/-!
# Maximum-density threshold templates minimize obligatory fluid cost

This is the finite categorical form of the pointwise completion envelope.
A threshold closure satisfying the maximum-density identity minimizes the
stationary obligatory objective among all Boolean early templates.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open RandomizedOptional
open RandomizedObligatory

noncomputable section

private def restrictedMass {β : Type*} [Fintype β]
    (μ : β → ℝ) (S : β → Bool) : ℝ :=
  ∑ b, if S b then μ b else 0

private def restrictedMoment {β : Type*} [Fintype β]
    (q μ : β → ℝ) (S : β → Bool) : ℝ :=
  ∑ b, if S b then q b * μ b else 0

private def restrictedPair {β : Type*} [Fintype β]
    (q u v : β → ℝ) : ℝ :=
  ∑ b, ∑ c, min (q b) (q c) * u b * v c

private theorem restrictedPair_comm
    {β : Type*} [Fintype β] (q u v : β → ℝ) :
    restrictedPair q u v = restrictedPair q v u := by
  unfold restrictedPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [min_comm]
  ring

private theorem restrictedPair_add
    {β : Type*} [Fintype β] (q u v : β → ℝ) :
    restrictedPair q (fun b => u b + v b) (fun b => u b + v b) =
      restrictedPair q u u + 2 * restrictedPair q u v +
        restrictedPair q v v := by
  unfold restrictedPair
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  have hcomm := restrictedPair_comm q u v
  unfold restrictedPair at hcomm
  nlinarith

private theorem restrictedPair_le_moment_mul_mass
    {β : Type*} [Fintype β] (q u v : β → ℝ)
    (hu : ∀ b, 0 ≤ u b) (hv : ∀ b, 0 ≤ v b) :
    restrictedPair q u v ≤
      (∑ b, q b * u b) * (∑ c, v c) := by
  unfold restrictedPair
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hweight : 0 ≤ u b * v c := mul_nonneg (hu b) (hv c)
  have hmin : min (q b) (q c) ≤ q b := min_le_left _ _
  nlinarith

private theorem restrictedPair_lower_of_bounded
    {β : Type*} [Fintype β] (θ : ℝ) (q u : β → ℝ)
    (hu : ∀ b, 0 ≤ u b)
    (hsupport : ∀ b, u b ≠ 0 → q b ≤ θ) :
    2 * (∑ b, q b * u b) * (∑ b, u b) -
        θ * (∑ b, u b) ^ 2 ≤
      restrictedPair q u u := by
  unfold restrictedPair
  have hexpand :
      2 * (∑ b, q b * u b) * (∑ b, u b) -
          θ * (∑ b, u b) ^ 2 =
        ∑ b, ∑ c, (q b + q c - θ) * u b * u c := by
    calc
      _ = (∑ b, q b * u b) * (∑ c, u c) +
          (∑ b, u b) * (∑ c, q c * u c) -
          θ * (∑ b, u b) * (∑ c, u c) := by ring
      _ = ∑ b, ∑ c, (q b + q c - θ) * u b * u c := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b _
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
  rw [hexpand]
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  by_cases hb : u b = 0
  · simp [hb]
  by_cases hc : u c = 0
  · simp [hc]
  have hqb := hsupport b hb
  have hqc := hsupport c hc
  have hkernel :
      q b + q c - θ ≤ min (q b) (q c) := by
    apply le_min <;> linarith
  have hweight : 0 ≤ u b * u c := mul_nonneg (hu b) (hu c)
  nlinarith

private theorem restrictedPair_eq_moment_mul_mass_of_separated
    {β : Type*} [Fintype β] (θ : ℝ) (q u v : β → ℝ)
    (huSupport : ∀ b, u b ≠ 0 → q b ≤ θ)
    (hvSupport : ∀ b, v b ≠ 0 → θ < q b) :
    restrictedPair q u v =
      (∑ b, q b * u b) * (∑ c, v c) := by
  unfold restrictedPair
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hb : u b = 0
  · simp [hb]
  by_cases hc : v c = 0
  · simp [hc]
  rw [min_eq_left (huSupport b hb |>.trans (hvSupport c hc).le)]

/-- A complete maximum-density threshold closure minimizes the obligatory
stationary fluid objective.  The density identity is the only optimizer
certificate needed by the proof. -/
theorem thresholdClosure_minimizes_obligatoryTemplateValue
    {β : Type*} [Fintype β]
    (μ q : β → ℝ) (θ : ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hmass : ∑ b, μ b = 1)
    (hθ : 0 ≤ θ)
    (hidentity :
      1 + templateEarlyMoment μ q
          (fun b => decide (thresholdClosure q θ b)) =
        templateEarlyMass μ (fun b => decide (thresholdClosure q θ b)) * θ)
    (target : β → Bool) :
    obligatoryTemplateValue μ q
        (fun b => decide (thresholdClosure q θ b)) ≤
      obligatoryTemplateValue μ q target := by
  let early : β → Bool := fun b => decide (thresholdClosure q θ b)
  let xSet : β → Bool := fun b => early b && !target b
  let ySet : β → Bool := fun b => !early b && target b
  let zSet : β → Bool := fun b => !early b && !target b
  let xw : β → ℝ := fun b => if xSet b then μ b else 0
  let yw : β → ℝ := fun b => if ySet b then μ b else 0
  let zw : β → ℝ := fun b => if zSet b then μ b else 0
  let a := templateEarlyMass μ early
  let m := templateEarlyMoment μ q early
  let aT := templateEarlyMass μ target
  let mT := templateEarlyMoment μ q target
  let x := ∑ b, xw b
  let y := ∑ b, yw b
  let z := ∑ b, zw b
  let mx := ∑ b, q b * xw b
  let my := ∑ b, q b * yw b
  let Kxx := restrictedPair q xw xw
  let Kxz := restrictedPair q xw zw
  let Kyy := restrictedPair q yw yw
  let Kyz := restrictedPair q yw zw
  let Kzz := restrictedPair q zw zw
  have hxw : ∀ b, 0 ≤ xw b := by
    intro b
    dsimp [xw]
    split
    · exact hμ b
    · norm_num
  have hyw : ∀ b, 0 ≤ yw b := by
    intro b
    dsimp [yw]
    split
    · exact hμ b
    · norm_num
  have hzw : ∀ b, 0 ≤ zw b := by
    intro b
    dsimp [zw]
    split
    · exact hμ b
    · norm_num
  have hx0 : 0 ≤ x := Finset.sum_nonneg fun b _ => hxw b
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun b _ => hyw b
  have hz0 : 0 ≤ z := Finset.sum_nonneg fun b _ => hzw b
  have ha0 : 0 ≤ a := by
    unfold a templateEarlyMass finiteExpectation
    exact Finset.sum_nonneg fun b _ => by
      cases he : early b <;> simp [he, hμ b]
  have hax : x ≤ a := by
    unfold x a xw xSet templateEarlyMass finiteExpectation
    apply Finset.sum_le_sum
    intro b _
    cases he : early b <;> cases ht : target b <;>
      simp [he, ht, hμ b]
  have haT0 : 0 ≤ aT := by
    unfold aT templateEarlyMass finiteExpectation
    exact Finset.sum_nonneg fun b _ => by
      cases ht : target b <;> simp [ht, hμ b]
  have hmassSplit : a + y + z = 1 := by
    rw [← hmass]
    unfold a y z yw zw ySet zSet templateEarlyMass finiteExpectation
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases he : early b <;> cases ht : target b <;>
      simp [he, ht]
  have haT : aT = a - x + y := by
    unfold aT a x y xw yw xSet ySet templateEarlyMass finiteExpectation
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases he : early b <;> cases ht : target b <;>
      simp [he, ht]
  have hmT : mT = m - mx + my := by
    unfold mT m mx my xw yw xSet ySet templateEarlyMoment
      finiteExpectation
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases he : early b <;> cases ht : target b <;>
      simp [he, ht] <;> ring
  have hxSupport : ∀ b, xw b ≠ 0 → q b ≤ θ := by
    intro b hb
    have he : early b = true := by
      by_contra hnot
      have heFalse := Bool.eq_false_of_not_eq_true hnot
      simp [xw, xSet, heFalse] at hb
    simpa [early, thresholdClosure] using he
  have hySupport : ∀ b, yw b ≠ 0 → θ < q b := by
    intro b hb
    have he : early b = false := by
      cases heq : early b
      · rfl
      · simp [yw, ySet, heq] at hb
    have hnot : ¬q b ≤ θ := by
      simpa [early, thresholdClosure] using he
    exact lt_of_not_ge hnot
  have hzSupport : ∀ b, zw b ≠ 0 → θ < q b := by
    intro b hb
    have he : early b = false := by
      cases heq : early b
      · rfl
      · simp [zw, zSet, heq] at hb
    have hnot : ¬q b ≤ θ := by
      simpa [early, thresholdClosure] using he
    exact lt_of_not_ge hnot
  have hmxLe : mx ≤ θ * x := by
    unfold mx x
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : xw b = 0
    · simp [hb]
    exact mul_le_mul_of_nonneg_right (hxSupport b hb) (hxw b)
  have hmyGe : θ * y ≤ my := by
    unfold my y
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : yw b = 0
    · simp [hb]
    exact mul_le_mul_of_nonneg_right (hySupport b hb).le (hyw b)
  have hKxx :
      2 * mx * x - θ * x ^ 2 ≤ Kxx := by
    exact restrictedPair_lower_of_bounded θ q xw hxw hxSupport
  have hKxz : Kxz = mx * z := by
    exact restrictedPair_eq_moment_mul_mass_of_separated
      θ q xw zw hxSupport hzSupport
  have hKyy : Kyy ≤ my * y :=
    restrictedPair_le_moment_mul_mass q yw yw hyw hyw
  have hKyz : Kyz ≤ my * z :=
    restrictedPair_le_moment_mul_mass q yw zw hyw hzw
  have hlateEarly :
      templateLatePair μ q early = Kyy + 2 * Kyz + Kzz := by
    have heq : templateLatePair μ q early = restrictedPair q
        (fun b => μ b * (if early b then 0 else 1))
        (fun b => μ b * (if early b then 0 else 1)) := by
      unfold templateLatePair finiteProductExpectation restrictedPair
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hweights : (fun b => μ b * (if early b then 0 else 1)) =
        fun b => yw b + zw b := by
      funext b
      dsimp [yw, zw, ySet, zSet]
      rcases Bool.eq_false_or_eq_true (early b) with he | he <;>
        rcases Bool.eq_false_or_eq_true (target b) with ht | ht <;>
        simp [he, ht]
    rw [heq, hweights, restrictedPair_add]
  have hlateTarget :
      templateLatePair μ q target = Kxx + 2 * Kxz + Kzz := by
    have heq : templateLatePair μ q target = restrictedPair q
        (fun b => μ b * (if target b then 0 else 1))
        (fun b => μ b * (if target b then 0 else 1)) := by
      unfold templateLatePair finiteProductExpectation restrictedPair
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hweights : (fun b => μ b * (if target b then 0 else 1)) =
        fun b => xw b + zw b := by
      funext b
      dsimp [xw, zw, xSet, zSet]
      rcases Bool.eq_false_or_eq_true (early b) with he | he <;>
        rcases Bool.eq_false_or_eq_true (target b) with ht | ht <;>
        simp [he, ht]
    rw [heq, hweights, restrictedPair_add]
  have hmodule : 1 + m = a * θ := by
    simpa [early, a, m] using hidentity
  have hu0 : 0 ≤ my - θ * y := sub_nonneg.mpr hmyGe
  have hv0 : 0 ≤ θ * x - mx := sub_nonneg.mpr hmxLe
  have hcoefU : 0 ≤ a + x := add_nonneg ha0 hx0
  have hcoefV : 0 ≤ a - x + y := by linarith
  have hnonneg :
      0 ≤ (my - θ * y) * (a + x) +
        (θ * x - mx) * (a - x + y) :=
    add_nonneg (mul_nonneg hu0 hcoefU) (mul_nonneg hv0 hcoefV)
  have hlateEarlyUpper :
      templateLatePair μ q early ≤ my * y + 2 * my * z + Kzz := by
    rw [hlateEarly]
    nlinarith
  have hlateTargetLower :
      2 * mx * x - θ * x ^ 2 + 2 * mx * z + Kzz ≤
        templateLatePair μ q target := by
    rw [hlateTarget, hKxz]
    nlinarith
  have hpairGap :
      (2 * mx * x - θ * x ^ 2 + 2 * mx * z + Kzz) -
          (my * y + 2 * my * z + Kzz) ≤
        templateLatePair μ q target - templateLatePair μ q early := by
    linarith
  have hmEq : m = a * θ - 1 := by linarith
  have hzEq : z = 1 - a - y := by linarith
  have halgebra :
      2 * ((1 + mT) * (1 - aT / 2) -
          (1 + m) * (1 - a / 2)) +
          ((2 * mx * x - θ * x ^ 2 + 2 * mx * z + Kzz) -
            (my * y + 2 * my * z + Kzz)) =
        (my - θ * y) * (a + x) +
          (θ * x - mx) * (a - x + y) := by
    rw [haT, hmT, hmEq, hzEq]
    ring
  have hgap :
      (my - θ * y) * (a + x) +
          (θ * x - mx) * (a - x + y) ≤
        2 * (obligatoryTemplateValue μ q target -
          obligatoryTemplateValue μ q early) := by
    change (my - θ * y) * (a + x) +
        (θ * x - mx) * (a - x + y) ≤
      2 * (((1 + mT) * (1 - aT / 2) +
          templateLatePair μ q target / 2) -
        ((1 + m) * (1 - a / 2) + templateLatePair μ q early / 2))
    nlinarith [hpairGap, halgebra]
  linarith

/-- The threshold returned by the growing maximum-density learner is an exact
empirical minimizer of the obligatory template objective. -/
theorem growingLearner_minimizes_obligatoryTemplateValue
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Online.Label n × ℝ)) {θ : ℝ}
    (hlearn : Online.growingLearnedThresholdFromResults?
      B d η hη results = some θ)
    (target : QuantizedCategory d → Bool) :
    let μ := Online.resultCategoryFraction d η hη results
    let q := Online.growingQuantizedRepresentative d η
    obligatoryTemplateValue μ q
        (fun b => decide (thresholdClosure q θ b)) ≤
      obligatoryTemplateValue μ q target := by
  dsimp only
  apply thresholdClosure_minimizes_obligatoryTemplateValue
  · exact Online.resultCategoryFraction_nonneg d η hη results
  · exact Online.growingQuantizedRepresentative_nonneg d hη.le
  · have hne : results ≠ [] := by
      intro hempty
      subst results
      have hs := Online.growingLearnedThresholdFromResults_some
        B d η hη ([] : List (Online.Label n × ℝ)) hlearn
      dsimp only at hs
      have hzero : subsetMass
          (Online.resultCategoryFraction (n := n) d η hη [])
          (Online.growingResultMaximumDensitySet (n := n) d η hη []) = 0 := by
        simp [Online.resultCategoryFraction, subsetMass]
      linarith [hs.1]
    exact Online.sum_resultCategoryFraction_eq_one d η hη results hne
  · exact (Online.growingLearnedThresholdFromResults_closure_certificate
      B d η hη results hlearn).1
  · have hcert :=
      (Online.growingLearnedThresholdFromResults_closure_certificate
        B d η hη results hlearn).2.2
    simpa [templateEarlyMoment, templateEarlyMass, finiteExpectation,
      selectedMoment, selectedMass, mul_assoc, mul_comm, mul_left_comm]
      using hcert

end

end ObligatoryInstance
end SchedulingPaper
