import SchedulingPaper.RandomizedDensityOptimizer
import SchedulingPaper.RandomizedObligatoryUpper
import SchedulingPaper.RandomizedQuantization
import Mathlib.Tactic

/-!
# Properties of the learned density threshold

This module connects the concrete cutoff-32 histogram, its finite
maximum-density optimizer, threshold closure, and the population/sample
transfer inequalities.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

/-- In learned mode (`rhoHat ≥ 1/16`), a maximum-density sample set has a
positive inverse density at most sixteen.  Its full threshold closure keeps
the density identity and has sample mass at least `1/16`. -/
theorem learned_maximumDensity_properties
    {β : Type*} [Fintype β] [DecidableEq β]
    {μ q : β → ℝ} {S : Finset β}
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hmax : IsMaximumDensitySubset μ q S)
    (hlearned : 1 / 16 ≤ subsetDensity μ q S) :
    let θ := (1 + subsetMoment μ q S) / subsetMass μ S
    0 < θ ∧ θ ≤ 16 ∧
      1 + selectedMoment μ q (thresholdClosure q θ) =
        θ * selectedMass μ (thresholdClosure q θ) ∧
      1 / 16 ≤ selectedMass μ (thresholdClosure q θ) := by
  dsimp only
  have hm0 := subsetMoment_nonneg hμ hq S
  have hden : 0 < 1 + subsetMoment μ q S := by linarith
  have ha0 := subsetMass_nonneg hμ S
  have ha : 0 < subsetMass μ S := by
    by_contra hnot
    have hazero : subsetMass μ S = 0 := le_antisymm (le_of_not_gt hnot) ha0
    unfold subsetDensity at hlearned
    rw [hazero] at hlearned
    norm_num at hlearned
  let θ := (1 + subsetMoment μ q S) / subsetMass μ S
  have hθ : 0 < θ := by
    dsimp [θ]
    exact div_pos hden ha
  have hθ16 : θ ≤ 16 := by
    have hcross := (le_div_iff₀ hden).mp hlearned
    dsimp [θ]
    apply (div_le_iff₀ ha).2
    norm_num at hcross ⊢
    linarith
  have hdensity :
      1 + subsetMoment μ q S = subsetMass μ S * θ := by
    dsimp [θ]
    exact inverseDensity_identity ha
  have hclosed := maximumDensity_thresholdClosure_preserves
    hμ hq hmax ha hdensity
  have hmClosed :
      0 ≤ selectedMoment μ q (thresholdClosure q θ) := by
    unfold selectedMoment
    exact Finset.sum_nonneg fun b _ => by
      by_cases hb : thresholdClosure q θ b
      · simp [hb, mul_nonneg (hμ b) (hq b)]
      · simp [hb]
  have haClosed := inverseDensity_le_sixteen_mass_lower
    (a := selectedMass μ (thresholdClosure q θ))
    (m := selectedMoment μ q (thresholdClosure q θ)) (θ := θ)
    hmClosed hθ.le hθ16 (by simpa [mul_comm] using hclosed)
  exact ⟨hθ, hθ16, hclosed, haClosed⟩

/-- Deterministic population/sample transfer for the actual cutoff-32
quantizer and a learned threshold at most sixteen. -/
theorem learned_histogram_transfer_B32
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (samplePositions : Finset α) (σ : Equiv.Perm α)
    (d : ℕ) {η θ : ℝ} (hη : 0 < η)
    (hcutoff : (d : ℝ) * η = 32) (hθ : θ ≤ 16)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    let c := fun a => quantizedCategory d η (p a) hη
    let q := quantizedRepresentative d η
    let selected := thresholdClosure q θ
    let μ := fun b => ((categoryClass c b).card : ℝ) / Fintype.card α
    let μHat := fun b => sampleCategoryFraction samplePositions
      (categoryClass c b) σ
    let actualMoment :=
      (∑ a, p a * (if selected (c a) then 1 else 0)) / Fintype.card α
    |selectedMass μ selected - selectedMass μHat selected| ≤
        histogramL1Error samplePositions c σ ∧
      |actualMoment - selectedMoment μHat q selected| ≤
        32 * histogramL1Error samplePositions c σ + η := by
  dsimp only
  let c := fun a => quantizedCategory d η (p a) hη
  let q := quantizedRepresentative d η
  let selected := thresholdClosure q θ
  let μ := fun b => ((categoryClass c b).card : ℝ) / Fintype.card α
  let μHat := fun b => sampleCategoryFraction samplePositions
    (categoryClass c b) σ
  constructor
  · exact selectedMass_population_sample_le_histogramL1Error
      samplePositions c σ selected
  · have hround := quantized_jobAverage_rounding_error_B32
      d hη hcutoff hθ p hp
    have hhist :
        |selectedMoment μ q selected - selectedMoment μHat q selected| ≤
          32 * histogramL1Error samplePositions c σ := by
      apply selectedMoment_population_sample_le_histogramL1Error
        samplePositions c σ q selected (by norm_num)
      · intro b
        exact quantizedRepresentative_nonneg d hη.le b
      · intro b hb
        have hbθ : q b ≤ θ := hb
        linarith
    exact selectedMoment_actual_sample_le hround hhist

/-- On the good histogram event, the true inverse density is within
`1536 Δ + 32 η` of the learned inverse density. -/
theorem learned_true_threshold_distance_B32
    {a aHat m mHat θHat Δ η : ℝ}
    (haHat : 1 / 16 ≤ aHat)
    (hθHat : 0 ≤ θHat) (hθHat16 : θHat ≤ 16)
    (hgood : Δ ≤ 1 / (32 * 33))
    (hMass : |a - aHat| ≤ Δ)
    (hMoment : |m - mHat| ≤ 32 * Δ + η)
    (hDensityHat : 1 + mHat = aHat * θHat) :
    |(1 + m) / a - θHat| ≤ 1536 * Δ + 32 * η := by
  have ha := learned_mass_lower_B32 haHat hgood hMass
  exact learned_threshold_distance_B32 ha hθHat hθHat16 hMass hMoment
    rfl hDensityHat

/-- Concrete early categories lie below the learned threshold in actual,
not only rounded, processing time. -/
theorem quantized_early_actual_le_threshold
    (d : ℕ) {η θ p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hθ : θ ≤ 16)
    (hselected : thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    p ≤ θ := by
  by_cases hp0 : p = 0
  · subst p
    simpa [thresholdClosure, quantizedCategory, quantizedRepresentative]
      using hselected
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hqθ : quantizedRepresentative d η (quantizedCategory d η p hη) ≤ θ :=
    hselected
  by_cases hcap : p ≤ (d : ℝ) * η
  · exact (quantized_rounding_bounds d hη hpPos hcap).1.trans hqθ
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    rw [quantizedCategory_overflow d hη hover,
      quantizedRepresentative_overflow] at hqθ
    exfalso
    linarith

theorem quantized_early_actual_le_representative
    (d : ℕ) {η θ p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hθ : θ ≤ 16)
    (hselected : thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    p ≤ quantizedRepresentative d η (quantizedCategory d η p hη) := by
  by_cases hp0 : p = 0
  · subst p
    simp [quantizedCategory, quantizedRepresentative]
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  by_cases hcap : p ≤ (d : ℝ) * η
  · exact (quantized_rounding_bounds d hη hpPos hcap).1
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    have hq : (33 : ℝ) ≤ θ := by
      rw [quantizedCategory_overflow d hη hover] at hselected
      have hq := thresholdClosure_early_le hselected
      rw [quantizedRepresentative_overflow] at hq
      exact hq
    exfalso
    linarith

/-- Every category outside the closure has actual processing time at least
`thetaHat-η`; overflow is handled separately by the fixed cutoff. -/
theorem quantized_late_actual_ge_threshold_sub_eta_B32
    (d : ℕ) {η θ p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hcutoff : (d : ℝ) * η = 32) (hθ : θ ≤ 16)
    (hlate : ¬ thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    θ - η ≤ p := by
  by_cases hp0 : p = 0
  · subst p
    have hq := thresholdClosure_late_gt hlate
    rw [quantizedCategory_zero d hη, quantizedRepresentative_zero] at hq
    linarith
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  by_cases hcap : p ≤ (d : ℝ) * η
  · have hround := (quantized_rounding_bounds d hη hpPos hcap).2
    have hq := thresholdClosure_late_gt hlate
    linarith
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    rw [hcutoff] at hover
    linarith

/-- Consecutive nonoverflow bins make the actual learned early/late split
ordered, despite upward rounding. -/
theorem quantized_threshold_split_ordered_B32
    (d : ℕ) {η θ pEarly pLate : ℝ}
    (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hθ0 : 0 ≤ θ) (hθ16 : θ ≤ 16)
    (hpEarly : 0 ≤ pEarly) (hpLate : 0 ≤ pLate)
    (hearly : thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η pEarly hη))
    (hlate : ¬ thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η pLate hη)) :
    pEarly ≤ pLate := by
  let bE := quantizedCategory d η pEarly hη
  let bL := quantizedCategory d η pLate hη
  let q := quantizedRepresentative d η
  have hpEq : pEarly ≤ q bE :=
    quantized_early_actual_le_representative d hη hpEarly hθ16 hearly
  have hqOrder : q bE < q bL :=
    lt_of_le_of_lt (show q bE ≤ θ from hearly)
      (thresholdClosure_late_gt hlate)
  by_cases hLateCap : pLate ≤ (d : ℝ) * η
  · have hpLatePos : 0 < pLate := by
      by_contra hnot
      have hpZero : pLate = 0 := le_antisymm (le_of_not_gt hnot) hpLate
      subst pLate
      have hqLate := thresholdClosure_late_gt hlate
      simp [bL, q, quantizedCategory, quantizedRepresentative] at hqLate
      linarith
    have hroundLate := (quantized_rounding_bounds d hη hpLatePos hLateCap).2
    have hbL : bL.val ≤ d := by
      dsimp [bL, quantizedCategory]
      simp only [hpLatePos.ne', ↓reduceDIte, hLateCap]
      exact Nat.ceil_le.mpr (by
        rw [div_le_iff₀ hη]
        simpa [mul_comm] using hLateCap)
    have hbE : bE.val ≤ d := by
      by_contra hb
      have hbOverflow : bE.val = d + 1 := by
        have hbTop : bE.val < d + 2 := bE.isLt
        omega
      have hqE : q bE = 33 := by
        dsimp [q]
        unfold quantizedRepresentative
        simp [hbOverflow]
      rw [hqE] at hqOrder
      have hqLB := quantizedRepresentative_le_cutoff d hη.le hbL
      rw [hcutoff] at hqLB
      linarith
    have hrepE := quantizedRepresentative_eq_mul_of_le d η hbE
    have hrepL := quantizedRepresentative_eq_mul_of_le d η hbL
    dsimp [q] at hqOrder hpEq
    rw [hrepE] at hqOrder hpEq
    rw [hrepL] at hqOrder
    have hval : bE.val + 1 ≤ bL.val := by
      have hcast : (bE.val : ℝ) < (bL.val : ℝ) := by
        by_contra hnot
        have hle : (bL.val : ℝ) ≤ (bE.val : ℝ) := le_of_not_gt hnot
        have hmul := mul_le_mul_of_nonneg_right hle hη.le
        linarith
      exact Nat.add_one_le_iff.mpr (by exact_mod_cast hcast)
    have hgap : (bE.val : ℝ) * η + η ≤ (bL.val : ℝ) * η := by
      have hcast : ((bE.val + 1 : ℕ) : ℝ) ≤ (bL.val : ℝ) := by
        exact_mod_cast hval
      have := mul_le_mul_of_nonneg_right hcast hη.le
      push_cast at this
      nlinarith
    change q bL < pLate + η at hroundLate
    dsimp [q] at hroundLate
    rw [hrepL] at hroundLate
    nlinarith
  · have hover : (d : ℝ) * η < pLate := lt_of_not_ge hLateCap
    have hpEθ := quantized_early_actual_le_threshold d hη hpEarly hθ16 hearly
    rw [hcutoff] at hover
    linarith

/-- Moving from the learned threshold to the true population inverse density
turns the preceding pointwise bounds into the robust separation used by the
`4/3` certificate. -/
theorem robust_separation_from_threshold_distance
    {p θ θHat distance η : ℝ}
    (hdistance : |θ - θHat| ≤ distance)
    (hη : 0 ≤ η) :
    (p ≤ θHat → p ≤ θ + distance + η) ∧
      (θHat - η ≤ p → θ - (distance + η) ≤ p) := by
  have hleft : θHat - θ ≤ distance :=
    (le_abs_self (θHat - θ)).trans (by simpa [abs_sub_comm] using hdistance)
  have hright : θ - θHat ≤ distance :=
    (le_abs_self (θ - θHat)).trans hdistance
  constructor <;> intro hp <;> linarith

end

end RandomizedObligatory
end SchedulingPaper
