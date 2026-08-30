import SchedulingPaper.ObligatoryGrowingCutoffExpected
import SchedulingPaper.RandomizedGoodLearned
import SchedulingPaper.RandomizedFourThirds
import Mathlib.Tactic

/-!
# The growing-cutoff obligatory policy is uniformly `4/3` competitive

This file supplies the certificate that was previously available only for
the fixed-cutoff companion.  All statements here concern the literal
`growingObligatoryStrategy`, with its supplied cutoff `B`, grid mesh `η`, and
sample size `k`.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

def growingLearnedEarly
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) : Bool :=
  decide (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
    (quantizedCategory d η (p i) hη))

@[simp] theorem growingLearnedEarly_eq_true_iff
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) :
    growingLearnedEarly d η hη p θHat i = true ↔
      thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) := by
  simp [growingLearnedEarly]

@[simp] theorem growingLearnedEarly_eq_false_iff
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) :
    growingLearnedEarly d η hη p θHat i = false ↔
      ¬ thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) := by
  simp [growingLearnedEarly]

theorem growingLearnedEarly_mass_eq_populationMass
    {n : ℕ} (hn : 0 < n)
    (d : ℕ) {η θHat : ℝ} (hη : 0 < η) (p : Fin n → ℝ) :
    weightedMass (earlyJobWeight (growingLearnedEarly d η hη p θHat)) =
      selectedMass
        (fun b => ((categoryClass
          (fun i => quantizedCategory d η (p i) hη) b).card : ℝ) / n)
        (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpopulation := selectedMass_population_eq_jobAverage
    (fun i => quantizedCategory d η (p i) hη)
    (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat)
  simp only [Fintype.card_fin] at hpopulation
  unfold weightedMass earlyJobWeight growingLearnedEarly
  rw [hpopulation]
  rw [show (fun i =>
      if decide (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη)) = true then 1 / (n : ℝ) else 0) =
    (fun i => (if thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
      (quantizedCategory d η (p i) hη) then (1 : ℝ) else 0) / (n : ℝ)) by
      funext i
      by_cases hi : thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) <;> simp [hi]]
  rw [Finset.sum_div]

theorem growingLearnedEarly_moment_eq_populationMoment
    {n : ℕ} (d : ℕ) {η θHat : ℝ} (hη : 0 < η) (p : Fin n → ℝ) :
    weightedMoment (earlyJobWeight
        (growingLearnedEarly d η hη p θHat)) p =
      (∑ i, p i *
        (if thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη) then 1 else 0)) / n := by
  unfold weightedMoment earlyJobWeight growingLearnedEarly
  rw [show (fun i =>
      (if decide (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη)) = true then 1 / (n : ℝ) else 0) *
        p i) =
    (fun i => (p i *
      (if thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) then 1 else 0)) / n) by
      funext i
      by_cases hi : thresholdClosure (Online.growingQuantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη) <;> simp [hi] <;> ring]
  rw [Finset.sum_div]

/-- The variable-cutoff analogue of the population/sample transfer lemma. -/
theorem growing_learned_histogram_transfer
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (samplePositions : Finset α) (σ : Equiv.Perm α)
    (d : ℕ) {B η θ : ℝ} (hη : 0 < η)
    (hB0 : 0 ≤ B) (hBgrid : B ≤ (d : ℝ) * η) (hθ : θ ≤ B)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    let c := fun a => quantizedCategory d η (p a) hη
    let q := Online.growingQuantizedRepresentative d η
    let selected := thresholdClosure q θ
    let μ := fun b => ((categoryClass c b).card : ℝ) / Fintype.card α
    let μHat := fun b => sampleCategoryFraction samplePositions
      (categoryClass c b) σ
    let actualMoment :=
      (∑ a, p a * (if selected (c a) then 1 else 0)) / Fintype.card α
    |selectedMass μ selected - selectedMass μHat selected| ≤
        histogramL1Error samplePositions c σ ∧
      |actualMoment - selectedMoment μHat q selected| ≤
        B * histogramL1Error samplePositions c σ + η := by
  dsimp only
  let c := fun a => quantizedCategory d η (p a) hη
  let q := Online.growingQuantizedRepresentative d η
  let selected := thresholdClosure q θ
  let μ := fun b => ((categoryClass c b).card : ℝ) / Fintype.card α
  let μHat := fun b => sampleCategoryFraction samplePositions
    (categoryClass c b) σ
  constructor
  · exact selectedMass_population_sample_le_histogramL1Error
      samplePositions c σ selected
  · have hround :
        |(∑ a, p a * (if selected (c a) then 1 else 0)) /
              Fintype.card α - selectedMoment μ q selected| ≤ η := by
      apply jobAverage_rounding_error_le p c q selected hη.le
      intro a ha
      have hpa := hp a
      have hselected : q (c a) ≤ θ := ha
      have hpgrid : p a ≤ (d : ℝ) * η := by
        by_contra hnot
        have hover : (d : ℝ) * η < p a := lt_of_not_ge hnot
        have hcat := quantizedCategory_overflow d hη hover
        have hnotSelected := Online.growingThresholdClosure_excludes_overflow
          d hη (hθ.trans hBgrid)
        exact hnotSelected (by simpa [c, hcat] using ha)
      have hb := Online.growingQuantized_rounding_bounds d hη hpa hpgrid
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hb.1)]
      linarith
    have hhist :
        |selectedMoment μ q selected - selectedMoment μHat q selected| ≤
          B * histogramL1Error samplePositions c σ := by
      apply selectedMoment_population_sample_le_histogramL1Error
        samplePositions c σ q selected hB0
      · exact Online.growingQuantizedRepresentative_nonneg d hη.le
      · intro b hb
        exact hb.trans hθ
    exact selectedMoment_actual_sample_le hround hhist

/-- A successful variable-cutoff learner has sample mass at least `1/B`. -/
theorem growing_sample_mass_lower
    {B aHat mHat θHat : ℝ}
    (hB : 0 < B) (hmHat : 0 ≤ mHat)
    (hθ0 : 0 ≤ θHat) (hθ : θHat ≤ B)
    (hdensity : 1 + mHat = aHat * θHat) :
    1 / B ≤ aHat := by
  have hprod : 1 ≤ aHat * B := by
    calc
      1 ≤ 1 + mHat := by linarith
      _ = aHat * θHat := hdensity
      _ ≤ aHat * B := by
        have ha0 : 0 ≤ aHat := by
          by_contra hnot
          have haNeg : aHat < 0 := lt_of_not_ge hnot
          have : aHat * θHat ≤ 0 := mul_nonpos_of_nonpos_of_nonneg haNeg.le hθ0
          linarith
        exact mul_le_mul_of_nonneg_left hθ ha0
  exact (div_le_iff₀ hB).2 hprod

/-- The good event leaves population selected mass at least `1/(B+1)`. -/
theorem growing_population_mass_lower
    {B a aHat Δ : ℝ}
    (hB : 0 < B) (haHat : 1 / B ≤ aHat)
    (hgood : Δ ≤ 1 / (B * (B + 1)))
    (hMass : |a - aHat| ≤ Δ) :
    1 / (B + 1) ≤ a := by
  have hB1 : 0 < B + 1 := by linarith
  have hlower : aHat - a ≤ Δ := by
    exact (le_abs_self (aHat - a)).trans (by simpa [abs_sub_comm] using hMass)
  have hid : 1 / B - 1 / (B + 1) = 1 / (B * (B + 1)) := by
    field_simp [hB.ne', hB1.ne']
    ring
  rw [← hid] at hgood
  linarith

/-- Parametric transfer of the inverse density. -/
theorem growing_threshold_distance
    {B a aHat m mHat θ θHat Δ η : ℝ}
    (hB : 0 < B) (ha : 1 / (B + 1) ≤ a)
    (hθHat0 : 0 ≤ θHat) (hθHatB : θHat ≤ B)
    (hMass : |a - aHat| ≤ Δ)
    (hMoment : |m - mHat| ≤ B * Δ + η)
    (hθ : θ = (1 + m) / a)
    (hθHat : 1 + mHat = aHat * θHat) :
    |θ - θHat| ≤ 2 * B * (B + 1) * Δ + (B + 1) * η := by
  have hB1 : 0 < B + 1 := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (one_div_pos.mpr hB1) ha
  have hMass' : |aHat - a| ≤ Δ := by simpa [abs_sub_comm] using hMass
  have hnum :
      |(m - mHat) + θHat * (aHat - a)| ≤ 2 * B * Δ + η := by
    calc
      |(m - mHat) + θHat * (aHat - a)| ≤
          |m - mHat| + |θHat * (aHat - a)| := abs_add_le _ _
      _ = |m - mHat| + θHat * |aHat - a| := by
        rw [abs_mul, abs_of_nonneg hθHat0]
      _ ≤ (B * Δ + η) + B * Δ := by gcongr
      _ = 2 * B * Δ + η := by ring
  have hid :
      θ - θHat = ((m - mHat) + θHat * (aHat - a)) / a := by
    rw [hθ]
    field_simp [ha0.ne']
    nlinarith [hθHat]
  rw [hid, abs_div, abs_of_pos ha0]
  apply (div_le_iff₀ ha0).2
  have hnum0 : 0 ≤ 2 * B * Δ + η :=
    (abs_nonneg ((m - mHat) + θHat * (aHat - a))).trans hnum
  have hone : 1 ≤ a * (B + 1) := by
    have := (div_le_iff₀ hB1).1 ha
    simpa [one_mul] using this
  calc
    |(m - mHat) + θHat * (aHat - a)| ≤ 2 * B * Δ + η := hnum
    _ = (2 * B * Δ + η) * 1 := by ring
    _ ≤ (2 * B * Δ + η) * (a * (B + 1)) :=
      mul_le_mul_of_nonneg_left hone hnum0
    _ = (2 * B * (B + 1) * Δ + (B + 1) * η) * a := by ring

theorem growing_early_actual_le_threshold
    (d : ℕ) {B η θ p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hBgrid : B ≤ (d : ℝ) * η) (hθ : θ ≤ B)
    (hselected : thresholdClosure
      (Online.growingQuantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    p ≤ θ := by
  by_cases hcap : p ≤ (d : ℝ) * η
  · exact (Online.growingQuantized_rounding_bounds d hη hp hcap).1.trans
      hselected
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    have hcat := quantizedCategory_overflow d hη hover
    have hnot := Online.growingThresholdClosure_excludes_overflow
      d hη (hθ.trans hBgrid)
    exact False.elim (hnot (by simpa [hcat] using hselected))

theorem growing_late_actual_ge_threshold_sub_eta
    (d : ℕ) {B η θ p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hBgrid : B ≤ (d : ℝ) * η) (hθ : θ ≤ B)
    (hlate : ¬ thresholdClosure
      (Online.growingQuantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    θ - η ≤ p := by
  by_cases hcap : p ≤ (d : ℝ) * η
  · have hround :=
      (Online.growingQuantized_rounding_bounds d hη hp hcap).2
    have hq := thresholdClosure_late_gt hlate
    linarith
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    linarith

theorem growing_threshold_split_ordered
    (d : ℕ) {B η θ pEarly pLate : ℝ}
    (hη : 0 < η) (hBgrid : B ≤ (d : ℝ) * η)
    (hθ0 : 0 ≤ θ) (hθB : θ ≤ B)
    (hpEarly : 0 ≤ pEarly) (hpLate : 0 ≤ pLate)
    (hearly : thresholdClosure
      (Online.growingQuantizedRepresentative d η) θ
      (quantizedCategory d η pEarly hη))
    (hlate : ¬ thresholdClosure
      (Online.growingQuantizedRepresentative d η) θ
      (quantizedCategory d η pLate hη)) :
    pEarly ≤ pLate := by
  let bE := quantizedCategory d η pEarly hη
  let bL := quantizedCategory d η pLate hη
  let q := Online.growingQuantizedRepresentative d η
  have hEarlyCap : pEarly ≤ (d : ℝ) * η := by
    by_contra hnot
    have hover : (d : ℝ) * η < pEarly := lt_of_not_ge hnot
    have hcat := quantizedCategory_overflow d hη hover
    have hnotSelected := Online.growingThresholdClosure_excludes_overflow
      d hη (hθB.trans hBgrid)
    exact hnotSelected (by simpa [bE, hcat] using hearly)
  have hpEq : pEarly ≤ q bE :=
    (Online.growingQuantized_rounding_bounds d hη hpEarly hEarlyCap).1
  have hqOrder : q bE < q bL :=
    lt_of_le_of_lt (show q bE ≤ θ from hearly)
      (thresholdClosure_late_gt hlate)
  by_cases hLateCap : pLate ≤ (d : ℝ) * η
  · have hroundLate :=
      (Online.growingQuantized_rounding_bounds d hη hpLate hLateCap).2
    have hbL : bL.val ≤ d := by
      by_cases hpLate0 : pLate = 0
      · subst pLate
        simp [bL, quantizedCategory]
      · have hpLatePos : 0 < pLate := lt_of_le_of_ne hpLate (Ne.symm hpLate0)
        dsimp [bL, quantizedCategory]
        simp only [hpLatePos.ne', ↓reduceDIte, hLateCap]
        exact Nat.ceil_le.mpr (by
          rw [div_le_iff₀ hη]
          simpa [mul_comm] using hLateCap)
    have hbE : bE.val ≤ d := by
      by_contra hb
      have hbOverflow : bE.val = d + 1 := by omega
      have hqE : q bE = (d + 1 : ℕ) * η := by
        dsimp [q]
        rw [show bE = (⟨d + 1, by omega⟩ : QuantizedCategory d) by
          apply Fin.ext
          exact hbOverflow]
        exact Online.growingQuantizedRepresentative_overflow d η
      have hqL : q bL = (bL.val : ℝ) * η := by
        unfold q Online.growingQuantizedRepresentative
        by_cases hb0 : bL.val = 0 <;> simp [hb0]
      rw [hqE, hqL] at hqOrder
      have hcast : (bL.val : ℝ) ≤ d := by exact_mod_cast hbL
      have hmul := mul_le_mul_of_nonneg_right hcast hη.le
      push_cast at hqOrder
      nlinarith
    have hrepE : q bE = (bE.val : ℝ) * η := by
      unfold q Online.growingQuantizedRepresentative
      by_cases hb0 : bE.val = 0 <;> simp [hb0]
    have hrepL : q bL = (bL.val : ℝ) * η := by
      unfold q Online.growingQuantizedRepresentative
      by_cases hb0 : bL.val = 0 <;> simp [hb0]
    change q bL ≤ pLate + η at hroundLate
    rw [hrepE] at hqOrder hpEq
    rw [hrepL] at hqOrder hroundLate
    have hval : bE.val + 1 ≤ bL.val := by
      apply Nat.add_one_le_iff.mpr
      exact_mod_cast (show (bE.val : ℝ) < (bL.val : ℝ) by
        by_contra hnot
        have hle : (bL.val : ℝ) ≤ (bE.val : ℝ) := le_of_not_gt hnot
        have hmul := mul_le_mul_of_nonneg_right hle hη.le
        linarith)
    have hcast : ((bE.val + 1 : ℕ) : ℝ) ≤ (bL.val : ℝ) := by
      exact_mod_cast hval
    have hgap := mul_le_mul_of_nonneg_right hcast hη.le
    push_cast at hgap
    nlinarith
  · have hover : (d : ℝ) * η < pLate := lt_of_not_ge hLateCap
    have hpEθ := growing_early_actual_le_threshold d hη hpEarly hBgrid hθB hearly
    linarith

/-- With all selected processing times at most `B`, the crude bad-sample
loss of the stationary schedule is at most `B/2`. -/
theorem finite_boundedEarly_directFluid_le_offline_add_half_B
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (B : ℝ) (hB1 : 1 ≤ B) (early : Fin n → Bool)
    (hEarly : ∀ i, early i = true → p i ≤ B)
    (hordered : ∀ i j, early i = true → early j = false → p i ≤ p j) :
    (1 + weightedMoment (earlyJobWeight early) p) *
          (1 - weightedMass (earlyJobWeight early) / 2) +
        weightedMinPair (lateJobWeight early) p / 2 ≤
      finiteOfflineFluid p + B / 2 := by
  let a := weightedMass (earlyJobWeight early)
  let m := weightedMoment (earlyJobWeight early) p
  let h := weightedMass (lateJobWeight early)
  let KE := weightedMinPair (earlyJobWeight early) p
  let KL := weightedMinPair (lateJobWeight early) p
  have ha0 : 0 ≤ a := by
    dsimp [a]
    unfold weightedMass earlyJobWeight
    positivity
  have hmass := weightedMass_late_eq_one_sub_early hn early
  have ha1 : a ≤ 1 := by
    have hh0 : 0 ≤ h := by
      dsimp [h]
      unfold weightedMass lateJobWeight
      positivity
    dsimp [a, h] at hmass ⊢
    linarith
  have hmB : m ≤ B * a := by
    unfold m a weightedMoment weightedMass
    calc
      (∑ i, earlyJobWeight early i * p i) ≤
          ∑ i, earlyJobWeight early i * B := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : early i = true
        · exact mul_le_mul_of_nonneg_left (hEarly i hi) (by
            simp [earlyJobWeight, hi])
        · have hiFalse : early i = false := Bool.eq_false_of_not_eq_true hi
          simp [earlyJobWeight, hiFalse]
      _ = B * ∑ i, earlyJobWeight early i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hKE0 : 0 ≤ KE := by
    dsimp [KE]
    unfold weightedMinPair earlyJobWeight
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (le_min (hp i) (hp j))
  have hsplit := uniformMinPair_split early p hordered
  have hcorner : 1 - a + a * m - KE ≤ B := by
    have ham := mul_le_mul_of_nonneg_left hmB ha0
    have haa : a ^ 2 ≤ a := by nlinarith
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
    have hBaa := mul_le_mul_of_nonneg_left haa hB0
    have hBa : 1 - a + B * a ≤ B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hB1) (sub_nonneg.mpr ha1)]
    nlinarith
  have hid :
      (1 + m) * (1 - a / 2) + KL / 2 =
        (1 + (KE + 2 * h * m + KL)) / 2 +
          (1 - a + a * m - KE) / 2 := by
    have hmass' : h = 1 - a := by simpa [h, a] using hmass
    rw [hmass']
    ring
  unfold finiteOfflineFluid
  rw [hsplit]
  change (1 + m) * (1 - a / 2) + KL / 2 ≤
    (1 + (KE + 2 * h * m + KL)) / 2 + B / 2
  rw [hid]
  linarith

/-- A good sample for the growing learner yields the robust `4/3` fluid
certificate with the cutoff-parametric slack from the paper. -/
theorem growing_goodLearned_fluid_certificate
    {n : ℕ} (hn : 0 < n)
    (samplePositions : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (d : ℕ) {B η θHat : ℝ} (hη : 0 < η)
    (hB : 0 < B) (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hθHat0 : 0 ≤ θHat) (hθHatB : θHat ≤ B)
    (hDensityHat :
      1 + selectedMoment
        (fun b => sampleCategoryFraction samplePositions
          (categoryClass (fun i => quantizedCategory d η (p i) hη) b) σ)
        (Online.growingQuantizedRepresentative d η)
        (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat) =
      selectedMass
        (fun b => sampleCategoryFraction samplePositions
          (categoryClass (fun i => quantizedCategory d η (p i) hη) b) σ)
        (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat) * θHat)
    (hgood : histogramL1Error samplePositions
      (fun i => quantizedCategory d η (p i) hη) σ ≤
        1 / (B * (B + 1))) :
    let early := growingLearnedEarly d η hη p θHat
    let a := weightedMass (earlyJobWeight early)
    let m := weightedMoment (earlyJobWeight early) p
    let θ := (1 + m) / a
    stationaryFluidCost θ a (weightedMinPair (lateJobWeight early) p) ≤
      4 / 3 * finiteOfflineFluid p +
        2 / 3 * (2 * B * (B + 1) *
          histogramL1Error samplePositions
            (fun i => quantizedCategory d η (p i) hη) σ +
          (B + 2) * η) := by
  dsimp only
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let c := fun i => quantizedCategory d η (p i) hη
  let q := Online.growingQuantizedRepresentative d η
  let selected := thresholdClosure q θHat
  let μ := fun b => ((categoryClass c b).card : ℝ) / n
  let μHat := fun b => sampleCategoryFraction samplePositions
    (categoryClass c b) σ
  let Δ := histogramL1Error samplePositions c σ
  let early := growingLearnedEarly d η hη p θHat
  let a := weightedMass (earlyJobWeight early)
  let m := weightedMoment (earlyJobWeight early) p
  let θ := (1 + m) / a
  let distance := 2 * B * (B + 1) * Δ + (B + 1) * η
  let s := distance + η
  have htransfer := growing_learned_histogram_transfer
    samplePositions σ d hη hB.le hBgrid hθHatB p hp
  dsimp only at htransfer
  have haEq : a = selectedMass μ selected := by
    dsimp [a, early, μ, selected, c, q]
    exact growingLearnedEarly_mass_eq_populationMass hn d hη p
  have hmEq : m =
      (∑ i, p i * (if selected (c i) then 1 else 0)) / n := by
    dsimp [m, early, selected, c, q]
    exact growingLearnedEarly_moment_eq_populationMoment d hη p
  have hMass : |a - selectedMass μHat selected| ≤ Δ := by
    rw [haEq]
    simpa [μ, μHat, selected, c, Δ] using htransfer.1
  have hMoment : |m - selectedMoment μHat q selected| ≤ B * Δ + η := by
    rw [hmEq]
    simpa [μHat, selected, c, q, Δ] using htransfer.2
  have hmHat0 : 0 ≤ selectedMoment μHat q selected := by
    unfold selectedMoment
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg
      (mul_nonneg (by
        dsimp [μHat]
        unfold sampleCategoryFraction permutationSampleSum categoryIndicator
        positivity) (Online.growingQuantizedRepresentative_nonneg d hη.le b))
      (by positivity)
  have haHat : 1 / B ≤ selectedMass μHat selected :=
    growing_sample_mass_lower hB hmHat0 hθHat0 hθHatB
      (by simpa [μHat, selected, c, q] using hDensityHat)
  have haLower : 1 / (B + 1) ≤ a :=
    growing_population_mass_lower hB haHat hgood hMass
  have haPos : 0 < a :=
    lt_of_lt_of_le (one_div_pos.mpr (by linarith [hB])) haLower
  have hdistance : |θ - θHat| ≤ distance := by
    dsimp [θ, distance]
    exact growing_threshold_distance hB haLower hθHat0 hθHatB hMass hMoment
      rfl (by simpa [μHat, selected, c, q] using hDensityHat)
  have hDensity : m = a * θ - 1 := by
    dsimp [θ]
    field_simp [haPos.ne']
    ring
  have hs0 : 0 ≤ s := by
    have hdist0 : 0 ≤ distance :=
      (abs_nonneg (θ - θHat)).trans hdistance
    dsimp [s]
    linarith [hη]
  have hθPos : 0 < θ := by
    have hm0 : 0 ≤ m := by
      unfold m weightedMoment
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (by
          unfold earlyJobWeight early growingLearnedEarly
          split_ifs <;> positivity) (hp i)
    dsimp [θ]
    exact div_pos (by linarith) haPos
  have hEarly : ∀ i, early i = true → p i ≤ θ + s := by
    intro i hi
    have hsel : selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hpHat := growing_early_actual_le_threshold
      d hη (hp i) hBgrid hθHatB hsel
    have hrobust := robust_separation_from_threshold_distance
      (p := p i) hdistance hη.le
    dsimp [s, distance]
    nlinarith [hrobust.1 hpHat]
  have hLate : ∀ i, early i = false → θ - s ≤ p i := by
    intro i hi
    have hlate : ¬ selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hpHat := growing_late_actual_ge_threshold_sub_eta
      d hη (hp i) hBgrid hθHatB hlate
    have hrobust := robust_separation_from_threshold_distance
      (p := p i) hdistance hη.le
    dsimp [s, distance]
    nlinarith [hrobust.2 hpHat]
  have hordered : ∀ i j, early i = true → early j = false → p i ≤ p j := by
    intro i j hi hj
    have hsel : selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hlate : ¬ selected (c j) := by
      dsimp [early, selected, c, q] at hj ⊢
      simpa using hj
    exact growing_threshold_split_ordered d hη hBgrid hθHat0 hθHatB
      (hp i) (hp j) hsel hlate
  have hcert := finiteApproximateThreshold_fluid_le_four_thirds
    hn p hp early hθPos hs0 hEarly hLate hordered hDensity
  dsimp [s, distance, Δ, c, early, a, m, θ] at hcert ⊢
  convert hcert using 1 <;> ring

theorem growingLearnedEarlyFor_eq_growingLearnedEarly
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) {θHat : ℝ}
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = some θHat) :
    growingLearnedEarlyFor k r d B η hη p =
      growingLearnedEarly d η hη p θHat := by
  funext i
  unfold growingLearnedEarlyFor Online.growingLearnedClassifiesEarly
    growingLearnedEarly
  rw [hlearn]

theorem growingLearnedEarlyFor_eq_false_of_none
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ)
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = none) :
    growingLearnedEarlyFor k r d B η hη p = fun _ => false := by
  funext i
  unfold growingLearnedEarlyFor Online.growingLearnedClassifiesEarly
  rw [hlearn]

/-- Complete deterministic good-learned bound for one outer relabelling. -/
theorem growing_learned_good_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB : 0 < B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θHat : ℝ}
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = some θHat)
    (hgood : histogramL1Error (firstBlockPositions k r)
      (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) ≤
        1 / (B * (B + 1))) :
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (4 / 3 * B * (B + 1) *
              histogramL1Error (firstBlockPositions k r)
                (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) +
            2 / 3 * (B + 2) * η) +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let sample := firstBlockPositions k r
  let c := fun i : Fin (k + r) => quantizedCategory d η (p i) hη
  let Δ := histogramL1Error sample c (Equiv.refl _)
  let earlyθ := growingLearnedEarly d η hη p θHat
  have hclosure := Online.growingLearnedThresholdFromResults_closure_certificate
    B d η hη ((Online.fixedTestResults p).take k) hlearn
  dsimp only at hclosure
  have hhist := resultCategoryFraction_fixedTake_eq_sampleHistogram
    k r d η hη p
  rw [hhist] at hclosure
  have hfluidθ := growing_goodLearned_fluid_certificate
    hn sample (Equiv.refl _) d hη hB hBgrid p hp
      hclosure.1 hclosure.2.1 hclosure.2.2 hgood
  dsimp only at hfluidθ
  have htransfer := growing_learned_histogram_transfer
    sample (Equiv.refl _) d hη hB.le hBgrid hclosure.2.1 p hp
  dsimp only at htransfer
  have hmHat0 : 0 ≤ selectedMoment
      (fun b => sampleCategoryFraction sample
        (categoryClass c b) (Equiv.refl _))
      (Online.growingQuantizedRepresentative d η)
      (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat) := by
    unfold selectedMoment
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg
      (mul_nonneg (by
        unfold sampleCategoryFraction permutationSampleSum categoryIndicator
        positivity) (Online.growingQuantizedRepresentative_nonneg d hη.le b))
      (by positivity)
  have haHat : 1 / B ≤ selectedMass
      (fun b => sampleCategoryFraction sample
        (categoryClass c b) (Equiv.refl _))
      (thresholdClosure (Online.growingQuantizedRepresentative d η) θHat) :=
    growing_sample_mass_lower hB hmHat0 hclosure.1 hclosure.2.1
      (by simpa [sample, c] using hclosure.2.2)
  have haLower : 1 / (B + 1) ≤
      weightedMass (earlyJobWeight earlyθ) := by
    apply growing_population_mass_lower hB haHat hgood
    rw [growingLearnedEarly_mass_eq_populationMass hn d hη p]
    simpa [Fintype.card_fin, sample, c] using htransfer.1
  have haPos : 0 < weightedMass (earlyJobWeight earlyθ) :=
    lt_of_lt_of_le (one_div_pos.mpr (by linarith [hB])) haLower
  have hscalarEq := stationaryScalarCost_eq_finiteFluid hn p earlyθ haPos
  have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
  let s := 2 * B * (B + 1) * Δ + (B + 2) * η
  have hs : 0 ≤ s := by
    have hΔ0 : 0 ≤ Δ := by
      dsimp [Δ]
      unfold histogramL1Error
      positivity
    have hB2 : 0 ≤ B + 2 := by linarith [hB]
    dsimp [s]
    positivity
  have hstationary :
      stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) ≤
        4 / 3 * finiteObligatoryOPT p +
          (k + r : ℝ) ^ 2 *
            (4 / 3 * B * (B + 1) * Δ + 2 / 3 * (B + 2) * η) := by
    have hfinite := finite_goodLearned_cost_bound
      (n := (k + r : ℝ))
      (e := earlyMassCount earlyθ)
      (sumP := ∑ i, p i)
      (P := stationaryFluidCost
        ((1 + weightedMoment (earlyJobWeight earlyθ) p) /
          weightedMass (earlyJobWeight earlyθ))
        (weightedMass (earlyJobWeight earlyθ))
        (weightedMinPair (lateJobWeight earlyθ) p))
      (O := finiteOfflineFluid p)
      (s := s)
      (ideal := stationaryScalarCost (k + r)
        (earlyMassCount earlyθ)
        ((∑ i, discoveryBlock p earlyθ i) - (k + r))
        (classifiedLateWork (baseClassifiedJobs p earlyθ))
        (classifiedLatePairMin (baseClassifiedJobs p earlyθ)))
      (actual := stationaryScalarCost (k + r)
        (earlyMassCount earlyθ)
        ((∑ i, discoveryBlock p earlyθ i) - (k + r))
        (classifiedLateWork (baseClassifiedJobs p earlyθ))
        (classifiedLatePairMin (baseClassifiedJobs p earlyθ)))
      (overhead := 0)
      (finiteOpt := finiteObligatoryOPT p)
      (by positivity) (earlyMassCount_nonneg _)
      (by simpa only [Nat.cast_add] using earlyMassCount_le_card earlyθ)
      hsum hs hfluidθ
      (by simpa only [Nat.cast_add] using hscalarEq) (by linarith)
      (by unfold finiteObligatoryOPT finiteOfflineCorrection; rw [Nat.cast_add])
    dsimp [s] at hfinite
    nlinarith
  have hsample := growingLearnedSampleFirstScalarCost_le_stationary_add
    k r d B η hη hB.le hBgrid p hp
  rw [growingLearnedEarlyFor_eq_growingLearnedEarly
    k r d B η hη p hlearn] at hsample
  dsimp [Δ, sample, c] at hstationary ⊢
  linarith

/-- Crude learned-mode bound used on bad samples. -/
theorem growing_learned_crude_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB1 : 1 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θHat : ℝ}
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = some θHat) :
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      finiteObligatoryOPT p + B / 2 * (k + r : ℝ) ^ 2 +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  let earlyθ := growingLearnedEarly d η hη p θHat
  have hclosure := Online.growingLearnedThresholdFromResults_closure_certificate
    B d η hη ((Online.fixedTestResults p).take k) hlearn
  dsimp only at hclosure
  have hEarly : ∀ i, earlyθ i = true → p i ≤ B := by
    intro i hi
    exact (growing_early_actual_le_threshold d (B := B) (θ := θHat)
      hη (hp i) hBgrid hclosure.2.1
      (by simpa [earlyθ, growingLearnedEarly] using hi)).trans hclosure.2.1
  have hordered : ∀ i j, earlyθ i = true → earlyθ j = false → p i ≤ p j := by
    intro i j hi hj
    exact growing_threshold_split_ordered d (B := B) (θ := θHat)
      hη hBgrid hclosure.1 hclosure.2.1
      (hp i) (hp j)
      (by simpa [earlyθ, growingLearnedEarly] using hi)
      (by simpa [earlyθ, growingLearnedEarly] using hj)
  have hfluid := finite_boundedEarly_directFluid_le_offline_add_half_B
    hn p hp B hB1 earlyθ hEarly hordered
  have hscalarEq := stationaryScalarCost_eq_directFiniteFluid hn p earlyθ
  have hcorr : (earlyMassCount earlyθ + ∑ i, p i) / 2 ≤
      finiteOfflineCorrection p := by
    unfold finiteOfflineCorrection
    have he := earlyMassCount_le_card earlyθ
    nlinarith
  have hstationary :
      stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) ≤
        finiteObligatoryOPT p + B / 2 * (k + r : ℝ) ^ 2 := by
    unfold finiteObligatoryOPT
    simp only [Nat.cast_add]
    rw [show stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) =
        (↑k + ↑r) ^ 2 *
            ((1 + weightedMoment (earlyJobWeight earlyθ) p) *
                (1 - weightedMass (earlyJobWeight earlyθ) / 2) +
              weightedMinPair (lateJobWeight earlyθ) p / 2) +
          (earlyMassCount earlyθ + ∑ i, p i) / 2 by
      simpa only [Nat.cast_add] using hscalarEq]
    have hn2 : 0 ≤ (↑k + ↑r : ℝ) ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left hfluid hn2
    linarith
  have hsample := growingLearnedSampleFirstScalarCost_le_stationary_add
    k r d B η hη (le_trans (by norm_num) hB1) hBgrid p hp
  rw [growingLearnedEarlyFor_eq_growingLearnedEarly
    k r d B η hη p hlearn] at hsample
  linarith

theorem growing_fallback_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB0 : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = none) :
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      finiteObligatoryOPT p + (k + r : ℝ) ^ 2 / 2 +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  have hsample := growingLearnedSampleFirstScalarCost_le_stationary_add
    k r d B η hη hB0 hBgrid p hp
  rw [growingLearnedEarlyFor_eq_false_of_none
    k r d B η hη p hlearn] at hsample
  have hstationary := stationaryScalarCost_allLate_le_opt_add_half hn p
  simp only [Nat.cast_add] at hstationary
  linarith

/-- Rounding a true threshold closure to the growing grid loses at most one
mesh cell in its reciprocal density. -/
theorem growing_quantized_threshold_gridDensity_lower
    {n : ℕ} (hn : 0 < n)
    (d : ℕ) {B η θ : ℝ} (hη : 0 < η)
    (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hθ : 0 < θ) (hwithin : θ + η ≤ B)
    (hdensity :
      1 + selectedMoment (uniformJobWeight n) p (fun i => p i ≤ θ) =
        θ * selectedMass (uniformJobWeight n) (fun i => p i ≤ θ)) :
    1 / (θ + η) ≤
      subsetDensity
        (fun b => ((categoryClass
          (fun i => quantizedCategory d η (p i) hη) b).card : ℝ) / n)
        (Online.growingQuantizedRepresentative d η)
        (Finset.univ.filter fun b =>
          Online.growingQuantizedRepresentative d η b ≤ θ + η) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let c := fun i : Fin n => quantizedCategory d η (p i) hη
  let q := Online.growingQuantizedRepresentative d η
  let μ := fun b : QuantizedCategory d =>
    ((categoryClass c b).card : ℝ) / n
  let selectedGrid := fun b : QuantizedCategory d => q b ≤ θ + η
  let J := Finset.univ.filter selectedGrid
  let trueSelected := fun i : Fin n => p i ≤ θ
  let a := selectedMass (uniformJobWeight n) trueSelected
  let m := selectedMoment (uniformJobWeight n) p trueSelected
  let A := selectedMass μ selectedGrid
  let M := selectedMoment μ q selectedGrid
  have hθη : 0 < θ + η := add_pos hθ hη
  have hsub : ∀ i, trueSelected i → selectedGrid (c i) := by
    intro i hi
    dsimp [trueSelected, selectedGrid, c, q] at hi ⊢
    have hcap : p i ≤ (d : ℝ) * η :=
      (hi.trans (by linarith)).trans (hwithin.trans hBgrid)
    have hround := (Online.growingQuantized_rounding_bounds
      d hη (hp i) hcap).2
    linarith
  have hpoint : ∀ i,
      q (c i) * (if selectedGrid (c i) then 1 else 0) ≤
        p i * (if trueSelected i then 1 else 0) +
          η * (if trueSelected i then 1 else 0) +
          (θ + η) *
            ((if selectedGrid (c i) then 1 else 0) -
              (if trueSelected i then 1 else 0)) := by
    intro i
    by_cases hi : trueSelected i
    · have hgi := hsub i hi
      have hcap : p i ≤ (d : ℝ) * η := by
        dsimp [trueSelected] at hi
        exact (hi.trans (by linarith)).trans (hwithin.trans hBgrid)
      have hq := (Online.growingQuantized_rounding_bounds
        d hη (hp i) hcap).2
      simp [hi, hgi]
      linarith
    · by_cases hgi : selectedGrid (c i)
      · have hq : q (c i) ≤ θ + η := hgi
        simp [hi, hgi]
        exact hq
      · simp [hi, hgi]
  have hsum := Finset.sum_le_sum fun i
      (_hi : i ∈ (Finset.univ : Finset (Fin n))) => hpoint i
  have hAeq : A =
      (∑ i, if selectedGrid (c i) then (1 : ℝ) else 0) / n := by
    dsimp [A, μ]
    simpa only [Fintype.card_fin] using
      (selectedMass_population_eq_jobAverage c selectedGrid)
  have hMeq : M =
      (∑ i, q (c i) * (if selectedGrid (c i) then 1 else 0)) / n := by
    dsimp [M, μ]
    simpa only [Fintype.card_fin] using
      (selectedMoment_population_eq_jobAverage c q selectedGrid)
  have haeq : a =
      (∑ i, if trueSelected i then (1 : ℝ) else 0) / n := by
    unfold a selectedMass uniformJobWeight
    rw [show (fun i : Fin n =>
        (1 / (n : ℝ)) * (if trueSelected i then 1 else 0)) =
      fun i => (if trueSelected i then (1 : ℝ) else 0) / (n : ℝ) by
        funext i
        ring]
    rw [Finset.sum_div]
  have hmeq : m =
      (∑ i, p i * (if trueSelected i then 1 else 0)) / n := by
    unfold m selectedMoment uniformJobWeight
    rw [show (fun i : Fin n =>
        (1 / (n : ℝ)) * p i * (if trueSelected i then 1 else 0)) =
      fun i => (p i * (if trueSelected i then 1 else 0)) / n by
        funext i
        ring]
    rw [Finset.sum_div]
  have hM : M ≤ m + η * a + (θ + η) * (A - a) := by
    rw [hMeq, hmeq, haeq, hAeq]
    calc
      (∑ i, q (c i) * (if selectedGrid (c i) then 1 else 0)) / n ≤
          (∑ i : Fin n,
            ((p i * (if trueSelected i then 1 else 0) +
                η * (if trueSelected i then 1 else 0)) +
              (θ + η) *
                ((if selectedGrid (c i) then 1 else 0) -
                  (if trueSelected i then 1 else 0)))) / n :=
        div_le_div_of_nonneg_right hsum (by positivity)
      _ =
          (∑ i, p i * (if trueSelected i then 1 else 0)) / n +
            η * ((∑ i, if trueSelected i then 1 else 0) / n) +
            (θ + η) *
              ((∑ i, if selectedGrid (c i) then 1 else 0) / n -
                (∑ i, if trueSelected i then 1 else 0) / n) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
        ring
  have ha0 : 0 ≤ a := by
    dsimp [a]
    unfold selectedMass uniformJobWeight
    positivity
  have haPos : 0 < a := by
    have hm0 : 0 ≤ m := by
      dsimp [m]
      unfold selectedMoment uniformJobWeight
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (mul_nonneg (by positivity) (hp i)) (by positivity)
    have hdensityAM : 1 + m = θ * a := by
      simpa [a, m, trueSelected] using hdensity
    by_contra hnot
    have haZero : a = 0 := le_antisymm (le_of_not_gt hnot) ha0
    nlinarith
  have hApos : 0 < A := by
    have haLeA : a ≤ A := by
      rw [haeq, hAeq]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : trueSelected i
      · simp [hi, hsub i hi]
      · by_cases hgi : selectedGrid (c i) <;> simp [hi, hgi]
    exact lt_of_lt_of_le haPos haLeA
  have hdenGrid : 1 + M ≤ A * (θ + η) := by
    have hdensityAM : 1 + m = θ * a := by
      simpa [a, m, trueSelected] using hdensity
    nlinarith
  have hM0 : 0 ≤ M := by
    unfold M selectedMoment
    exact Finset.sum_nonneg fun b _ =>
      mul_nonneg
        (mul_nonneg (by dsimp [μ]; positivity)
          (Online.growingQuantizedRepresentative_nonneg d hη.le b))
        (by positivity)
  have hdenPos : 0 < 1 + M := by linarith
  have hratio : 1 / (θ + η) ≤ A / (1 + M) := by
    rw [div_le_div_iff₀ hθη hdenPos]
    nlinarith
  unfold subsetDensity
  change 1 / (θ + η) ≤ subsetMass μ J / (1 + subsetMoment μ q J)
  have hmassJ : subsetMass μ J = A := by
    unfold J A subsetMass selectedMass selectedGrid
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : q b ≤ θ + η <;> simp [hb]
  have hmomJ : subsetMoment μ q J = M := by
    unfold J M subsetMoment selectedMoment selectedGrid
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : q b ≤ θ + η <;> simp [hb]
  rw [hmassJ, hmomJ]
  exact hratio

theorem growingResultMaximumDensity_fallback_lt
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η) (hB : 0 < B)
    (results : List (Online.Label n × ℝ))
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη results = none) :
    subsetDensity
        (Online.resultCategoryFraction d η hη results)
        (Online.growingQuantizedRepresentative d η)
        (Online.growingResultMaximumDensitySet d η hη results) < 1 / B := by
  let μ := Online.resultCategoryFraction d η hη results
  let q := Online.growingQuantizedRepresentative d η
  let selected := Online.growingResultMaximumDensitySet d η hη results
  have hμ : ∀ b, 0 ≤ μ b :=
    Online.resultCategoryFraction_nonneg d η hη results
  have hq : ∀ b, 0 ≤ q b :=
    Online.growingQuantizedRepresentative_nonneg d hη.le
  have ha0 : 0 ≤ subsetMass μ selected := subsetMass_nonneg hμ selected
  have hm0 : 0 ≤ subsetMoment μ q selected :=
    subsetMoment_nonneg hμ hq selected
  unfold Online.growingLearnedThresholdFromResults? at hlearn
  dsimp only at hlearn
  split at hlearn
  next ha =>
    split at hlearn
    next => simp at hlearn
    next hθ =>
      have hθlt : B < (1 + subsetMoment μ q selected) /
          subsetMass μ selected := lt_of_not_ge hθ
      unfold subsetDensity
      have hden : 0 < 1 + subsetMoment μ q selected := by linarith
      apply (div_lt_iff₀ hden).2
      have hcross := (lt_div_iff₀ ha).1 hθlt
      have hBden : 0 < B * (1 + subsetMoment μ q selected) :=
        mul_pos hB hden
      field_simp [hB.ne'] at hcross ⊢
      nlinarith
  next ha =>
    have haZero : subsetMass μ selected = 0 :=
      le_antisymm (le_of_not_gt ha) ha0
    unfold subsetDensity
    rw [haZero, zero_div]
    exact one_div_pos.mpr hB

theorem growing_fallback_threshold_ge_quarter
    {B θ η ρGrid : ℝ}
    (hB : 0 < B) (hθ : 0 < θ) (hη0 : 0 ≤ η)
    (hη : η ≤ B / 12)
    (hρ : ρGrid < 3 / B)
    (hgrid : θ + η ≤ B → 1 / (θ + η) ≤ ρGrid) :
    B / 4 ≤ θ := by
  by_cases hwithin : θ + η ≤ B
  · have hsum : 0 < θ + η := add_pos_of_pos_of_nonneg hθ hη0
    have hrecip : 1 / (θ + η) < 3 / B := (hgrid hwithin).trans_lt hρ
    have hcross := (div_lt_div_iff₀ hsum hB).1 hrecip
    norm_num at hcross
    nlinarith
  · have hout : B < θ + η := lt_of_not_ge hwithin
    nlinarith

/-- On a good sample, fallback certifies a large true offline value, so the
safe test-all branch is already below `4 OPT / 3`. -/
theorem growing_fallback_good_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB32 : 32 ≤ B)
    (hcutoff : (d : ℝ) * η = B) (hηUpper : η ≤ B / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hlearn : Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) = none)
    (hgood : histogramL1Error (firstBlockPositions k r)
      (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) ≤
        1 / (B * (B + 1))) :
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      4 / 3 * finiteObligatoryOPT p +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB32
  have hBgrid : B ≤ (d : ℝ) * η := hcutoff.ge
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let n := k + r
  let sample := firstBlockPositions k r
  let c := fun i : Fin n => quantizedCategory d η (p i) hη
  let q := Online.growingQuantizedRepresentative d η
  let Δ := histogramL1Error sample c (Equiv.refl _)
  let μTrue := uniformJobWeight n
  let trueSet := chosenMaximumDensitySubset μTrue p
  have hmaxTrue : IsMaximumDensitySubset μTrue p trueSet :=
    chosenMaximumDensitySubset_isMaximum μTrue p
  have hμTruePos : ∀ i, 0 < μTrue i := by
    intro i
    dsimp [μTrue, uniformJobWeight, n]
    positivity
  have haTrue : 0 < subsetMass μTrue trueSet :=
    maximumDensitySubset_mass_pos hμTruePos hp hmaxTrue
  let θ := (1 + subsetMoment μTrue p trueSet) /
    subsetMass μTrue trueSet
  have hθPos : 0 < θ := by
    dsimp [θ]
    exact inverseDensity_pos (fun i => (hμTruePos i).le) hp haTrue
  have htrueClosureRaw := maximumDensity_thresholdClosure_preserves
    (fun i => (hμTruePos i).le) hp hmaxTrue haTrue
    (inverseDensity_identity haTrue)
  have htrueClosure :
      1 + selectedMoment μTrue p (fun i => p i ≤ θ) =
        θ * selectedMass μTrue (fun i => p i ≤ θ) := by
    simpa [thresholdClosure, θ] using htrueClosureRaw
  let μPop := fun b : QuantizedCategory d =>
    ((categoryClass c b).card : ℝ) / n
  let μSample := fun b : QuantizedCategory d =>
    sampleCategoryFraction sample (categoryClass c b) (Equiv.refl _)
  let gridSet := chosenMaximumDensitySubset μPop q
  let ρGrid := subsetDensity μPop q gridSet
  have hgridSetMax : IsMaximumDensitySubset μPop q gridSet :=
    chosenMaximumDensitySubset_isMaximum μPop q
  have hgrid : θ + η ≤ B → 1 / (θ + η) ≤ ρGrid := by
    intro hwithin
    let T := Finset.univ.filter fun b : QuantizedCategory d => q b ≤ θ + η
    have hlower : 1 / (θ + η) ≤ subsetDensity μPop q T := by
      exact growing_quantized_threshold_gridDensity_lower hn d hη hBgrid p hp
        hθPos hwithin (by simpa [μTrue, μPop, c, q, n, T] using htrueClosure)
    exact hlower.trans (hgridSetMax T)
  have hhist := resultCategoryFraction_fixedTake_eq_sampleHistogram
    k r d η hη p
  have hsampleMax := growingResultMaximumDensity_fallback_lt
    B d η hη hB ((Online.fixedTestResults p).take k) hlearn
  have hmaxSample := Online.growingResultMaximumDensitySet_isMaximum
    d η hη ((Online.fixedTestResults p).take k)
  have hsampleJ : subsetDensity μSample q gridSet < 1 / B := by
    have hle := hmaxSample gridSet
    have hlt := hle.trans_lt hsampleMax
    simpa [μSample, q, hhist] using hlt
  have hΔ0 : 0 ≤ Δ := by
    dsimp [Δ]
    unfold histogramL1Error
    positivity
  have hMass : |subsetMass μPop gridSet - subsetMass μSample gridSet| ≤ Δ := by
    have h := selectedMass_population_sample_le_histogramL1Error
      sample c (Equiv.refl _) (fun b => b ∈ gridSet)
    simpa [μPop, μSample, Δ, n, subsetMass, selectedMass,
      Fintype.card_fin] using h
  let top := (d + 1 : ℕ) * η
  have htop0 : 0 ≤ top := by dsimp [top]; positivity
  have hMoment : |subsetMoment μPop q gridSet -
      subsetMoment μSample q gridSet| ≤ top * Δ := by
    have h := selectedMoment_population_sample_le_histogramL1Error
      (B := top) sample c (Equiv.refl _) q (fun b => b ∈ gridSet)
      htop0 (Online.growingQuantizedRepresentative_nonneg d hη.le)
      (fun b _ => growingQuantizedRepresentative_le_top d η hη b)
    simpa [μPop, μSample, Δ, n, subsetMoment, selectedMoment,
      Fintype.card_fin, top] using h
  have hPopMass0 : 0 ≤ subsetMass μPop gridSet := by
    apply subsetMass_nonneg
    intro b
    dsimp [μPop]
    positivity
  have hSampleMass0 : 0 ≤ subsetMass μSample gridSet := by
    apply subsetMass_nonneg
    intro b
    dsimp [μSample]
    unfold sampleCategoryFraction permutationSampleSum categoryIndicator
    positivity
  have hSampleMass1 : subsetMass μSample gridSet ≤ 1 := by
    dsimp [μSample]
    exact subsetMass_sampleCategoryFraction_le_one sample
      (firstBlockPositions_nonempty (r := r) hk) c (Equiv.refl _) gridSet
  have hPopMoment0 : 0 ≤ subsetMoment μPop q gridSet :=
    subsetMoment_nonneg
      (fun b => by dsimp [μPop]; positivity)
      (Online.growingQuantizedRepresentative_nonneg d hη.le) gridSet
  have hSampleMoment0 : 0 ≤ subsetMoment μSample q gridSet :=
    subsetMoment_nonneg
      (fun b => by
        dsimp [μSample]
        unfold sampleCategoryFraction permutationSampleSum categoryIndicator
        positivity)
      (Online.growingQuantizedRepresentative_nonneg d hη.le) gridSet
  have hdensityTransfer := subsetDensity_le_of_mass_moment_error
    hPopMass0 hSampleMass0 hSampleMass1 hPopMoment0 hSampleMoment0
    hΔ0 htop0 hMass hMoment
  have htopLe : top ≤ 2 * (B + 1) - 1 := by
    have hetaB : η ≤ B := hηUpper.trans (by nlinarith [hB32])
    dsimp [top]
    push_cast
    rw [show ((d : ℝ) + 1) * η = (d : ℝ) * η + η by ring,
      hcutoff]
    nlinarith
  have herrorTerm : (1 + top) * Δ ≤ 2 / B := by
    have hfactor0 : 0 ≤ 1 + top := by positivity
    have hscaledGood := mul_le_mul_of_nonneg_left hgood hfactor0
    have hfactorLe : 1 + top ≤ 2 * (B + 1) := by linarith
    have hden0 : 0 ≤ 1 / (B * (B + 1)) := by positivity
    have hscaledFactor := mul_le_mul_of_nonneg_right hfactorLe hden0
    calc
      (1 + top) * Δ ≤ (1 + top) * (1 / (B * (B + 1))) := hscaledGood
      _ ≤ 2 * (B + 1) * (1 / (B * (B + 1))) := by
        simpa [mul_assoc] using hscaledFactor
      _ = 2 / B := by
        field_simp [hB.ne', (show B + 1 ≠ 0 by linarith)]
  have hgridLT : ρGrid < 3 / B := by
    dsimp [ρGrid]
    unfold subsetDensity at hdensityTransfer hsampleJ ⊢
    calc
      subsetMass μPop gridSet / (1 + subsetMoment μPop q gridSet) ≤
          subsetMass μSample gridSet / (1 + subsetMoment μSample q gridSet) +
            (1 + top) * Δ := hdensityTransfer
      _ < 1 / B + 2 / B := add_lt_add_of_lt_of_le hsampleJ herrorTerm
      _ = 3 / B := by ring
  have hθQuarter := growing_fallback_threshold_ge_quarter
    hB hθPos hη.le hηUpper hgridLT hgrid
  have hθEight : 8 ≤ θ := by nlinarith [hB32]
  have hOffline : 57 / 16 ≤ finiteOfflineFluid p :=
    maximumDensity_offlineFluid_lower_B32 hn p hp trueSet hmaxTrue haTrue
      (by simpa [θ, μTrue, n] using hθEight)
  have hfallback := growing_fallback_sampleFirstCost_bound
    k r d hk hr B η hη hB.le hBgrid p hp hlearn
  have hcorrection0 : 0 ≤ finiteOfflineCorrection p := by
    unfold finiteOfflineCorrection
    have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
    positivity
  have hoptFluid : (n : ℝ) ^ 2 * finiteOfflineFluid p ≤
      finiteObligatoryOPT p := by
    unfold finiteObligatoryOPT
    exact le_add_of_nonneg_right hcorrection0
  have hbase :
      growingLearnedSampleFirstScalarCost k r d B η hη p -
          (B + 1) * (n : ℝ) * k / 2 ≤
        finiteObligatoryOPT p + (n : ℝ) ^ 2 / 2 := by
    simpa [n] using (sub_le_iff_le_add.mpr hfallback)
  have hfour := fallback_le_four_thirds
    (n := (n : ℝ)) (O := finiteOfflineFluid p)
    (opt := finiteObligatoryOPT p)
    (alg := growingLearnedSampleFirstScalarCost k r d B η hη p -
      (B + 1) * (n : ℝ) * k / 2)
    (by positivity) hOffline hoptFluid hbase
  dsimp [n] at hfour ⊢
  simp only [Nat.cast_add] at hfour ⊢
  linarith

/-- Good/bad averaging at a variable cutoff. -/
theorem expectedCost_le_of_good_bad_growing
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {cost error : Ω → ℝ} {bad : Ω → Prop} [DecidablePred bad]
    {B n opt rounding overhead : ℝ}
    (hB : 0 ≤ B) (hn : 0 ≤ n)
    (herror : ∀ ω, 0 ≤ error ω)
    (hrounding : 0 ≤ rounding) (hoverhead : 0 ≤ overhead)
    (hgood : ∀ ω, ¬ bad ω →
      cost ω ≤ 4 / 3 * opt +
        n ^ 2 * (4 / 3 * B * (B + 1) * error ω + rounding) + overhead)
    (hbad : ∀ ω, bad ω →
      cost ω ≤ 4 / 3 * opt + B / 2 * n ^ 2 + overhead)
    (hprob : uniformProbability bad ≤
      B * (B + 1) * uniformAverage error) :
    uniformAverage cost ≤
      4 / 3 * opt + n ^ 2 *
        (B * (B + 1) * (3 * B + 8) / 6 * uniformAverage error +
          rounding) + overhead := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hB1 : 0 ≤ B + 1 := by linarith
  let A := 4 / 3 * B * (B + 1)
  let E := B / 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hpoint : ∀ ω,
      cost ω ≤ 4 / 3 * opt +
        (A * n ^ 2) * error ω + n ^ 2 * rounding + overhead +
        (E * n ^ 2) * (if bad ω then 1 else 0) := by
    intro ω
    by_cases hb : bad ω
    · have h := hbad ω hb
      simp only [if_pos hb]
      have herr0 : 0 ≤ (A * n ^ 2) * error ω :=
        mul_nonneg (mul_nonneg hA0 hn2) (herror ω)
      have hr0 : 0 ≤ n ^ 2 * rounding := by positivity
      dsimp [E]
      nlinarith
    · have h := hgood ω hb
      simp only [if_neg hb]
      dsimp [A]
      nlinarith
  have havg := uniformAverage_mono hpoint
  have haffine := uniformAverage_affine_event
    (Ω := Ω) (4 / 3 * opt + n ^ 2 * rounding + overhead)
    (A * n ^ 2) (E * n ^ 2) error bad
  have hrewrite :
      uniformAverage (fun ω =>
        4 / 3 * opt + (A * n ^ 2) * error ω +
          n ^ 2 * rounding + overhead +
          (E * n ^ 2) * (if bad ω then 1 else 0)) =
        4 / 3 * opt + n ^ 2 * rounding + overhead +
          (A * n ^ 2) * uniformAverage error +
          (E * n ^ 2) * uniformProbability bad := by
    calc
      uniformAverage (fun ω =>
          4 / 3 * opt + (A * n ^ 2) * error ω +
            n ^ 2 * rounding + overhead +
            (E * n ^ 2) * (if bad ω then 1 else 0)) =
          uniformAverage (fun ω =>
            (4 / 3 * opt + n ^ 2 * rounding + overhead) +
              (A * n ^ 2) * error ω +
              (E * n ^ 2) * (if bad ω then 1 else 0)) := by
        congr 1
        funext ω
        ring
      _ = _ := haffine
  rw [hrewrite] at havg
  have hprobScaled :
      (E * n ^ 2) * uniformProbability bad ≤
        (E * n ^ 2) * (B * (B + 1) * uniformAverage error) :=
    mul_le_mul_of_nonneg_left hprob (mul_nonneg hE0 hn2)
  dsimp [A, E] at havg hprobScaled ⊢
  nlinarith

theorem expectedCost_le_histogram_growing
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (c : α → β)
    (hS : S.Nonempty) (hcard : 1 < Fintype.card α)
    (cost : Equiv.Perm α → ℝ)
    {B n opt rounding overhead : ℝ}
    (hB : 0 < B) (hn : 0 ≤ n)
    (hrounding : 0 ≤ rounding) (hoverhead : 0 ≤ overhead)
    (hgood : ∀ σ,
      ¬(1 / (B * (B + 1)) < histogramL1Error S c σ) →
      cost σ ≤ 4 / 3 * opt +
        n ^ 2 * (4 / 3 * B * (B + 1) *
          histogramL1Error S c σ + rounding) + overhead)
    (hbad : ∀ σ,
      1 / (B * (B + 1)) < histogramL1Error S c σ →
      cost σ ≤ 4 / 3 * opt + B / 2 * n ^ 2 + overhead) :
    uniformAverage cost ≤
      4 / 3 * opt + n ^ 2 *
        (B * (B + 1) * (3 * B + 8) / 6 *
          Real.sqrt ((Fintype.card β : ℝ) / S.card) + rounding) +
        overhead := by
  let error : Equiv.Perm α → ℝ := histogramL1Error S c
  have herror0 : ∀ σ, 0 ≤ error σ := fun σ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hthreshold : 0 < 1 / (B * (B + 1)) := by positivity
  have hprob :
      uniformProbability
          (fun σ : Equiv.Perm α => 1 / (B * (B + 1)) < error σ) ≤
        B * (B + 1) * uniformAverage error := by
    have hmarkov := uniformProbability_lt_le_average_div
      error herror0 hthreshold
    calc
      uniformProbability
          (fun σ : Equiv.Perm α => 1 / (B * (B + 1)) < error σ) ≤
          uniformAverage error / (1 / (B * (B + 1))) := hmarkov
      _ = B * (B + 1) * uniformAverage error := by
        field_simp [hB.ne', (show B + 1 ≠ 0 by linarith)]
  have haggregate := expectedCost_le_of_good_bad_growing
    (cost := cost) (error := error)
    (bad := fun σ => 1 / (B * (B + 1)) < error σ)
    hB.le hn herror0 hrounding hoverhead hgood hbad hprob
  have herrAvg := uniformAverage_histogramL1Error_le_sqrt S c hS hcard
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hcoeff0 : 0 ≤ B * (B + 1) * (3 * B + 8) / 6 := by
    have : 0 ≤ 3 * B + 8 := by linarith
    positivity
  have hscaled :
      n ^ 2 *
          (B * (B + 1) * (3 * B + 8) / 6 * uniformAverage error +
            rounding) ≤
        n ^ 2 *
          (B * (B + 1) * (3 * B + 8) / 6 *
            Real.sqrt ((Fintype.card β : ℝ) / S.card) + rounding) := by
    apply mul_le_mul_of_nonneg_left _ hn2
    exact add_le_add
      (mul_le_mul_of_nonneg_left herrAvg hcoeff0) le_rfl
  exact haggregate.trans (by linarith)

/-- Concentration for the exact conditional scalar cost of the growing
learner, including both learned and fallback branches. -/
theorem uniformAverage_growingLearnedSampleFirstScalarCost_four_thirds
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hnCard : 1 < k + r)
    (B η : ℝ) (hη : 0 < η) (hB32 : 32 ≤ B)
    (hcutoff : (d : ℝ) * η = B) (hηUpper : η ≤ B / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage (fun σ : Equiv.Perm (Fin (k + r)) =>
        growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ σ)) ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (B * (B + 1) * (3 * B + 8) / 6 *
              Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) +
            2 / 3 * (B + 2) * η) +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB32
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let sample := firstBlockPositions k r
  let c := fun i : Fin (k + r) => quantizedCategory d η (p i) hη
  let cost := fun σ : Equiv.Perm (Fin (k + r)) =>
    growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ σ)
  have hSample : sample.Nonempty := firstBlockPositions_nonempty (r := r) hk
  have hopt0 : 0 ≤ finiteObligatoryOPT p := by
    have hlower := finiteObligatoryOPT_lower p hp
    simp only [Nat.cast_add] at hlower
    exact (show 0 ≤ (k + r : ℝ) * ((k + r : ℝ) + 1) / 2 by
      positivity).trans hlower
  have hgood : ∀ σ : Equiv.Perm (Fin (k + r)),
      ¬(1 / (B * (B + 1)) < histogramL1Error sample c σ) →
      cost σ ≤ 4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (4 / 3 * B * (B + 1) * histogramL1Error sample c σ +
            2 / 3 * (B + 2) * η) +
        (B + 1) * (k + r : ℝ) * k / 2 := by
    intro σ hgoodσ
    have hgoodσ' :
        histogramL1Error (firstBlockPositions k r)
          (fun i => quantizedCategory d η ((p ∘ σ) i) hη)
          (Equiv.refl _) ≤ 1 / (B * (B + 1)) := by
      rw [show (fun i => quantizedCategory d η ((p ∘ σ) i) hη) =
          c ∘ σ by rfl,
        histogramL1Error_comp_perm_refl]
      dsimp [sample, c] at hgoodσ ⊢
      exact le_of_not_gt hgoodσ
    cases hlearn : Online.growingLearnedThresholdFromResults? B d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) with
    | none =>
        have hfb := growing_fallback_good_sampleFirstCost_bound
          k r d hk hr B η hη hB32 hcutoff hηUpper (p ∘ σ)
          (fun i => hp (σ i)) hlearn hgoodσ'
        have hΔ0 : 0 ≤ histogramL1Error sample c σ := by
          dsimp [sample]
          unfold histogramL1Error
          positivity
        have hn2 : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
        have hbracket : 0 ≤
            4 / 3 * B * (B + 1) * histogramL1Error sample c σ +
              2 / 3 * (B + 2) * η := by
          have hB2 : 0 ≤ B + 2 := by linarith [hB]
          positivity
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hfb
        nlinarith [mul_nonneg hn2 hbracket]
    | some θHat =>
        have hlearned := growing_learned_good_sampleFirstCost_bound
          k r d hk hr B η hη hB hcutoff.ge (p ∘ σ)
          (fun i => hp (σ i)) hlearn hgoodσ'
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hlearned
        rw [show histogramL1Error (firstBlockPositions k r)
            (fun i => quantizedCategory d η ((p ∘ σ) i) hη)
            (Equiv.refl _) = histogramL1Error sample c σ by
          rw [show (fun i => quantizedCategory d η ((p ∘ σ) i) hη) =
              c ∘ σ by rfl,
            histogramL1Error_comp_perm_refl]] at hlearned
        exact hlearned
  have hbad : ∀ σ : Equiv.Perm (Fin (k + r)),
      1 / (B * (B + 1)) < histogramL1Error sample c σ →
      cost σ ≤ 4 / 3 * finiteObligatoryOPT p +
        B / 2 * (k + r : ℝ) ^ 2 +
        (B + 1) * (k + r : ℝ) * k / 2 := by
    intro σ _hbadσ
    cases hlearn : Online.growingLearnedThresholdFromResults? B d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) with
    | none =>
        have hfb := growing_fallback_sampleFirstCost_bound
          k r d hk hr B η hη hB.le hcutoff.ge (p ∘ σ)
          (fun i => hp (σ i)) hlearn
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hfb
        have hn2 : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
        nlinarith
    | some θHat =>
        have hlearned := growing_learned_crude_sampleFirstCost_bound
          k r d hk hr B η hη (by linarith [hB32]) hcutoff.ge
          (p ∘ σ) (fun i => hp (σ i)) hlearn
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hlearned
        nlinarith [hopt0]
  have hcard : 1 < Fintype.card (Fin (k + r)) := by
    simpa only [Fintype.card_fin] using hnCard
  have havg := expectedCost_le_histogram_growing
    sample c hSample hcard cost
    (B := B) (n := (k + r : ℝ)) (opt := finiteObligatoryOPT p)
    (rounding := 2 / 3 * (B + 2) * η)
    (overhead := (B + 1) * (k + r : ℝ) * k / 2)
    hB (by positivity) (by positivity) (by positivity) hgood hbad
  simpa [sample, c, cost, firstBlockPositions_card, Fintype.card_fin,
    Nat.cast_add, Nat.cast_ofNat] using havg

/-- End-to-end uniform `4/3` estimate for the literal terminating growing
policy.  This is equation `rand-explicit-upper` of the manuscript. -/
theorem uniformAverage_physicalGrowingRunCost_four_thirds
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hnCard : 1 < k + r)
    (B η : ℝ) (hη : 0 < η) (hB32 : 32 ≤ B)
    (hcutoff : (d : ℝ) * η = B) (hηUpper : η ≤ B / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage (physicalGrowingRunCost (k + r) k d B η hη p) ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (B * (B + 1) * (3 * B + 8) / 6 *
              Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) +
            2 / 3 * (B + 2) * η) +
        (B + 1) * ((k + r : ℝ) * k / 2 + (k : ℝ) ^ 2) := by
  have hop := uniformAverage_physicalGrowingRunCost_le
    k r d hk hr B η hη (by linarith [hB32]) hcutoff.ge p hp
  have han := uniformAverage_growingLearnedSampleFirstScalarCost_four_thirds
    k r d hk hr hnCard B η hη hB32 hcutoff hηUpper p hp
  linarith

end

end RandomizedObligatory
end SchedulingPaper
