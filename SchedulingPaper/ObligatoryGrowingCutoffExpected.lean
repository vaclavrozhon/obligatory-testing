import SchedulingPaper.ObligatoryGrowingCutoffAnalytic
import SchedulingPaper.RandomizedOperationalExpected
import SchedulingPaper.ObligatoryTemplateLearning
import SchedulingPaper.RandomizedOptionalPilotKernel
import Mathlib.Tactic

/-!
# Expected population-template bound for the growing-cutoff policy

This module applies without-replacement pilot concentration to the actual
maximum-density learner and combines it with the literal operational run.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced
open RandomizedOptional
open ObligatoryInstance

noncomputable section

/-- Boolean grid template encoded by the growing learner, including its
all-late fallback. -/
def growingResultTemplate
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Online.Label n × ℝ)) : QuantizedCategory d → Bool :=
  match Online.growingLearnedThresholdFromResults? B d η hη results with
  | none => fun _ => false
  | some θ => fun b =>
      decide (thresholdClosure (Online.growingQuantizedRepresentative d η) θ b)

theorem growingLearnedClassifiesEarly_eq_resultTemplate
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Online.Label n × ℝ)) (p : ℝ) :
    Online.growingLearnedClassifiesEarly B d η hη results p =
      growingResultTemplate B d η hη results
        (quantizedCategory d η p hη) := by
  unfold Online.growingLearnedClassifiesEarly growingResultTemplate
  split <;> simp_all

theorem growingQuantizedRepresentative_le_top
    (d : ℕ) (η : ℝ) (hη : 0 < η) (b : QuantizedCategory d) :
    Online.growingQuantizedRepresentative d η b ≤ (d + 1 : ℕ) * η := by
  unfold Online.growingQuantizedRepresentative
  split
  · positivity
  · have hb : b.val ≤ d + 1 := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hη.le

/-- A nonempty bounded first block forces the successful learned branch. -/
theorem growingFixedPilot_uses_learnedBranch
    (k r d : ℕ) (hk : 0 < k)
    (B η L : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hgrid : L ≤ (d : ℝ) * η) (hB : 1 + L + η ≤ B) :
    Online.growingLearnedThresholdFromResults? B d η hη
      ((Online.fixedTestResults p).take k) ≠ none := by
  apply Online.boundedPilot_uses_learnedBranch B d η L hη
  · have hlen : ((Online.fixedTestResults p).take k).length = k := by
      simp [Online.fixedTestResults_length]
    intro hempty
    have := congrArg List.length hempty
    simp [hlen] at this
    omega
  · intro result hresult
    rw [List.mem_take_iff_getElem] at hresult
    obtain ⟨i, hi, hget⟩ := hresult
    unfold Online.fixedTestResults at hget
    have hpair := congrArg Prod.snd hget
    simp only [List.getElem_ofFn] at hpair
    rw [← hpair]
    exact ⟨hp0 _, hpL _⟩
  · exact hgrid
  · exact hB

theorem resultCategoryFraction_fixedTake_eq_sampleHistogram_perm
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) (σ : Equiv.Perm (Fin (k + r))) :
    Online.resultCategoryFraction d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) =
      sampleHistogram (firstBlockPositions k r)
        (fun i => quantizedCategory d η (p i) hη) σ := by
  funext b
  rw [resultCategoryFraction_fixedTake_eq_sampleCategoryFraction]
  exact sampleCategoryFraction_comp_perm_refl
    (firstBlockPositions k r)
    (fun i => quantizedCategory d η (p i) hη) σ b

/-- The actual maximum-density pilot learner enjoys the same empirical
minimizer bound as the abstract chosen-minimum template. -/
theorem uniformAverage_growingResultTemplate_le_minimum
    (k r d : ℕ) (hk : 0 < k) (hnCard : 1 < k + r)
    (B η L : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hgrid : L ≤ (d : ℝ) * η) (hB : 1 + L + η ≤ B) :
    let category := fun i => quantizedCategory d η (p i) hη
    let price := Online.growingQuantizedRepresentative d η
    uniformAverage (fun σ : Equiv.Perm (Fin (k + r)) =>
        obligatoryTemplateValue (populationHistogram category) price
          (growingResultTemplate B d η hη
            ((Online.fixedTestResults (p ∘ σ)).take k))) ≤
      minimumObligatoryTemplateValue
          (populationHistogram category) price +
        6 * ((d + 1 : ℕ) * η + 2) *
          Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) := by
  dsimp only
  let sample := firstBlockPositions k r
  let category := fun i : Fin (k + r) =>
    quantizedCategory d η (p i) hη
  let price := Online.growingQuantizedRepresentative d η
  let chosen : Equiv.Perm (Fin (k + r)) →
      (QuantizedCategory d → Bool) := fun σ =>
    growingResultTemplate B d η hη
      ((Online.fixedTestResults (p ∘ σ)).take k)
  let target := minimizingObligatoryTemplate
    (populationHistogram category) price
  have hSample : sample.Nonempty :=
    firstBlockPositions_nonempty (r := r) hk
  have hcard : 1 < Fintype.card (Fin (k + r)) := by
    simpa using hnCard
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, by omega⟩⟩
  have hprice0 : ∀ b, 0 ≤ price b :=
    Online.growingQuantizedRepresentative_nonneg d hη.le
  have hpriceTop : ∀ b, price b ≤ (d + 1 : ℕ) * η :=
    growingQuantizedRepresentative_le_top d η hη
  have hchosen : ∀ σ (T : QuantizedCategory d → Bool),
      obligatoryTemplateValue (sampleHistogram sample category σ) price
          (chosen σ) ≤
        obligatoryTemplateValue (sampleHistogram sample category σ) price T := by
    intro σ T
    have hbranch := growingFixedPilot_uses_learnedBranch
      k r d hk B η L hη (p ∘ σ) (fun i => hp0 (σ i))
        (fun i => hpL (σ i)) hgrid hB
    cases hlearn : Online.growingLearnedThresholdFromResults? B d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) with
    | none => exact (hbranch hlearn).elim
    | some θ =>
        have hmin := growingLearner_minimizes_obligatoryTemplateValue
          B d η hη ((Online.fixedTestResults (p ∘ σ)).take k) hlearn T
        rw [resultCategoryFraction_fixedTake_eq_sampleHistogram_perm
          k r d η hη p σ] at hmin
        simpa [chosen, growingResultTemplate, hlearn] using hmin
  have hstable : ∀ σ (T : QuantizedCategory d → Bool),
      |obligatoryTemplateValue (sampleHistogram sample category σ) price T -
          obligatoryTemplateValue (populationHistogram category) price T| ≤
        (3 * ((d + 1 : ℕ) * η + 2)) *
          histogramL1Error sample category σ := by
    intro σ T
    simpa [finiteL1_sampleHistogram_populationHistogram] using
      obligatoryTemplateValue_lipschitz
        (sampleHistogram_nonneg sample category σ)
        (populationHistogram_nonneg category)
        (sampleHistogram_mass_one sample hSample category σ)
        (populationHistogram_mass_one category)
        hprice0 hpriceTop T
  have hlearn := uniformSample_empirical_minimizer_le
    sample category hSample hcard
    (C := 3 * ((d + 1 : ℕ) * η + 2))
    (by
      have htop0 : 0 ≤ (d + 1 : ℕ) * η := by positivity
      positivity)
    hstable hchosen (targetMin := target)
  dsimp [sample, category, price, chosen, target,
    minimumObligatoryTemplateValue] at hlearn ⊢
  simp only [firstBlockPositions_card, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hlearn ⊢
  nlinarith

/-! ## From a categorical template to the finite stationary fluid value -/

theorem weightedMass_categoryTemplate_eq
    {n : ℕ} (hn : 0 < n) {d : ℕ}
    (category : Fin n → QuantizedCategory d)
    (early : QuantizedCategory d → Bool) :
    weightedMass (earlyJobWeight (fun i => early (category i))) =
      templateEarlyMass (populationHistogram category) early := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold templateEarlyMass
  rw [finiteExpectation_populationHistogram]
  unfold weightedMass earlyJobWeight empiricalSingleAverage
  simp only [Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : early (category i) = true <;> simp [hi]

theorem weightedMoment_categoryTemplate_eq
    {n : ℕ} (hn : 0 < n) {d : ℕ}
    (category : Fin n → QuantizedCategory d)
    (price : QuantizedCategory d → ℝ)
    (early : QuantizedCategory d → Bool) :
    weightedMoment (earlyJobWeight (fun i => early (category i)))
        (fun i => price (category i)) =
      templateEarlyMoment (populationHistogram category) price early := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold templateEarlyMoment
  rw [finiteExpectation_populationHistogram]
  unfold weightedMoment earlyJobWeight empiricalSingleAverage
  simp only [Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : early (category i) = true <;> simp [hi] <;> ring

theorem weightedMinPair_categoryTemplate_eq
    {n : ℕ} (hn : 0 < n) {d : ℕ}
    (category : Fin n → QuantizedCategory d)
    (price : QuantizedCategory d → ℝ)
    (early : QuantizedCategory d → Bool) :
    weightedMinPair (lateJobWeight (fun i => early (category i)))
        (fun i => price (category i)) =
      templateLatePair (populationHistogram category) price early := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold templateLatePair
  rw [finiteProductExpectation_populationHistogram]
  unfold weightedMinPair lateJobWeight
    empiricalProductPairAverage
  simp only [Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : early (category i) = true <;>
    by_cases hj : early (category j) = true <;> simp [hi, hj] <;> ring

/-- Upward rounding every processing time can only increase the finite
stationary fluid objective of a fixed categorical early/late template. -/
theorem directFiniteFluid_le_categoryTemplate
    {n : ℕ} (hn : 0 < n) {d : ℕ}
    (p : Fin n → ℝ) (category : Fin n → QuantizedCategory d)
    (price : QuantizedCategory d → ℝ)
    (early : QuantizedCategory d → Bool)
    (hround : ∀ i, p i ≤ price (category i)) :
    (1 + weightedMoment
          (earlyJobWeight (fun i => early (category i))) p) *
        (1 - weightedMass
          (earlyJobWeight (fun i => early (category i))) / 2) +
      weightedMinPair
          (lateJobWeight (fun i => early (category i))) p / 2 ≤
      obligatoryTemplateValue (populationHistogram category) price early := by
  let selected : Fin n → Bool := fun i => early (category i)
  let rounded : Fin n → ℝ := fun i => price (category i)
  have hmoment :
      weightedMoment (earlyJobWeight selected) p ≤
        weightedMoment (earlyJobWeight selected) rounded := by
    unfold weightedMoment
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (hround i)
    unfold earlyJobWeight
    split <;> positivity
  have hpair :
      weightedMinPair (lateJobWeight selected) p ≤
        weightedMinPair (lateJobWeight selected) rounded := by
    unfold weightedMinPair
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (min_le_min (hround i) (hround j))
    have hi : 0 ≤ lateJobWeight selected i := by
      unfold lateJobWeight
      split <;> positivity
    have hj : 0 ≤ lateJobWeight selected j := by
      unfold lateJobWeight
      split <;> positivity
    positivity
  have hmass : weightedMass (earlyJobWeight selected) ≤ 1 := by
    rw [← earlyMassCount_div_eq_weightedMass hn]
    have hcount := earlyMassCount_le_card selected
    have hnR : (0 : ℝ) < n := by positivity
    exact (div_le_one hnR).2 hcount
  have hfactor : 0 ≤
      1 - weightedMass (earlyJobWeight selected) / 2 := by
    linarith
  have hfirst :
      (1 + weightedMoment (earlyJobWeight selected) p) *
          (1 - weightedMass (earlyJobWeight selected) / 2) ≤
        (1 + weightedMoment (earlyJobWeight selected) rounded) *
          (1 - weightedMass (earlyJobWeight selected) / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hfactor
  rw [obligatoryTemplateValue,
    ← weightedMass_categoryTemplate_eq hn category early,
    ← weightedMoment_categoryTemplate_eq hn category price early,
    ← weightedMinPair_categoryTemplate_eq hn category price early]
  change _ ≤
    (1 + weightedMoment (earlyJobWeight selected) rounded) *
        (1 - weightedMass (earlyJobWeight selected) / 2) +
      weightedMinPair (lateJobWeight selected) rounded / 2
  linarith

theorem growingLearnedEarlyFor_eq_resultTemplate
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) :
    growingLearnedEarlyFor k r d B η hη p =
      fun i => growingResultTemplate B d η hη
        ((Online.fixedTestResults p).take k)
        (quantizedCategory d η (p i) hη) := by
  funext i
  exact growingLearnedClassifiesEarly_eq_resultTemplate
    B d η hη ((Online.fixedTestResults p).take k) (p i)

/-- Pointwise scalar bound for one outer relabelling.  It retains the exact
population value of the template chosen from that relabelling's pilot. -/
theorem growingLearnedSampleFirstScalarCost_le_populationTemplate
    (k r d : ℕ) (hk : 0 < k)
    (B η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hgrid : L ≤ (d : ℝ) * η) :
    let category := fun i => quantizedCategory d η (p i) hη
    let price := Online.growingQuantizedRepresentative d η
    let learned := growingResultTemplate B d η hη
      ((Online.fixedTestResults p).take k)
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      (k + r : ℝ) ^ 2 *
          obligatoryTemplateValue (populationHistogram category) price learned +
        (B + 1) * (k + r : ℝ) * k / 2 +
        (k + r : ℝ) * (1 + L) / 2 := by
  dsimp only
  have hn : 0 < k + r := Nat.add_pos_left hk r
  let category := fun i : Fin (k + r) =>
    quantizedCategory d η (p i) hη
  let price := Online.growingQuantizedRepresentative d η
  let learned := growingResultTemplate B d η hη
    ((Online.fixedTestResults p).take k)
  let early := growingLearnedEarlyFor k r d B η hη p
  have hearly : early = fun i => learned (category i) := by
    exact growingLearnedEarlyFor_eq_resultTemplate k r d B η hη p
  have hround : ∀ i, p i ≤ price (category i) := by
    intro i
    exact (Online.growingQuantized_rounding_bounds d hη (hp0 i)
      ((hpL i).trans hgrid)).1
  have hfluid := directFiniteFluid_le_categoryTemplate
    hn p category price learned hround
  have hsample := growingLearnedSampleFirstScalarCost_le_stationary_add
    k r d B η hη hB0 hBgrid p hp0
  have hstationary := stationaryScalarCost_eq_directFiniteFluid hn p early
  simp only [Nat.cast_add] at hstationary
  rw [hstationary] at hsample
  rw [hearly] at hsample
  have hsum : (∑ i, p i) ≤ (k + r : ℝ) * L := by
    calc
      (∑ i, p i) ≤ ∑ _i : Fin (k + r), L := by
        apply Finset.sum_le_sum
        intro i _
        exact hpL i
      _ = (k + r : ℝ) * L := by simp
  have hearlyCount := earlyMassCount_le_card
    (fun i => learned (category i))
  simp only [Nat.cast_add] at hearlyCount
  have hdiag :
      (earlyMassCount (fun i => learned (category i)) + ∑ i, p i) / 2 ≤
        (k + r : ℝ) * (1 + L) / 2 := by
    nlinarith
  have hnSq : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hfluid hnSq
  dsimp [early, category, price, learned] at hsample hscaled hdiag ⊢
  linarith

theorem populationHistogram_comp_perm
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β]
    (category : α → β) (σ : Equiv.Perm α) :
    populationHistogram (category ∘ σ) = populationHistogram category := by
  classical
  funext b
  unfold populationHistogram
  rw [categoryClass_card_comp_perm]

/-- Expected conditional scalar cost of the learned growing-cutoff policy,
against the best population template on its upward-rounded grid. -/
theorem uniformAverage_growingLearnedSampleFirstScalarCost_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (hgrid : L ≤ (d : ℝ) * η)
    (hBcover : 1 + L + η ≤ B)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L) :
    let category := fun i => quantizedCategory d η (p i) hη
    let price := Online.growingQuantizedRepresentative d η
    uniformAverage (fun σ : Equiv.Perm (Fin (k + r)) =>
        growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ σ)) ≤
      (k + r : ℝ) ^ 2 *
          minimumObligatoryTemplateValue
            (populationHistogram category) price +
        (k + r : ℝ) ^ 2 *
          (6 * ((d + 1 : ℕ) * η + 2) *
            Real.sqrt ((d + 2 : ℕ) / (k : ℝ))) +
        (B + 1) * (k + r : ℝ) * k / 2 +
        (k + r : ℝ) * (1 + L) / 2 := by
  dsimp only
  have hnCard : 1 < k + r := by omega
  have hn : 0 < k + r := by omega
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let category := fun i : Fin (k + r) =>
    quantizedCategory d η (p i) hη
  let price := Online.growingQuantizedRepresentative d η
  let value : Equiv.Perm (Fin (k + r)) → ℝ := fun σ =>
    obligatoryTemplateValue (populationHistogram category) price
      (growingResultTemplate B d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k))
  let overhead : ℝ :=
    (B + 1) * (k + r : ℝ) * k / 2 +
      (k + r : ℝ) * (1 + L) / 2
  have hpoint : ∀ σ : Equiv.Perm (Fin (k + r)),
      growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ σ) ≤
        (k + r : ℝ) ^ 2 * value σ + overhead := by
    intro σ
    have h := growingLearnedSampleFirstScalarCost_le_populationTemplate
      k r d hk B η L hη hB0 hBgrid (p ∘ σ)
      (fun i => hp0 (σ i)) (fun i => hpL (σ i)) hgrid
    dsimp only [Function.comp_apply] at h
    have hpopulation :
        populationHistogram
            (fun i : Fin (k + r) => quantizedCategory d η (p (σ i)) hη) =
          populationHistogram category := by
      simpa [category, Function.comp_def] using
        populationHistogram_comp_perm category σ
    rw [hpopulation] at h
    dsimp [value, overhead, price, Function.comp_def] at h ⊢
    linarith
  have havg := uniformAverage_mono hpoint
  have havgAffine :
      uniformAverage (fun σ : Equiv.Perm (Fin (k + r)) =>
        (k + r : ℝ) ^ 2 * value σ + overhead) =
        (k + r : ℝ) ^ 2 * uniformAverage value + overhead := by
    rw [uniformAverage_add, uniformAverage_smul, uniformAverage_const]
  rw [havgAffine] at havg
  have hlearn := uniformAverage_growingResultTemplate_le_minimum
    k r d hk hnCard B η L hη p hp0 hpL hgrid hBcover
  have hnSq : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hlearn hnSq
  dsimp [category, price, value, overhead] at havg hscaled ⊢
  linarith

/-- End-to-end theorem for the literal terminating online execution.  The
right side separates the population benchmark, statistical pilot error,
sample-first cross-block overhead, finite diagonal, and operational pilot
placement overhead. -/
theorem uniformAverage_physicalGrowingRunCost_le_minimum
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η)
    (hgrid : L ≤ (d : ℝ) * η)
    (hBcover : 1 + L + η ≤ B)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L) :
    let category := fun i => quantizedCategory d η (p i) hη
    let price := Online.growingQuantizedRepresentative d η
    uniformAverage
        (physicalGrowingRunCost (k + r) k d B η hη p) ≤
      (k + r : ℝ) ^ 2 *
          minimumObligatoryTemplateValue
            (populationHistogram category) price +
        (k + r : ℝ) ^ 2 *
          (6 * ((d + 1 : ℕ) * η + 2) *
            Real.sqrt ((d + 2 : ℕ) / (k : ℝ))) +
        (B + 1) * (k + r : ℝ) * k / 2 +
        (k + r : ℝ) * (1 + L) / 2 +
        (B + 1) * (k : ℝ) ^ 2 := by
  dsimp only
  have hrun := uniformAverage_physicalGrowingRunCost_le
    k r d hk hr B η hη hB0 hBgrid p hp0
  have hscalar := uniformAverage_growingLearnedSampleFirstScalarCost_le
    k r d hk hr B η L hη hB0 hBgrid hgrid hBcover p hp0 hpL
  dsimp only at hscalar
  linarith

end

end RandomizedObligatory
end SchedulingPaper
