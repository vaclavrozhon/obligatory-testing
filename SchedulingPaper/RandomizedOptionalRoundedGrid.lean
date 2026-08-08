import SchedulingPaper.RandomizedOptionalObservedEnvelope
import Mathlib.Tactic

/-!
# Positive grids obtained by zero-preserving upward rounding

Unlike `ExactPositiveGrid`, a class price may exceed the actual processing
time by a common mesh `h`.  Zero remains a separate class.  The lemmas below
quantify the resulting work error for arbitrary operational transcripts.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedEnvelope

open ObservedOnline
open Randomized

noncomputable section

structure RoundedPositiveGrid {n : ℕ} (ι : Type*) [Fintype ι]
    (processing : Fin n → ℝ) where
  price : ι → ℝ
  category : ι → ℝ → Bool
  mesh : ℝ
  processing_nonneg : ∀ job, 0 ≤ processing job
  price_nonneg : ∀ i, 0 ≤ price i
  mesh_nonneg : 0 ≤ mesh
  category_positive : ∀ i job,
    category i (processing job) = true → 0 < processing job
  category_upper : ∀ i job,
    category i (processing job) = true →
      processing job ≤ price i ∧ price i ≤ processing job + mesh
  category_unique : ∀ job, 0 < processing job →
    ∃! i, category i (processing job) = true

def RoundedPositiveGrid.placed
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (σ : Equiv.Perm (Fin n)) :
    RoundedPositiveGrid ι (fun job => processing (σ job)) where
  price := G.price
  category := G.category
  mesh := G.mesh
  processing_nonneg job := G.processing_nonneg (σ job)
  price_nonneg := G.price_nonneg
  mesh_nonneg := G.mesh_nonneg
  category_positive i job := G.category_positive i (σ job)
  category_upper i job := G.category_upper i (σ job)
  category_unique job := G.category_unique (σ job)

def RoundedPositiveGrid.roundedProcessing
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) : ℝ :=
  ∑ i, G.price i *
    (if G.category i (processing job) then (1 : ℝ) else 0)

theorem RoundedPositiveGrid.sum_category_indicator
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) :
    (∑ i, if G.category i (processing job) then (1 : ℝ) else 0) =
      if processing job = 0 then 0 else 1 := by
  by_cases hz : processing job = 0
  · rw [if_pos hz]
    apply Finset.sum_eq_zero
    intro i hi
    have hfalse : G.category i (processing job) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have := G.category_positive i job htrue
      linarith
    simp [hfalse]
  · rw [if_neg hz]
    have hp : 0 < processing job := lt_of_le_of_ne
      (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, hunique⟩ := G.category_unique job hp
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j hj hji
      have hfalse : G.category j (processing job) = false := by
        apply Bool.eq_false_iff.mpr
        intro hjtrue
        exact hji (hunique j hjtrue)
      simp [hfalse]
    · simp

theorem RoundedPositiveGrid.roundedProcessing_eq_zero_of_eq_zero
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    {job : Fin n} (hz : processing job = 0) :
    G.roundedProcessing job = 0 := by
  unfold roundedProcessing
  apply Finset.sum_eq_zero
  intro i hi
  have hfalse : G.category i (processing job) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have := G.category_positive i job htrue
    linarith
  simp [hfalse]

theorem RoundedPositiveGrid.roundedProcessing_eq_price_of_category
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    {i : ι} {job : Fin n} (hi : G.category i (processing job) = true) :
    G.roundedProcessing job = G.price i := by
  unfold roundedProcessing
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    have hp := G.category_positive i job hi
    obtain ⟨_witness, _hwitness, hunique⟩ := G.category_unique job hp
    have hfalse : G.category j (processing job) = false := by
      apply Bool.eq_false_iff.mpr
      intro hjtrue
      exact hji ((hunique j hjtrue).trans (hunique i hi).symm)
    simp [hfalse]
  · simp

theorem RoundedPositiveGrid.roundedProcessing_nonneg
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) : 0 ≤ G.roundedProcessing job := by
  unfold roundedProcessing
  exact Finset.sum_nonneg fun i _ => mul_nonneg (G.price_nonneg i) (by
    by_cases h : G.category i (processing job) = true <;> simp [h])

theorem RoundedPositiveGrid.roundedProcessing_le
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) :
    G.roundedProcessing job ≤ processing job + G.mesh := by
  by_cases hz : processing job = 0
  · rw [G.roundedProcessing_eq_zero_of_eq_zero hz, hz]
    simpa using G.mesh_nonneg
  · have hp : 0 < processing job := lt_of_le_of_ne
      (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, _hunique⟩ := G.category_unique job hp
    rw [G.roundedProcessing_eq_price_of_category hi]
    exact (G.category_upper i job hi).2

theorem RoundedPositiveGrid.processing_le_roundedProcessing
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (job : Fin n) : processing job ≤ G.roundedProcessing job := by
  by_cases hz : processing job = 0
  · rw [G.roundedProcessing_eq_zero_of_eq_zero hz, hz]
  · have hp : 0 < processing job := lt_of_le_of_ne
      (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, _hunique⟩ := G.category_unique job hp
    rw [G.roundedProcessing_eq_price_of_category hi]
    exact (G.category_upper i job hi).1

/-- Averaging upward rounding costs at most one mesh. -/
theorem RoundedPositiveGrid.populationMean_roundedProcessing_le
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing) :
    populationMean G.roundedProcessing ≤
      populationMean processing + G.mesh := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ job, G.roundedProcessing job) ≤
      (∑ job, processing job) + n * G.mesh := by
    calc
      (∑ job, G.roundedProcessing job) ≤
          ∑ job, (processing job + G.mesh) :=
        Finset.sum_le_sum fun job _ => G.roundedProcessing_le job
      _ = (∑ job, processing job) + n * G.mesh := by
        rw [Finset.sum_add_distrib]
        simp
  simp only [populationMean, Fintype.card_fin]
  rw [div_le_iff₀ hnR]
  field_simp [hnR.ne']
  exact hsum

/-- Upward rounding can only increase the empirical mean. -/
theorem RoundedPositiveGrid.populationMean_le_roundedProcessing
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing) :
    populationMean processing ≤ populationMean G.roundedProcessing := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [populationMean, Fintype.card_fin]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun job _ => G.processing_le_roundedProcessing job)
    hnR.le

/-- Positive processed class counts still partition all positive processing
operations; exact class prices are not needed for this counting identity. -/
theorem RoundedPositiveGrid.sum_processedClassCount_eq_positiveProcessedCount
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (transcript : Transcript n) :
    (∑ i, (ObservedOnline.processedClassCount processing (G.category i)
      transcript : ℝ)) = positiveProcessedCount processing transcript := by
  induction transcript with
  | nil => simp [ObservedOnline.processedClassCount, positiveProcessedCount]
  | cons observation rest ih =>
      cases observation with
      | testResult job value =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            positiveProcessedCount] using ih
      | blindCompleted job value =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            positiveProcessedCount] using ih
      | processed job =>
          have hstep : ∀ i,
              (ObservedOnline.processedClassCount processing (G.category i)
                (.processed job :: rest) : ℝ) =
                (if G.category i (processing job) then 1 else 0) +
                  ObservedOnline.processedClassCount processing
                    (G.category i) rest := by
            intro i
            by_cases hi : G.category i (processing job) = true <;>
              simp [ObservedOnline.processedClassCount,
                Transcript.processedLabels, hi] <;> ring
          rw [show (∑ i,
              (ObservedOnline.processedClassCount processing (G.category i)
                (.processed job :: rest) : ℝ)) =
              ∑ i, ((if G.category i (processing job) then (1 : ℝ) else 0) +
                (ObservedOnline.processedClassCount processing
                  (G.category i) rest : ℝ)) by
              exact Finset.sum_congr rfl fun i _ => hstep i,
            Finset.sum_add_distrib, G.sum_category_indicator job, ih]
          by_cases hz : processing job = 0 <;>
            simp [positiveProcessedCount, hz] <;> ring

/-- Upward-rounded known work exceeds actual known work by at most one mesh
per positive processed job. -/
theorem RoundedPositiveGrid.sum_price_processedClassCount_le
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (transcript : Transcript n) :
    (∑ i, G.price i *
      (ObservedOnline.processedClassCount processing (G.category i) transcript : ℝ)) ≤
      processedWork processing transcript +
        G.mesh * positiveProcessedCount processing transcript := by
  induction transcript with
  | nil => simp [ObservedOnline.processedClassCount, processedWork,
      positiveProcessedCount]
  | cons observation rest ih =>
      cases observation with
      | testResult job value =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            processedWork, positiveProcessedCount] using ih
      | blindCompleted job value =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            processedWork, positiveProcessedCount] using ih
      | processed job =>
          have hstep : ∀ i,
              (ObservedOnline.processedClassCount processing (G.category i)
                (.processed job :: rest) : ℝ) =
                (if G.category i (processing job) then 1 else 0) +
                  ObservedOnline.processedClassCount processing
                    (G.category i) rest := by
            intro i
            by_cases hi : G.category i (processing job) = true <;>
              simp [ObservedOnline.processedClassCount,
                Transcript.processedLabels, hi] <;> ring
          rw [show (∑ i, G.price i *
              (ObservedOnline.processedClassCount processing (G.category i)
                (.processed job :: rest) : ℝ)) =
              G.roundedProcessing job +
                ∑ i, G.price i *
                  (ObservedOnline.processedClassCount processing
                    (G.category i) rest : ℝ) by
              unfold roundedProcessing
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              rw [hstep i]
              ring]
          by_cases hz : processing job = 0
          · rw [G.roundedProcessing_eq_zero_of_eq_zero hz]
            simp [processedWork, positiveProcessedCount, hz]
            exact ih
          · have hp : 0 < processing job := lt_of_le_of_ne
                (G.processing_nonneg job) (Ne.symm hz)
            have hround := G.roundedProcessing_le job
            simp [processedWork, positiveProcessedCount, hz]
            linarith

end

end ObservedEnvelope
end RandomizedOptional
end SchedulingPaper
