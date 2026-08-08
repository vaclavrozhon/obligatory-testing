import SchedulingPaper.RandomizedOptionalObservedTrace
import SchedulingPaper.RandomizedOptionalGridBridge
import Mathlib.Tactic

/-!
# Optional testing: operational prefixes enter the fluid envelope

This file connects the observed online semantics to the deterministic grid
bridge.  It contains no probability: a simultaneous urn good event is supplied
as two discrepancy hypotheses.  The conclusion is the pointwise completion
envelope inequality for the literal operational prefix.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedEnvelope

open ObservedOnline
open ObservedTrace
open TraceBijection
open Randomized

noncomputable section

/-- An exact positive grid for a fixed finite occurrence vector.  Zero is
kept separate; every positive occurrence belongs to exactly one class and
the class endpoint is its processing time. -/
structure ExactPositiveGrid {n : ℕ} (ι : Type*) [Fintype ι]
    (processing : Fin n → ℝ) where
  price : ι → ℝ
  category : ι → ℝ → Bool
  processing_nonneg : ∀ job, 0 ≤ processing job
  price_nonneg : ∀ i, 0 ≤ price i
  category_positive : ∀ i job,
    category i (processing job) = true → 0 < processing job
  category_price : ∀ i job,
    category i (processing job) = true → processing job = price i
  category_unique : ∀ job, 0 < processing job →
    ∃! i, category i (processing job) = true

def zeroCategory (x : ℝ) : Bool := decide (x = 0)

@[simp] theorem zeroCategory_eq_true_iff (x : ℝ) :
    zeroCategory x = true ↔ x = 0 := by
  simp [zeroCategory]

theorem ExactPositiveGrid.sum_category_indicator
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : ExactPositiveGrid ι processing)
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

theorem ExactPositiveGrid.sum_price_indicator
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : ExactPositiveGrid ι processing)
    (job : Fin n) :
    (∑ i, G.price i *
      (if G.category i (processing job) then (1 : ℝ) else 0)) =
      processing job := by
  by_cases hz : processing job = 0
  · rw [hz]
    apply Finset.sum_eq_zero
    intro i hi
    have hfalse : G.category i (processing job) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have := G.category_positive i job htrue
      linarith
    have hfalse0 : G.category i 0 = false := by simpa [hz] using hfalse
    simp [hfalse0]
  · have hp : 0 < processing job := lt_of_le_of_ne
      (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, hunique⟩ := G.category_unique job hp
    rw [Finset.sum_eq_single i]
    · simp [hi, ← G.category_price i job hi]
    · intro j hj hji
      have hfalse : G.category j (processing job) = false := by
        apply Bool.eq_false_iff.mpr
        intro hjtrue
        exact hji (hunique j hjtrue)
      simp [hfalse]
    · simp

theorem sum_processedClassCount_eq_positiveProcessedCount
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : ExactPositiveGrid ι processing)
    (transcript : Transcript n) :
    (∑ i, (ObservedOnline.processedClassCount processing (G.category i)
      transcript : ℝ)) = positiveProcessedCount processing transcript := by
  induction transcript with
  | nil => simp [ObservedOnline.processedClassCount, positiveProcessedCount]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            positiveProcessedCount] using ih
      | blindCompleted job p =>
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

theorem sum_price_processedClassCount_eq_processedWork
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : ExactPositiveGrid ι processing)
    (transcript : Transcript n) :
    (∑ i, G.price i *
      (ObservedOnline.processedClassCount processing (G.category i) transcript : ℝ)) =
      processedWork processing transcript := by
  induction transcript with
  | nil => simp [ObservedOnline.processedClassCount, processedWork]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            processedWork] using ih
      | blindCompleted job p =>
          simpa [ObservedOnline.processedClassCount, Transcript.processedLabels,
            processedWork] using ih
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
              ∑ i, (G.price i *
                  (if G.category i (processing job) then 1 else 0) +
                G.price i * ObservedOnline.processedClassCount processing
                  (G.category i) rest) by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hstep i]
              ring,
            Finset.sum_add_distrib, G.sum_price_indicator job, ih]
          rfl

theorem zeroTestCount_eq_testClassCount_zero
    {n : ℕ} (transcript : Transcript n) :
    zeroTestCount transcript = ObservedOnline.testClassCount zeroCategory transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job value =>
          by_cases hz : value = 0 <;>
            simp [zeroTestCount, ObservedOnline.testClassCount,
              Transcript.testResults, zeroCategory, hz, ih] <;> omega
      | processed job =>
          simpa [zeroTestCount, ObservedOnline.testClassCount,
            Transcript.testResults] using ih
      | blindCompleted job value =>
          simpa [zeroTestCount, ObservedOnline.testClassCount,
            Transcript.testResults] using ih

theorem touchChoices_length_eq_test_add_blind
    {n : ℕ} (transcript : Transcript n) :
    (touchChoices transcript).length =
      transcript.testResults.length + blindCount transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [touchChoices, observationTouchChoice?, Transcript.testResults,
          blindCount, ih] <;> omega

/-! ## One literal prefix under a simultaneous discrepancy event -/

/-- Deterministic scheduler-to-envelope bridge for one nonempty regulated
operational prefix.  The two discrepancy assumptions are precisely the
pathwise complements of the bad events exported by
`RandomizedOptionalObservedTrace`.

The greedy variables describe the ideal fractional knapsack at the prefix's
inflated physical work. -/
theorem operational_prefix_completion_le_greedy
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : ExactPositiveGrid ι p) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1)
    (selected : ι → Bool)
    {γ zeroMass τ μ blindError greedyModule greedyBlind pivotCost : ℝ}
    {mass completion greedyResidual : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hμDef : μ = populationMean p)
    (hγ : 0 ≤ γ) (hblindError : 0 ≤ blindError)
    (hclassGood : ∀ i,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        mass i *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hzeroGood :
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if zeroCategory
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        zeroMass *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hblindGood :
      |(∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            p (revealOrder (touchTrace p policy) σ k)) -
        μ *
          ∑ k ∈ positionsThrough cutoff,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ blindError * n)
    (hmax : ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
      τ * RandomizedAnnounced.discoveryMass zeroMass x ≤
        RandomizedAnnounced.discoveryWork G.price x)
    (hmodulePositive :
      0 < RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass))
    (hmoduleDensity :
      τ * RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass) =
        RandomizedAnnounced.discoveryWork G.price
          (selectedPart selected mass))
    (hpivot : 0 < pivotCost)
    (hgreedyWork :
      ((elapsed (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript) / n) +
          blindError ≤
        optionalKnapsackWork τ μ greedyModule greedyBlind
          G.price greedyResidual)
    (hgreedyLow : ∀ item,
      optionalItemCost τ μ G.price item < pivotCost →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item =
          optionalItemCapacity
            ((∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)) / n)
            (RandomizedAnnounced.discoveryMass zeroMass
              (selectedPart selected mass))
            (residualPart selected mass) item)
    (hgreedyHigh : ∀ item,
      pivotCost < optionalItemCost τ μ G.price item →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item = 0) :
    (completionCount (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤
      optionalKnapsackMass greedyModule greedyBlind greedyResidual +
        (Fintype.card ι + 1) * γ := by
  let transcript :=
    (run (placedProcessing p σ) policy.strategy fuel).config.transcript
  let reveal := revealOrder (touchTrace p policy) σ
  let selectTest := compiledTestSelector p policy
  let selectBlind := compiledBlindSelector p policy
  let totalTest : ℝ := ∑ k, selectTest k reveal
  let prefixTest : ℝ := ∑ k ∈ positionsThrough cutoff, selectTest k reveal
  let prefixBlind : ℝ := ∑ k ∈ positionsThrough cutoff, selectBlind k reveal
  let t := prefixTest / n
  let q := totalTest / n
  let b := prefixBlind / n
  let c : ι → ℝ := fun i =>
    ObservedOnline.processedClassCount (placedProcessing p σ)
      (G.category i) transcript / n
  let z : ℝ := zeroTestCount transcript / n
  let actual : ℝ := completionCount (placedProcessing p σ) transcript / n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htest0 : ∀ k reveal, 0 ≤ compiledTestSelector p policy k reveal :=
    fun k r => ObservedTrace.compiledTestSelector_nonneg p policy k r
  have htest1 : ∀ k reveal, compiledTestSelector p policy k reveal ≤ 1 :=
    fun k r => ObservedTrace.compiledTestSelector_le_one p policy k r
  have hblind0 := compiledBlindSelector_nonneg p policy
  have hblind1 := compiledBlindSelector_le_one p policy
  have htestOperational := compiled_test_class_prefix_sum_eq_operational
    p policy σ (fun _ => true) hfuel cutoff hlength
  simp only [Bool.true_eq, if_true, testClassCount_true] at htestOperational
  have hblindCountOperational := compiled_blind_count_prefix_sum_eq_operational
    p policy σ hfuel cutoff hlength
  have hblindWorkOperational := compiled_blind_work_prefix_sum_eq_operational
    p policy σ hfuel cutoff hlength
  have hclassOperational : ∀ i,
      (∑ k ∈ positionsThrough cutoff,
          selectTest k reveal *
            (if G.category i (p (reveal k)) then 1 else 0)) =
        ObservedOnline.testClassCount (G.category i) transcript := by
    intro i
    exact compiled_test_class_prefix_sum_eq_operational
      p policy σ (G.category i) hfuel cutoff hlength
  have hzeroOperational :
      (∑ k ∈ positionsThrough cutoff,
          selectTest k reveal *
            (if zeroCategory (p (reveal k)) then 1 else 0)) =
        zeroTestCount transcript := by
    rw [compiled_test_class_prefix_sum_eq_operational
      p policy σ zeroCategory hfuel cutoff hlength]
    exact_mod_cast (zeroTestCount_eq_testClassCount_zero transcript).symm
  have ht0 : 0 ≤ t := by
    exact div_nonneg (Finset.sum_nonneg fun k _ => htest0 k reveal) hnR.le
  have hprefixTestLe : prefixTest ≤ totalTest := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _hk _hnot => htest0 k reveal)
  have htq : t ≤ q := div_le_div_of_nonneg_right hprefixTestLe hnR.le
  have hb0 : 0 ≤ b := by
    exact div_nonneg (Finset.sum_nonneg fun k _ => hblind0 k reveal) hnR.le
  have hsumBlind : (∑ k, selectBlind k reveal) = n - totalTest := by
    dsimp [selectBlind, compiledBlindSelector, totalTest, selectTest]
    rw [Finset.sum_sub_distrib]
    simp
  have hprefixBlindLe : prefixBlind ≤ ∑ k, selectBlind k reveal := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _hk _hnot => hblind0 k reveal)
  have hbCap : b ≤ 1 - q := by
    calc
      b ≤ (n - totalTest) / n := by
        dsimp [b]
        exact div_le_div_of_nonneg_right
          (hprefixBlindLe.trans_eq hsumBlind) hnR.le
      _ = 1 - q := by
        dsimp [q]
        field_simp [hnR.ne']
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn
      (fun occurrence => if G.category i (p occurrence) then 1 else 0)
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hzeroMass0 : 0 ≤ zeroMass := by
    rw [hzeroMassDef]
    exact (populationMean_mem_Icc hn
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0)
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])).1
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) hnR.le
  have hclassApprox : ∀ i, c i ≤ mass i * t + γ := by
    intro i
    have hupper := (abs_le.mp (hclassGood i)).2
    rw [hclassOperational i] at hupper
    have htestEq : prefixTest = transcript.testResults.length := by
      simpa [prefixTest, selectTest, reveal, transcript] using htestOperational
    change (ObservedOnline.testClassCount (G.category i) transcript : ℝ) -
      mass i * prefixTest ≤ γ * n at hupper
    have hprocessedLe :
        (ObservedOnline.processedClassCount (placedProcessing p σ)
            (G.category i) transcript : ℝ) ≤
          ObservedOnline.testClassCount (G.category i) transcript := by
      exact_mod_cast ObservedOnline.processedClassCount_le_testClassCount
        (run_historyInvariant (placedProcessing p σ) policy.strategy fuel)
          (G.category i)
    have hbound :
        (ObservedOnline.processedClassCount (placedProcessing p σ)
            (G.category i) transcript : ℝ) ≤
          mass i * prefixTest + γ * n := by
      linarith
    dsimp [c, t]
    rw [div_le_iff₀ hnR]
    calc
      (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ) ≤
          mass i * prefixTest + γ * n := hbound
      _ = (mass i * (prefixTest / n) + γ) * n := by
        field_simp [hnR.ne']
  have hzApprox : z ≤ zeroMass * t + γ := by
    have hupper := (abs_le.mp hzeroGood).2
    rw [hzeroOperational] at hupper
    change (zeroTestCount transcript : ℝ) - zeroMass * prefixTest ≤
      γ * n at hupper
    have hbound : (zeroTestCount transcript : ℝ) ≤
        zeroMass * prefixTest + γ * n := by
      linarith
    dsimp [z, t]
    rw [div_le_iff₀ hnR]
    calc
      (zeroTestCount transcript : ℝ) ≤
          zeroMass * prefixTest + γ * n := hbound
      _ = (zeroMass * (prefixTest / n) + γ) * n := by
        field_simp [hnR.ne']
  have hactual : actual ≤ z + b + ∑ i, c i := by
    have hcount := completionCount_eq_operation_counts
      (placedProcessing p σ) transcript
    have hclasses := sum_processedClassCount_eq_positiveProcessedCount
      (processing := placedProcessing p σ) (by
        exact {
          price := G.price
          category := G.category
          processing_nonneg := fun job => G.processing_nonneg (σ job)
          price_nonneg := G.price_nonneg
          category_positive := fun i job h => G.category_positive i (σ job) h
          category_price := fun i job h => by
            simpa [placedProcessing] using G.category_price i (σ job) h
          category_unique := fun job h => G.category_unique (σ job) h }) transcript
    have hblindEq : prefixBlind = (blindCount transcript : ℝ) := by
      change (∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ)) =
        (blindCount transcript : ℝ)
      simpa only [compiledBlindSelector] using hblindCountOperational
    change (∑ i,
        (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ)) =
        (positiveProcessedCount (placedProcessing p σ) transcript : ℝ) at hclasses
    change (completionCount (placedProcessing p σ) transcript : ℝ) / n ≤
      (zeroTestCount transcript : ℝ) / n + prefixBlind / n +
        ∑ i, (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ) / n
    rw [← Finset.sum_div, hclasses, hblindEq, hcount]
    push_cast
    simp only [add_div]
    linarith
  have hphysical :
      t + μ * b + ∑ i, G.price i * c i ≤
        elapsed (placedProcessing p σ) transcript / n + blindError := by
    have hblindUpper := (abs_le.mp hblindGood).1
    have hblindEq : prefixBlind = (blindCount transcript : ℝ) := by
      change (∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ)) =
        (blindCount transcript : ℝ)
      simpa only [compiledBlindSelector] using hblindCountOperational
    have hblindWorkEq :
        (∑ k ∈ positionsThrough cutoff,
            selectBlind k reveal * p (reveal k)) = blindWork transcript := by
      change (∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            p (revealOrder (touchTrace p policy) σ k)) =
        blindWork transcript
      simpa [transcript] using hblindWorkOperational
    rw [hblindWorkEq] at hblindUpper
    change -(blindError * n) ≤ blindWork transcript - μ * prefixBlind at hblindUpper
    rw [hblindEq] at hblindUpper
    have hwork := sum_price_processedClassCount_eq_processedWork
      (processing := placedProcessing p σ) (by
        exact {
          price := G.price
          category := G.category
          processing_nonneg := fun job => G.processing_nonneg (σ job)
          price_nonneg := G.price_nonneg
          category_positive := fun i job h => G.category_positive i (σ job) h
          category_price := fun i job h => by
            simpa [placedProcessing] using G.category_price i (σ job) h
          category_unique := fun job h => G.category_unique (σ job) h }) transcript
    change (∑ i, G.price i *
        (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ)) =
      processedWork (placedProcessing p σ) transcript at hwork
    have htestEq : prefixTest = transcript.testResults.length := by
      simpa [prefixTest, selectTest, reveal, transcript] using htestOperational
    rw [elapsed_eq_test_add_processed_add_blind]
    change prefixTest / n + μ * (prefixBlind / n) +
        ∑ i, G.price i *
          ((ObservedOnline.processedClassCount (placedProcessing p σ)
            (G.category i) transcript : ℝ) / n) ≤
      ((transcript.testResults.length : ℝ) +
          processedWork (placedProcessing p σ) transcript +
          blindWork transcript) / n + blindError
    rw [htestEq, hblindEq]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hwork]
    field_simp [hnR.ne']
    nlinarith
  have hactualDef : actual =
      (completionCount (placedProcessing p σ) transcript : ℝ) / n := rfl
  change actual ≤ _
  exact optional_all_class_grid_prefix_completion_le_greedy selected
    hγ hzeroMass0 hmass0 G.price_nonneg hc0 ht0 htq hzApprox hclassApprox
    hb0 hbCap hactual hphysical hmax hmodulePositive hmoduleDensity hpivot
    hgreedyWork hgreedyLow hgreedyHigh

end

end ObservedEnvelope
end RandomizedOptional
end SchedulingPaper
