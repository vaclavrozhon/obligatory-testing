import SchedulingPaper.RevealingOptimizationQuotaFluid
import SchedulingPaper.RandomizedOptionalRoundingUpper
import Mathlib.Tactic

/-!
# Rounded grids for executable revealing quota policies

An upward grid is used only to choose the low selector.  Physical processing
still uses the original, shorter durations.  Monotonicity of every quota
charge therefore compares the literal run directly with the rounded kernel;
there is no additional mesh loss in this model-specific step.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace QuotaRounding

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedEnvelope
open InstanceLearning
open QuotaKernel
open QuotaFluid

noncomputable section

theorem testedPairChargeOrdered_mono
    {p p' r r' : ℝ} (hp : p ≤ p') (hr : r ≤ r')
    (firstLow secondLow : Bool) :
    testedPairChargeOrdered firstLow secondLow p r ≤
      testedPairChargeOrdered firstLow secondLow p' r' := by
  cases firstLow <;> cases secondLow <;>
    simp [testedPairChargeOrdered, hp, hr, min_le_min hp hr]

theorem quotaPairCharge_mono_of_flags
    {n q : ℕ} (u : ℝ) (i j : Fin n)
    (low low' : ℝ → Bool) {p p' r r' : ℝ}
    (hp : p ≤ p') (hr : r ≤ r')
    (hlowP : low p = low' p') (hlowR : low r = low' r') :
    quotaPairCharge q u low i j p r ≤
      quotaPairCharge q u low' i j p' r' := by
  unfold quotaPairCharge
  split <;> split <;> try split
  all_goals
    first
    | simpa [hlowP, hlowR] using
        testedPairChargeOrdered_mono hp hr (low p) (low r)
    | simpa [hlowP, hlowR] using
        testedPairChargeOrdered_mono hr hp (low r) (low p)
    | linarith

/-- Pull a finite revealing-template selector back through an upward grid.
The explicit zero branch makes the policy legal even away from realized
processing values, where the grid categories carry no assumptions. -/
def roundedTemplateLow
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (T : InstanceLearning.Template ι n) (value : ℝ) : Bool :=
  if value = 0 then true
  else templateLowSelector G.price T (gridRoundValue G value)

@[simp] theorem roundedTemplateLow_zero
    {n : ℕ} {ι : Type*} [Fintype ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (T : InstanceLearning.Template ι n) :
    roundedTemplateLow G T 0 = true := by
  simp [roundedTemplateLow]

theorem roundedTemplateLow_at_job
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (T : InstanceLearning.Template ι n) (job : Fin n) :
    roundedTemplateLow G T (processing job) =
      T.lowWithZero (roundedGridCell G job) := by
  by_cases hz : processing job = 0
  · have hcell : roundedGridCell G job = none :=
      (roundedGridCell_eq_none_iff G job).2 hz
    simp [roundedTemplateLow, hz, hcell,
      InstanceLearning.Template.lowWithZero]
  · rw [roundedTemplateLow, if_neg hz]
    rw [gridRoundValue_processing, ← roundedGridCell_price G job]
    exact templateLowSelector_at_cell G.price hprice0 hprice T
      (roundedGridCell G job)

theorem roundedTemplateLow_eq_roundedSelector_at_job
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (T : InstanceLearning.Template ι n) (job : Fin n) :
    roundedTemplateLow G T (processing job) =
      templateLowSelector G.price T (G.roundedProcessing job) := by
  rw [roundedTemplateLow_at_job G hprice0 hprice T job]
  rw [← roundedGridCell_price G job]
  exact (templateLowSelector_at_cell G.price hprice0 hprice T
    (roundedGridCell G job)).symm

theorem quotaSingleKernel_upward_mono
    {n q : ℕ} (u : ℝ) {processing rounded : Fin n → ℝ}
    (hround : ∀ job, processing job ≤ rounded job)
    (i actual : Fin n) :
    quotaSingleKernel q u processing i actual ≤
      quotaSingleKernel q u rounded i actual := by
  unfold quotaSingleKernel
  split <;> linarith [hround actual]

theorem quotaKernelCost_upward_mono
    {n q : ℕ} (u : ℝ) {processing rounded : Fin n → ℝ}
    (hround : ∀ job, processing job ≤ rounded job)
    (low low' : ℝ → Bool)
    (hlow : ∀ job, low (processing job) = low' (rounded job))
    (order : Equiv.Perm (Fin n)) :
    quotaKernelCost q u processing low order ≤
      quotaKernelCost q u rounded low' order := by
  unfold quotaKernelCost positionKernelCost
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact quotaSingleKernel_upward_mono u hround i (order i)
  · apply Finset.sum_le_sum
    intro z _
    unfold quotaPairKernel
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact quotaPairCharge_mono_of_flags u z.val.1 z.val.2 low low'
      (hround (order z.val.1)) (hround (order z.val.2))
      (hlow (order z.val.1)) (hlow (order z.val.2))

theorem roundedQuotaKernelCost_mono
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (u : ℝ) (T : InstanceLearning.Template ι n)
    (order : Equiv.Perm (Fin n)) :
    quotaKernelCost T.quota.val u processing (roundedTemplateLow G T) order ≤
      quotaKernelCost T.quota.val u G.roundedProcessing
        (templateLowSelector G.price T) order := by
  apply quotaKernelCost_upward_mono u G.processing_le_roundedProcessing
  intro job
  exact roundedTemplateLow_eq_roundedSelector_at_job
    G hprice0 hprice T job

/-- A learned rounded template is a literal policy on the unrounded input.
Its expected normalized cost is bounded by the categorical rounded objective
plus only the finite without-replacement/diagonal correction. -/
theorem roundedRandomizedQuotaRun_le_gridTemplate
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (u : ℝ) (hu0 : 0 ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u)
    (T : InstanceLearning.Template ι n) :
    uniformAverage (fun order : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (QuotaStrategy.randomizedQuotaStrategy n T.quota.val
              (roundedTemplateLow G T) order) (2 * n + 1))) /
        (n : ℝ) ^ 2 ≤
      InstanceLearning.gridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price u T +
        (5 * u + 8) / (2 * n) := by
  let actualCost := fun order : Equiv.Perm (Fin n) =>
    Online.runCompletionCost (.finite u) processing
      (Online.run (.finite u) (Online.fixedOracle processing)
        (QuotaStrategy.randomizedQuotaStrategy n T.quota.val
          (roundedTemplateLow G T) order) (2 * n + 1))
  let roundedCost := quotaKernelCost T.quota.val u G.roundedProcessing
    (templateLowSelector G.price T)
  have hactual : ∀ order, actualCost order =
      quotaKernelCost T.quota.val u processing (roundedTemplateLow G T) order := by
    intro order
    exact randomizedQuotaRun_completionCost_eq_quotaKernelCost
      T.quota_le u processing (roundedTemplateLow G T)
      (roundedTemplateLow_zero G T) order
  have hmono : uniformAverage actualCost ≤ uniformAverage roundedCost := by
    apply uniformAverage_mono
    intro order
    rw [hactual order]
    exact roundedQuotaKernelCost_mono G hprice0 hprice u T order
  have hcategory : ∀ job,
      positiveGridPrice G.price (roundedGridCell G job) =
        G.roundedProcessing job := roundedGridCell_price G
  have hlow : ∀ job,
      templateLowSelector G.price T (G.roundedProcessing job) =
        T.lowWithZero (roundedGridCell G job) := by
    intro job
    rw [← roundedGridCell_price G job]
    exact templateLowSelector_at_cell G.price hprice0 hprice T _
  have hrounded := randomizedQuotaRun_gridTemplate_normalized_error hn
    (roundedGridCell G) G.price u hu0 T G.roundedProcessing
    G.roundedProcessing_nonneg hroundedU (templateLowSelector G.price T)
    (templateLowSelector_zero G.price T) hcategory hlow
  have hroundedUpper := (abs_le.mp hrounded).2
  have hroundedCostEq :
      (fun order : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) G.roundedProcessing
          (Online.run (.finite u) (Online.fixedOracle G.roundedProcessing)
            (QuotaStrategy.randomizedQuotaStrategy n T.quota.val
              (templateLowSelector G.price T) order) (2 * n + 1))) =
        roundedCost := by
    funext order
    exact randomizedQuotaRun_completionCost_eq_quotaKernelCost
      T.quota_le u G.roundedProcessing (templateLowSelector G.price T)
      (templateLowSelector_zero G.price T) order
  rw [hroundedCostEq] at hroundedUpper
  dsimp [actualCost, roundedCost] at hmono
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hnormalized := div_le_div_of_nonneg_right hmono hnSq
  linarith

/-- Rounded pilot learning followed by an independent literal quota run on
the original processing times.  The pilot observes grid cells, while the
main transcript observes actual values and pulls its selector back through
the grid. -/
theorem learnedRoundedRandomizedQuotaRun_le
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ i, 0 < G.price i)
    (hprice : Function.Injective G.price)
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (u : ℝ) (hu0 : 0 ≤ u)
    (hpriceU : ∀ i, G.price i ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u)
    (target : InstanceLearning.Template ι n) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      let learned := InstanceLearning.minimizingTemplate (n := n)
        (sampleHistogram pilotPositions (roundedGridCell G) pilotOrder)
          G.price u
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (QuotaStrategy.randomizedQuotaStrategy n learned.quota.val
              (roundedTemplateLow G learned) mainOrder) (2 * n + 1))) /
        (n : ℝ) ^ 2) ≤
      InstanceLearning.gridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) /
            pilotPositions.card) +
        (5 * u + 8) / (2 * n) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let learned := fun pilotOrder : Equiv.Perm (Fin n) =>
    InstanceLearning.minimizingTemplate (n := n)
      (sampleHistogram pilotPositions (roundedGridCell G) pilotOrder)
        G.price u
  let actualConditional := fun pilotOrder : Equiv.Perm (Fin n) =>
    uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (QuotaStrategy.randomizedQuotaStrategy n
            (learned pilotOrder).quota.val
            (roundedTemplateLow G (learned pilotOrder)) mainOrder)
          (2 * n + 1))) / (n : ℝ) ^ 2
  let roundedConditional := fun pilotOrder : Equiv.Perm (Fin n) =>
    uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) G.roundedProcessing
        (Online.run (.finite u) (Online.fixedOracle G.roundedProcessing)
          (QuotaStrategy.randomizedQuotaStrategy n
            (learned pilotOrder).quota.val
            (templateLowSelector G.price (learned pilotOrder)) mainOrder)
          (2 * n + 1))) / (n : ℝ) ^ 2
  have hconditional : ∀ pilotOrder,
      actualConditional pilotOrder ≤ roundedConditional pilotOrder := by
    intro pilotOrder
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply uniformAverage_mono
    intro mainOrder
    rw [randomizedQuotaRun_completionCost_eq_quotaKernelCost
        (learned pilotOrder).quota_le u processing
        (roundedTemplateLow G (learned pilotOrder))
        (roundedTemplateLow_zero G (learned pilotOrder)) mainOrder,
      randomizedQuotaRun_completionCost_eq_quotaKernelCost
        (learned pilotOrder).quota_le u G.roundedProcessing
        (templateLowSelector G.price (learned pilotOrder))
        (templateLowSelector_zero G.price (learned pilotOrder)) mainOrder]
    exact roundedQuotaKernelCost_mono G hprice0 hprice u
      (learned pilotOrder) mainOrder
  have houter : uniformAverage actualConditional ≤
      uniformAverage roundedConditional := uniformAverage_mono hconditional
  have hcategory : ∀ job,
      positiveGridPrice G.price (roundedGridCell G job) =
        G.roundedProcessing job := roundedGridCell_price G
  have hlearn := learnedRandomizedQuotaRun_le hn pilotPositions hpilot
    (roundedGridCell G) G.price hprice0 hprice u hu0 hpriceU
    G.roundedProcessing G.roundedProcessing_nonneg hroundedU hcategory target
  change uniformAverage actualConditional ≤ _
  apply houter.trans
  simpa [roundedConditional, learned] using hlearn

end

end QuotaRounding
end RevealingOptimization
end SchedulingPaper
