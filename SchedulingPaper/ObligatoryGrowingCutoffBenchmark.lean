import SchedulingPaper.ObligatoryGrowingCutoffExpected
import SchedulingPaper.ObligatoryInstanceLower
import Mathlib.Tactic

/-!
# A common benchmark for the growing-cutoff upper and obligatory lower bounds

The positive cells of the lower-bound rounded grid are aligned definitionally
with categories `1,...,d+1` of the growing quantizer; `none` corresponds to
category zero.  This makes the maximum-density completion envelope a literal
member of the upper bound's Boolean template family.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Randomized
open RandomizedAnnounced
open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.ObservedEnvelope
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

def growingPositiveCategory (d : ℕ) (i : Fin (d + 1)) :
    QuantizedCategory d :=
  ⟨i.val + 1, by omega⟩

/-- `none` is the exact zero cell and `some i` is growing category `i+1`. -/
def optionFinEquivQuantizedCategory (d : ℕ) :
    Option (Fin (d + 1)) ≃ QuantizedCategory d where
  toFun
    | none => ⟨0, by omega⟩
    | some i => growingPositiveCategory d i
  invFun b :=
    if hb : b.val = 0 then none
    else some ⟨b.val - 1, by omega⟩
  left_inv cell := by
    cases cell with
    | none => simp
    | some i =>
        simp [growingPositiveCategory]
  right_inv b := by
    by_cases hb : b.val = 0
    · apply Fin.ext
      simp [hb]
    · apply Fin.ext
      simp only [hb, dite_false]
      change (growingPositiveCategory d
        ⟨b.val - 1, by omega⟩).val = b.val
      simp [growingPositiveCategory]
      omega

@[simp] theorem optionFinEquivQuantizedCategory_none (d : ℕ) :
    optionFinEquivQuantizedCategory d none =
      (⟨0, by omega⟩ : QuantizedCategory d) := rfl

@[simp] theorem optionFinEquivQuantizedCategory_some
    (d : ℕ) (i : Fin (d + 1)) :
    optionFinEquivQuantizedCategory d (some i) =
      growingPositiveCategory d i := rfl

theorem growingQuantizedRepresentative_positiveCategory
    (d : ℕ) (η : ℝ) (i : Fin (d + 1)) :
    Online.growingQuantizedRepresentative d η
        (growingPositiveCategory d i) =
      (i.val + 1 : ℕ) * η := by
  simp [Online.growingQuantizedRepresentative, growingPositiveCategory]

/-- The rounded positive grid used by the lower bound, expressed with the
same category function as the growing online policy. -/
def growingAlignedRoundedGrid
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η) :
    RoundedPositiveGrid (Fin (d + 1)) p where
  price i := (i.val + 1 : ℕ) * η
  category i x := decide
    ((quantizedCategory d η x hη).val = i.val + 1)
  mesh := η
  processing_nonneg := hp0
  price_nonneg i := by positivity
  mesh_nonneg := hη.le
  category_positive i job hi := by
    simp only [decide_eq_true_eq] at hi
    by_contra hnot
    have hz : p job = 0 := le_antisymm (le_of_not_gt hnot) (hp0 job)
    rw [hz, quantizedCategory_zero d hη] at hi
    simp at hi
  category_upper i job hi := by
    simp only [decide_eq_true_eq] at hi
    have hcat : quantizedCategory d η (p job) hη =
        growingPositiveCategory d i := by
      apply Fin.ext
      exact hi
    have hround := Online.growingQuantized_rounding_bounds
      d hη (hp0 job) (hcap job)
    rw [hcat, growingQuantizedRepresentative_positiveCategory] at hround
    exact hround
  category_unique job hp := by
    have hne : (quantizedCategory d η (p job) hη).val ≠ 0 := by
      have hceil : 0 < ⌈p job / η⌉₊ :=
        Nat.ceil_pos.mpr (div_pos hp hη)
      simpa [quantizedCategory, hp.ne', hcap job] using hceil.ne'
    let i : Fin (d + 1) :=
      ⟨(quantizedCategory d η (p job) hη).val - 1, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      dsimp [i]
      omega
    · intro j hj
      simp only [decide_eq_true_eq] at hj
      apply Fin.ext
      dsimp [i]
      omega

@[simp] theorem growingAlignedRoundedGrid_mesh
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η) :
    (growingAlignedRoundedGrid d η hη p hp0 hcap).mesh = η := rfl

@[simp] theorem growingAlignedRoundedGrid_price
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (i : Fin (d + 1)) :
    (growingAlignedRoundedGrid d η hη p hp0 hcap).price i =
      (i.val + 1 : ℕ) * η := rfl

theorem growingAlignedRoundedGrid_price_equiv
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (cell : Option (Fin (d + 1))) :
    positiveGridPrice
        (growingAlignedRoundedGrid d η hη p hp0 hcap).price cell =
      Online.growingQuantizedRepresentative d η
        (optionFinEquivQuantizedCategory d cell) := by
  cases cell with
  | none =>
      change 0 = Online.growingQuantizedRepresentative d η
        (⟨0, by omega⟩ : QuantizedCategory d)
      exact (Online.growingQuantizedRepresentative_zero d η).symm
  | some i =>
      simp [positiveGridPrice,
        growingQuantizedRepresentative_positiveCategory]

theorem roundedGridCell_eq_some_iff
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (job : Fin n) (i : ι) :
    roundedGridCell G job = some i ↔ G.category i (p job) = true := by
  constructor
  · exact roundedGridCell_category G
  · intro hi
    have hp := G.category_positive i job hi
    unfold roundedGridCell
    simp only [ne_of_gt hp, dite_false, Option.some.injEq]
    exact ((G.category_unique job hp).choose_spec.2 i hi).symm

theorem growingAlignedRoundedGrid_cell_equiv
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (job : Fin n) :
    optionFinEquivQuantizedCategory d
        (roundedGridCell
          (growingAlignedRoundedGrid d η hη p hp0 hcap) job) =
      quantizedCategory d η (p job) hη := by
  let G := growingAlignedRoundedGrid d η hη p hp0 hcap
  cases hcell : roundedGridCell G job with
  | none =>
      have hz := (roundedGridCell_eq_none_iff G job).mp hcell
      simp [hcell, hz]
  | some i =>
      have hi := (roundedGridCell_eq_some_iff G job i).mp hcell
      change decide
          ((quantizedCategory d η (p job) hη).val = i.val + 1) = true at hi
      simp only [decide_eq_true_eq] at hi
      apply Fin.ext
      exact hi.symm

/-! ## The lower envelope as an obligatory Boolean template -/

def benchmarkCellHistogram
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : Option ι → ℝ
  | none => B.zeroMass
  | some i => B.mass i

def benchmarkCellEarly
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : Option ι → Bool
  | none => true
  | some i => B.selected i

theorem benchmarkCell_earlyMass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    templateEarlyMass (benchmarkCellHistogram B) (benchmarkCellEarly B) =
      RandomizedAnnounced.discoveryMass B.zeroMass
        (selectedPart B.selected B.mass) := by
  unfold templateEarlyMass RandomizedOptional.finiteExpectation
    benchmarkCellHistogram benchmarkCellEarly
    RandomizedAnnounced.discoveryMass selectedPart
  simp only [Fintype.sum_option]
  simp only [if_true, mul_one]
  apply congrArg (fun z : ℝ => B.zeroMass + z)
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : B.selected i = true <;> simp [hi]

theorem benchmarkCell_earlyMoment
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    templateEarlyMoment (benchmarkCellHistogram B)
        (positiveGridPrice G.price) (benchmarkCellEarly B) =
      ∑ i, G.price i * selectedPart B.selected B.mass i := by
  unfold templateEarlyMoment RandomizedOptional.finiteExpectation
    benchmarkCellHistogram benchmarkCellEarly positiveGridPrice selectedPart
  simp only [Fintype.sum_option]
  simp only [if_true, mul_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : B.selected i = true <;> simp [hi] <;> ring

theorem benchmarkCell_latePair
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    templateLatePair (benchmarkCellHistogram B)
        (positiveGridPrice G.price) (benchmarkCellEarly B) =
      weightedMinPair (residualPart B.selected B.mass) G.price := by
  unfold templateLatePair RandomizedOptional.finiteProductExpectation
    benchmarkCellHistogram
    benchmarkCellEarly positiveGridPrice weightedMinPair residualPart
  simp only [Fintype.sum_option]
  simp only [if_true, mul_zero, zero_mul, zero_add]
  simp only [Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : B.selected i = true <;>
    by_cases hj : B.selected j = true <;> simp [hi, hj] <;> ring

/-- The block-area lower benchmark is exactly the obligatory stationary
template value of its selected maximum-density module. -/
theorem roundedObligatoryValue_eq_benchmarkCellTemplate
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    roundedObligatoryValue B =
      obligatoryTemplateValue (benchmarkCellHistogram B)
        (positiveGridPrice G.price) (benchmarkCellEarly B) := by
  rw [roundedObligatoryValue_eq_stationaryFluidCost hn B]
  rw [obligatoryTemplateValue, benchmarkCell_earlyMass,
    benchmarkCell_earlyMoment, benchmarkCell_latePair]
  unfold RandomizedAnnounced.stationaryFluidCost
  have hmodule := B.module_density
  unfold RandomizedAnnounced.discoveryWork at hmodule
  rw [hmodule]

theorem populationHistogram_apply_eq_populationMean_indicator
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (category : Fin n → β) (b : β) :
    populationHistogram category b =
      populationMean (fun job => if category job = b then 1 else 0) := by
  unfold populationHistogram populationMean categoryClass
  simp only [Fintype.card_fin]
  congr 1
  rw [Finset.card_eq_sum_ones]
  simp

theorem benchmarkCellHistogram_eq_populationHistogram
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    benchmarkCellHistogram B = populationHistogram (roundedGridCell G) := by
  funext cell
  cases cell with
  | none =>
      rw [benchmarkCellHistogram, B.zeroMass_def,
        populationHistogram_apply_eq_populationMean_indicator hn]
      apply congrArg populationMean
      funext job
      rw [roundedGridCell_eq_none_iff]
      simp [zeroCategory]
  | some i =>
      rw [benchmarkCellHistogram, B.mass_def,
        populationHistogram_apply_eq_populationMean_indicator hn]
      apply congrArg populationMean
      funext job
      rw [roundedGridCell_eq_some_iff]
      by_cases hi : G.category i (p job) = true <;> simp [hi]

def benchmarkGrowingTemplate
    {n : ℕ} (d : ℕ) {p : Fin n → ℝ}
    {G : RoundedPositiveGrid (Fin (d + 1)) p}
    (B : BenchmarkData p G) : QuantizedCategory d → Bool :=
  fun b => benchmarkCellEarly B
    ((optionFinEquivQuantizedCategory d).symm b)

/-- For the aligned grid, the lower benchmark is exactly the value of one
template available to the growing learner. -/
theorem roundedObligatoryValue_eq_growingTemplate
    {n : ℕ} (hn : 0 < n) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0 hcap)) :
    roundedObligatoryValue B =
      obligatoryTemplateValue
        (populationHistogram (fun job =>
          quantizedCategory d η (p job) hη))
        (Online.growingQuantizedRepresentative d η)
        (benchmarkGrowingTemplate d B) := by
  let G := growingAlignedRoundedGrid d η hη p hp0 hcap
  let lowerCategory := roundedGridCell G
  let upperCategory := fun job : Fin n =>
    quantizedCategory d η (p job) hη
  let lowerPrice := positiveGridPrice G.price
  let upperPrice := Online.growingQuantizedRepresentative d η
  let lowerEarly := benchmarkCellEarly B
  let upperEarly := benchmarkGrowingTemplate d B
  have hcategory : ∀ job,
      optionFinEquivQuantizedCategory d (lowerCategory job) =
        upperCategory job := by
    exact growingAlignedRoundedGrid_cell_equiv d η hη p hp0 hcap
  have hearly :
      (fun job => upperEarly (upperCategory job)) =
        fun job => lowerEarly (lowerCategory job) := by
    funext job
    rw [← hcategory job]
    simp [upperEarly, benchmarkGrowingTemplate, lowerEarly]
  have hprice :
      (fun job => upperPrice (upperCategory job)) =
        fun job => lowerPrice (lowerCategory job) := by
    funext job
    rw [← hcategory job]
    exact (growingAlignedRoundedGrid_price_equiv
      d η hη p hp0 hcap (lowerCategory job)).symm
  rw [roundedObligatoryValue_eq_benchmarkCellTemplate hn B,
    benchmarkCellHistogram_eq_populationHistogram hn B]
  unfold obligatoryTemplateValue
  rw [← RandomizedObligatory.weightedMass_categoryTemplate_eq
        hn lowerCategory lowerEarly,
    ← RandomizedObligatory.weightedMoment_categoryTemplate_eq
        hn lowerCategory lowerPrice lowerEarly,
    ← RandomizedObligatory.weightedMinPair_categoryTemplate_eq
        hn lowerCategory lowerPrice lowerEarly,
    ← RandomizedObligatory.weightedMass_categoryTemplate_eq
        hn upperCategory upperEarly,
    ← RandomizedObligatory.weightedMoment_categoryTemplate_eq
        hn upperCategory upperPrice upperEarly,
    ← RandomizedObligatory.weightedMinPair_categoryTemplate_eq
        hn upperCategory upperPrice upperEarly]
  rw [hearly, hprice]

/-- Consequently the population optimum used by the upper theorem never
exceeds the common lower-envelope benchmark. -/
theorem minimumGrowingTemplateValue_le_roundedObligatoryValue
    {n : ℕ} (hn : 0 < n) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0 hcap)) :
    minimumObligatoryTemplateValue
        (populationHistogram (fun job =>
          quantizedCategory d η (p job) hη))
        (Online.growingQuantizedRepresentative d η) ≤
      roundedObligatoryValue B := by
  rw [roundedObligatoryValue_eq_growingTemplate hn d η hη p hp0 hcap B]
  unfold minimumObligatoryTemplateValue
  exact minimizingObligatoryTemplate_minimizes _ _ _

theorem exists_growingAlignedBenchmarkData
    {n : ℕ} (hn : 0 < n) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (hmean : 0 < populationMean p) :
    ∃ B : BenchmarkData p
        (growingAlignedRoundedGrid d η hη p hp0 hcap), True := by
  let G := growingAlignedRoundedGrid d η hη p hp0 hcap
  have hprice : ∀ i, 0 < G.price i := by
    intro i
    dsimp [G]
    positivity
  have hmeanRounded : 0 < populationMean G.roundedProcessing :=
    hmean.trans_le (G.populationMean_le_roundedProcessing hn)
  let ⟨B⟩ := exists_empiricalBenchmarkData hn p G hprice hmeanRounded
  exact ⟨B, trivial⟩

/-- The operational upper bound can be stated directly against any aligned
maximum-density lower benchmark. -/
theorem uniformAverage_physicalGrowingRunCost_le_roundedObligatoryValue
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (Bcut η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ Bcut)
    (hBgrid : Bcut ≤ (d : ℝ) * η)
    (hgrid : L ≤ (d : ℝ) * η)
    (hBcover : 1 + L + η ≤ Bcut)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0
        (fun i => (hpL i).trans hgrid))) :
    uniformAverage
        (physicalGrowingRunCost (k + r) k d Bcut η hη p) ≤
      (k + r : ℝ) ^ 2 * roundedObligatoryValue B +
        (k + r : ℝ) ^ 2 *
          (6 * ((d + 1 : ℕ) * η + 2) *
            Real.sqrt ((d + 2 : ℕ) / (k : ℝ))) +
        (Bcut + 1) * (k + r : ℝ) * k / 2 +
        (k + r : ℝ) * (1 + L) / 2 +
        (Bcut + 1) * (k : ℝ) ^ 2 := by
  have hupper :=
    uniformAverage_physicalGrowingRunCost_le_minimum
      k r d hk hr Bcut η L hη hB0 hBgrid hgrid hBcover p hp0 hpL
  have hbenchmark := minimumGrowingTemplateValue_le_roundedObligatoryValue
    (Nat.add_pos_left hk r) d η hη p hp0
      (fun i => (hpL i).trans hgrid) B
  have hscaled := mul_le_mul_of_nonneg_left hbenchmark
    (sq_nonneg (k + r : ℝ))
  dsimp only at hupper
  linarith

/-- The lower theorem on the very same aligned grid. -/
theorem exists_fixedPlacement_randomizedCost_ge_growingBenchmark
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hn : 1 < n) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0 hcap))
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e s : ℝ} (he : 0 < e) (hs : 0 < s) :
    let threshold := e + martingaleStep +
      (s + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)
    ∃ σ : ObservedTrace.Placement n,
      roundedObligatoryValue B - η -
          (d + 2 : ℕ) * γ * (1 + B.mean) -
          (1 + B.mean) * ((d + 2 : ℕ) * base) ≤
        uniformAverage fun seed => normalizedCost p (policy seed) σ := by
  have h := exists_fixedPlacement_randomizedCost_ge_roundedObligatoryValue
    hn p policy htest
      (growingAlignedRoundedGrid d η hη p hp0 hcap) B cutoff
      hMartingaleStep hSuffixStep he hs
  simp only [Fintype.card_fin, growingAlignedRoundedGrid_mesh,
    suffixPositions_card] at h ⊢
  convert h using 1 <;> push_cast <;> ring

def growingUpperRawError
    (n k d : ℕ) (Bcut η L : ℝ) : ℝ :=
  (n : ℝ) ^ 2 *
      (6 * ((d + 1 : ℕ) * η + 2) *
        Real.sqrt ((d + 2 : ℕ) / (k : ℝ))) +
    (Bcut + 1) * n * k / 2 +
    (n : ℝ) * (1 + L) / 2 +
    (Bcut + 1) * (k : ℝ) ^ 2

def growingLowerNormalizedError
    (d : ℕ) (η mean γ base : ℝ) : ℝ :=
  η + (d + 2 : ℕ) * γ * (1 + mean) +
    (1 + mean) * ((d + 2 : ℕ) * base)

def growingLowerUniformError
    (d : ℕ) (η L γ base : ℝ) : ℝ :=
  η + (d + 2 : ℕ) * γ * (1 + L + η) +
    (1 + L + η) * ((d + 2 : ℕ) * base)

theorem growingAlignedBenchmark_mean_le
    {n : ℕ} (hn : 0 < n) (d : ℕ) (η L : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hcap : ∀ job, p job ≤ (d : ℝ) * η)
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0 hcap)) :
    B.mean ≤ L + η := by
  rw [B.mean_def]
  apply populationMean_le_scale hn
  intro job
  have hround := (growingAlignedRoundedGrid d η hη p hp0 hcap
    |>.roundedProcessing_le job)
  rw [growingAlignedRoundedGrid_mesh] at hround
  linarith [hpL job]

/- Benchmark-free finite comparison: after fixing one oblivious placement
for the competitor, the literal growing policy loses only the displayed
uniform upper and lower error terms. -/
set_option maxHeartbeats 5000000 in
theorem exists_fixedPlacement_growingPolicy_le_randomizedCompetitor
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (Bcut η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ Bcut)
    (hBgrid : Bcut ≤ (d : ℝ) * η)
    (hgrid : L ≤ (d : ℝ) * η)
    (hBcover : 1 + L + η ≤ Bcut)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (cutoff : Fin (k + r)) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e s : ℝ} (he : 0 < e) (hs : 0 < s) :
    let threshold := e + martingaleStep +
      (s + 2 * suffixStep / (suffixPositions cutoff).card) * (k + r) +
      (suffixPositions cutoff).card
    let γ := threshold / (k + r)
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card *
          ((k + r : ℝ) / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η hη p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            growingLowerUniformError d η L γ base) +
          growingUpperRawError (k + r) k d Bcut η L := by
  dsimp only
  have hn : 0 < k + r := by omega
  have hnTwo : 1 < k + r := by omega
  obtain ⟨B, _⟩ := exists_growingAlignedBenchmarkData
    hn d η hη p hp0 (fun i => (hpL i).trans hgrid) hmean
  have hupper :=
    uniformAverage_physicalGrowingRunCost_le_roundedObligatoryValue
      k r d hk hr Bcut η L hη hB0 hBgrid hgrid hBcover
        p hp0 hpL B
  obtain ⟨σ, hlower⟩ :=
    exists_fixedPlacement_randomizedCost_ge_growingBenchmark
      hnTwo d η hη p hp0 (fun i => (hpL i).trans hgrid)
        policy htest B cutoff hMartingaleStep hSuffixStep he hs
  refine ⟨σ, ?_⟩
  have hmeanLe := growingAlignedBenchmark_mean_le hn d η L hη
    p hp0 hpL (fun i => (hpL i).trans hgrid) B
  let γ : ℝ :=
    (e + martingaleStep +
      (s + 2 * suffixStep / (suffixPositions cutoff).card) * (k + r) +
      (suffixPositions cutoff).card) / (k + r)
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card *
        ((k + r : ℝ) / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / s ^ 2)
  have hγ0 : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    positivity
  have herror : growingLowerNormalizedError d η B.mean γ base ≤
      growingLowerUniformError d η L γ base := by
    unfold growingLowerNormalizedError growingLowerUniformError
    have hcount0 : 0 ≤ (d + 2 : ℝ) * γ := by positivity
    have hbad0 : 0 ≤ (d + 2 : ℝ) * base := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmeanLe hcount0,
      mul_le_mul_of_nonneg_right hmeanLe hbad0]
  have hbenchmark : roundedObligatoryValue B ≤
      uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
        growingLowerUniformError d η L γ base := by
    unfold growingLowerNormalizedError at herror
    unfold growingLowerUniformError at herror ⊢
    dsimp only [γ, base] at herror ⊢
    push_cast at herror hlower ⊢
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbenchmark
    (sq_nonneg (k + r : ℝ))
  unfold growingUpperRawError
  simp only [Nat.cast_add, Nat.cast_ofNat] at hupper hscaled ⊢
  linarith

/-- Rate-ready corollary.  Once the displayed upper and lower error
expressions are each at most `δ`, the growing policy is within `2δ n²` of
the fixed-placement cost of every finitely randomized competitor. -/
theorem exists_fixedPlacement_growingPolicy_le_of_error_bounds
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (Bcut η L : ℝ) (hη : 0 < η) (hB0 : 0 ≤ Bcut)
    (hBgrid : Bcut ≤ (d : ℝ) * η)
    (hgrid : L ≤ (d : ℝ) * η)
    (hBcover : 1 + L + η ≤ Bcut)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (cutoff : Fin (k + r)) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e s δ : ℝ} (he : 0 < e) (hs : 0 < s) (hδ : 0 ≤ δ)
    (hUpper : growingUpperRawError (k + r) k d Bcut η L ≤
      (k + r : ℝ) ^ 2 * δ)
    (hLower :
      let threshold := e + martingaleStep +
        (s + 2 * suffixStep / (suffixPositions cutoff).card) * (k + r) +
        (suffixPositions cutoff).card
      let γ := threshold / (k + r)
      let base :=
        (backwardCheckpoints martingaleStep cutoff).card *
            ((k + r : ℝ) / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / s ^ 2)
      growingLowerUniformError d η L γ base ≤ δ) :
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η hη p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * δ) := by
  obtain ⟨σ, hcomparison⟩ :=
    exists_fixedPlacement_growingPolicy_le_randomizedCompetitor
      k r d hk hr Bcut η L hη hB0 hBgrid hgrid hBcover
        p hp0 hpL hmean policy htest cutoff hMartingaleStep hSuffixStep he hs
  refine ⟨σ, ?_⟩
  dsimp only at hLower hcomparison
  have hnSq : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
  have hLowerScaled := mul_le_mul_of_nonneg_left hLower hnSq
  nlinarith

end

end ObligatoryInstance
end SchedulingPaper
