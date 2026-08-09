import SchedulingPaper.RandomizedOptionalGridTemplate
import SchedulingPaper.RandomizedOptionalRoundingUpper
import Mathlib.Tactic

/-!
# From pilot histograms to executable canonical kernels

This file identifies categorical histogram moments with the empirical
one-job/two-job moments used by the finite canonical kernel.  It then compiles
a finite positive-grid template into selectors on rounded and actual values.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open AnnouncedRoundedLower

noncomputable section

/-! ## Push-forward identities -/

theorem finiteExpectation_populationHistogram
    {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (category : α → β) (f : β → ℝ) :
    finiteExpectation (populationHistogram category) f =
      empiricalSingleAverage (fun x => f (category x)) := by
  let n : ℝ := Fintype.card α
  let C : β → Finset α := fun b =>
    @categoryClass α β _ (fun a b => Classical.propDecidable (a = b))
      category b
  have hn0 : n ≠ 0 := by dsimp [n]; positivity
  unfold finiteExpectation populationHistogram empiricalSingleAverage
  calc
    (∑ b, ((C b).card : ℝ) /
        Fintype.card α * f b) =
        (∑ b, ((C b).card : ℝ) * f b) /
          Fintype.card α := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = (∑ x, f (category x)) / Fintype.card α := by
      apply congrArg (fun z : ℝ => z / Fintype.card α)
      calc
       (∑ b, (C b).card * f b) =
        ∑ b, ∑ x, (if category x = b then f b else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [show ((C b).card : ℝ) =
              ∑ x, if category x = b then (1 : ℝ) else 0 by
            have hC : C b = Finset.univ.filter (fun x => category x = b) := by
              ext x
              simp [C, categoryClass]
            rw [hC, Finset.card_eq_sum_ones]
            simp]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : category x = b <;> simp [h]
       _ = ∑ x, f (category x) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_eq_single (category x)]
          · simp
          · intro b _ hne
            simp [hne.symm]
          · simp

theorem finiteProductExpectation_populationHistogram
    {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (category : α → β) (g : β → β → ℝ) :
    finiteProductExpectation (populationHistogram category) g =
      empiricalProductPairAverage (fun x y => g (category x) (category y)) := by
  calc
    finiteProductExpectation (populationHistogram category) g =
        finiteExpectation (populationHistogram category) (fun i =>
          finiteExpectation (populationHistogram category) (g i)) := by
      unfold finiteProductExpectation finiteExpectation
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = empiricalSingleAverage (fun x =>
        finiteExpectation (populationHistogram category) (g (category x))) :=
      finiteExpectation_populationHistogram category _
    _ = empiricalSingleAverage (fun x =>
        empiricalSingleAverage (fun y => g (category x) (category y))) := by
      apply congrArg empiricalSingleAverage
      funext x
      exact finiteExpectation_populationHistogram category _
    _ = empiricalProductPairAverage
        (fun x y => g (category x) (category y)) := by
      unfold empiricalSingleAverage empiricalProductPairAverage
      rw [← Finset.sum_div]
      have hn0 : (Fintype.card α : ℝ) ≠ 0 := by positivity
      field_simp [hn0]

/-! ## The category of a rounded job -/

def roundedGridCell
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) (job : Fin n) : Option ι :=
  if hz : p job = 0 then none
  else some (G.category_unique job
    (lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm hz))).choose

theorem roundedGridCell_eq_none_iff
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) (job : Fin n) :
    roundedGridCell G job = none ↔ p job = 0 := by
  unfold roundedGridCell
  split <;> simp_all

theorem roundedGridCell_category
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    {job : Fin n} {i : ι} (hcell : roundedGridCell G job = some i) :
    G.category i (p job) = true := by
  unfold roundedGridCell at hcell
  split at hcell
  · simp at hcell
  · simp only [Option.some.injEq] at hcell
    subst i
    exact (G.category_unique job
      (lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm ‹p job ≠ 0›))).choose_spec.1

theorem roundedGridCell_price
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) (job : Fin n) :
    positiveGridPrice G.price (roundedGridCell G job) =
      G.roundedProcessing job := by
  cases hcell : roundedGridCell G job with
  | none =>
      have hz := (roundedGridCell_eq_none_iff G job).mp hcell
      simp [positiveGridPrice, hcell,
        G.roundedProcessing_eq_zero_of_eq_zero hz]
  | some i =>
      have hi := roundedGridCell_category G hcell
      simp [positiveGridPrice, hcell,
        G.roundedProcessing_eq_price_of_category hi]

/-! ## Compiling cell selectors -/

def gridTemplateRoundedLow
    {ι : Type*} [Fintype ι] {N : ℕ}
    (price : ι → ℝ) (T : GridTemplate ι N) (x : ℝ) : Bool := by
  classical
  exact decide (x = 0 ∨ ∃ i, price i = x ∧ T.1.low i = true)

def gridTemplateRoundedMedium
    {ι : Type*} [Fintype ι] {N : ℕ}
    (price : ι → ℝ) (T : GridTemplate ι N) (x : ℝ) : Bool := by
  classical
  exact decide (∃ i, price i = x ∧ T.1.medium i = true)

theorem gridTemplateRounded_disjoint
    {ι : Type*} [Fintype ι] {N : ℕ}
    {price : ι → ℝ} (hprice0 : ∀ i, 0 < price i)
    (hprice : Function.Injective price) (T : GridTemplate ι N) :
    ∀ x, gridTemplateRoundedLow price T x = true →
      gridTemplateRoundedMedium price T x = false := by
  classical
  intro x hlow
  apply Bool.eq_false_of_not_eq_true
  intro hmedium
  have hm : ∃ i, price i = x ∧ T.1.medium i = true := by
    simpa [gridTemplateRoundedMedium] using hmedium
  obtain ⟨i, hi, hmi⟩ := hm
  have hl : x = 0 ∨ ∃ j, price j = x ∧ T.1.low j = true := by
    simpa [gridTemplateRoundedLow] using hlow
  rcases hl with hx | ⟨j, hj, hlj⟩
  · exact (ne_of_gt (hprice0 i)) (hi.trans hx)
  · have hji : j = i := hprice (hj.trans hi.symm)
    subst j
    exact Bool.false_ne_true (T.2 i hlj ▸ hmi)

theorem gridTemplateRoundedLow_zero
    {ι : Type*} [Fintype ι] {N : ℕ}
    (price : ι → ℝ) (T : GridTemplate ι N) :
    gridTemplateRoundedLow price T 0 = true := by
  classical
  simp [gridTemplateRoundedLow]

theorem gridTemplateRoundedLow_at_job
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    {N : ℕ} (T : GridTemplate ι N) (job : Fin n) :
    boolWeight (gridTemplateRoundedLow G.price T
        (G.roundedProcessing job)) =
      T.positiveFluidTemplate.low (roundedGridCell G job) := by
  classical
  cases hcell : roundedGridCell G job with
  | none =>
      have hz := (roundedGridCell_eq_none_iff G job).mp hcell
      rw [G.roundedProcessing_eq_zero_of_eq_zero hz]
      simp [gridTemplateRoundedLow_zero, GridTemplate.positiveFluidTemplate,
        boolWeight, hcell]
  | some i =>
      have hi := roundedGridCell_category G hcell
      have hround := G.roundedProcessing_eq_price_of_category hi
      cases hlow : T.1.low i with
      | false =>
          have hfalse : gridTemplateRoundedLow G.price T (G.price i) = false := by
            apply Bool.eq_false_of_not_eq_true
            intro htrue
            have hprop : G.price i = 0 ∨
                ∃ j, G.price j = G.price i ∧ T.1.low j = true := by
              simpa [gridTemplateRoundedLow] using htrue
            rcases hprop with hzero | ⟨j, hj, hjlow⟩
            · exact (ne_of_gt (hprice0 i)) hzero
            · have hji : j = i := hprice hj
              subst j
              simp_all
          simp [hcell, hround, hfalse, hlow,
            GridTemplate.positiveFluidTemplate, boolWeight]
      | true =>
          have htrue : gridTemplateRoundedLow G.price T (G.price i) = true := by
            simp only [gridTemplateRoundedLow, decide_eq_true_eq]
            exact Or.inr ⟨i, rfl, hlow⟩
          simp [hcell, hround, htrue, hlow,
            GridTemplate.positiveFluidTemplate, boolWeight]

theorem gridTemplateRoundedMedium_at_job
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    {N : ℕ} (T : GridTemplate ι N) (job : Fin n) :
    boolWeight (gridTemplateRoundedMedium G.price T
        (G.roundedProcessing job)) =
      T.positiveFluidTemplate.medium (roundedGridCell G job) := by
  classical
  cases hcell : roundedGridCell G job with
  | none =>
      have hz := (roundedGridCell_eq_none_iff G job).mp hcell
      rw [G.roundedProcessing_eq_zero_of_eq_zero hz]
      have hfalse : gridTemplateRoundedMedium G.price T 0 = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        have hprop : ∃ i, G.price i = 0 ∧ T.1.medium i = true := by
          simpa [gridTemplateRoundedMedium] using htrue
        exact (ne_of_gt (hprice0 hprop.choose)) hprop.choose_spec.1
      simp [hcell, hfalse, GridTemplate.positiveFluidTemplate, boolWeight]
  | some i =>
      have hi := roundedGridCell_category G hcell
      have hround := G.roundedProcessing_eq_price_of_category hi
      cases hmedium : T.1.medium i with
      | false =>
          have hfalse :
              gridTemplateRoundedMedium G.price T (G.price i) = false := by
            apply Bool.eq_false_of_not_eq_true
            intro htrue
            have hprop : ∃ j, G.price j = G.price i ∧
                T.1.medium j = true := by
              simpa [gridTemplateRoundedMedium] using htrue
            obtain ⟨j, hj, hjmedium⟩ := hprop
            have hji : j = i := hprice hj
            subst j
            simp_all
          simp [hcell, hround, hfalse, hmedium,
            GridTemplate.positiveFluidTemplate, boolWeight]
      | true =>
          have htrue :
              gridTemplateRoundedMedium G.price T (G.price i) = true := by
            simp only [gridTemplateRoundedMedium, decide_eq_true_eq]
            exact ⟨i, rfl, hmedium⟩
          simp [hcell, hround, htrue, hmedium,
            GridTemplate.positiveFluidTemplate, boolWeight]

theorem gridTemplateRoundedHigh_at_job
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    {N : ℕ} (T : GridTemplate ι N) (job : Fin n) :
    boolWeight (canonicalHigh
        (gridTemplateRoundedLow G.price T)
        (gridTemplateRoundedMedium G.price T)
        (G.roundedProcessing job)) =
      T.positiveFluidTemplate.high (roundedGridCell G job) := by
  have hl := gridTemplateRoundedLow_at_job G hprice0 hprice T job
  have hm := gridTemplateRoundedMedium_at_job G hprice0 hprice T job
  cases hcell : roundedGridCell G job with
  | none =>
      have hz := (roundedGridCell_eq_none_iff G job).mp hcell
      have hlow := gridTemplateRoundedLow_zero G.price T
      simp [canonicalHigh, hcell, GridTemplate.positiveFluidTemplate,
        G.roundedProcessing_eq_zero_of_eq_zero hz, hlow, boolWeight]
  | some i =>
      cases hL : gridTemplateRoundedLow G.price T
          (G.roundedProcessing job) <;>
        cases hM : gridTemplateRoundedMedium G.price T
          (G.roundedProcessing job) <;>
        cases htL : T.1.low i <;> cases htM : T.1.medium i <;>
        simp [canonicalHigh, hcell, GridTemplate.positiveFluidTemplate,
          GridTemplate.high, boolWeight, hL, hM, htL, htM] at hl hm ⊢

private theorem fluidMoments_ext
    (A B : FluidMoments)
    (h1 : A.lowMass = B.lowMass)
    (h2 : A.lowMoment = B.lowMoment)
    (h3 : A.mediumMoment = B.mediumMoment)
    (h4 : A.highMass = B.highMass)
    (h5 : A.mean = B.mean)
    (h6 : A.mediumMinPair = B.mediumMinPair)
    (h7 : A.highMinPair = B.highMinPair) : A = B := by
  cases A
  cases B
  simp_all

/-- Exact push-forward of all seven canonical moments through the rounded
cell map. -/
theorem canonicalEmpiricalMoments_eq_positiveTemplate
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    {N : ℕ} (T : GridTemplate ι N) :
    canonicalEmpiricalMoments G.roundedProcessing
        (gridTemplateRoundedLow G.price T)
        (gridTemplateRoundedMedium G.price T)
        (canonicalHigh (gridTemplateRoundedLow G.price T)
          (gridTemplateRoundedMedium G.price T)) =
      templateMoments (populationHistogram (roundedGridCell G))
        (positiveGridPrice G.price) T.positiveFluidTemplate := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  apply fluidMoments_ext
  · change empiricalSingleAverage (fun job =>
        boolWeight (gridTemplateRoundedLow G.price T
          (G.roundedProcessing job))) =
      finiteExpectation (populationHistogram (roundedGridCell G))
        T.positiveFluidTemplate.low
    rw [finiteExpectation_populationHistogram]
    apply congrArg empiricalSingleAverage
    funext job
    exact gridTemplateRoundedLow_at_job G hprice0 hprice T job
  · change empiricalSingleAverage (fun job =>
        G.roundedProcessing job *
          boolWeight (gridTemplateRoundedLow G.price T
            (G.roundedProcessing job))) =
      finiteExpectation (populationHistogram (roundedGridCell G)) (fun b =>
        positiveGridPrice G.price b * T.positiveFluidTemplate.low b)
    rw [finiteExpectation_populationHistogram]
    apply congrArg empiricalSingleAverage
    funext job
    rw [roundedGridCell_price G job,
      gridTemplateRoundedLow_at_job G hprice0 hprice T job]
  · change empiricalSingleAverage (fun job =>
        G.roundedProcessing job *
          boolWeight (gridTemplateRoundedMedium G.price T
            (G.roundedProcessing job))) =
      finiteExpectation (populationHistogram (roundedGridCell G)) (fun b =>
        positiveGridPrice G.price b * T.positiveFluidTemplate.medium b)
    rw [finiteExpectation_populationHistogram]
    apply congrArg empiricalSingleAverage
    funext job
    rw [roundedGridCell_price G job,
      gridTemplateRoundedMedium_at_job G hprice0 hprice T job]
  · change empiricalSingleAverage (fun job => boolWeight
        (canonicalHigh (gridTemplateRoundedLow G.price T)
          (gridTemplateRoundedMedium G.price T)
          (G.roundedProcessing job))) =
      finiteExpectation (populationHistogram (roundedGridCell G))
        T.positiveFluidTemplate.high
    rw [finiteExpectation_populationHistogram]
    apply congrArg empiricalSingleAverage
    funext job
    exact gridTemplateRoundedHigh_at_job G hprice0 hprice T job
  · change empiricalSingleAverage G.roundedProcessing =
      finiteExpectation (populationHistogram (roundedGridCell G))
        (positiveGridPrice G.price)
    rw [finiteExpectation_populationHistogram]
    apply congrArg empiricalSingleAverage
    funext job
    exact (roundedGridCell_price G job).symm
  · change empiricalProductPairAverage (fun i j =>
        min (G.roundedProcessing i) (G.roundedProcessing j) *
          boolWeight (gridTemplateRoundedMedium G.price T
            (G.roundedProcessing i)) *
          boolWeight (gridTemplateRoundedMedium G.price T
            (G.roundedProcessing j))) =
      finiteProductExpectation (populationHistogram (roundedGridCell G))
        (fun i j => min (positiveGridPrice G.price i)
            (positiveGridPrice G.price j) *
          T.positiveFluidTemplate.medium i *
          T.positiveFluidTemplate.medium j)
    rw [finiteProductExpectation_populationHistogram]
    apply congrArg empiricalProductPairAverage
    funext i j
    rw [roundedGridCell_price G i, roundedGridCell_price G j,
      gridTemplateRoundedMedium_at_job G hprice0 hprice T i,
      gridTemplateRoundedMedium_at_job G hprice0 hprice T j]
  · change empiricalProductPairAverage (fun i j =>
        min (G.roundedProcessing i) (G.roundedProcessing j) *
          boolWeight (canonicalHigh (gridTemplateRoundedLow G.price T)
            (gridTemplateRoundedMedium G.price T)
            (G.roundedProcessing i)) *
          boolWeight (canonicalHigh (gridTemplateRoundedLow G.price T)
            (gridTemplateRoundedMedium G.price T)
            (G.roundedProcessing j))) =
      finiteProductExpectation (populationHistogram (roundedGridCell G))
        (fun i j => min (positiveGridPrice G.price i)
            (positiveGridPrice G.price j) *
          T.positiveFluidTemplate.high i *
          T.positiveFluidTemplate.high j)
    rw [finiteProductExpectation_populationHistogram]
    apply congrArg empiricalProductPairAverage
    funext i j
    rw [roundedGridCell_price G i, roundedGridCell_price G j,
      gridTemplateRoundedHigh_at_job G hprice0 hprice T i,
      gridTemplateRoundedHigh_at_job G hprice0 hprice T j]

/-! ## Executable cost of a learned template -/

/-- A fixed learned grid template is an actual legal canonical policy on the
unrounded population.  Its uniform-placement expected cost is its categorical
fluid value plus the finite-kernel and one-mesh perturbation errors. -/
theorem canonicalPlacedRunCost_le_positiveGridTemplateValue
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hprice0 : ∀ i, 0 < G.price i) (hprice : Function.Injective G.price)
    (T : GridTemplate ι n) {scale : ℝ}
    (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, p job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale) :
    uniformAverage (canonicalPlacedRunCost (q := T.1.quota.val) p
        (pullbackRoundedSelector G (gridTemplateRoundedLow G.price T))
        (pullbackRoundedSelector G (gridTemplateRoundedMedium G.price T))) /
          (n : ℝ) ^ 2 ≤
      positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price T +
        (5 + 18 * scale) / n + 12 * (scale + 1) * G.mesh := by
  let q := T.1.quota.val
  let lowR := gridTemplateRoundedLow G.price T
  let mediumR := gridTemplateRoundedMedium G.price T
  let highR := canonicalHigh lowR mediumR
  let lowA := pullbackRoundedSelector G lowR
  let mediumA := pullbackRoundedSelector G mediumR
  let highA := canonicalHigh lowA mediumA
  have hq : q ≤ n := T.quota_le
  have hdisjointR : ∀ x, lowR x = true → mediumR x = false := by
    exact gridTemplateRounded_disjoint hprice0 hprice T
  have hdisjointA : ∀ x, lowA x = true → mediumA x = false := by
    intro x hx
    exact hdisjointR (gridRoundValue G x) hx
  have hzeroA : ∀ job, p job = 0 → lowA (p job) = true := by
    intro job hz
    dsimp [lowA, lowR, pullbackRoundedSelector]
    rw [G.roundedProcessing_eq_zero_of_eq_zero hz]
    exact gridTemplateRoundedLow_zero G.price T
  have hcost :
      canonicalPlacedRunCost (q := q) p lowA mediumA =
        canonicalKernelCost q p lowA mediumA highA := by
    funext σ
    exact canonicalPlacedRunCost_eq_kernel hq p lowA mediumA
      hdisjointA hzeroA σ
  rw [hcost]
  have hkernel := canonicalKernelCost_fluid_normalized hn hq p
    lowA mediumA highA G.processing_nonneg hpScale
  have hcloseRaw := canonicalEmpiricalMoments_upward_round_componentClose
    (show 0 < n by omega) G lowR mediumR highR hscaleOne
  have hclose :
      (canonicalEmpiricalMoments p lowA mediumA highA).ComponentClose
        (canonicalEmpiricalMoments G.roundedProcessing lowR mediumR highR)
        scale G.mesh := by
    simpa [lowA, mediumA, highA, lowR, mediumR, highR,
      pullbackRoundedSelector, canonicalHigh] using hcloseRaw
  have hscale0 : 0 ≤ scale := le_trans (by norm_num) hscaleOne
  have hboxA := canonicalEmpiricalMoments_inBox (show 0 < n by omega) p
    lowA mediumA highA G.processing_nonneg hpScale
  have hboxR := canonicalEmpiricalMoments_inBox (show 0 < n by omega)
    G.roundedProcessing lowR mediumR highR
      G.roundedProcessing_nonneg hroundedScale
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) / n := by positivity
  have hq1 : (q : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    have hcast : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
    simpa using hcast
  have hstable := canonicalFluidCost_stable hscale0 G.mesh_nonneg hq0 hq1
    hboxA hboxR hclose
  have hmoments := canonicalEmpiricalMoments_eq_positiveTemplate
    (show 0 < n by omega) G hprice0 hprice T
  have hkernelUpper := (abs_le.mp hkernel).2
  have hstableUpper := (abs_le.mp hstable).2
  change uniformAverage (canonicalKernelCost q p lowA mediumA highA) /
      (n : ℝ) ^ 2 ≤ _
  have hfluidLe :
      canonicalFluidCost (canonicalEmpiricalMoments p lowA mediumA highA)
          ((q : ℝ) / n) ≤
        canonicalFluidCost
            (canonicalEmpiricalMoments G.roundedProcessing lowR mediumR highR)
            ((q : ℝ) / n) + 12 * (scale + 1) * G.mesh := by
    linarith
  rw [hmoments] at hfluidLe
  have hfraction : (q : ℝ) / n = T.fraction := rfl
  rw [hfraction] at hfluidLe hkernelUpper
  dsimp [positiveGridTemplateValue]
  linarith

/-! ## The announced benchmark as one target template -/

/-- Every empirical announced benchmark supplies one member of the common
finite template family.  Its categorical fluid value is within `O(1/n)` of
the benchmark in both the short- and long-test regimes. -/
theorem exists_gridTemplateValue_le_benchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G)
    (hprice : Function.Injective G.price)
    {scale : ℝ} (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale) :
    ∃ T : GridTemplate ι n,
      positiveGridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price T ≤
        B.value + (12 + 45 * scale) / n := by
  obtain ⟨q, hq, hplaced⟩ :=
    exists_canonicalPlacedRunCost_le_benchmark_all_regimes
      hn B hprice hroundedScale
  let raw : RawGridTemplate ι n := {
    low := B.selected
    medium := fun i => !B.selected i && decide (G.price i < B.mean)
    quota := ⟨q, by omega⟩ }
  have hvalid : raw.Valid := by
    intro i hlow
    change B.selected i = true at hlow
    change (!B.selected i && decide (G.price i < B.mean)) = false
    simp [hlow]
  let T : GridTemplate ι n := ⟨raw, hvalid⟩
  have hlow : gridTemplateRoundedLow G.price T = benchmarkLowSelector B := by
    funext x
    simp only [gridTemplateRoundedLow, benchmarkLowSelector,
      decide_eq_decide]
    constructor
    · intro hx
      rcases hx with hx | ⟨i, hi, hselected⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi, by simpa [T, raw] using hselected⟩
    · intro hx
      rcases hx with hx | ⟨i, hi, hselected⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi, by simpa [T, raw] using hselected⟩
  have hmedium :
      gridTemplateRoundedMedium G.price T = benchmarkMediumSelector B := by
    funext x
    simp only [gridTemplateRoundedMedium, benchmarkMediumSelector,
      decide_eq_decide]
    constructor
    · rintro ⟨i, hi, hcell⟩
      have hparts : B.selected i = false ∧ G.price i < B.mean := by
        simpa [T, raw] using hcell
      exact ⟨i, hi, hparts.1, hparts.2⟩
    · rintro ⟨i, hi, hselected, hmean⟩
      exact ⟨i, hi, by simp [T, raw, hselected, hmean]⟩
  have hprice0 : ∀ i, 0 < G.price i := B.price_pos
  have hmoments := canonicalEmpiricalMoments_eq_positiveTemplate
    (show 0 < n by omega) G hprice0 hprice T
  have hdisjoint := benchmarkSelectors_disjoint_of_injective B hprice
  have hzero : ∀ job, G.roundedProcessing job = 0 →
      benchmarkLowSelector B (G.roundedProcessing job) = true :=
    fun _job hzero => benchmarkLowSelector_zero_of_rounded B hzero
  have hcost :
      canonicalPlacedRunCost (q := q) G.roundedProcessing
          (benchmarkLowSelector B) (benchmarkMediumSelector B) =
        canonicalKernelCost q G.roundedProcessing
          (benchmarkLowSelector B) (benchmarkMediumSelector B)
          (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B)) := by
    funext σ
    exact canonicalPlacedRunCost_eq_kernel hq G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      hdisjoint hzero σ
  have hkernel := canonicalKernelCost_fluid_normalized hn hq
    G.roundedProcessing (benchmarkLowSelector B) (benchmarkMediumSelector B)
    (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))
    G.roundedProcessing_nonneg hroundedScale
  have hkernelLower := (abs_le.mp hkernel).1
  rw [hcost] at hplaced
  have hfluid :
      canonicalFluidCost
          (canonicalEmpiricalMoments G.roundedProcessing
            (benchmarkLowSelector B) (benchmarkMediumSelector B)
            (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B)))
          ((q : ℝ) / n) ≤
        B.value + (12 + 45 * scale) / n := by
    have herr : (7 + 27 * scale) / (n : ℝ) +
        (5 + 18 * scale) / n = (12 + 45 * scale) / n := by ring
    linarith
  refine ⟨T, ?_⟩
  rw [← hlow, ← hmedium] at hfluid
  rw [hmoments] at hfluid
  have hfraction : ((q : ℝ) / n) = T.fraction := rfl
  rw [hfraction] at hfluid
  exact hfluid

end

end RandomizedOptional
end SchedulingPaper
