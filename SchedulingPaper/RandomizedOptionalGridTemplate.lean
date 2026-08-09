import SchedulingPaper.RandomizedOptionalLearning
import SchedulingPaper.RandomizedOptionalCanonicalKernel
import Mathlib.Tactic

/-!
# Distribution-independent finite templates for optional testing

The announced benchmark contains population-specific mass equalities and is
therefore the wrong object to learn from a pilot sample.  This file isolates
the genuinely executable data: two disjoint cell selectors and an integral
testing quota.  The resulting type is finite, so empirical minimization needs
no measurable-choice or compactness argument.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Raw finite data of a canonical grid policy.  `quota` is an element of
`Fin (N+1)`, hence is definitionally a legal number of tests on `N` jobs. -/
structure RawGridTemplate (β : Type*) (N : ℕ) where
  low : β → Bool
  medium : β → Bool
  quota : Fin (N + 1)
  deriving DecidableEq, Fintype

/-- Low and medium cells must be disjoint.  The high class is their Boolean
complement.  The distinguished zero-cell convention is imposed by the
compiler that turns a positive-grid template into an online selector. -/
def RawGridTemplate.Valid {β : Type*} {N : ℕ}
    (T : RawGridTemplate β N) : Prop :=
  ∀ b, T.low b = true → T.medium b = false

abbrev GridTemplate (β : Type*) (N : ℕ) :=
  {T : RawGridTemplate β N // T.Valid}

instance {β : Type*} {N : ℕ} [Fintype β] : Fintype (GridTemplate β N) :=
  Fintype.ofFinite _

instance {β : Type*} {N : ℕ} [Fintype β] : Nonempty (GridTemplate β N) := by
  let T : RawGridTemplate β N := {
    low := fun _ => false
    medium := fun _ => false
    quota := ⟨0, by omega⟩ }
  exact ⟨⟨T, by simp [RawGridTemplate.Valid]⟩⟩

/-- The pure-YOLO member of the finite family: test no job and put every
positive grid cell in the high residual class. -/
def zeroQuotaGridTemplate {β : Type*} (N : ℕ) : GridTemplate β N :=
  ⟨{ low := fun _ => false
     medium := fun _ => false
     quota := ⟨0, by omega⟩ }, by
    simp [RawGridTemplate.Valid]⟩

@[simp] theorem zeroQuotaGridTemplate_quota
    {β : Type*} (N : ℕ) :
    (zeroQuotaGridTemplate (β := β) N).1.quota.val = 0 := rfl

def GridTemplate.high {β : Type*} {N : ℕ}
    (T : GridTemplate β N) (b : β) : Bool :=
  !T.1.low b && !T.1.medium b

def GridTemplate.fluidTemplate {β : Type*} {N : ℕ}
    (T : GridTemplate β N) : FluidTemplate β where
  low := fun b => boolWeight (T.1.low b)
  medium := fun b => boolWeight (T.1.medium b)
  high := fun b => boolWeight (T.high b)

def GridTemplate.fraction {β : Type*} {N : ℕ}
    (T : GridTemplate β N) : ℝ :=
  (T.1.quota : ℝ) / N

@[simp] theorem zeroQuotaGridTemplate_fraction
    {β : Type*} (N : ℕ) :
    (zeroQuotaGridTemplate (β := β) N).fraction = 0 := by
  simp [GridTemplate.fraction]

/-- Leading fluid value of one fixed finite template under histogram `D`. -/
def gridTemplateValue {β : Type*} [Fintype β] {N : ℕ}
    (D price : β → ℝ) (T : GridTemplate β N) : ℝ :=
  canonicalFluidCost (templateMoments D price T.fluidTemplate) T.fraction

theorem GridTemplate.quota_le {β : Type*} {N : ℕ}
    (T : GridTemplate β N) : T.1.quota.val ≤ N := by
  omega

theorem GridTemplate.fraction_nonneg {β : Type*} {N : ℕ}
    (T : GridTemplate β N) : 0 ≤ T.fraction := by
  unfold fraction
  positivity

theorem GridTemplate.fraction_le_one {β : Type*} {N : ℕ}
    (hN : 0 < N) (T : GridTemplate β N) : T.fraction ≤ 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hNR).2
  have hcast : (T.1.quota.val : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast T.quota_le
  simpa using hcast

theorem GridTemplate.selector_bounds {β : Type*} {N : ℕ}
    (T : GridTemplate β N) :
    (∀ b, 0 ≤ T.fluidTemplate.low b) ∧
    (∀ b, T.fluidTemplate.low b ≤ 1) ∧
    (∀ b, 0 ≤ T.fluidTemplate.medium b) ∧
    (∀ b, T.fluidTemplate.medium b ≤ 1) ∧
    (∀ b, 0 ≤ T.fluidTemplate.high b) ∧
    (∀ b, T.fluidTemplate.high b ≤ 1) := by
  exact ⟨fun b => (boolWeight_mem_Icc _).1,
    fun b => (boolWeight_mem_Icc _).2,
    fun b => (boolWeight_mem_Icc _).1,
    fun b => (boolWeight_mem_Icc _).2,
    fun b => (boolWeight_mem_Icc _).1,
    fun b => (boolWeight_mem_Icc _).2⟩

/-- A concrete empirical minimizer over the finite template family. -/
noncomputable def minimizingGridTemplate
    {β : Type*} [Fintype β] [DecidableEq β] {N : ℕ}
    (D price : β → ℝ) : GridTemplate β N :=
  (Finset.exists_min_image (Finset.univ : Finset (GridTemplate β N))
    (gridTemplateValue D price) Finset.univ_nonempty).choose

theorem minimizingGridTemplate_minimizes
    {β : Type*} [Fintype β] [DecidableEq β] {N : ℕ}
    (D price : β → ℝ) (T : GridTemplate β N) :
    gridTemplateValue D price (minimizingGridTemplate (N := N) D price) ≤
      gridTemplateValue D price T := by
  exact (Finset.exists_min_image
    (Finset.univ : Finset (GridTemplate β N))
      (gridTemplateValue D price) Finset.univ_nonempty).choose_spec.2
      T (by simp)

/-- Histogram stability, uniform over the entire finite executable family. -/
theorem gridTemplateValue_lipschitz
    {β : Type*} [Fintype β] {N : ℕ}
    {D E price : β → ℝ} {L : ℝ} (hN : 0 < N)
    (hD : ∀ b, 0 ≤ D b) (hE : ∀ b, 0 ≤ E b)
    (hDmass : ∑ b, D b = 1) (hEmass : ∑ b, E b = 1)
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L)
    (T : GridTemplate β N) :
    |gridTemplateValue D price T - gridTemplateValue E price T| ≤
      12 * (L + 1) * finiteL1 D E := by
  obtain ⟨hlow0, hlow1, hmedium0, hmedium1, hhigh0, hhigh1⟩ :=
    T.selector_bounds
  exact template_canonicalFluidCost_lipschitz
    hD hE hDmass hEmass hprice0 hpriceL
      hlow0 hlow1 hmedium0 hmedium1 hhigh0 hhigh1
      T.fraction_nonneg (T.fraction_le_one hN)

/-- The empirical optimizer pays twice the histogram perturbation against
any target template.  This is the deterministic heart of pilot learning. -/
theorem minimizingGridTemplate_transfer
    {β : Type*} [Fintype β] [DecidableEq β] {N : ℕ}
    {D E price : β → ℝ} {L : ℝ} (hN : 0 < N)
    (hD : ∀ b, 0 ≤ D b) (hE : ∀ b, 0 ≤ E b)
    (hDmass : ∑ b, D b = 1) (hEmass : ∑ b, E b = 1)
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L)
    (target : GridTemplate β N) :
    gridTemplateValue E price (minimizingGridTemplate (N := N) D price) ≤
      gridTemplateValue E price target +
        24 * (L + 1) * finiteL1 D E := by
  let ε := 12 * (L + 1) * finiteL1 D E
  have hstable : ∀ T : GridTemplate β N,
      |gridTemplateValue D price T - gridTemplateValue E price T| ≤ ε :=
    fun T => gridTemplateValue_lipschitz hN hD hE hDmass hEmass
      hprice0 hpriceL T
  have hmin := minimizingGridTemplate_minimizes (N := N) D price target
  have htransfer := empirical_minimizer_transfer hstable hmin
  dsimp [ε] at htransfer ⊢
  linarith

/-! ## Histograms generated by a uniform pilot -/

def sampleHistogram
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (category : α → β) (σ : Equiv.Perm α) : β → ℝ :=
  fun b => sampleCategoryFraction S (categoryClass category b) σ

def populationHistogram
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (category : α → β) : β → ℝ :=
  fun b => ((categoryClass category b).card : ℝ) / Fintype.card α

theorem sampleHistogram_nonneg
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (category : α → β) (σ : Equiv.Perm α) :
    ∀ b, 0 ≤ sampleHistogram S category σ b := by
  intro b
  unfold sampleHistogram sampleCategoryFraction permutationSampleSum
    categoryIndicator
  positivity

theorem populationHistogram_nonneg
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [DecidableEq α] (category : α → β) :
    ∀ b, 0 ≤ populationHistogram category b := by
  intro b
  unfold populationHistogram
  positivity

theorem sampleHistogram_mass_one
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (hS : S.Nonempty)
    (category : α → β) (σ : Equiv.Perm α) :
    ∑ b, sampleHistogram S category σ b = 1 := by
  unfold sampleHistogram sampleCategoryFraction permutationSampleSum
    categoryIndicator
  rw [← Finset.sum_div]
  simp only [categoryClass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simp [hcard]

theorem populationHistogram_mass_one
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [DecidableEq α] (category : α → β) :
    ∑ b, populationHistogram category b = 1 := by
  unfold populationHistogram
  rw [← Finset.sum_div]
  rw [show (∑ b, ((categoryClass category b).card : ℝ)) =
      Fintype.card α by exact_mod_cast sum_categoryClass_card category]
  field_simp

@[simp] theorem finiteL1_sampleHistogram_populationHistogram
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (category : α → β) (σ : Equiv.Perm α) :
    finiteL1 (sampleHistogram S category σ)
        (populationHistogram category) =
      histogramL1Error S category σ := by
  unfold finiteL1 sampleHistogram populationHistogram histogramL1Error
  apply Finset.sum_congr rfl
  intro b _
  have hclass :
      @categoryClass α β _ (fun a b => Classical.propDecidable (a = b))
          category b =
        @categoryClass α β _ _ category b := by
    ext a
    simp [categoryClass]
  rw [hclass]

/-- Fully specialized pilot-learning theorem.  The pilot chooses the exact
minimum over the finite executable family, and its expected value on the
target histogram is within the standard `sqrt(card β / |S|)` loss of any
fixed target template. -/
theorem uniformSample_minimizingGridTemplate_le
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    {N : ℕ} (hN : 0 < N)
    (S : Finset α) (category : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    (price : β → ℝ) {L : ℝ} (hL0 : 0 ≤ L)
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L)
    (target : GridTemplate β N) :
    uniformAverage (fun σ : Equiv.Perm α =>
        gridTemplateValue (populationHistogram category) price
          (minimizingGridTemplate (N := N)
            (sampleHistogram S category σ) price)) ≤
      gridTemplateValue (populationHistogram category) price target +
        24 * (L + 1) *
          Real.sqrt ((Fintype.card β : ℝ) / S.card) := by
  let sampleValue : Equiv.Perm α → GridTemplate β N → ℝ := fun σ T =>
    gridTemplateValue (sampleHistogram S category σ) price T
  let targetValue : GridTemplate β N → ℝ := fun T =>
    gridTemplateValue (populationHistogram category) price T
  let chosen : Equiv.Perm α → GridTemplate β N := fun σ =>
    minimizingGridTemplate (N := N) (sampleHistogram S category σ) price
  have hstable : ∀ σ T,
      |sampleValue σ T - targetValue T| ≤
        (12 * (L + 1)) * histogramL1Error S category σ := by
    intro σ T
    dsimp [sampleValue, targetValue]
    simpa using gridTemplateValue_lipschitz hN
      (sampleHistogram_nonneg S category σ)
      (populationHistogram_nonneg category)
      (sampleHistogram_mass_one S hS category σ)
      (populationHistogram_mass_one category)
      hprice0 hpriceL T
  have hchosen : ∀ σ T, sampleValue σ (chosen σ) ≤ sampleValue σ T := by
    intro σ T
    exact minimizingGridTemplate_minimizes
      (sampleHistogram S category σ) price T
  have hC : 0 ≤ 12 * (L + 1) := by positivity
  have hlearn := uniformSample_empirical_minimizer_le S category hS hn hC
    hstable hchosen (targetMin := target)
  dsimp [sampleValue, targetValue, chosen] at hlearn ⊢
  convert hlearn using 1 <;> ring

/-! ## Positive grids with a distinguished zero atom -/

def positiveGridPrice {ι : Type*} (price : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => price i

def GridTemplate.positiveFluidTemplate
    {ι : Type*} {N : ℕ} (T : GridTemplate ι N) : FluidTemplate (Option ι) where
  low
    | none => 1
    | some i => boolWeight (T.1.low i)
  medium
    | none => 0
    | some i => boolWeight (T.1.medium i)
  high
    | none => 0
    | some i => boolWeight (T.high i)

def positiveGridTemplateValue
    {ι : Type*} [Fintype ι] {N : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (T : GridTemplate ι N) : ℝ :=
  canonicalFluidCost
    (templateMoments D (positiveGridPrice price) T.positiveFluidTemplate)
    T.fraction

noncomputable def minimizingPositiveGridTemplate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) : GridTemplate ι N :=
  (Finset.exists_min_image (Finset.univ : Finset (GridTemplate ι N))
    (positiveGridTemplateValue D price) Finset.univ_nonempty).choose

theorem minimizingPositiveGridTemplate_minimizes
    {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (T : GridTemplate ι N) :
    positiveGridTemplateValue D price
        (minimizingPositiveGridTemplate (N := N) D price) ≤
      positiveGridTemplateValue D price T := by
  exact (Finset.exists_min_image
    (Finset.univ : Finset (GridTemplate ι N))
      (positiveGridTemplateValue D price) Finset.univ_nonempty).choose_spec.2
      T (by simp)

theorem GridTemplate.positive_selector_bounds
    {ι : Type*} {N : ℕ} (T : GridTemplate ι N) :
    (∀ b, 0 ≤ T.positiveFluidTemplate.low b) ∧
    (∀ b, T.positiveFluidTemplate.low b ≤ 1) ∧
    (∀ b, 0 ≤ T.positiveFluidTemplate.medium b) ∧
    (∀ b, T.positiveFluidTemplate.medium b ≤ 1) ∧
    (∀ b, 0 ≤ T.positiveFluidTemplate.high b) ∧
    (∀ b, T.positiveFluidTemplate.high b ≤ 1) := by
  constructor
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).1
  constructor
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).2
  constructor
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).1
  constructor
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).2
  constructor
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).1
  · intro b; cases b with
    | none => simp [positiveFluidTemplate]
    | some i => exact (boolWeight_mem_Icc _).2

theorem positiveGridTemplateValue_lipschitz
    {ι : Type*} [Fintype ι] [Nonempty ι] {N : ℕ}
    {D E : Option ι → ℝ} {price : ι → ℝ} {L : ℝ} (hN : 0 < N)
    (hD : ∀ b, 0 ≤ D b) (hE : ∀ b, 0 ≤ E b)
    (hDmass : ∑ b, D b = 1) (hEmass : ∑ b, E b = 1)
    (hprice0 : ∀ i, 0 ≤ price i) (hpriceL : ∀ i, price i ≤ L)
    (T : GridTemplate ι N) :
    |positiveGridTemplateValue D price T -
        positiveGridTemplateValue E price T| ≤
      12 * (L + 1) * finiteL1 D E := by
  have hoption0 : ∀ b, 0 ≤ positiveGridPrice price b := by
    intro b; cases b with
    | none => simp [positiveGridPrice]
    | some i => simpa [positiveGridPrice] using hprice0 i
  have hoptionL : ∀ b, positiveGridPrice price b ≤ L := by
    intro b; cases b with
    | none =>
        have hL0 : 0 ≤ L := (hprice0 (Classical.choice inferInstance)).trans
          (hpriceL (Classical.choice inferInstance))
        simpa [positiveGridPrice] using hL0
    | some i => simpa [positiveGridPrice] using hpriceL i
  obtain ⟨hlow0, hlow1, hmedium0, hmedium1, hhigh0, hhigh1⟩ :=
    T.positive_selector_bounds
  exact template_canonicalFluidCost_lipschitz
    hD hE hDmass hEmass hoption0 hoptionL
      hlow0 hlow1 hmedium0 hmedium1 hhigh0 hhigh1
      T.fraction_nonneg (T.fraction_le_one hN)

/-- Pilot learning for the actual zero-preserving grid used in the optional
testing theorem. -/
theorem uniformSample_minimizingPositiveGridTemplate_le
    {α ι : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (hN : 0 < N)
    (S : Finset α) (category : α → Option ι)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    (price : ι → ℝ) {L : ℝ} (hL0 : 0 ≤ L)
    (hprice0 : ∀ i, 0 ≤ price i) (hpriceL : ∀ i, price i ≤ L)
    (target : GridTemplate ι N) :
    uniformAverage (fun σ : Equiv.Perm α =>
        positiveGridTemplateValue (populationHistogram category) price
          (minimizingPositiveGridTemplate (N := N)
            (sampleHistogram S category σ) price)) ≤
      positiveGridTemplateValue (populationHistogram category) price target +
        24 * (L + 1) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) := by
  let sampleValue : Equiv.Perm α → GridTemplate ι N → ℝ := fun σ T =>
    positiveGridTemplateValue (sampleHistogram S category σ) price T
  let targetValue : GridTemplate ι N → ℝ := fun T =>
    positiveGridTemplateValue (populationHistogram category) price T
  let chosen : Equiv.Perm α → GridTemplate ι N := fun σ =>
    minimizingPositiveGridTemplate (N := N)
      (sampleHistogram S category σ) price
  have hstable : ∀ σ T,
      |sampleValue σ T - targetValue T| ≤
        (12 * (L + 1)) * histogramL1Error S category σ := by
    intro σ T
    dsimp [sampleValue, targetValue]
    simpa using positiveGridTemplateValue_lipschitz hN
      (sampleHistogram_nonneg S category σ)
      (populationHistogram_nonneg category)
      (sampleHistogram_mass_one S hS category σ)
      (populationHistogram_mass_one category)
      hprice0 hpriceL T
  have hchosen : ∀ σ T, sampleValue σ (chosen σ) ≤ sampleValue σ T := by
    intro σ T
    exact minimizingPositiveGridTemplate_minimizes
      (sampleHistogram S category σ) price T
  have hC : 0 ≤ 12 * (L + 1) := by positivity
  have hlearn := uniformSample_empirical_minimizer_le S category hS hn hC
    hstable hchosen (targetMin := target)
  dsimp [sampleValue, targetValue, chosen] at hlearn ⊢
  convert hlearn using 1 <;> ring

end

end RandomizedOptional
end SchedulingPaper
