import SchedulingPaper.RandomizedOperationalStrategy
import Mathlib.Tactic

/-!
# The obligatory learner with a variable cutoff

The sharp worst-case theorem uses the fixed companion cutoff `32`, whereas
instance optimality needs one size-indexed policy whose cutoff tends to
infinity.  This file separates that genuinely variable part from the fixed
constant proof.  The overflow representative is `(d+1)η`, so it remains
strictly beyond the cutoff `dη` for every positive mesh.

The policy is otherwise the same public-transcript policy: test a pilot,
compute a maximum-density category set, drain the positive early pilot jobs,
process later early jobs immediately, and finish the deferred tail in SPT
order.  The generic work-rank proof from `RandomizedOperationalStrategy`
then gives legality and termination without any cutoff-specific argument.
-/

namespace SchedulingPaper
namespace Online

open RandomizedObligatory

noncomputable section

/-- Rounded representative for a variable cutoff.  The last category is the
first grid point strictly beyond `dη`, rather than the fixed sentinel `33`. -/
def growingQuantizedRepresentative (d : ℕ) (η : ℝ)
    (b : QuantizedCategory d) : ℝ :=
  if b.val = 0 then 0 else (b.val : ℝ) * η

theorem growingQuantizedRepresentative_nonneg
    (d : ℕ) {η : ℝ} (hη : 0 ≤ η) (b : QuantizedCategory d) :
    0 ≤ growingQuantizedRepresentative d η b := by
  unfold growingQuantizedRepresentative
  split_ifs <;> positivity

@[simp] theorem growingQuantizedRepresentative_zero
    (d : ℕ) (η : ℝ) :
    growingQuantizedRepresentative d η
      (⟨0, by omega⟩ : QuantizedCategory d) = 0 := by
  simp [growingQuantizedRepresentative]

@[simp] theorem growingQuantizedRepresentative_overflow
    (d : ℕ) (η : ℝ) :
    growingQuantizedRepresentative d η
      (⟨d + 1, by omega⟩ : QuantizedCategory d) = (d + 1 : ℕ) * η := by
  simp [growingQuantizedRepresentative]

/-- On all nonoverflow categories, the variable representative is exactly
the original finite-bin representative. -/
theorem growingQuantizedRepresentative_eq_fixed_of_le
    (d : ℕ) (η : ℝ) {b : QuantizedCategory d} (hb : b.val ≤ d) :
    growingQuantizedRepresentative d η b =
      quantizedRepresentative d η b := by
  rw [quantizedRepresentative_eq_mul_of_le d η hb]
  unfold growingQuantizedRepresentative
  by_cases hb0 : b.val = 0 <;> simp [hb0]

/-- The variable overflow category lies strictly beyond the cutoff. -/
theorem growingThresholdClosure_excludes_overflow
    (d : ℕ) {η θ : ℝ} (hη : 0 < η) (hθ : θ ≤ (d : ℝ) * η) :
    ¬ thresholdClosure (growingQuantizedRepresentative d η) θ
      (⟨d + 1, by omega⟩ : QuantizedCategory d) := by
  simp only [thresholdClosure, growingQuantizedRepresentative_overflow]
  push_cast
  nlinarith

/-- The sample maximum-density set computed with the variable grid
representatives. -/
def growingResultMaximumDensitySet
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) : Finset (QuantizedCategory d) :=
  chosenMaximumDensitySubset
    (resultCategoryFraction d η hη results)
    (growingQuantizedRepresentative d η)

theorem growingResultMaximumDensitySet_isMaximum
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) :
    IsMaximumDensitySubset
      (resultCategoryFraction d η hη results)
      (growingQuantizedRepresentative d η)
      (growingResultMaximumDensitySet d η hη results) :=
  chosenMaximumDensitySubset_isMaximum _ _

/-- Category fractions of a nonempty public sample form a probability
histogram. -/
theorem sum_resultCategoryFraction_eq_one
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (hne : results ≠ []) :
    ∑ b, resultCategoryFraction d η hη results b = 1 := by
  classical
  have hcount :
      (∑ b : QuantizedCategory d,
        (results.filter fun result =>
          quantizedCategory d η result.2 hη = b).length) =
        results.length := by
    clear hne
    induction results with
    | nil => simp
    | cons result results ih =>
        rw [show (fun b : QuantizedCategory d =>
            ((result :: results).filter fun item =>
              quantizedCategory d η item.2 hη = b).length) =
            (fun b => (if quantizedCategory d η result.2 hη = b then 1 else 0) +
              (results.filter fun item =>
                quantizedCategory d η item.2 hη = b).length) by
          funext b
          by_cases hb : quantizedCategory d η result.2 hη = b <;>
            simp [List.filter_cons, hb] <;> omega]
        rw [Finset.sum_add_distrib, ih]
        simp
        omega
  unfold resultCategoryFraction
  rw [← Finset.sum_div]
  have hcountR :
      (∑ b : QuantizedCategory d,
        ((results.filter fun result =>
          quantizedCategory d η result.2 hη = b).length : ℝ)) =
        results.length := by
    exact_mod_cast hcount
  rw [hcountR]
  exact div_self (by
    have hlen : 0 < results.length := List.length_pos_iff.mpr hne
    positivity)

/-- A bounded nonnegative processing time has a nonoverflow category and is
rounded upward by less than one variable-grid cell. -/
theorem growingQuantized_rounding_bounds
    (d : ℕ) {η p : ℝ} (hη : 0 < η) (hp : 0 ≤ p)
    (hcap : p ≤ (d : ℝ) * η) :
    p ≤ growingQuantizedRepresentative d η
        (quantizedCategory d η p hη) ∧
      growingQuantizedRepresentative d η
          (quantizedCategory d η p hη) ≤ p + η := by
  by_cases hp0 : p = 0
  · subst p
    rw [quantizedCategory_zero d hη,
      growingQuantizedRepresentative_zero]
    exact ⟨le_rfl, by simpa using hη.le⟩
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  obtain ⟨hlower, hupper⟩ :=
    quantized_rounding_bounds d hη hpPos hcap
  have hratio : p / η ≤ (d : ℝ) := by
    rw [div_le_iff₀ hη]
    simpa [mul_comm] using hcap
  have hceil : ⌈p / η⌉₊ ≤ d := Nat.ceil_le.mpr hratio
  have hcat : (quantizedCategory d η p hη).val ≤ d := by
    simp [quantizedCategory, hp0, hcap, hceil]
  rw [growingQuantizedRepresentative_eq_fixed_of_le d η hcat]
  exact ⟨hlower, hupper.le⟩

private theorem sum_filterLength_mul_representative
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (q : QuantizedCategory d → ℝ)
    (results : List (Label n × ℝ)) :
    (∑ b : QuantizedCategory d,
        ((results.filter fun result =>
          quantizedCategory d η result.2 hη = b).length : ℝ) * q b) =
      (results.map fun result =>
        q (quantizedCategory d η result.2 hη)).sum := by
  classical
  induction results with
  | nil => simp
  | cons result results ih =>
      rw [show (fun b : QuantizedCategory d =>
          (((result :: results).filter fun item =>
            quantizedCategory d η item.2 hη = b).length : ℝ) * q b) =
          (fun b =>
            (if quantizedCategory d η result.2 hη = b then q b else 0) +
              ((results.filter fun item =>
                quantizedCategory d η item.2 hη = b).length : ℝ) * q b) by
        funext b
        by_cases hb : quantizedCategory d η result.2 hη = b <;>
          simp [hb] <;> ring]
      rw [Finset.sum_add_distrib, ih]
      simp

/-- The rounded first moment of a nonempty bounded public sample is at most
`L+η`. -/
theorem resultCategoryFraction_growingMoment_le
    {n : ℕ} (d : ℕ) (η L : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (hne : results ≠ [])
    (hbounded : ∀ result ∈ results, 0 ≤ result.2 ∧ result.2 ≤ L)
    (hcutoff : L ≤ (d : ℝ) * η) :
    subsetMoment (resultCategoryFraction d η hη results)
      (growingQuantizedRepresentative d η) Finset.univ ≤ L + η := by
  let q := growingQuantizedRepresentative d η
  have hpoint : ∀ result ∈ results,
      q (quantizedCategory d η result.2 hη) ≤ L + η := by
    intro result hresult
    have hp := hbounded result hresult
    have hround := growingQuantized_rounding_bounds d hη hp.1
      (hp.2.trans hcutoff)
    exact hround.2.trans (by linarith)
  have hsum :
      (results.map fun result =>
        q (quantizedCategory d η result.2 hη)).sum ≤
        results.length * (L + η) := by
    have h := List.sum_le_sum
      (l := results)
      (f := fun result => q (quantizedCategory d η result.2 hη))
      (g := fun _result => L + η) hpoint
    convert h using 1 <;> simp <;> ring
  unfold subsetMoment resultCategoryFraction
  rw [show (fun b : QuantizedCategory d =>
      ((results.filter fun result =>
        quantizedCategory d η result.2 hη = b).length : ℝ) /
          results.length * growingQuantizedRepresentative d η b) =
      (fun b =>
        (((results.filter fun result =>
          quantizedCategory d η result.2 hη = b).length : ℝ) *
            growingQuantizedRepresentative d η b) / results.length) by
    funext b
    ring]
  rw [← Finset.sum_div]
  rw [show (∑ b : QuantizedCategory d,
      ((results.filter fun result =>
        quantizedCategory d η result.2 hη = b).length : ℝ) *
          q b) =
      (results.map fun result =>
        q (quantizedCategory d η result.2 hη)).sum by
    exact sum_filterLength_mul_representative d η hη q results]
  have hlen : 0 < (results.length : ℝ) := by
    have : 0 < results.length := List.length_pos_iff.mpr hne
    positivity
  apply (div_le_iff₀ hlen).2
  have hsum' :
      (results.map fun result =>
        q (quantizedCategory d η result.2 hη)).sum ≤
        (results.length : ℝ) * (L + η) := by
    simpa using hsum
  simpa [mul_comm] using hsum'

/-- Learned inverse density, with fallback exactly when the selected inverse
density exceeds the supplied cutoff `B`. -/
def growingLearnedThresholdFromResults?
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) : Option ℝ :=
  let μ := resultCategoryFraction d η hη results
  let q := growingQuantizedRepresentative d η
  let selected := growingResultMaximumDensitySet d η hη results
  let a := subsetMass μ selected
  let m := subsetMoment μ q selected
  if _ha : 0 < a then
    let θ := (1 + m) / a
    if θ ≤ B then some θ else none
  else none

theorem growingLearnedThresholdFromResults_some
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) {θ : ℝ}
    (hlearn : growingLearnedThresholdFromResults? B d η hη results = some θ) :
    let μ := resultCategoryFraction d η hη results
    let q := growingQuantizedRepresentative d η
    let selected := growingResultMaximumDensitySet d η hη results
    0 < subsetMass μ selected ∧
      θ = (1 + subsetMoment μ q selected) / subsetMass μ selected ∧
      θ ≤ B := by
  unfold growingLearnedThresholdFromResults? at hlearn
  dsimp only at hlearn ⊢
  split at hlearn
  next ha =>
    split at hlearn
    next hθ =>
      simp only [Option.some.injEq] at hlearn
      subst θ
      exact ⟨ha, rfl, hθ⟩
    next => simp at hlearn
  next => simp at hlearn

/-- A positive competitor with inverse density at most `B` prevents
fallback.  This isolates the only fact later needed from bounded inputs: the
full pilot histogram is such a competitor. -/
theorem growingLearnedThresholdFromResults_ne_none_of_competitor
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ))
    (S : Finset (QuantizedCategory d))
    (hS : 0 < subsetMass (resultCategoryFraction d η hη results) S)
    (hSinv :
      (1 + subsetMoment (resultCategoryFraction d η hη results)
        (growingQuantizedRepresentative d η) S) /
          subsetMass (resultCategoryFraction d η hη results) S ≤ B) :
    growingLearnedThresholdFromResults? B d η hη results ≠ none := by
  let μ := resultCategoryFraction d η hη results
  let q := growingQuantizedRepresentative d η
  let selected := growingResultMaximumDensitySet d η hη results
  have hμ : ∀ b, 0 ≤ μ b :=
    resultCategoryFraction_nonneg d η hη results
  have hq : ∀ b, 0 ≤ q b :=
    growingQuantizedRepresentative_nonneg d hη.le
  have hmS : 0 ≤ subsetMoment μ q S := subsetMoment_nonneg hμ hq S
  have hdenS : 0 < 1 + subsetMoment μ q S := by linarith
  have hdensityS : 0 < subsetDensity μ q S := by
    exact div_pos hS hdenS
  have hmax := growingResultMaximumDensitySet_isMaximum d η hη results
  have hdensitySelected : 0 < subsetDensity μ q selected :=
    hdensityS.trans_le (hmax S)
  have ha0 : 0 ≤ subsetMass μ selected := subsetMass_nonneg hμ selected
  have hm0 : 0 ≤ subsetMoment μ q selected :=
    subsetMoment_nonneg hμ hq selected
  have ha : 0 < subsetMass μ selected := by
    by_contra hnot
    have hz : subsetMass μ selected = 0 :=
      le_antisymm (le_of_not_gt hnot) ha0
    rw [subsetDensity, hz, zero_div] at hdensitySelected
    exact (lt_irrefl 0) hdensitySelected
  have hden : 0 < 1 + subsetMoment μ q selected := by linarith
  have hinv :
      (1 + subsetMoment μ q selected) / subsetMass μ selected ≤
        (1 + subsetMoment μ q S) / subsetMass μ S := by
    rw [div_le_div_iff₀ ha hS]
    have hcompare := hmax S
    unfold subsetDensity at hcompare
    rw [div_le_div_iff₀ hdenS hden] at hcompare
    nlinarith
  have hcap :
      (1 + subsetMoment μ q selected) / subsetMass μ selected ≤ B :=
    hinv.trans hSinv
  unfold growingLearnedThresholdFromResults?
  dsimp only
  split
  next => simp
  next hnot => exact False.elim (hnot ha)

/-- On a nonempty `L`-bounded pilot the full category set has inverse
density at most `1+L+η`; consequently any cutoff above that quantity makes
the learned branch unconditional. -/
theorem growingLearnedThresholdFromResults_ne_none_of_bounded
    {n : ℕ} (B : ℝ) (d : ℕ) (η L : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (hne : results ≠ [])
    (hbounded : ∀ result ∈ results, 0 ≤ result.2 ∧ result.2 ≤ L)
    (hgrid : L ≤ (d : ℝ) * η) (hB : 1 + L + η ≤ B) :
    growingLearnedThresholdFromResults? B d η hη results ≠ none := by
  let μ := resultCategoryFraction d η hη results
  let q := growingQuantizedRepresentative d η
  have hmass : subsetMass μ Finset.univ = 1 := by
    unfold subsetMass
    simpa [μ] using sum_resultCategoryFraction_eq_one d η hη results hne
  have hmoment : subsetMoment μ q Finset.univ ≤ L + η := by
    simpa [μ, q] using
      resultCategoryFraction_growingMoment_le d η L hη results hne
        hbounded hgrid
  apply growingLearnedThresholdFromResults_ne_none_of_competitor
    B d η hη results Finset.univ
  · rw [hmass]
    norm_num
  · rw [hmass]
    simp only [div_one]
    linarith

/-- Short public export name for the bounded-pilot no-fallback theorem. -/
theorem boundedPilot_uses_learnedBranch
    {n : ℕ} (B : ℝ) (d : ℕ) (η L : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (hne : results ≠ [])
    (hbounded : ∀ result ∈ results, 0 ≤ result.2 ∧ result.2 ≤ L)
    (hgrid : L ≤ (d : ℝ) * η) (hB : 1 + L + η ≤ B) :
    growingLearnedThresholdFromResults? B d η hη results ≠ none :=
  growingLearnedThresholdFromResults_ne_none_of_bounded
    B d η L hη results hne hbounded hgrid hB

/-- Successful learning supplies the complete threshold-closure density
identity, now with the variable cutoff. -/
theorem growingLearnedThresholdFromResults_closure_certificate
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) {θ : ℝ}
    (hlearn : growingLearnedThresholdFromResults? B d η hη results = some θ) :
    let μ := resultCategoryFraction d η hη results
    let q := growingQuantizedRepresentative d η
    0 ≤ θ ∧ θ ≤ B ∧
      1 + selectedMoment μ q (thresholdClosure q θ) =
        selectedMass μ (thresholdClosure q θ) * θ := by
  dsimp only
  let μ := resultCategoryFraction d η hη results
  let q := growingQuantizedRepresentative d η
  let selected := growingResultMaximumDensitySet d η hη results
  obtain ⟨ha, hθeq, hθB⟩ :=
    growingLearnedThresholdFromResults_some B d η hη results hlearn
  have hμ : ∀ b, 0 ≤ μ b :=
    resultCategoryFraction_nonneg d η hη results
  have hq : ∀ b, 0 ≤ q b :=
    growingQuantizedRepresentative_nonneg d hη.le
  have hmax : IsMaximumDensitySubset μ q selected :=
    growingResultMaximumDensitySet_isMaximum d η hη results
  have hθpos : 0 < θ := by
    rw [hθeq]
    exact inverseDensity_pos hμ hq ha
  have hclosure := maximumDensity_thresholdClosure_preserves hμ hq hmax ha
    (by simpa [hθeq] using inverseDensity_identity ha)
  rw [← hθeq] at hclosure
  exact ⟨hθpos.le, hθB, by nlinarith [hclosure]⟩

/-- Canonical complete threshold closure for the variable-cutoff learner. -/
def growingLearnedClassifiesEarly
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (p : ℝ) : Bool :=
  match growingLearnedThresholdFromResults? B d η hη results with
  | none => false
  | some θ => decide <|
      thresholdClosure (growingQuantizedRepresentative d η) θ
        (quantizedCategory d η p hη)

/-- Every job selected by a successful variable-cutoff learner has actual
processing time at most `B`, provided the cutoff lies within the finite grid.
This is the cutoff-parametric replacement for the hardcoded `p≤16` lemma in
the fixed companion proof. -/
theorem growingLearnedClassifiesEarly_processing_le
    {n : ℕ} (B : ℝ) (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (p : ℝ) (hp : 0 ≤ p)
    (hBgrid : B ≤ (d : ℝ) * η)
    (hearly : growingLearnedClassifiesEarly B d η hη results p = true) :
    p ≤ B := by
  unfold growingLearnedClassifiesEarly at hearly
  cases hlearn : growingLearnedThresholdFromResults? B d η hη results with
  | none => simp [hlearn] at hearly
  | some θ =>
      have hcertificate :=
        growingLearnedThresholdFromResults_some B d η hη results hlearn
      have hθB := hcertificate.2.2
      have hselected :
          thresholdClosure (growingQuantizedRepresentative d η) θ
            (quantizedCategory d η p hη) := by
        simpa [hlearn] using hearly
      have hpgrid : p ≤ (d : ℝ) * η := by
        by_contra hnot
        have hover : (d : ℝ) * η < p := lt_of_not_ge hnot
        have hcat := quantizedCategory_overflow d hη hover
        have hnotSelected := growingThresholdClosure_excludes_overflow
          d hη (hθB.trans hBgrid)
        exact hnotSelected (by simpa [hcat] using hselected)
      have hround := growingQuantized_rounding_bounds d hη hp hpgrid
      have hqθ :
          growingQuantizedRepresentative d η
              (quantizedCategory d η p hη) ≤ θ := by
        simpa [thresholdClosure] using hselected
      exact hround.1.trans (hqθ.trans hθB)

def Transcript.growingSampleRemainingResults
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : List (Label n × ℝ) :=
  let sample := transcript.testResults.take k
  transcript.remainingTestResults.filter fun result =>
    result.1.val < k && decide (0 < result.2) &&
      growingLearnedClassifiesEarly B d η hη sample result.2

def Transcript.growingSamplePending?
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : Option (Label n) :=
  (shortestResult? <|
    transcript.growingSampleRemainingResults n k d B η hη).map Prod.fst

def Transcript.growingObligatoryPending?
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : Option (Label n) :=
  let tested := transcript.testResults.length
  if tested < k then none
  else
    match transcript.growingSamplePending? n k d B η hη with
    | some job => some job
    | none =>
        match transcript.getLast? with
        | some (.testResult job p) =>
            if k < tested &&
                growingLearnedClassifiesEarly B d η hη
                  (transcript.testResults.take k) p
              then some job else none
        | some (.processed _) | some (.rawCompleted _) | none => none

/-- Literal transcript-only obligatory policy at arbitrary cutoff and mesh. -/
def growingObligatoryStrategy
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η) : Strategy n :=
  testProcessStrategy fun transcript =>
    transcript.growingObligatoryPending? n k d B η hη

/-- Finite private-seed family obtained by uniformly relabelling the one
canonical transcript-only growing-cutoff policy. -/
def randomizedGrowingObligatoryStrategy
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η) :
    Equiv.Perm (Label n) → Strategy n :=
  fun order => (growingObligatoryStrategy n k d B η hη).relabel order

theorem growingSamplePending_selectsRemaining
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η) :
    SelectsRemainingTest fun transcript =>
      transcript.growingSamplePending? n k d B η hη := by
  intro transcript job hpending
  unfold Transcript.growingSamplePending? at hpending
  cases hshort : shortestResult?
      (transcript.growingSampleRemainingResults n k d B η hη) with
  | none => simp [hshort] at hpending
  | some result =>
      have hjob : result.1 = job := by simpa [hshort] using hpending
      have hmem := shortestResult?_mem hshort
      unfold Transcript.growingSampleRemainingResults at hmem
      simp only at hmem
      have hfiltered := List.mem_filter.mp hmem
      unfold Transcript.remainingTestResults at hfiltered
      have hremaining := List.mem_filter.mp hfiltered.1
      subst job
      left
      refine ⟨result.2, hremaining.1, ?_⟩
      simpa using hremaining.2

theorem growingObligatoryPending_selectsRemaining
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η) :
    SelectsRemainingTest fun transcript =>
      transcript.growingObligatoryPending? n k d B η hη := by
  intro transcript job hpending
  by_cases hsample : transcript.testResults.length < k
  · simp [Transcript.growingObligatoryPending?, hsample] at hpending
  · cases hselected :
        transcript.growingSamplePending? n k d B η hη with
    | some selectedJob =>
      have hremaining := growingSamplePending_selectsRemaining n k d B η hη
        transcript selectedJob hselected
      simp [Transcript.growingObligatoryPending?, hsample, hselected] at hpending
      subst job
      exact hremaining
    | none =>
      cases hlast : transcript.getLast? with
      | none =>
          simp [Transcript.growingObligatoryPending?, hsample,
            hselected, hlast] at hpending
      | some observation =>
          cases observation with
          | processed processedJob =>
              simp [Transcript.growingObligatoryPending?, hsample,
                hselected, hlast] at hpending
          | rawCompleted rawJob =>
              simp [Transcript.growingObligatoryPending?, hsample,
                hselected, hlast] at hpending
          | testResult testedJob p =>
              by_cases htake : k < transcript.testResults.length &&
                  growingLearnedClassifiesEarly B d η hη
                    (transcript.testResults.take k) p
              · simp [Transcript.growingObligatoryPending?, hsample,
                    hselected, hlast, htake] at hpending
                subst job
                exact Or.inr ⟨p, rfl⟩
              · simp [Transcript.growingObligatoryPending?, hsample,
                  hselected, hlast, htake] at hpending

/-- Every variable-cutoff policy is legal and completes all jobs within the
same universal work-rank bound as the fixed-cutoff companion. -/
theorem run_growingObligatoryStrategy_completed
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η) (oracle : Oracle n) :
    let result := run .infinite oracle
      (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run growingObligatoryStrategy
  simpa using
    runFuel_testProcessStrategy_completed_of_selectsRemaining
      (.infinite) oracle
      (growingObligatoryPending_selectsRemaining n k d B η hη) 0

/-- On a fixed input the completed growing-cutoff run records every label
exactly once, enabling the generic completion-cost accounting lemmas. -/
theorem run_growingObligatoryStrategy_completionLabels_perm
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let result := run .infinite (fixedOracle processingTime)
      (growingObligatoryStrategy n k d B η hη) (2 * n + 1)
    (result.config.transcript.completionLabels processingTime).Perm
      (List.ofFn id) := by
  unfold run growingObligatoryStrategy
  have hrun :=
    runFuel_testProcessStrategy_completed_with_completionInvariant_of_selectsRemaining
      (.infinite) processingTime
      (growingObligatoryPending_selectsRemaining n k d B η hη) 0
  let result :=
    runFuel (.infinite) (fixedOracle processingTime)
      (testProcessStrategy fun transcript =>
        transcript.growingObligatoryPending? n k d B η hη)
      (2 * n + 1) (Config.initial n)
  have hnodup :
      (result.config.transcript.completionLabels processingTime).Nodup :=
    hrun.2.2.2.1.nodup
  have hmem :
      ∀ job,
        job ∈ result.config.transcript.completionLabels processingTime := by
    intro job
    rw [hrun.2.2.2.1.mem_iff]
    simp [hrun.2.2.2.2 job, JobState.completionRecorded]
  apply
    (List.perm_ext_iff_of_nodup hnodup
      (List.nodup_ofFn.mpr Function.injective_id)).mpr
  intro job
  simp [hmem job]

end

end Online
end SchedulingPaper
