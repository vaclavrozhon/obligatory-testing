import SchedulingPaper.BlindOptimizationObservedTrace
import SchedulingPaper.BlindOptimizationAdversary
import SchedulingPaper.RandomizedHistogramL1

/-!
# Arbitrary-input lower bound for blind optimization

The hidden occurrence vector is placed uniformly behind the public labels.
The causal trace bijection turns the adaptive first-touch order into a fresh
uniform reveal permutation.  A centered urn increment has mean zero, while
the remaining-suffix mean has variance `O(1/k)`.  This gives a finite
`O(u n^(3/2))` remainder, uniformly over every complete deterministic policy.
-/

namespace SchedulingPaper
namespace BlindOptimization

open Randomized
open RandomizedOptional

noncomputable section

def normalizedProcessing {n : ℕ} (u : ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun job ↦ p job / u

theorem normalizedProcessing_mem_Icc {n : ℕ} {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u) :
    ∀ job, normalizedProcessing u p job ∈ Set.Icc (0 : ℝ) 1 := by
  intro job
  constructor
  · exact div_nonneg (hp job).1 hu.le
  · exact (div_le_one hu).2 (hp job).2

theorem processing_eq_u_mul_normalized {n : ℕ} {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (job : Fin n) :
    p job = u * normalizedProcessing u p job := by
  unfold normalizedProcessing
  field_simp [hu.ne']

theorem populationMean_eq_u_mul_normalized {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : 0 < u) (p : Fin n → ℝ) :
    populationMean p = u * populationMean (normalizedProcessing u p) := by
  unfold populationMean normalizedProcessing
  simp only [Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (∑ job, p job) = u * ∑ job, p job / u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro job _
    field_simp [hu.ne']
  rw [hsum]
  field_simp [hnR]

/-- First absolute moment of a remaining-suffix empirical mean. -/
theorem uniformAverage_abs_suffixMean_sub_populationMean_le
    {n : ℕ} (hn : 1 < n) (value : Fin n → ℝ)
    (hvalue0 : ∀ job, 0 ≤ value job) (hvalue1 : ∀ job, value job ≤ 1)
    (j : Fin n) :
    uniformAverage (fun reveal : Equiv.Perm (Fin n) ↦
      |permutationSuffixMean value reveal j - populationMean value|) ≤
      Real.sqrt (2 / (suffixPositions j).card) := by
  have habsSq := Randomized.uniformAverage_abs_sq_le_uniformAverage_sq
    (fun reveal : Equiv.Perm (Fin n) ↦
      permutationSuffixMean value reveal j - populationMean value)
  have hvariance := uniformAverage_permutationSuffixMean_sq_le
    hn value j hvalue0 hvalue1
  apply Real.le_sqrt_of_sq_le
  exact habsSq.trans hvariance

/-- A predictable zero-one selector cannot make the suffix-mean error more
negative than its first absolute moment. -/
theorem predictable_selected_suffixMean_lower
    {n : ℕ} (hn : 1 < n) (value : Fin n → ℝ)
    (hvalue0 : ∀ job, 0 ≤ value job) (hvalue1 : ∀ job, value job ≤ 1)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hzeroOne : ∀ j reveal, select j reveal = 0 ∨ select j reveal = 1)
    (j : Fin n) :
    -Real.sqrt (2 / (suffixPositions j).card) ≤
      uniformAverage (fun reveal ↦ select j reveal *
        (permutationSuffixMean value reveal j - populationMean value)) := by
  let difference : Equiv.Perm (Fin n) → ℝ := fun reveal ↦
    permutationSuffixMean value reveal j - populationMean value
  have habs := uniformAverage_abs_suffixMean_sub_populationMean_le
    hn value hvalue0 hvalue1 j
  calc
    -Real.sqrt (2 / (suffixPositions j).card) ≤
        -uniformAverage (fun reveal ↦ |difference reveal|) := neg_le_neg habs
    _ = uniformAverage (fun reveal ↦ -|difference reveal|) := by
      simpa using (uniformAverage_smul (-1)
        (fun reveal ↦ |difference reveal|)).symm
    _ ≤ uniformAverage (fun reveal ↦ select j reveal * difference reveal) := by
      apply uniformAverage_mono
      intro reveal
      rcases hzeroOne j reveal with hzero | hone
      · rw [hzero]
        simp
      · rw [hone]
        simpa using neg_abs_le (difference reveal)
    _ = uniformAverage (fun reveal ↦ select j reveal *
        (permutationSuffixMean value reveal j - populationMean value)) := rfl

/-- Expected duration contribution at one reveal position. -/
theorem predictable_position_duration_lower
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hpredictable : PredictableSelector select)
    (hzeroOne : ∀ j reveal, select j reveal = 0 ∨ select j reveal = 1)
    (j : Fin n) :
    min u (1 + populationMean p) -
        u * Real.sqrt (2 / (suffixPositions j).card) ≤
      uniformAverage (fun reveal ↦
        u + select j reveal * (1 + p (reveal j) - u)) := by
  let value := normalizedProcessing u p
  let selector := select j
  let suffixError : Equiv.Perm (Fin n) → ℝ := fun reveal ↦
    selector reveal *
      (permutationSuffixMean value reveal j - populationMean value)
  have hvalue := normalizedProcessing_mem_Icc hu p hp
  have hmean : populationMean p = u * populationMean value := by
    exact populationMean_eq_u_mul_normalized (by omega) hu p
  have hcentered :
      uniformAverage (fun reveal ↦ selector reveal *
        (value (reveal j) - permutationSuffixMean value reveal j)) = 0 := by
    exact (hpredictable j).uniformAverage_mul_next_sub_suffixMean_eq_zero
      value selector j
  have hsuffix : -Real.sqrt (2 / (suffixPositions j).card) ≤
      uniformAverage suffixError := by
    exact predictable_selected_suffixMean_lower hn value
      (fun job ↦ (hvalue job).1) (fun job ↦ (hvalue job).2)
      select hzeroOne j
  have hselector0 : 0 ≤ uniformAverage selector := by
    apply uniformAverage_nonneg
    intro reveal
    rcases hzeroOne j reveal with h | h <;>
      simp [selector, h]
  have hselector1 : uniformAverage selector ≤ 1 := by
    simpa using uniformAverage_mono (f := selector)
      (g := fun _ : Equiv.Perm (Fin n) ↦ (1 : ℝ)) (by
        intro reveal
        rcases hzeroOne j reveal with h | h <;>
          simp [selector, h])
  have havg :
      uniformAverage (fun reveal ↦
          u + selector reveal * (1 + p (reveal j) - u)) =
        u + (1 + u * populationMean value - u) * uniformAverage selector +
          u * uniformAverage suffixError := by
    have hpoint : (fun reveal ↦
        u + selector reveal * (1 + p (reveal j) - u)) =
      (fun reveal ↦
        u + (1 + u * populationMean value - u) * selector reveal +
          u * (selector reveal *
            (value (reveal j) - permutationSuffixMean value reveal j)) +
          u * suffixError reveal) := by
      funext reveal
      rw [processing_eq_u_mul_normalized hu p (reveal j)]
      dsimp [value, selector, suffixError]
      ring
    rw [hpoint]
    simp only [uniformAverage_add, uniformAverage_const, uniformAverage_smul,
      hcentered, mul_zero, add_zero]
  have hbase : min u (1 + u * populationMean value) ≤
      u + (1 + u * populationMean value - u) * uniformAverage selector := by
    by_cases hcoefficient : 0 ≤ 1 + u * populationMean value - u
    · exact (min_le_left _ _).trans <| by
        nlinarith [mul_nonneg hcoefficient hselector0]
    · have hneg : 1 + u * populationMean value - u < 0 :=
        lt_of_not_ge hcoefficient
      exact (min_le_right _ _).trans <| by
        nlinarith
  rw [hmean]
  rw [havg]
  have husuffix :
      -(u * Real.sqrt (2 / (suffixPositions j).card)) ≤
        u * uniformAverage suffixError := by
    nlinarith [mul_le_mul_of_nonneg_left hsuffix hu.le]
  linarith

def revealDuration {n : ℕ} (u : ℝ) (p : Fin n → ℝ)
    (policy : ObservedTrace.CompletePolicy p) (position : Fin n)
    (reveal : Equiv.Perm (Fin n)) : ℝ :=
  u + ObservedTrace.compiledOptimizeSelector p policy position reveal *
    (1 + p (reveal position) - u)

def revealWeightedCost {n : ℕ} (u : ℝ) (p : Fin n → ℝ)
    (policy : ObservedTrace.CompletePolicy p)
    (reveal : Equiv.Perm (Fin n)) : ℝ :=
  ∑ position : Fin n, (n - position.val : ℕ) *
    revealDuration u p policy position reveal

/-- Exact pathwise accounting after the causal reveal-order change of
variables. -/
theorem runCost_eq_revealWeightedCost_revealOrder
    {n : ℕ} (u : ℝ) (p : Fin n → ℝ)
    (policy : ObservedTrace.CompletePolicy p)
    (placement : Equiv.Perm (Fin n)) :
    Online.runCost u (ObservedTrace.placedProcessing p placement)
        policy.strategy n =
      revealWeightedCost u p policy
        (RandomizedOptional.TraceBijection.revealOrder
          (ObservedTrace.touchTrace p policy) placement) := by
  let transcript :=
    (ObservedTrace.settledRun p policy placement).config.transcript
  have hlength : transcript.length = n := by
    exact Online.transcript_length_eq_n_of_completes (policy.completes placement)
  unfold Online.runCost Online.completionCost
  change prefixCost (transcript.map (Online.Observation.duration u)) = _
  rw [← RandomizedOptional.ObservedTrace.list_ofFn_cast_get transcript hlength,
    List.map_ofFn, Adversary.prefixCost_ofFn_eq_weighted_sum]
  unfold revealWeightedCost
  apply Finset.sum_congr rfl
  intro position _
  congr 1
  unfold revealDuration ObservedTrace.compiledOptimizeSelector
  rw [RandomizedOptional.TraceBijection.compiledTestSelector_on_revealOrder]
  let observation :=
    (ObservedTrace.settledRun p policy placement).config.transcript.get
      (Fin.cast (ObservedTrace.settled_length p policy placement).symm position)
  have hchoice := ObservedTrace.touchTrace_choice p policy placement position
  have htruth := Online.run_truthful
    (ObservedTrace.placedProcessing p placement) policy.strategy n
  have hmem : observation ∈ transcript := by
    exact List.get_mem transcript
      (Fin.cast (ObservedTrace.settled_length p policy placement).symm position)
  change Online.Observation.duration u observation = _
  cases hobservation : observation with
  | rawCompleted job =>
      have hobs :
          (ObservedTrace.settledRun p policy placement).config.transcript.get
              (Fin.cast (ObservedTrace.settled_length p policy placement).symm position) =
            Online.Observation.rawCompleted job := by
        simpa [observation] using hobservation
      have hpair :
          ((ObservedTrace.touchTrace p policy placement).label position,
            (ObservedTrace.touchTrace p policy placement).kind position) =
          (job, RandomizedOptional.TraceBijection.TouchKind.blind) := by
        apply Prod.ext
        · change (ObservedTrace.touchTrace p policy placement).label position = job
          rw [show (ObservedTrace.touchTrace p policy placement).label position =
              ObservedTrace.touchLabelOrder p policy placement position by rfl,
            ObservedTrace.touchLabelOrder_apply, hobs]
          rfl
        · change ObservedTrace.observationKind
              ((ObservedTrace.settledRun p policy placement).config.transcript.get
                (Fin.cast (ObservedTrace.settled_length p policy placement).symm position)) = _
          rw [hobs]
          rfl
      have hlabel : (ObservedTrace.touchTrace p policy placement).label position = job := by
        exact congrArg Prod.fst hpair
      have hkind : (ObservedTrace.touchTrace p policy placement).kind position =
          RandomizedOptional.TraceBijection.TouchKind.blind := by
        exact congrArg Prod.snd hpair
      simp [Online.Observation.duration, hkind]
  | optimizedCompleted job processing =>
      have hobs :
          (ObservedTrace.settledRun p policy placement).config.transcript.get
              (Fin.cast (ObservedTrace.settled_length p policy placement).symm position) =
            Online.Observation.optimizedCompleted job processing := by
        simpa [observation] using hobservation
      have hpair :
          ((ObservedTrace.touchTrace p policy placement).label position,
            (ObservedTrace.touchTrace p policy placement).kind position) =
          (job, RandomizedOptional.TraceBijection.TouchKind.test) := by
        apply Prod.ext
        · change (ObservedTrace.touchTrace p policy placement).label position = job
          rw [show (ObservedTrace.touchTrace p policy placement).label position =
              ObservedTrace.touchLabelOrder p policy placement position by rfl,
            ObservedTrace.touchLabelOrder_apply, hobs]
          rfl
        · change ObservedTrace.observationKind
              ((ObservedTrace.settledRun p policy placement).config.transcript.get
                (Fin.cast (ObservedTrace.settled_length p policy placement).symm position)) = _
          rw [hobs]
          rfl
      have hlabel : (ObservedTrace.touchTrace p policy placement).label position = job := by
        exact congrArg Prod.fst hpair
      have hkind : (ObservedTrace.touchTrace p policy placement).kind position =
          RandomizedOptional.TraceBijection.TouchKind.test := by
        exact congrArg Prod.snd hpair
      have hprocessing : processing =
          ObservedTrace.placedProcessing p placement job := by
        apply htruth job processing
        change Online.Observation.optimizedCompleted job processing ∈ transcript
        rw [← hobs]
        exact hmem
      simp [Online.Observation.duration, hkind,
        RandomizedOptional.TraceBijection.revealOrder, hlabel,
        ObservedTrace.placedProcessing, hprocessing]

/-- Uniform hidden placement is exactly the uniform average of the compiled
predictable reveal formula. -/
theorem uniformAverage_runCost_eq_revealWeightedCost
    {n : ℕ} (u : ℝ) (p : Fin n → ℝ)
    (policy : ObservedTrace.CompletePolicy p) :
    uniformAverage (fun placement : Equiv.Perm (Fin n) ↦
      Online.runCost u (ObservedTrace.placedProcessing p placement)
        policy.strategy n) =
      uniformAverage (revealWeightedCost u p policy) := by
  have hpoint : (fun placement : Equiv.Perm (Fin n) ↦
      Online.runCost u (ObservedTrace.placedProcessing p placement)
        policy.strategy n) =
      (fun placement ↦ revealWeightedCost u p policy
        (RandomizedOptional.TraceBijection.revealOrder
          (ObservedTrace.touchTrace p policy) placement)) := by
    funext placement
    exact runCost_eq_revealWeightedCost_revealOrder u p policy placement
  rw [hpoint]
  exact RandomizedOptional.TraceBijection.uniformAverage_revealOrder p
    (ObservedTrace.touchTrace p policy)
    (ObservedTrace.touchTrace_causal p policy)
    (revealWeightedCost u p policy)

theorem reverseWeight_mul_sqrt_suffix_le {n : ℕ} (j : Fin n) :
    ((n - j.val : ℕ) : ℝ) *
        Real.sqrt (2 / (suffixPositions j).card) ≤
      Real.sqrt (2 * n) := by
  let K : ℝ := ((n - j.val : ℕ) : ℝ)
  have hKnat : 0 < n - j.val := by omega
  have hK : 0 < K := by
    change (0 : ℝ) < ((n - j.val : ℕ) : ℝ)
    exact_mod_cast hKnat
  have hKn : K ≤ (n : ℝ) := by
    dsimp [K]
    exact_mod_cast Nat.sub_le n j.val
  have hdiv0 : 0 ≤ 2 / K := by positivity
  simp only [suffixPositions_card]
  change K * Real.sqrt (2 / K) ≤ Real.sqrt (2 * (n : ℝ))
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt hdiv0]
  field_simp [hK.ne']
  nlinarith

/-- The finite arbitrary-input lower bound for every deterministic complete
blind-optimization policy.  Its normalized remainder is at most
`u * sqrt (2*n) / n`, hence vanishes for fixed `u`. -/
theorem completePolicy_expectedCost_ge_instanceBenchmark
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u)
    (policy : ObservedTrace.CompletePolicy p) :
    (n : ℝ) * (n + 1) / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      uniformAverage (fun placement : Equiv.Perm (Fin n) ↦
        Online.runCost u (ObservedTrace.placedProcessing p placement)
          policy.strategy n) := by
  let select := ObservedTrace.compiledOptimizeSelector p policy
  let best := min u (1 + populationMean p)
  have hposition : ∀ position : Fin n,
      ((n - position.val : ℕ) : ℝ) *
          (best - u * Real.sqrt (2 / (suffixPositions position).card)) ≤
        ((n - position.val : ℕ) : ℝ) *
          uniformAverage (fun reveal : Equiv.Perm (Fin n) ↦
            revealDuration u p policy position reveal) := by
    intro position
    apply mul_le_mul_of_nonneg_left
    · exact predictable_position_duration_lower hn hu p hp select
        (ObservedTrace.compiledOptimizeSelector_predictable p policy)
        (ObservedTrace.compiledOptimizeSelector_zero_one p policy) position
    · positivity
  have hweighted :
      (∑ position : Fin n,
        ((n - position.val : ℕ) : ℝ) *
          (best - u * Real.sqrt (2 / (suffixPositions position).card))) ≤
      ∑ position : Fin n,
        ((n - position.val : ℕ) : ℝ) *
          uniformAverage (fun reveal : Equiv.Perm (Fin n) ↦
            revealDuration u p policy position reveal) := by
    exact Finset.sum_le_sum fun position _ ↦ hposition position
  have herror :
      (∑ position : Fin n,
        ((n - position.val : ℕ) : ℝ) * u *
          Real.sqrt (2 / (suffixPositions position).card)) ≤
        n * u * Real.sqrt (2 * n) := by
    calc
      (∑ position : Fin n,
          ((n - position.val : ℕ) : ℝ) * u *
            Real.sqrt (2 / (suffixPositions position).card)) ≤
          ∑ _position : Fin n, u * Real.sqrt (2 * n) := by
        apply Finset.sum_le_sum
        intro position _
        have hweight := reverseWeight_mul_sqrt_suffix_le position
        nlinarith [mul_le_mul_of_nonneg_left hweight hu.le]
      _ = n * u * Real.sqrt (2 * n) := by simp; ring
  have hweights :
      (∑ position : Fin n, ((n - position.val : ℕ) : ℝ)) =
        (n : ℝ) * (n + 1) / 2 := by
    have htwo := Adversary.two_mul_sum_fin_reverse_weights n
    have htwoR :
        2 * (∑ position : Fin n, ((n - position.val : ℕ) : ℝ)) =
          (n : ℝ) * (n + 1) := by
      exact_mod_cast htwo
    linarith
  have hleft :
      (n : ℝ) * (n + 1) / 2 * best -
          n * u * Real.sqrt (2 * n) ≤
        ∑ position : Fin n,
          ((n - position.val : ℕ) : ℝ) *
            (best - u * Real.sqrt (2 / (suffixPositions position).card)) := by
    have herror' :
        (∑ position : Fin n,
          ((n - position.val : ℕ) : ℝ) *
            (u * Real.sqrt (2 / (suffixPositions position).card))) ≤
          n * u * Real.sqrt (2 * n) := by
      simpa [mul_assoc] using herror
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hweights]
    linarith
  rw [uniformAverage_runCost_eq_revealWeightedCost u p policy]
  calc
    (n : ℝ) * (n + 1) / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      ∑ position : Fin n,
        ((n - position.val : ℕ) : ℝ) *
          (best - u * Real.sqrt (2 / (suffixPositions position).card)) := by
        exact hleft
    _ ≤ ∑ position : Fin n,
        ((n - position.val : ℕ) : ℝ) *
          uniformAverage (fun reveal : Equiv.Perm (Fin n) ↦
            revealDuration u p policy position reveal) := hweighted
    _ = uniformAverage (revealWeightedCost u p policy) := by
      unfold revealWeightedCost
      rw [uniformAverage_fintype_sum]
      apply Finset.sum_congr rfl
      intro position _
      rw [uniformAverage_smul]

/-- The paper's `n²/2` normalization, obtained from the slightly stronger
triangular finite leading term above. -/
theorem completePolicy_expectedCost_ge_instanceBenchmark_nsq
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u)
    (policy : ObservedTrace.CompletePolicy p) :
    (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      uniformAverage (fun placement : Equiv.Perm (Fin n) ↦
        Online.runCost u (ObservedTrace.placedProcessing p placement)
          policy.strategy n) := by
  have hfinite := completePolicy_expectedCost_ge_instanceBenchmark
    hn hu p hp policy
  have hn0 : 0 < n := by omega
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun job _ ↦ (hp job).1
    · positivity
  have hbest0 : 0 ≤ min u (1 + populationMean p) :=
    le_min hu.le (by linarith)
  calc
    (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      (n : ℝ) * (n + 1) / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) := by
          have hnR : 0 ≤ (n : ℝ) := by positivity
          nlinarith
    _ ≤ _ := hfinite

/-- Finite-private-seed randomized lower bound.  Both expectations are
literal finite uniform averages: first over the hidden placement, then over
the algorithm's private seed. -/
theorem finiteSeed_expectedCost_ge_instanceBenchmark_nsq
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u)
    (Seeds : Type*) [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Online.Strategy n)
    (hcompletes : ∀ seed placement,
      Online.Completes (ObservedTrace.placedProcessing p placement)
        (strategy seed)) :
    (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      uniformAverage (fun seed : Seeds ↦
        uniformAverage (fun placement : Equiv.Perm (Fin n) ↦
          Online.runCost u (ObservedTrace.placedProcessing p placement)
            (strategy seed) n)) := by
  let policy : Seeds → ObservedTrace.CompletePolicy p := fun seed ↦
    ⟨strategy seed, hcompletes seed⟩
  let lower := (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
    n * u * Real.sqrt (2 * n)
  calc
    (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) =
      uniformAverage (fun _seed : Seeds ↦ lower) := by
        simp [lower]
    _ ≤ uniformAverage (fun seed : Seeds ↦
        uniformAverage (fun placement : Equiv.Perm (Fin n) ↦
          Online.runCost u (ObservedTrace.placedProcessing p placement)
            (strategy seed) n)) := by
      apply uniformAverage_mono
      intro seed
      exact completePolicy_expectedCost_ge_instanceBenchmark_nsq
        hn hu p hp (policy seed)

/-- The normalized remainder in the arbitrary-input lower bound is
`o_u(1)` for every fixed cap. -/
theorem instanceBenchmark_normalizedError_tendsto_zero (u : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ u * Real.sqrt (2 / (n : ℝ)))
      Filter.atTop (nhds 0) := by
  have hdiv : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have hsqrt := hdiv.sqrt
  simpa using (tendsto_const_nhds.mul hsqrt :
    Filter.Tendsto (fun n : ℕ ↦ u * Real.sqrt (2 / (n : ℝ)))
      Filter.atTop (nhds (u * Real.sqrt 0)))

end
end BlindOptimization
end SchedulingPaper
