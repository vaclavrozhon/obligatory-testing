import SchedulingPaper.RevealingOptimizationBenchmarkBridge
import SchedulingPaper.RandomizedOptionalUnknownRates
import Mathlib.Tactic

/-!
# Finite instance-optimal revealing optimization

This module places the operational learned upper bound and the arbitrary
adaptive observed-policy lower bound around one shared raw-block benchmark.
The benchmark is only a proof certificate: the executable strategy learns
its template from its private pilot and does not receive the multiset.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace InstanceOptimal

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.ObservedEnvelope
open RandomizedOptional.AnnouncedRoundedLower
open ObligatoryInstance
open InstanceBenchmark
open InstanceLearning
open BenchmarkBridge
open ObservedAreaLower
open RawObserved

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Expected normalized cost of the literal learned revealing strategy. -/
def compiledExpectedNormalizedCost
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n)) (u : ℝ) : ℝ :=
  uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
    uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (CompiledStrategy.compiledLearnedStrategy n G.category G.price u
            positions pilotOrder mainOrder) (4 * n + 2)) /
        (n : ℝ) ^ 2))

def completionTriangle (n : ℕ) : ℝ := (n : ℝ) * (n + 1) / 2

/-- If a completion step finishes at most one job and every finishing step
has duration at least `c`, its suffix-weighted cost dominates the homogeneous
triangle of side `c`.  Non-completing nonnegative steps can only add cost. -/
theorem completionStepsCost_ge_completionTriangle
    {steps : List CompletionStep} {c : ℝ}
    (hduration : ∀ step ∈ steps, 0 ≤ step.duration)
    (hcompletion : ∀ step ∈ steps, step.completions ≤ 1)
    (hfinishing : ∀ step ∈ steps, step.completions = 1 →
      c ≤ step.duration) :
    c * completionTriangle (completionStepsCount steps) ≤
      completionStepsCost steps := by
  induction steps with
  | nil => simp [completionStepsCount, completionStepsCost, completionTriangle]
  | cons step rest ih =>
      have hstep0 : 0 ≤ step.duration := hduration step (by simp)
      have hstepCompletion : step.completions ≤ 1 :=
        hcompletion step (by simp)
      have hrestDuration : ∀ next ∈ rest, 0 ≤ next.duration := by
        intro next hnext
        exact hduration next (by simp [hnext])
      have hrestCompletion : ∀ next ∈ rest, next.completions ≤ 1 := by
        intro next hnext
        exact hcompletion next (by simp [hnext])
      have hrestFinishing : ∀ next ∈ rest, next.completions = 1 →
          c ≤ next.duration := by
        intro next hnext
        exact hfinishing next (by simp [hnext])
      have htail := ih hrestDuration hrestCompletion hrestFinishing
      have hcases : step.completions = 0 ∨ step.completions = 1 := by omega
      rcases hcases with hzero | hone
      · simp only [completionStepsCount, completionStepsCost]
        rw [hzero]
        simp only [zero_add]
        exact htail.trans (le_add_of_nonneg_left
          (mul_nonneg hstep0 (by positivity)))
      · have hstepC : c ≤ step.duration :=
          hfinishing step (by simp) hone
        simp only [completionStepsCount, completionStepsCost]
        rw [hone]
        simp only [Nat.cast_add, Nat.cast_one]
        have hhead := mul_le_mul_of_nonneg_right hstepC
          (by positivity : 0 ≤ 1 + (completionStepsCount rest : ℝ))
        dsimp [completionTriangle] at htail ⊢
        push_cast
        nlinarith [hhead]

theorem rawCompletionCost_ge_zero_population_triangle
    {n : ℕ} {u : ℝ} (hu : 0 < u)
    (transcript : RandomizedOptional.ObservedOnline.Transcript n) :
    min u 1 * completionTriangle
        (completionCount (fun _ : Fin n => (0 : ℝ)) transcript) ≤
      rawCompletionCost u (fun _ : Fin n => (0 : ℝ)) transcript := by
  let steps := rawTranscriptCompletionSteps u
    (fun _ : Fin n => (0 : ℝ)) transcript
  have hduration : ∀ step ∈ steps, 0 ≤ step.duration :=
    rawTranscriptCompletionSteps_duration_nonneg hu.le
      (fun _ => by norm_num) transcript
  have hcompletion : ∀ step ∈ steps, step.completions ≤ 1 := by
    intro step hstep
    obtain ⟨observation, _hmem, rfl⟩ := List.mem_map.mp hstep
    change (if (observation.completionLabel
      (fun _ : Fin n => (0 : ℝ))).isSome then 1 else 0) ≤ 1
    split <;> omega
  have hfinishing : ∀ step ∈ steps, step.completions = 1 →
      min u 1 ≤ step.duration := by
    intro step hstep hfinish
    obtain ⟨observation, _hmem, rfl⟩ := List.mem_map.mp hstep
    cases observation with
    | testResult job value =>
        exact min_le_right _ _
    | processed job =>
        simp [observationCompletionCount,
          ObservedOnline.Observation.completionLabel] at hfinish
    | blindCompleted job value =>
        exact min_le_left _ _
  simpa [steps] using completionStepsCost_ge_completionTriangle
    hduration hcompletion hfinishing

theorem settled_zero_population_rawCost_ge_half_min
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 < u)
    (policy : CompletePolicy (fun _ : Fin n => (0 : ℝ)))
    (σ : Placement n) :
    min u 1 / 2 ≤
      normalizedRawCost u (fun _ : Fin n => (0 : ℝ)) policy σ := by
  let p : Fin n → ℝ := fun _ => 0
  let transcript :=
    (settledRun p policy.strategy σ).config.transcript
  have hmatch := (run_historyInvariant (placedProcessing p σ)
    policy.strategy (2 * n + 1)).revealsMatch
  have hpPlaced : placedProcessing p σ = fun _ : Fin n => (0 : ℝ) := by
    funext job
    rfl
  have hzeroTestAux : ∀ t : Transcript n,
      AllRevealsMatch (placedProcessing p σ) t →
        zeroTestCount t = t.testResults.length := by
    intro t
    induction t with
    | nil => intro _; rfl
    | cons observation rest ih =>
        intro ht
        have htail : AllRevealsMatch (placedProcessing p σ) rest := by
          intro job value hmem
          apply ht job value
          cases observation with
          | testResult head value =>
              exact List.mem_cons_of_mem _ hmem
          | processed head => exact hmem
          | blindCompleted head value =>
              exact List.mem_cons_of_mem _ hmem
        have ih' := ih htail
        cases observation with
        | testResult job value =>
            have hvalue := ht job value (by
              simp [Transcript.revealedResults])
            rw [hpPlaced] at hvalue
            simp [zeroTestCount, Transcript.testResults, hvalue, ih',
              Nat.add_comm]
        | processed job =>
            simpa [zeroTestCount, Transcript.testResults] using ih'
        | blindCompleted job value =>
            simpa [zeroTestCount, Transcript.testResults] using ih'
  have hzeroTest : zeroTestCount transcript = transcript.testResults.length :=
    hzeroTestAux transcript hmatch
  have hprocessed :
      positiveProcessedCount (placedProcessing p σ) transcript = 0 := by
    rw [hpPlaced]
    induction transcript with
    | nil => rfl
    | cons observation rest ih =>
        cases observation <;>
          simp [positiveProcessedCount, ih]
  have hchoices : (touchChoices transcript).length = n := by
    have h := congrArg List.length
      (touchTrace_choices_ofFn p policy σ)
    simpa [transcript] using h.symm
  have htestBlind : transcript.testResults.length + blindCount transcript = n := by
    rw [← touchChoices_length_eq_test_add_blind]
    exact hchoices
  have hcount : completionCount (placedProcessing p σ) transcript = n := by
    rw [completionCount_eq_operation_counts, hzeroTest, hprocessed]
    simpa [Nat.add_assoc] using htestBlind
  have hcost := rawCompletionCost_ge_zero_population_triangle hu transcript
  rw [← hpPlaced, hcount] at hcost
  unfold normalizedRawCost
  change min u 1 / 2 ≤
    rawCompletionCost u (placedProcessing p σ) transcript / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv := div_le_div_of_nonneg_right hcost (sq_nonneg (n : ℝ))
  dsimp [completionTriangle] at hdiv
  have hc0 : 0 ≤ min u 1 := le_min hu.le (by norm_num)
  calc
    min u 1 / 2 ≤
        min u 1 * ((n : ℝ) * (n + 1) / 2) / (n : ℝ) ^ 2 := by
      field_simp [hnR.ne']
      nlinarith
    _ ≤ _ := hdiv

def zeroRawTemplate {ι : Type*} (n : ℕ) : Template ι n where
  low := fun _ => false
  quota := ⟨0, by omega⟩

def zeroTestAllTemplate {ι : Type*} (n : ℕ) : Template ι n where
  low := fun _ => false
  quota := ⟨n, by omega⟩

theorem zero_population_zeroRawTemplate_value
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hp : ∀ job, p job = 0) (u : ℝ) :
    InstanceLearning.gridTemplateValue
        (populationHistogram (roundedGridCell G)) G.price u
        (zeroRawTemplate n) = u / 2 := by
  rw [RandomizedOptional.populationHistogram_roundedGridCell_eq_zeroAtom
    hn G hp]
  simp [InstanceLearning.gridTemplateValue, InstanceLearning.gridPairCharge,
    InstanceLearning.fluidPairChargeFlags,
    finiteProductExpectation, positiveGridPrice, zeroRawTemplate,
    Template.fraction]

theorem zero_population_testAllTemplate_value
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hp : ∀ job, p job = 0) (u : ℝ) :
    InstanceLearning.gridTemplateValue
        (populationHistogram (roundedGridCell G)) G.price u
        (zeroTestAllTemplate n) = 1 / 2 := by
  rw [RandomizedOptional.populationHistogram_roundedGridCell_eq_zeroAtom
    hn G hp]
  simp [InstanceLearning.gridTemplateValue, InstanceLearning.gridPairCharge,
    InstanceLearning.fluidPairChargeFlags,
    InstanceLearning.testedPairChargeFlags, finiteProductExpectation,
    positiveGridPrice,
    zeroTestAllTemplate, Template.fraction,
    InstanceLearning.Template.lowWithZero, hn.ne']

/-- The literal compiled learner is also controlled on the degenerate
all-zero population.  The comparison template is chosen only in the proof:
raw completion has value `u / 2`, while testing everything has value `1 / 2`.
The learner itself still minimizes its empirical finite template family. -/
theorem zero_population_compiledExpected_le_half_min
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hp : ∀ job, p job = 0)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (u : ℝ) (hu : 0 < u)
    (hpriceU : ∀ cell, G.price cell ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u) :
    compiledExpectedNormalizedCost G positions u ≤
        min u 1 / 2 +
          2 * (u + 2) *
            Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
          (5 * u + 8) / (2 * n) +
          2 * positions.card * (u + 1) / n := by
  by_cases huOne : u ≤ 1
  · have hrun := CompiledRun.compiledLearnedStrategy_expectedCost_le
      hn G hprice0 hprice positions hpositions u hu.le hpriceU hroundedU
        (zeroRawTemplate n)
    rw [zero_population_zeroRawTemplate_value (by omega) G hp u] at hrun
    simpa [compiledExpectedNormalizedCost, min_eq_left huOne] using hrun
  · have honeU : (1 : ℝ) ≤ u := le_of_lt (lt_of_not_ge huOne)
    have hrun := CompiledRun.compiledLearnedStrategy_expectedCost_le
      hn G hprice0 hprice positions hpositions u hu.le hpriceU hroundedU
        (zeroTestAllTemplate n)
    rw [zero_population_testAllTemplate_value (by omega) G hp u] at hrun
    simpa [compiledExpectedNormalizedCost, min_eq_right honeU] using hrun

/-- Every completing observed policy pays at least the homogeneous completion
triangle when all processing times vanish.  The statement keeps the original
processing function in its type, so dependent policies need no manual cast. -/
theorem settled_zero_processing_rawCost_ge_half_min
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job = 0)
    (policy : CompletePolicy p) (σ : Placement n) :
    min u 1 / 2 ≤ normalizedRawCost u p policy σ := by
  have hpEq : p = fun _ : Fin n => (0 : ℝ) := funext hp
  subst p
  exact settled_zero_population_rawCost_ge_half_min hn hu policy σ

/-- The zero-population lower bound is pointwise in the private random seed,
hence survives any finite uniform randomization on the same placement. -/
theorem randomized_zero_processing_rawCost_ge_half_min
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job = 0)
    (policy : Seeds → CompletePolicy p) (σ : Placement n) :
    min u 1 / 2 ≤
      uniformAverage fun seed => normalizedRawCost u p (policy seed) σ := by
  have h := uniformAverage_mono (f := fun _ : Seeds => min u 1 / 2)
    (g := fun seed => normalizedRawCost u p (policy seed) σ)
    (fun seed => settled_zero_processing_rawCost_ge_half_min
      hn hu p hp (policy seed) σ)
  simpa using h

/-- A reusable arithmetic wrapper for the three operational learner errors
that remain after fixing a target template. -/
theorem compiledError_le_inverse_parameter_rate
    {n m k : ℕ} (hm : 2 ≤ m) (hk : 0 < k)
    (hkUpper : (k : ℝ) * (m : ℝ) ^ 2 ≤ n)
    {u : ℝ} (hu : 0 < u)
    (pilot : Finset (Fin n)) (hpilotCard : pilot.card = k)
    (hLearning : Real.sqrt ((m + 1 : ℝ) / k) ≤
      30 * (u + 1) / m)
    (hInverse : 1 / (n : ℝ) ≤ 30 * (u + 1) / m)
    (hPilot : (k : ℝ) * u / n ≤ 30 * (u + 1) / m) :
    2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
          (5 * u + 8) / (2 * n) +
          2 * pilot.card * (u + 1) / n ≤
        500 * (u + 1) ^ 2 / m := by
  let δ : ℝ := 30 * (u + 1) / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < n := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    nlinarith [mul_pos hkR (sq_pos_of_pos hmR)]
  have hlearning : Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤ δ := by
    simpa [hpilotCard, δ] using hLearning
  have hinverse : 1 / (n : ℝ) ≤ δ := by simpa [δ] using hInverse
  have hpilu : pilot.card * u / (n : ℝ) ≤ δ := by
    simpa [hpilotCard, δ] using hPilot
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hkOverN : (k : ℝ) / n ≤ 1 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hnR (sq_pos_of_pos hmR)]
    nlinarith
  have hmLeSq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith [mul_le_mul_of_nonneg_left hmOne hmR.le]
  have hmInv : 1 / (m : ℝ) ^ 2 ≤ 1 / m :=
    one_div_le_one_div_of_le hmR hmLeSq
  have honeOverM : 1 / (m : ℝ) ≤ δ := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (by nlinarith) hmR.le
  have hkOverNDelta : (k : ℝ) / n ≤ δ :=
    hkOverN.trans (hmInv.trans honeOverM)
  have hpiluOne : pilot.card * (u + 1) / (n : ℝ) ≤ 2 * δ := by
    rw [hpilotCard]
    calc
      (k : ℝ) * (u + 1) / n =
          (k : ℝ) * u / n + (k : ℝ) / n := by ring
      _ ≤ δ + δ := add_le_add (by simpa [hpilotCard] using hpilu)
        hkOverNDelta
      _ = 2 * δ := by ring
  have hlearnTerm :
      2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤
        2 * (u + 2) * δ :=
    mul_le_mul_of_nonneg_left hlearning (by positivity)
  have hkernel : (5 * u + 8) / (2 * (n : ℝ)) ≤
      (5 * u + 8) / 2 * δ := by
    have hcoeff : 0 ≤ (5 * u + 8) / 2 := by linarith
    calc
      (5 * u + 8) / (2 * (n : ℝ)) =
          ((5 * u + 8) / 2) * (1 / n) := by ring
      _ ≤ ((5 * u + 8) / 2) * δ :=
        mul_le_mul_of_nonneg_left hinverse hcoeff
  have hpilotTerm : 2 * pilot.card * (u + 1) / (n : ℝ) ≤ 4 * δ := by
    calc
      2 * pilot.card * (u + 1) / (n : ℝ) =
          2 * (pilot.card * (u + 1) / n) := by ring
      _ ≤ 2 * (2 * δ) := mul_le_mul_of_nonneg_left hpiluOne (by norm_num)
      _ = 4 * δ := by ring
  have hrough :
      2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
            (5 * u + 8) / (2 * n) +
            2 * pilot.card * (u + 1) / n ≤
          12 * (u + 1) * δ := by
    nlinarith
  calc
    _ ≤ 12 * (u + 1) * δ := hrough
    _ = 360 * (u + 1) ^ 2 / m := by dsimp [δ]; ring
    _ ≤ 500 * (u + 1) ^ 2 / m := by
      have hbase : 0 ≤ (u + 1) ^ 2 / (m : ℝ) := by positivity
      calc
        360 * (u + 1) ^ 2 / (m : ℝ) =
            360 * ((u + 1) ^ 2 / m) := by ring
        _ ≤ 500 * ((u + 1) ^ 2 / m) :=
          mul_le_mul_of_nonneg_right (by norm_num) hbase
        _ = 500 * (u + 1) ^ 2 / m := by ring

/-- On every positive-mean bounded multiset, the universal learned policy and
every finite randomized completing observed policy meet at one concrete
rounded raw-block benchmark.  The fixed placement in the second conjunct is
chosen before the competitor's private seed. -/
theorem exists_boundedUniform_matching_rawBenchmark
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u) (hmean : 0 < populationMean p)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (policy : Seeds → CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hu p hp0 hpu
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ B : BenchmarkData p G, ∃ R : RawBenchmarkData B u,
      compiledExpectedNormalizedCost G positions u ≤
          R.value + 4 * (u + 1) / n +
            2 * (u + 2) *
              Real.sqrt ((K + 1 : ℝ) / positions.card) +
            (5 * u + 8) / (2 * n) +
            2 * positions.card * (u + 1) / n ∧
        ∃ σ : Placement n,
          R.value - (u / K + γ * ∑ i, G.price i) -
              (K + 1) * γ * (1 + u) -
              (1 + u) * ((K + 1) * base) ≤
            uniformAverage fun seed =>
              normalizedRawCost u p (policy seed) σ := by
  dsimp
  let G := boundedUniformRoundedGrid hK hu p hp0 hpu
  have hn0 : 0 < n := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmesh : 0 < u / (K : ℝ) := div_pos hu hKR
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have hprice0 : ∀ i, 0 < G.price i := by
    intro i
    exact uniformGridPrice_pos hmesh i
  have hprice : Function.Injective G.price := by
    intro i j hij
    apply Fin.ext
    dsimp [G, boundedUniformRoundedGrid, uniformRoundedGrid,
      uniformGridPrice] at hij
    have hcast : (i.val : ℝ) = j.val := by nlinarith
    exact_mod_cast hcast
  have hpriceU : ∀ i, G.price i ≤ u := by
    intro i
    have hiNat : i.val + 1 ≤ K := by omega
    have hiReal : (i.val + 1 : ℝ) ≤ K := by exact_mod_cast hiNat
    rw [show G.price i = uniformGridPrice (u / K) i by rfl]
    unfold uniformGridPrice
    have hmul := mul_le_mul_of_nonneg_right hiReal hmesh.le
    rw [mul_div_cancel₀ u hKR.ne'] at hmul
    exact hmul
  have hroundedU : ∀ job, G.roundedProcessing job ≤ u := by
    intro job
    rw [← roundedGridCell_price G job]
    cases roundedGridCell G job with
    | none => simpa [positiveGridPrice] using hu.le
    | some i => simpa [positiveGridPrice] using hpriceU i
  have hmeanRounded : 0 < populationMean G.roundedProcessing :=
    hmean.trans_le (G.populationMean_le_roundedProcessing hn0)
  let ⟨B⟩ := exists_empiricalBenchmarkData hn0 p G hprice0 hmeanRounded
  let ⟨R⟩ := exists_rawBenchmarkData B u
  have hupper := compiledLearnedStrategy_expectedCost_le_rawBenchmark
    hn G hprice0 hprice positions hpositions u hu hpriceU hroundedU B R
  have hlower := exists_fixedPlacement_randomizedRawCost_ge_rawBenchmarkValue
    hn p policy G B R hu hpu cutoff hMartingaleStep hSuffixStep he hr
  refine ⟨B, R, ?_, ?_⟩
  · simpa [compiledExpectedNormalizedCost] using hupper
  · simpa [G, boundedUniformRoundedGrid_mesh] using hlower

set_option maxHeartbeats 1000000 in
/-- A concrete slower rate obtained from the already checked inverse-power
parameter package.  It is uniform over the bounded positive-mean multiset
and over every finite private randomization of the competing policy. -/
theorem boundedUniform_matching_rawBenchmark_inverse_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u) (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p) :
    let scales := RandomizedOptional.parameter_scales hm hn
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m scales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ B : BenchmarkData p G, ∃ R : RawBenchmarkData B u,
      compiledExpectedNormalizedCost G pilot u ≤
          R.value + 500 * (u + 1) ^ 2 / m ∧
        ∃ σ : Placement n,
          R.value - 150 * (u + 1) ^ 2 / m ≤
            uniformAverage fun seed =>
              normalizedRawCost u p (policy seed) σ := by
  dsimp
  obtain ⟨hkpos, hklt, hdpos, hkLower, hkUpper,
      _hdLower, _hdUpper⟩ := RandomizedOptional.parameter_scales hm hn
  let k := RandomizedOptional.inverseSquareSize n m
  let d := RandomizedOptional.inverseFourthStep n m
  let pilot := RandomizedOptional.inverseSquarePilotPositions n m hklt
  let cutoff := RandomizedOptional.inverseSquareCutoff n m hkpos
  let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
  let δ : ℝ := 30 * (u + 1) / m
  have hnTwo : 1 < n := lt_of_lt_of_le
    (Nat.one_lt_pow (by omega) (by omega)) hn
  have hpilotNonempty : pilot.Nonempty :=
    RandomizedOptional.inverseSquarePilotPositions_nonempty n m hklt hkpos
  have hmatch := exists_boundedUniform_matching_rawBenchmark
    (Seeds := Seeds) hnTwo (show 0 < m by omega) hu p hp0 hpu hmean
      pilot hpilotNonempty policy cutoff (show 0 < d by exact hdpos)
      (show 0 < d by exact hdpos)
      (e := (n : ℝ) / (m : ℝ) ^ 2) (r := 1 / (m : ℝ) ^ 2)
      (by positivity) (by positivity)
  obtain ⟨B, R, hupper, σ, hlower⟩ := hmatch
  obtain ⟨_hDiscovery, hCounts, hBad, hLearning, hInverse, hMesh,
      hPilot⟩ := RandomizedOptional.inverse_parameter_error_bounds hm hn hu
  have hpilotCard : pilot.card = k := by
    exact RandomizedOptional.inverseSquarePilotPositions_card n m hklt
  have hsuffixCard : (suffixPositions cutoff).card = k := by
    exact RandomizedOptional.inverseSquareCutoff_suffix_card n m hkpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < n := by positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  let γ : ℝ :=
    ((n : ℝ) / (m : ℝ) ^ 2 + d +
      (1 / (m : ℝ) ^ 2 +
        2 * d / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card) / n
  let base : ℝ :=
    (backwardCheckpoints d cutoff).card *
        (n / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
      (backwardCheckpoints d cutoff).card *
        ((2 / (suffixPositions cutoff).card) /
          (1 / (m : ℝ) ^ 2) ^ 2)
  have hcounts : (m + 1 : ℝ) * γ ≤ δ := by
    simpa [γ, δ, d, cutoff] using hCounts
  have hbad : (m + 2 : ℝ) * base ≤ δ := by
    simpa [base, δ, d, cutoff] using hBad
  have hlearning : Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤ δ := by
    simpa [hpilotCard] using hLearning
  have hmesh : u / (m : ℝ) ≤ δ := by simpa [δ] using hMesh
  have hinverse : 1 / (n : ℝ) ≤ δ := by simpa [δ] using hInverse
  have hpilu : pilot.card * u / (n : ℝ) ≤ δ := by
    simpa [hpilotCard, δ] using hPilot
  have hγnonneg : 0 ≤ γ := by
    dsimp [γ]
    positivity
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    positivity
  have hpriceSum0 : 0 ≤ ∑ i, G.price i :=
    Finset.sum_nonneg fun i _ => G.price_nonneg i
  have hpriceU : ∀ i, G.price i ≤ u := by
    intro i
    have hiNat : i.val + 1 ≤ m := by omega
    have hiReal : (i.val + 1 : ℝ) ≤ m := by exact_mod_cast hiNat
    rw [show G.price i = uniformGridPrice (u / m) i by rfl]
    unfold uniformGridPrice
    have hmul := mul_le_mul_of_nonneg_right hiReal (div_nonneg hu.le hmR.le)
    rw [mul_div_cancel₀ u hmR.ne'] at hmul
    exact hmul
  have hpriceSum : (∑ i, G.price i) ≤ m * u := by
    calc
      (∑ i, G.price i) ≤ ∑ _i : Fin m, u :=
        Finset.sum_le_sum fun i _ => hpriceU i
      _ = m * u := by simp
  have hmgamma : (m : ℝ) * γ ≤ δ := by
    have hstep : (m : ℝ) * γ ≤ (m + 1 : ℝ) * γ := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hγnonneg
    exact hstep.trans hcounts
  have hweightedPrice : γ * ∑ i, G.price i ≤ u * δ := by
    calc
      γ * ∑ i, G.price i ≤ γ * (m * u) :=
        mul_le_mul_of_nonneg_left hpriceSum hγnonneg
      _ = ((m : ℝ) * γ) * u := by ring
      _ ≤ δ * u := mul_le_mul_of_nonneg_right hmgamma hu.le
      _ = u * δ := by ring
  have hcountTerm : (m + 1 : ℝ) * γ * (1 + u) ≤
      δ * (1 + u) :=
    mul_le_mul_of_nonneg_right hcounts (by linarith)
  have hbadTerm : (1 + u) * ((m + 1 : ℝ) * base) ≤
      (1 + u) * δ := by
    have hmbad : (m + 1 : ℝ) * base ≤ (m + 2 : ℝ) * base :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase0
    exact mul_le_mul_of_nonneg_left (hmbad.trans hbad) (by linarith)
  have hlowerError :
      u / (m : ℝ) + γ * ∑ i, G.price i +
          (m + 1 : ℝ) * γ * (1 + u) +
          (1 + u) * ((m + 1 : ℝ) * base) ≤
        150 * (u + 1) ^ 2 / m := by
    have hrough :
        u / (m : ℝ) + γ * ∑ i, G.price i +
            (m + 1 : ℝ) * γ * (1 + u) +
            (1 + u) * ((m + 1 : ℝ) * base) ≤
          4 * (u + 1) * δ := by
      nlinarith
    calc
      _ ≤ 4 * (u + 1) * δ := hrough
      _ ≤ 150 * (u + 1) ^ 2 / m := by
        dsimp [δ]
        calc
          4 * (u + 1) * (30 * (u + 1) / (m : ℝ)) =
              120 * (u + 1) ^ 2 / m := by ring
          _ =
              120 * ((u + 1) ^ 2 / m) := by ring
          _ ≤ 150 * ((u + 1) ^ 2 / m) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = 150 * (u + 1) ^ 2 / m := by ring
  have hkOverN : (k : ℝ) / n ≤ 1 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hnR (sq_pos_of_pos hmR)]
    nlinarith
  have hmLeSq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith [mul_le_mul_of_nonneg_left hmOne hmR.le]
  have hmInv : 1 / (m : ℝ) ^ 2 ≤ 1 / m :=
    one_div_le_one_div_of_le hmR hmLeSq
  have honeOverM : 1 / (m : ℝ) ≤ δ := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (by nlinarith) hmR.le
  have hkOverNDelta : (k : ℝ) / n ≤ δ :=
    hkOverN.trans (hmInv.trans honeOverM)
  have hpiluOne : pilot.card * (u + 1) / (n : ℝ) ≤ 2 * δ := by
    have hpiluK : (k : ℝ) * u / (n : ℝ) ≤ δ := by
      simpa [hpilotCard] using hpilu
    rw [hpilotCard]
    calc
      (k : ℝ) * (u + 1) / n =
          (k : ℝ) * u / n + (k : ℝ) / n := by ring
      _ ≤ δ + δ := add_le_add hpiluK hkOverNDelta
      _ = 2 * δ := by ring
  have hquota : 4 * (u + 1) / (n : ℝ) ≤ 4 * (u + 1) * δ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinverse)
      (by positivity)
  have hlearnTerm :
      2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤
        2 * (u + 2) * δ :=
    mul_le_mul_of_nonneg_left hlearning (by positivity)
  have hkernel : (5 * u + 8) / (2 * (n : ℝ)) ≤
      (5 * u + 8) / 2 * δ := by
    have hcoeff : 0 ≤ (5 * u + 8) / 2 := by linarith
    calc
      (5 * u + 8) / (2 * (n : ℝ)) =
          ((5 * u + 8) / 2) * (1 / n) := by ring
      _ ≤ ((5 * u + 8) / 2) * δ :=
        mul_le_mul_of_nonneg_left hinverse hcoeff
  have hpilotTerm : 2 * pilot.card * (u + 1) / (n : ℝ) ≤ 4 * δ := by
    calc
      2 * pilot.card * (u + 1) / (n : ℝ) =
          2 * (pilot.card * (u + 1) / n) := by ring
      _ ≤ 2 * (2 * δ) := mul_le_mul_of_nonneg_left hpiluOne (by norm_num)
      _ = 4 * δ := by ring
  have hupperError :
      4 * (u + 1) / (n : ℝ) +
          2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
          (5 * u + 8) / (2 * n) +
          2 * pilot.card * (u + 1) / n ≤
        500 * (u + 1) ^ 2 / m := by
    have hrough :
        4 * (u + 1) / (n : ℝ) +
            2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
            (5 * u + 8) / (2 * n) +
            2 * pilot.card * (u + 1) / n ≤
          16 * (u + 1) * δ := by
      nlinarith
    calc
      _ ≤ 16 * (u + 1) * δ := hrough
      _ = 480 * (u + 1) ^ 2 / m := by dsimp [δ]; ring
      _ ≤ 500 * (u + 1) ^ 2 / m := by
        calc
          480 * (u + 1) ^ 2 / (m : ℝ) =
              480 * ((u + 1) ^ 2 / m) := by ring
          _ ≤ 500 * ((u + 1) ^ 2 / m) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = 500 * (u + 1) ^ 2 / m := by ring
  refine ⟨B, R, ?_, σ, ?_⟩
  · have hupper' : compiledExpectedNormalizedCost G pilot u ≤
        R.value +
          (4 * (u + 1) / n +
            2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
            (5 * u + 8) / (2 * n) +
            2 * pilot.card * (u + 1) / n) := by
      simpa [hpilotCard, add_assoc] using hupper
    linarith
  · have hlower' :
        R.value -
            (u / (m : ℝ) + γ * ∑ i, G.price i) -
            (m + 1 : ℝ) * γ * (1 + u) -
            (1 + u) * ((m + 1 : ℝ) * base) ≤
          uniformAverage fun seed => normalizedRawCost u p (policy seed) σ := by
      simpa [G, γ, base, hsuffixCard] using hlower
    linarith

set_option maxHeartbeats 1000000 in
/-- The same input-size-only compiled policy on the zero-mean branch.  Its
upper comparison value is exactly `min u 1 / 2`, and every randomized
completing observed policy is bounded below by that value on every placement. -/
theorem boundedUniform_zero_matching_value_inverse_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u) (hmean : populationMean p = 0)
    (policy : Seeds → CompletePolicy p) :
    let scales := RandomizedOptional.parameter_scales hm hn
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m scales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    compiledExpectedNormalizedCost G pilot u ≤
          min u 1 / 2 + 500 * (u + 1) ^ 2 / m ∧
      ∀ σ : Placement n,
        min u 1 / 2 ≤
          uniformAverage fun seed => normalizedRawCost u p (policy seed) σ := by
  dsimp
  obtain ⟨hkpos, hklt, _hdpos, _hkLower, hkUpper,
      _hdLower, _hdUpper⟩ := RandomizedOptional.parameter_scales hm hn
  let k := RandomizedOptional.inverseSquareSize n m
  let pilot := RandomizedOptional.inverseSquarePilotPositions n m hklt
  let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
  have hnPos : 0 < n := lt_of_lt_of_le (pow_pos (by omega) 16) hn
  have hnTwo : 1 < n := lt_of_lt_of_le
    (Nat.one_lt_pow (by omega) (by omega)) hn
  have hpzero := RandomizedOptional.processing_eq_zero_of_populationMean_eq_zero
    hnPos p hp0 hmean
  have hpilotNonempty : pilot.Nonempty :=
    RandomizedOptional.inverseSquarePilotPositions_nonempty n m hklt hkpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : 0 < u / (m : ℝ) := div_pos hu hmR
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  have hprice0 : ∀ i, 0 < G.price i := by
    intro i
    exact uniformGridPrice_pos hmesh i
  have hprice : Function.Injective G.price := by
    intro i j hij
    apply Fin.ext
    dsimp [G, boundedUniformRoundedGrid, uniformRoundedGrid,
      uniformGridPrice] at hij
    have hcast : (i.val : ℝ) = j.val := by nlinarith
    exact_mod_cast hcast
  have hpriceU : ∀ i, G.price i ≤ u := by
    intro i
    have hiNat : i.val + 1 ≤ m := by omega
    have hiReal : (i.val + 1 : ℝ) ≤ m := by exact_mod_cast hiNat
    rw [show G.price i = uniformGridPrice (u / m) i by rfl]
    unfold uniformGridPrice
    have hmul := mul_le_mul_of_nonneg_right hiReal hmesh.le
    rw [mul_div_cancel₀ u hmR.ne'] at hmul
    exact hmul
  have hroundedU : ∀ job, G.roundedProcessing job ≤ u := by
    intro job
    rw [G.roundedProcessing_eq_zero_of_eq_zero (hpzero job)]
    exact hu.le
  have hupper := zero_population_compiledExpected_le_half_min hnTwo G hpzero
    hprice0 hprice pilot hpilotNonempty u hu hpriceU hroundedU
  obtain ⟨_hDiscovery, _hCounts, _hBad, hLearning, hInverse, _hMesh,
      hPilot⟩ := RandomizedOptional.inverse_parameter_error_bounds hm hn hu
  have hpilotCard : pilot.card = k :=
    RandomizedOptional.inverseSquarePilotPositions_card n m hklt
  have herror :
      2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
            (5 * u + 8) / (2 * n) +
            2 * pilot.card * (u + 1) / n ≤
          500 * (u + 1) ^ 2 / m :=
    compiledError_le_inverse_parameter_rate hm hkpos hkUpper hu pilot
      hpilotCard hLearning hInverse hPilot
  constructor
  · have hupper' : compiledExpectedNormalizedCost G pilot u ≤
        min u 1 / 2 +
          (2 * (u + 2) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
            (5 * u + 8) / (2 * n) +
            2 * pilot.card * (u + 1) / n) := by
      simpa [add_assoc] using hupper
    linarith
  · intro σ
    exact randomized_zero_processing_rawCost_ge_half_min
      hnPos hu p hpzero policy σ

set_option maxHeartbeats 1000000 in
/-- Finite all-instance instance-optimal sandwich for the literal universal
revealing strategy.  The scalar `benchmark` is a proof witness shared by the
algorithmic upper bound and the Yao-style lower bound against an arbitrary
finite randomization of completing transcript-only policies.  It is the raw
block benchmark for positive mean and `min u 1 / 2` for zero mean. -/
theorem boundedUniform_matching_value_inverse_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Seeds → CompletePolicy p) :
    let scales := RandomizedOptional.parameter_scales hm hn
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m scales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ benchmark : ℝ,
      compiledExpectedNormalizedCost G pilot u ≤
          benchmark + 500 * (u + 1) ^ 2 / m ∧
        ∃ σ : Placement n,
          benchmark - 500 * (u + 1) ^ 2 / m ≤
            uniformAverage fun seed =>
              normalizedRawCost u p (policy seed) σ := by
  dsimp
  let scales := RandomizedOptional.parameter_scales hm hn
  let pilot := RandomizedOptional.inverseSquarePilotPositions n m scales.2.1
  let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
  have hnPos : 0 < n := lt_of_lt_of_le (pow_pos (by omega) 16) hn
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun job _ => hp0 job) (by positivity)
  rcases hmean0.eq_or_lt with hmean | hmean
  · have hzero := boundedUniform_zero_matching_value_inverse_parameter_rate
      (Seeds := Seeds) hm hn hu p hp0 hpu hmean.symm policy
    obtain ⟨hupper, hlower⟩ := hzero
    have herror0 : 0 ≤ 500 * (u + 1) ^ 2 / (m : ℝ) := by positivity
    refine ⟨min u 1 / 2, hupper, Equiv.refl (Fin n), ?_⟩
    exact (sub_le_self _ herror0).trans (hlower (Equiv.refl (Fin n)))
  · have hpositive := boundedUniform_matching_rawBenchmark_inverse_parameter_rate
      (Seeds := Seeds) hm hn hu p hp0 hpu hmean policy
    obtain ⟨B, R, hupper, σ, hlower⟩ := hpositive
    have hbase0 : 0 ≤ (u + 1) ^ 2 / (m : ℝ) := by positivity
    have hcoeff : 150 * ((u + 1) ^ 2 / (m : ℝ)) ≤
        500 * ((u + 1) ^ 2 / m) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase0
    have hweaken : R.value - 500 * (u + 1) ^ 2 / (m : ℝ) ≤
        R.value - 150 * (u + 1) ^ 2 / m := by
      calc
        R.value - 500 * (u + 1) ^ 2 / (m : ℝ) =
            R.value - 500 * ((u + 1) ^ 2 / m) := by ring
        _ ≤ R.value - 150 * ((u + 1) ^ 2 / m) := by linarith
        _ = R.value - 150 * (u + 1) ^ 2 / m := by ring
    exact ⟨R.value, hupper, σ, hweaken.trans hlower⟩

/-- Direct finite instance-optimal consequence of the shared-benchmark
sandwich.  The placement is fixed before the competitor's private seed. -/
theorem exists_fixedPlacement_compiled_le_randomizedCompetitor_inverse_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Seeds → CompletePolicy p) :
    let scales := RandomizedOptional.parameter_scales hm hn
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m scales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ σ : Placement n,
      compiledExpectedNormalizedCost G pilot u ≤
        (uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ) +
          1000 * (u + 1) ^ 2 / m := by
  dsimp
  obtain ⟨benchmark, hupper, σ, hlower⟩ :=
    boundedUniform_matching_value_inverse_parameter_rate
      (Seeds := Seeds) hm hn hu p hp0 hpu policy
  refine ⟨σ, ?_⟩
  calc
    _ ≤ benchmark + 500 * (u + 1) ^ 2 / (m : ℝ) := hupper
    _ ≤ (uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ) +
        2 * (500 * (u + 1) ^ 2 / m) := by linarith
    _ = (uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ) +
        1000 * (u + 1) ^ 2 / m := by ring

def concreteRevealingUpperError (u : ℝ) (n : ℕ) : ℝ :=
  500 * (u + 1) ^ 2 /
    RandomizedOptional.concreteUnknownParameter n

def concreteRevealingLowerError (u : ℝ) (n : ℕ) : ℝ :=
  150 * (u + 1) ^ 2 /
    RandomizedOptional.concreteUnknownParameter n

def concreteRevealingComparisonError (u : ℝ) (n : ℕ) : ℝ :=
  1000 * (u + 1) ^ 2 /
    RandomizedOptional.concreteUnknownParameter n

theorem concreteRevealingUpperError_tendsto_zero (u : ℝ) :
    Filter.Tendsto (concreteRevealingUpperError u)
      Filter.atTop (nhds 0) := by
  unfold concreteRevealingUpperError
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp
      RandomizedOptional.concreteUnknownParameter_tendsto_atTop)
    (500 * (u + 1) ^ 2)

theorem concreteRevealingLowerError_tendsto_zero (u : ℝ) :
    Filter.Tendsto (concreteRevealingLowerError u)
      Filter.atTop (nhds 0) := by
  unfold concreteRevealingLowerError
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp
      RandomizedOptional.concreteUnknownParameter_tendsto_atTop)
    (150 * (u + 1) ^ 2)

theorem concreteRevealingComparisonError_tendsto_zero (u : ℝ) :
    Filter.Tendsto (concreteRevealingComparisonError u)
      Filter.atTop (nhds 0) := by
  unfold concreteRevealingComparisonError
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp
      RandomizedOptional.concreteUnknownParameter_tendsto_atTop)
    (1000 * (u + 1) ^ 2)

/-- Input-size-only positive-mean family.  The grid accuracy, pilot size,
checkpoint spacing, and suffix cutoff are all functions of `n`; no accuracy
parameter is supplied by the caller. -/
theorem boundedUniform_matching_rawBenchmark_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ}
    (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u) (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p) :
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ B : BenchmarkData p G, ∃ R : RawBenchmarkData B u,
      compiledExpectedNormalizedCost G pilot u ≤
          R.value + concreteRevealingUpperError u n ∧
        ∃ σ : Placement n,
          R.value - concreteRevealingLowerError u n ≤
            uniformAverage fun seed =>
              normalizedRawCost u p (policy seed) σ := by
  dsimp
  let m := RandomizedOptional.concreteUnknownParameter n
  obtain ⟨hm, hn⟩ :=
    RandomizedOptional.concreteUnknownParameter_bounds n hroot
  simpa [m, concreteRevealingUpperError, concreteRevealingLowerError] using
    (boundedUniform_matching_rawBenchmark_inverse_parameter_rate
      (Seeds := Seeds) (m := m) hm hn hu p hp0 hpu hmean policy)

/-- Final all-instance input-size-only theorem.  For every bounded nonnegative
multiset and every finite randomization of completing observed policies, the
single executable learned policy is within the same vanishing additive error
of a shared benchmark from above, while one placement puts the competitor
within that error from below. -/
theorem boundedUniform_matching_value_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ}
    (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Seeds → CompletePolicy p) :
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ benchmark : ℝ,
      compiledExpectedNormalizedCost G pilot u ≤
          benchmark + concreteRevealingUpperError u n ∧
        ∃ σ : Placement n,
          benchmark - concreteRevealingUpperError u n ≤
            uniformAverage fun seed =>
              normalizedRawCost u p (policy seed) σ := by
  dsimp
  let m := RandomizedOptional.concreteUnknownParameter n
  obtain ⟨hm, hn⟩ :=
    RandomizedOptional.concreteUnknownParameter_bounds n hroot
  simpa [m, concreteRevealingUpperError] using
    (boundedUniform_matching_value_inverse_parameter_rate
      (Seeds := Seeds) (m := m) hm hn hu p hp0 hpu policy)

/-- Public direct input-size-only instance-optimality theorem. -/
theorem exists_fixedPlacement_compiled_le_randomizedCompetitor_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ}
    (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Seeds → CompletePolicy p) :
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    ∃ σ : Placement n,
      compiledExpectedNormalizedCost G pilot u ≤
        (uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ) +
          concreteRevealingComparisonError u n := by
  dsimp
  let m := RandomizedOptional.concreteUnknownParameter n
  obtain ⟨hm, hn⟩ :=
    RandomizedOptional.concreteUnknownParameter_bounds n hroot
  simpa [m, concreteRevealingComparisonError] using
    (exists_fixedPlacement_compiled_le_randomizedCompetitor_inverse_parameter_rate
      (Seeds := Seeds) (m := m) hm hn hu p hp0 hpu policy)

end

end InstanceOptimal
end RevealingOptimization
end SchedulingPaper
