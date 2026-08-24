import SchedulingPaper.FluidToFiniteTransfer
import SchedulingPaper.RandomizedObligatoryLower
import SchedulingPaper.RandomizedOptionalBenchmarkKernel
import SchedulingPaper.RandomizedOptionalRoundedAnnouncedLower
import SchedulingPaper.RandomizedOptionalUniformRoundedGrid
import Mathlib.Tactic

/-!
# Operational lower bound for obligatory-testing instance optimality

The optional-testing announced lower bound already treats arbitrary adaptive
first-touch orders.  An obligatory-testing policy is exactly its test-only
specialization: every first touch is a test, so the compiled test selector is
identically one and the compiled blind selector is identically zero.  This
file performs that specialization and obtains the model-specific finite
completion-envelope lower bound, including the uniform-placement averaging
step.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.TraceBijection
open RandomizedOptional.ObservedEnvelope
open RandomizedOptional.AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Operational characterization of an obligatory-testing policy inside the
more general observed optional-testing runtime. -/
def FirstTouchesAreTests {n : ℕ} {p : Fin n → ℝ}
    (policy : CompletePolicy p) : Prop :=
  ∀ σ k, (touchTrace p policy σ).kind k = .test

/-- A test-only policy has deterministic compiled selector one, even after
the adaptive first-touch bijection has reindexed the hidden placement. -/
theorem compiledTestSelector_eq_one_of_firstTouchesAreTests
    {n : ℕ} {p : Fin n → ℝ} {policy : CompletePolicy p}
    (htest : FirstTouchesAreTests policy)
    (k : Fin n) (reveal : Equiv.Perm (Fin n)) :
    compiledTestSelector p policy k reveal = 1 := by
  unfold ObservedTrace.compiledTestSelector
  unfold TraceBijection.compiledTestSelector
  rw [if_pos]
  exact htest _ k

/-- Consequently the complementary blind selector is zero. -/
theorem compiledBlindSelector_eq_zero_of_firstTouchesAreTests
    {n : ℕ} {p : Fin n → ℝ} {policy : CompletePolicy p}
    (htest : FirstTouchesAreTests policy)
    (k : Fin n) (reveal : Equiv.Perm (Fin n)) :
    compiledBlindSelector p policy k reveal = 0 := by
  unfold compiledBlindSelector
  rw [compiledTestSelector_eq_one_of_firstTouchesAreTests htest]
  norm_num

/-- The realized tested fraction in every hidden placement is exactly one. -/
theorem compiledTestFraction_eq_one_of_firstTouchesAreTests
    {n : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    {policy : CompletePolicy p}
    (htest : FirstTouchesAreTests policy)
    (reveal : Equiv.Perm (Fin n)) :
    (∑ k, compiledTestSelector p policy k reveal) / n = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [compiledTestSelector_eq_one_of_firstTouchesAreTests htest]
  simp [hnR]

/-- The rounded obligatory fluid benchmark is the sorted block area with
tested fraction fixed to one.  The maximum-density module and residual SPT
tail are supplied by the common empirical benchmark data. -/
def roundedObligatoryValue
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : ℝ :=
  fluidBlocksArea (optionalSortedBlocks 1
    (RandomizedAnnounced.discoveryMass B.zeroMass
      (selectedPart B.selected B.mass)) B.tau B.mean G.price
    (residualPart B.selected B.mass))

/-- The obligatory benchmark has the same crude horizon bound needed to
average away a bad placement. -/
theorem roundedObligatoryValue_le_one_add_mean
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    roundedObligatoryValue B ≤ 1 + B.mean := by
  let low := selectedPart B.selected B.mass
  let residual := residualPart B.selected B.mass
  let a := RandomizedAnnounced.discoveryMass B.zeroMass low
  let blocks := optionalSortedBlocks 1 a B.tau B.mean G.price residual
  have hmass0 : ∀ i, 0 ≤ B.mass i := by
    intro i
    rw [B.mass_def i]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hzero0 : 0 ≤ B.zeroMass := by
    rw [B.zeroMass_def]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])).1
  have hlow0 : ∀ i, 0 ≤ low i := selectedPart_nonneg hmass0
  have hresidual0 : ∀ i, 0 ≤ residual i := residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := by
    unfold a RandomizedAnnounced.discoveryMass
    exact add_nonneg hzero0 (Finset.sum_nonneg fun i _ => hlow0 i)
  have hmassPartition : a + ∑ i, residual i = 1 := by
    unfold a RandomizedAnnounced.discoveryMass low residual
    have hsplit := sum_selectedPart_add_sum_residualPart B.selected B.mass
    linarith [B.population_mass]
  let lowWork := ∑ i, G.price i * low i
  have hmeanPartition : lowWork + ∑ i, G.price i * residual i = B.mean := by
    simpa [lowWork, low, residual] using B.mean_partition
  have hmodule : B.tau * a = 1 + lowWork := by
    simpa [a, lowWork, low, RandomizedAnnounced.discoveryWork] using
      B.module_density
  have hmassOne : fluidBlocksMass blocks = 1 := by
    dsimp [blocks]
    exact optionalSortedBlocks_mass_eq_one 1 a B.tau B.mean G.price residual
      hmassPartition
  have hwork : fluidBlocksWork blocks = 1 + B.mean := by
    dsimp [blocks]
    exact optionalSortedBlocks_work_eq_q_add_mean 1 a B.tau B.mean
      lowWork G.price residual hmodule hmeanPartition
  have hcost : ∀ b ∈ blocks, 0 ≤ b.cost := by
    intro b hb
    exact (optionalSortedBlocks_cost_pos B.tau_pos B.mean_pos B.price_pos
      b (by simpa [blocks] using hb)).le
  have hblockMass : ∀ b ∈ blocks, 0 ≤ b.mass := by
    intro b hb
    exact optionalSortedBlocks_mass_nonneg
      (q := (1 : ℝ)) (a := a) (τ := B.tau) (μ := B.mean)
      (p := G.price) (residualMass := residual)
      (by norm_num) (by norm_num) ha0 hresidual0 b
      (by simpa [blocks] using hb)
  have harea := fluidBlocksArea_le_work_mul_mass blocks hcost hblockMass
  unfold roundedObligatoryValue
  change fluidBlocksArea blocks ≤ 1 + B.mean
  rw [hwork, hmassOne] at harea
  simpa using harea

/-- The block-area presentation is exactly the familiar stationary
maximum-density formula: one module block followed by the residual SPT
minimum-pair term. -/
theorem roundedObligatoryValue_eq_stationaryFluidCost
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    roundedObligatoryValue B =
      RandomizedAnnounced.stationaryFluidCost B.tau
        (RandomizedAnnounced.discoveryMass B.zeroMass
          (selectedPart B.selected B.mass))
        (RandomizedAnnounced.weightedMinPair
          (residualPart B.selected B.mass) G.price) := by
  let a := RandomizedAnnounced.discoveryMass B.zeroMass
    (selectedPart B.selected B.mass)
  let residual := residualPart B.selected B.mass
  rw [roundedObligatoryValue,
    optionalSortedBlocks_area_eq_half_minPair,
    optionalSortedBlocks_minPair_eq_fintype]
  simp only [Fintype.sum_option, optionalItemCost, optionalItemCapacity]
  simp only [min_self, mul_one, one_mul, sub_self, mul_zero, zero_mul,
    zero_add, Finset.sum_const_zero]
  have hresidual := benchmarkData_residual_eq_zero_or_tau_le_price hn B
  have hmass : a + ∑ i, residual i = 1 := by
    dsimp [a, residual, RandomizedAnnounced.discoveryMass]
    have hsplit := sum_selectedPart_add_sum_residualPart B.selected B.mass
    linarith [B.population_mass]
  have hcrossRight :
      (∑ i, min B.tau (G.price i) * a * residual i) =
        B.tau * a * ∑ i, residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rcases hresidual i with hz | hle
    · have hz' : residual i = 0 := by simpa [residual] using hz
      rw [hz']
      ring
    · rw [min_eq_left hle]
  have hcrossLeft :
      (∑ i, min (G.price i) B.tau * residual i * a) =
        B.tau * a * ∑ i, residual i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rcases hresidual i with hz | hle
    · have hz' : residual i = 0 := by simpa [residual] using hz
      rw [hz']
      ring
    · rw [min_eq_right hle]
      ring
  have hpair :
      (∑ i, ∑ j,
        min (G.price i) (G.price j) * residual i * residual j) =
        RandomizedAnnounced.weightedMinPair residual G.price := by
    unfold RandomizedAnnounced.weightedMinPair
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  change
    (B.tau * a * a +
        ∑ i, min B.tau (G.price i) * a * residual i +
        ∑ i, (min (G.price i) B.tau * residual i * a +
          ∑ j, min (G.price i) (G.price j) * residual i * residual j)) /
      2 =
      RandomizedAnnounced.stationaryFluidCost B.tau a
        (RandomizedAnnounced.weightedMinPair residual G.price)
  rw [Finset.sum_add_distrib, hcrossRight, hcrossLeft, hpair]
  unfold RandomizedAnnounced.stationaryFluidCost
  have hscaled := congrArg (fun x : ℝ => B.tau * a * x) hmass
  ring_nf at hscaled ⊢
  linarith

/-- The simultaneous class-count event needed by the obligatory envelope.
There is no blind-work condition because a test-only policy has zero blind
selector identically. -/
structure ObligatoryPlacementGood
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (policy : CompletePolicy p)
    (γ : ℝ) (σ : ObservedTrace.Placement n) : Prop where
  class_good : ∀ cutoff i,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if G.category i
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.mass i *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n
  zero_good : ∀ cutoff,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if zeroCategory
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.zeroMass *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n

/-- On every good hidden placement, every completing adaptive obligatory
policy is bounded below by the rounded empirical completion envelope. -/
theorem normalizedCost_ge_roundedObligatoryValue_of_good
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (htest : FirstTouchesAreTests policy)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {γ : ℝ} (hγ : 0 ≤ γ) (σ : ObservedTrace.Placement n)
    (hgood : ObligatoryPlacementGood B policy γ σ) :
    roundedObligatoryValue B - G.mesh -
        (Fintype.card ι + 1) * γ * (1 + B.mean) ≤
      normalizedCost p policy σ := by
  have hblind : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            G.roundedProcessing
              (revealOrder (touchTrace p policy) σ k)) -
        B.mean *
          ∑ k ∈ positionsThrough cutoff,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ (0 : ℝ) * n := by
    intro cutoff
    simp_rw [compiledBlindSelector_eq_zero_of_firstTouchesAreTests htest]
    simp
  have hpath := settled_cost_ge_sortedBlocksArea_rounded hn p policy σ G
    B.selected B.mass_def B.zeroMass_def B.mean_def hγ (by norm_num)
    B.tau_pos B.mean_pos B.price_pos B.population_mass B.mean_partition
    hgood.class_good hgood.zero_good hblind B.density_max B.module_pos
    B.module_density
  have hq := compiledTestFraction_eq_one_of_firstTouchesAreTests
    hn htest (revealOrder (touchTrace p policy) σ)
  dsimp at hpath
  rw [hq] at hpath
  simpa [roundedObligatoryValue, normalizedCost] using hpath

/-- The all-class predictable-urn estimate, with the zero class included as
`none`, supplies the good event for every operation prefix of a test-only
adaptive policy. -/
theorem obligatoryPlacementGood_bad_probability_le
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    uniformProbability
        (fun σ => ¬ ObligatoryPlacementGood B policy γ σ) ≤
      (Fintype.card ι + 1) * base := by
  dsimp
  classical
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  let Bad : ObservedTrace.Placement n → Prop := fun σ =>
    ∃ c : Option ι, ∃ j : Fin n,
      threshold <
        |(∑ k ∈ positionsThrough j,
            compiledTestSelector p policy k
                (revealOrder (touchTrace p policy) σ) *
              AnnouncedRoundedLower.gridIndicator G c
                (revealOrder (touchTrace p policy) σ k)) -
          populationMean (AnnouncedRoundedLower.gridIndicator G c) *
            ∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                (revealOrder (touchTrace p policy) σ)|
  have hvalue0 : ∀ c i,
      0 ≤ AnnouncedRoundedLower.gridIndicator G c i := by
    intro c i
    rcases c with _ | c <;>
      simp only [AnnouncedRoundedLower.gridIndicator] <;>
      split <;> norm_num
  have hvalue1 : ∀ c i,
      AnnouncedRoundedLower.gridIndicator G c i ≤ 1 := by
    intro c i
    rcases c with _ | c <;>
      simp only [AnnouncedRoundedLower.gridIndicator] <;>
      split <;> norm_num
  have hbad : uniformProbability Bad ≤ (Fintype.card ι + 1) * base := by
    have h := adaptivePolicy_all_categories_global_prefix_probability_le
      hn p policy (AnnouncedRoundedLower.gridIndicator G) cutoff
      hMartingaleStep hSuffixStep hvalue0 hvalue1 he hr
    simpa [Bad, threshold, base] using h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hthreshold : threshold = γ * n := by
    dsimp [γ]
    field_simp [hnR.ne']
  have hcontain : ∀ σ,
      ¬ ObligatoryPlacementGood B policy γ σ → Bad σ := by
    intro σ hnotGood
    by_contra hnotBad
    apply hnotGood
    constructor
    · intro j i
      have hle := le_of_not_gt fun h => hnotBad ⟨some i, j, h⟩
      simpa [AnnouncedRoundedLower.gridIndicator, B.mass_def i,
        hthreshold] using hle
    · intro j
      have hle := le_of_not_gt fun h => hnotBad ⟨none, j, h⟩
      have hmeanZero :
          populationMean (AnnouncedRoundedLower.gridIndicator G none) =
            B.zeroMass := by
        change populationMean
          (fun occurrence => if zeroCategory (p occurrence) then 1 else 0) =
            B.zeroMass
        exact B.zeroMass_def.symm
      rw [hmeanZero, hthreshold] at hle
      simpa [AnnouncedRoundedLower.gridIndicator] using hle
  exact (uniformProbability_mono hcontain).trans hbad

/-- Complete finite announced lower bound for obligatory testing.  It
quantifies over the literal cost of every completing adaptive test-only
policy and averages only over a uniform hidden placement. -/
theorem uniformAverage_normalizedCost_ge_roundedObligatoryValue
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (htest : FirstTouchesAreTests policy)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    roundedObligatoryValue B - G.mesh -
        (Fintype.card ι + 1) * γ * (1 + B.mean) -
        (1 + B.mean) * ((Fintype.card ι + 1) * base) ≤
      uniformAverage (normalizedCost p policy) := by
  dsimp
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  let Bad : ObservedTrace.Placement n → Prop := fun σ =>
    ¬ ObligatoryPlacementGood B policy γ σ
  let repaired := roundedObligatoryValue B - G.mesh -
    (Fintype.card ι + 1) * γ * (1 + B.mean)
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hγ : 0 ≤ γ := by
    dsimp [γ, threshold]
    positivity
  have hbad : uniformProbability Bad ≤
      (Fintype.card ι + 1) * base := by
    have h := obligatoryPlacementGood_bad_probability_le hn p policy G B
      cutoff hMartingaleStep hSuffixStep he hr
    simpa [Bad, threshold, γ, base] using h
  have hprocessing : ∀ σ job, 0 ≤ placedProcessing p σ job := by
    intro σ job
    exact G.processing_nonneg (σ job)
  have hcost0 : ∀ σ, 0 ≤ normalizedCost p policy σ := by
    intro σ
    unfold normalizedCost
    apply div_nonneg
    · apply completionCost_nonneg_of_revealsMatch (hprocessing σ)
      dsimp [settledRun]
      exact (run_historyInvariant (placedProcessing p σ) policy.strategy
        (2 * n + 1)).revealsMatch
    · positivity
  have hgood : ∀ σ, ¬ Bad σ → repaired ≤ normalizedCost p policy σ := by
    intro σ hnotBad
    apply normalizedCost_ge_roundedObligatoryValue_of_good hn0 p policy
      htest G B hγ σ
    simpa [Bad] using hnotBad
  have hupper := roundedObligatoryValue_le_one_add_mean hn0 B
  have hmean0 : 0 ≤ B.mean := B.mean_pos.le
  have hrepairedUpper : repaired ≤ 1 + B.mean := by
    dsimp [repaired]
    have hrepair0 : 0 ≤ G.mesh +
        (Fintype.card ι + 1 : ℝ) * γ * (1 + B.mean) := by
      exact add_nonneg G.mesh_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hγ)
          (by linarith))
    linarith
  have havg := uniformAverage_ge_of_good_event
    (normalizedCost p policy) Bad hcost0 hgood hrepairedUpper
    (by linarith : 0 ≤ 1 + B.mean) hbad
  simpa [repaired, Bad, threshold, γ, base, sub_eq_add_neg, add_assoc]
    using havg

/-- Finite Yao conclusion.  For every finite private randomization over
completing adaptive obligatory policies, one fixed oblivious labeling pays
the same empirical-envelope lower bound. -/
theorem exists_fixedPlacement_randomizedCost_ge_roundedObligatoryValue
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ σ : ObservedTrace.Placement n,
      roundedObligatoryValue B - G.mesh -
          (Fintype.card ι + 1) * γ * (1 + B.mean) -
          (1 + B.mean) * ((Fintype.card ι + 1) * base) ≤
        uniformAverage fun seed => normalizedCost p (policy seed) σ := by
  dsimp
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  let lower := roundedObligatoryValue B - G.mesh -
    (Fintype.card ι + 1) * γ * (1 + B.mean) -
    (1 + B.mean) * ((Fintype.card ι + 1) * base)
  have hseed : ∀ seed,
      lower ≤ uniformAverage (normalizedCost p (policy seed)) := by
    intro seed
    have h := uniformAverage_normalizedCost_ge_roundedObligatoryValue
      hn p (policy seed) (htest seed) G B cutoff
      hMartingaleStep hSuffixStep he hr
    simpa [lower, threshold, γ, base] using h
  have hseedAverage :
      lower ≤ uniformAverage (fun seed =>
        uniformAverage (normalizedCost p (policy seed))) := by
    rw [show lower = uniformAverage (fun _seed : Seeds => lower) by
      symm
      exact uniformAverage_const lower]
    exact uniformAverage_mono hseed
  have hjoint : lower ≤ uniformAverage (fun σ : ObservedTrace.Placement n =>
      uniformAverage fun seed => normalizedCost p (policy seed) σ) := by
    rw [RandomizedObligatory.uniformAverage_comm]
    exact hseedAverage
  obtain ⟨σ, hσ⟩ := RandomizedObligatory.finite_yao_select_fixed_input
    (fun σ : ObservedTrace.Placement n => fun seed =>
      normalizedCost p (policy seed) σ) hjoint
  exact ⟨σ, by simpa [lower, threshold, γ, base] using hσ⟩

/-- Closed bounded-input form: the uniform upward grid and its
maximum-density benchmark are constructed internally before finite Yao fixes
one oblivious labeling. -/
theorem exists_boundedUniformBenchmark_fixedPlacement_randomized_lower
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ B : BenchmarkData p G, ∃ σ : ObservedTrace.Placement n,
      roundedObligatoryValue B - L / K -
          (K + 1) * γ * (1 + B.mean) -
          (1 + B.mean) * ((K + 1) * base) ≤
        uniformAverage fun seed => normalizedCost p (policy seed) σ := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hprice : ∀ i, 0 < G.price i := by
    intro i
    dsimp [G]
    exact uniformGridPrice_pos (div_pos hL hKR) i
  have hmeanRounded : 0 < populationMean G.roundedProcessing :=
    hmean.trans_le (G.populationMean_le_roundedProcessing hn0)
  let ⟨B⟩ := exists_empiricalBenchmarkData hn0 p G hprice hmeanRounded
  obtain ⟨σ, hσ⟩ :=
    exists_fixedPlacement_randomizedCost_ge_roundedObligatoryValue
      hn p policy htest G B cutoff hMartingaleStep hSuffixStep he hr
  refine ⟨B, σ, ?_⟩
  simpa [G, boundedUniformRoundedGrid_mesh] using hσ

end

end ObligatoryInstance
end SchedulingPaper
