import SchedulingPaper.RevealingOptimizationObservedEnvelope
import Mathlib.Tactic

/-!
# Integrating the revealing-optimization completion envelope

This module turns the raw-timing prefix domination into a lower bound for
the entire sum of completion times.  The theorem is stated on the one
simultaneous placement event used by the urn argument.  Its two scalar
side conditions isolate the terminal-work repair and the public horizon;
subsequent finite-probability modules can discharge them independently.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace ObservedAreaLower

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.TraceBijection
open RandomizedOptional.ObservedEnvelope
open RandomizedOptional.AnnouncedRoundedLower
open InstanceBenchmark
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

def normalizedRawCost {n : ℕ} (u : ℝ) (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : ObservedTrace.Placement n) : ℝ :=
  RawObserved.rawCompletionCost u (placedProcessing p σ)
      (settledRun p policy.strategy σ).config.transcript / (n : ℝ) ^ 2

/-- Cellwise full-trace discrepancy, weighted by the rounded prices, bounds
the ideal tested processing work by the actually selected processing work.
One mesh pays for upward rounding. -/
theorem weighted_test_work_le_actual_add_repair
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hclassFull : ∀ i,
      |(∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n) :
    B.mean *
        (∑ k, compiledTestSelector p policy k
          (revealOrder (touchTrace p policy) σ)) ≤
      (∑ k, compiledTestSelector p policy k
          (revealOrder (touchTrace p policy) σ) *
        p (revealOrder (touchTrace p policy) σ k)) +
      G.mesh *
        (∑ k, compiledTestSelector p policy k
          (revealOrder (touchTrace p policy) σ)) +
      γ * n * ∑ i, G.price i := by
  let reveal := revealOrder (touchTrace p policy) σ
  let select := compiledTestSelector p policy
  let total : ℝ := ∑ k, select k reveal
  let roundedSelected : ℝ := ∑ k, select k reveal * G.roundedProcessing (reveal k)
  let actualSelected : ℝ := ∑ k, select k reveal * p (reveal k)
  have hmeanMass : (∑ i, G.price i * B.mass i) = B.mean := by
    calc
      (∑ i, G.price i * B.mass i) =
          ∑ i, G.price i *
            (selectedPart B.selected B.mass i +
              residualPart B.selected B.mass i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [selectedPart_add_residualPart]
      _ = (∑ i, G.price i * selectedPart B.selected B.mass i) +
          ∑ i, G.price i * residualPart B.selected B.mass i := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ = B.mean := B.mean_partition
  have hweighted :
      (∑ i, G.price i * (B.mass i * total)) ≤
        (∑ i, G.price i *
          (∑ k, select k reveal *
            (if G.category i (p (reveal k)) then 1 else 0))) +
          γ * n * ∑ i, G.price i := by
    have hpoint : ∀ i,
        G.price i * (B.mass i * total) ≤
          G.price i *
              (∑ k, select k reveal *
                (if G.category i (p (reveal k)) then 1 else 0)) +
            G.price i * (γ * n) := by
      intro i
      have hlower := (abs_le.mp (hclassFull i)).1
      have hbase : B.mass i * total - γ * n ≤
          ∑ k, select k reveal *
            (if G.category i (p (reveal k)) then 1 else 0) := by
        dsimp [total, select, reveal]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hbase (G.price_nonneg i)]
    calc
      (∑ i, G.price i * (B.mass i * total)) ≤
          ∑ i, (G.price i *
              (∑ k, select k reveal *
                (if G.category i (p (reveal k)) then 1 else 0)) +
            G.price i * (γ * n)) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = (∑ i, G.price i *
          (∑ k, select k reveal *
            (if G.category i (p (reveal k)) then 1 else 0))) +
          γ * n * ∑ i, G.price i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hclasses :
      (∑ i, G.price i *
          (∑ k, select k reveal *
            (if G.category i (p (reveal k)) then 1 else 0))) =
        roundedSelected := by
    dsimp [roundedSelected, RoundedPositiveGrid.roundedProcessing]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrounded : roundedSelected ≤ actualSelected + G.mesh * total := by
    calc
      roundedSelected ≤ ∑ k, select k reveal * (p (reveal k) + G.mesh) := by
        dsimp [roundedSelected]
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (G.roundedProcessing_le (reveal k))
          (compiledTestSelector_nonneg p policy k reveal)
      _ = actualSelected + G.mesh * total := by
        dsimp [actualSelected, total]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hleft :
      (∑ i, G.price i * (B.mass i * total)) = B.mean * total := by
    calc
      (∑ i, G.price i * (B.mass i * total)) =
          (∑ i, G.price i * B.mass i) * total := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = B.mean * total := by rw [hmeanMass]
  rw [hleft, hclasses] at hweighted
  dsimp [total, roundedSelected, actualSelected, select, reveal] at hweighted hrounded ⊢
  linarith

/-- The weighted full-trace event discharges the terminal-work side
condition with the explicit repair `mesh + γ * sum(price)`. -/
theorem rawBenchmarkBlocks_work_le_settled_add_repair
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u γ : ℝ} (hu : 0 ≤ u) (hγ : 0 ≤ γ)
    (hclassFull : ∀ i,
      |(∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n) :
    fluidBlocksWork
        (rawBenchmarkBlocks B u
          ((∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)) / n)) ≤
      RawObserved.rawElapsed u (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript / n +
        (G.mesh + γ * ∑ i, G.price i) := by
  let reveal := revealOrder (touchTrace p policy) σ
  let select := compiledTestSelector p policy
  let total : ℝ := ∑ k, select k reveal
  let q : ℝ := total / n
  let actual : ℝ := ∑ k, select k reveal * p (reveal k)
  let blind : ℝ := blindCount
    (settledRun p policy.strategy σ).config.transcript
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htotal0 : 0 ≤ total := by
    dsimp [total]
    exact Finset.sum_nonneg fun k _ =>
      compiledTestSelector_nonneg p policy k reveal
  have htotalLe : total ≤ n := by
    dsimp [total]
    calc
      (∑ k, select k reveal) ≤ ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          compiledTestSelector_le_one p policy k reveal
      _ = n := by simp
  let lowWork := ∑ i, G.price i * selectedPart B.selected B.mass i
  let residual := residualPart B.selected B.mass
  let a := RandomizedAnnounced.discoveryMass B.zeroMass
    (selectedPart B.selected B.mass)
  have hmodule : B.tau * a = 1 + lowWork := by
    simpa [a, lowWork, RandomizedAnnounced.discoveryWork] using B.module_density
  have hmean : lowWork + ∑ i, G.price i * residual i = B.mean := by
    simpa [lowWork, residual] using B.mean_partition
  have hblockWork :
      fluidBlocksWork (rawBenchmarkBlocks B u q) =
        q * (1 + B.mean) + u * (1 - q) := by
    rw [rawBenchmarkBlocks, optionalSortedBlocks_work]
    dsimp [a, residual] at hmodule hmean ⊢
    linear_combination q * hmodule + q * hmean
  have hweighted := weighted_test_work_le_actual_add_repair
    hn p policy σ G B hγ hclassFull
  have hraw := RawObserved.settled_rawElapsed_eq_compiledTestWork
    u p policy σ
  have hcount := RawObserved.settled_testCount_add_blindCount_eq_n
    p policy σ
  change total + blind = n at hcount
  change RawObserved.rawElapsed u (placedProcessing p σ)
      (settledRun p policy.strategy σ).config.transcript =
        total + actual + u * blind at hraw
  change B.mean * total ≤ actual + G.mesh * total +
      γ * n * ∑ i, G.price i at hweighted
  rw [show ((∑ k, compiledTestSelector p policy k
      (revealOrder (touchTrace p policy) σ)) / n) = q by rfl]
  rw [hblockWork, hraw]
  dsimp [q]
  field_simp [hnR.ne']
  have hmeshTotal := mul_le_mul_of_nonneg_left htotalLe G.mesh_nonneg
  nlinarith

/-- On one simultaneous class-discrepancy event, a completed adaptive run
pays the minimum raw-block area, up to the supplied horizontal terminal
repair and the standard vertical completion repair. -/
theorem settled_rawCost_ge_rawBenchmarkValue_of_terminal
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u γ ζ : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hγ : 0 ≤ γ) (hζ : 0 ≤ ζ)
    (hmeshζ : G.mesh ≤ ζ)
    (hclassGood : ∀ cutoff i,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hzeroGood : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if zeroCategory
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.zeroMass *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hterminal : fluidBlocksWork
        (rawBenchmarkBlocks B u
          ((∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)) / n)) ≤
      RawObserved.rawElapsed u (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript / n + ζ)
    (hhorizon : RawObserved.rawElapsed u (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript / n ≤ 1 + u) :
    R.value - ζ -
        (Fintype.card ι + 1) * γ * (1 + u) ≤
      RawObserved.rawCompletionCost u (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript /
        (n : ℝ) ^ 2 := by
  let reveal := revealOrder (touchTrace p policy) σ
  let q : ℝ := (∑ k, compiledTestSelector p policy k reveal) / n
  let blocks := rawBenchmarkBlocks B u q
  let transcript := (settledRun p policy.strategy σ).config.transcript
  let ε : ℝ := (Fintype.card ι + 1) * γ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Finset.sum_nonneg fun k _ =>
      compiledTestSelector_nonneg p policy k reveal) hnR.le
  have hsumTestLe : (∑ k, compiledTestSelector p policy k reveal) ≤ n := by
    calc
      (∑ k, compiledTestSelector p policy k reveal) ≤
          ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          compiledTestSelector_le_one p policy k reveal
      _ = n := by simp
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hnR]
    exact hsumTestLe
  have hblocksCost : ∀ block ∈ blocks, 0 < block.cost := by
    dsimp [blocks]
    exact rawBenchmarkBlocks_cost_pos B hu
  have hblocksMass : ∀ block ∈ blocks, 0 ≤ block.mass := by
    dsimp [blocks]
    exact rawBenchmarkBlocks_mass_nonneg B hq0 hq1
  have hblocksMassOne : fluidBlocksMass blocks = 1 := by
    dsimp [blocks]
    exact rawBenchmarkBlocks_mass_eq_one B u q
  have hprocessing : ∀ job, 0 ≤ placedProcessing p σ job := by
    intro job
    exact G.processing_nonneg (σ job)
  have hcomplete : completionCount (placedProcessing p σ) transcript = n := by
    dsimp [transcript, settledRun]
    exact run_completionCount_eq_n_of_done (placedProcessing p σ)
      policy.strategy (2 * n + 1) (policy.completes σ)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hcurveMono : Monotone (fluidBlocksCompleted blocks) :=
    fluidBlocksCompleted_monotone hblocksCost
  have hprefix : ∀ pre, pre <+: transcript →
      (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
        fluidBlocksCompleted blocks
            (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + ζ) + ε := by
    intro pre hpre
    have hpref := raw_settled_prefix_completion_le_sortedEnvelope_rounded
      hn p policy σ G B.selected
      B.mass_def B.zeroMass_def hγ B.tau_pos hu B.price_pos
      B.population_mass B.mean_partition hclassGood hzeroGood
      B.density_max B.module_pos B.module_density pre
      (by simpa [transcript] using hpre)
    have hworkLe :
        RawObserved.rawElapsed u (placedProcessing p σ) pre / n + G.mesh ≤
          RawObserved.rawElapsed u (placedProcessing p σ) pre / n + ζ := by
      linarith
    have hmono := hcurveMono hworkLe
    have hpref' :
        (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
          fluidBlocksCompleted blocks
              (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + G.mesh) + ε := by
      simpa [blocks, rawBenchmarkBlocks, q, reveal, ε] using hpref
    calc
      (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
          fluidBlocksCompleted blocks
              (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + G.mesh) + ε := hpref'
      _ ≤ fluidBlocksCompleted blocks
              (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + ζ) + ε := by
        linarith
  have harea := RawObserved.rawTranscriptCost_ge_fluidBlocksArea_of_terminal_le_shift
    hn transcript blocks ζ ε hζ hu.le hprocessing hcomplete hblocksCost
      hblocksMass hblocksMassOne (by simpa [blocks, q, reveal, transcript] using hterminal)
      hprefix
  have hminimum : R.value ≤ fluidBlocksArea blocks := by
    dsimp [RawBenchmarkData.value, blocks, q]
    exact R.minimizes _ hq0 hq1
  have hvertical :
      ε * (RawObserved.rawElapsed u (placedProcessing p σ) transcript / n) ≤
        ε * (1 + u) := mul_le_mul_of_nonneg_left
          (by simpa [transcript] using hhorizon) hε
  dsimp [ε] at hvertical ⊢
  linarith

/-- Fully discharged pathwise lower bound on one simultaneous urn event.
The cap supplies the deterministic horizon; the full-trace instance of the
same class event supplies the terminal horizontal repair. -/
theorem settled_rawCost_ge_rawBenchmarkValue
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u γ : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hcap : ∀ job, p job ≤ u) (hγ : 0 ≤ γ)
    (hclassGood : ∀ cutoff i,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hzeroGood : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if zeroCategory
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.zeroMass *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hclassFull : ∀ i,
      |(∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n) :
    R.value - (G.mesh + γ * ∑ i, G.price i) -
        (Fintype.card ι + 1) * γ * (1 + u) ≤
      RawObserved.rawCompletionCost u (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript /
        (n : ℝ) ^ 2 := by
  let ζ := G.mesh + γ * ∑ i, G.price i
  have hpriceSum : 0 ≤ ∑ i, G.price i :=
    Finset.sum_nonneg fun i _ => G.price_nonneg i
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact add_nonneg G.mesh_nonneg (mul_nonneg hγ hpriceSum)
  have hmeshζ : G.mesh ≤ ζ := by
    dsimp [ζ]
    linarith [mul_nonneg hγ hpriceSum]
  have hterminal := rawBenchmarkBlocks_work_le_settled_add_repair
    hn p policy σ G B hu.le hγ hclassFull
  have hhorizon := RawObserved.settled_rawElapsed_div_le_one_add_cap
    hn policy σ hu.le hcap
  simpa [ζ] using settled_rawCost_ge_rawBenchmarkValue_of_terminal
    hn p policy σ G B R hu hγ hζ hmeshζ hclassGood hzeroGood
      hterminal hhorizon

/-- The all-prefix good event already exported for the predictable urn also
contains its full-trace instance. -/
theorem normalizedRawCost_ge_rawBenchmarkValue_of_good
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u γ : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hcap : ∀ job, p job ≤ u) (hγ : 0 ≤ γ)
    (σ : ObservedTrace.Placement n)
    (hgood : ObligatoryInstance.ObligatoryPlacementGood B policy γ σ) :
    R.value - (G.mesh + γ * ∑ i, G.price i) -
        (Fintype.card ι + 1) * γ * (1 + u) ≤
      normalizedRawCost u p policy σ := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hpositions : positionsThrough last = Finset.univ := by
    ext k
    simp [positionsThrough, last]
    omega
  have hfull : ∀ i,
      |(∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        B.mass i *
          ∑ k, compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n := by
    intro i
    have h := hgood.class_good last i
    simpa [hpositions] using h
  simpa [normalizedRawCost] using settled_rawCost_ge_rawBenchmarkValue
    hn p policy σ G B R hu hcap hγ hgood.class_good hgood.zero_good hfull

/-- Uniform-placement announced lower bound for revealing optimization. -/
theorem uniformAverage_normalizedRawCost_ge_rawBenchmarkValue
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hcap : ∀ job, p job ≤ u)
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
    R.value - (G.mesh + γ * ∑ i, G.price i) -
        (Fintype.card ι + 1) * γ * (1 + u) -
        (1 + u) * ((Fintype.card ι + 1) * base) ≤
      Randomized.uniformAverage (normalizedRawCost u p policy) := by
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
    ¬ ObligatoryInstance.ObligatoryPlacementGood B policy γ σ
  let repaired := R.value - (G.mesh + γ * ∑ i, G.price i) -
    (Fintype.card ι + 1) * γ * (1 + u)
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hγ : 0 ≤ γ := by
    dsimp [γ, threshold]
    positivity
  have hbad : Randomized.uniformProbability Bad ≤
      (Fintype.card ι + 1) * base := by
    have h := ObligatoryInstance.obligatoryPlacementGood_bad_probability_le
      hn p policy G B cutoff hMartingaleStep hSuffixStep he hr
    simpa [Bad, threshold, γ, base] using h
  have hcost0 : ∀ σ, 0 ≤ normalizedRawCost u p policy σ := by
    intro σ
    unfold normalizedRawCost
    exact div_nonneg
      (RawObserved.rawCompletionCost_nonneg hu.le
        (fun job => G.processing_nonneg (σ job)) _)
      (sq_nonneg _)
  have hgood : ∀ σ, ¬ Bad σ →
      repaired ≤ normalizedRawCost u p policy σ := by
    intro σ hnotBad
    apply normalizedRawCost_ge_rawBenchmarkValue_of_good
      hn0 p policy G B R hu hcap hγ σ
    simpa [Bad] using hnotBad
  have hpriceSum : 0 ≤ ∑ i, G.price i :=
    Finset.sum_nonneg fun i _ => G.price_nonneg i
  have hrepair0 : 0 ≤ (G.mesh + γ * ∑ i, G.price i) +
      (Fintype.card ι + 1) * γ * (1 + u) := by
    have hu1 : 0 ≤ 1 + u := by linarith
    exact add_nonneg
      (add_nonneg G.mesh_nonneg (mul_nonneg hγ hpriceSum))
      (mul_nonneg (mul_nonneg (by positivity) hγ) hu1)
  have hvalue := R.value_le_half_raw
  have hhalf : u / 2 ≤ 1 + u := by linarith
  have hrepairedUpper : repaired ≤ 1 + u := by
    dsimp [repaired]
    linarith
  have havg := RandomizedOptional.uniformAverage_ge_of_good_event
    (normalizedRawCost u p policy) Bad hcost0 hgood hrepairedUpper
    (by linarith : 0 ≤ 1 + u) hbad
  simpa [repaired, Bad, threshold, γ, base, sub_eq_add_neg, add_assoc]
    using havg

/-- Finite Yao selection: every finite private randomization over completing
adaptive revealing policies has one fixed oblivious labeling paying the
same raw benchmark lower bound. -/
theorem exists_fixedPlacement_randomizedRawCost_ge_rawBenchmarkValue
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : Seeds → CompletePolicy p)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {u : ℝ} (R : RawBenchmarkData B u)
    (hu : 0 < u) (hcap : ∀ job, p job ≤ u)
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
      R.value - (G.mesh + γ * ∑ i, G.price i) -
          (Fintype.card ι + 1) * γ * (1 + u) -
          (1 + u) * ((Fintype.card ι + 1) * base) ≤
        Randomized.uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ := by
  dsimp
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  let lower := R.value - (G.mesh + γ * ∑ i, G.price i) -
    (Fintype.card ι + 1) * γ * (1 + u) -
    (1 + u) * ((Fintype.card ι + 1) * base)
  have hseed : ∀ seed,
      lower ≤ Randomized.uniformAverage
        (normalizedRawCost u p (policy seed)) := by
    intro seed
    have h := uniformAverage_normalizedRawCost_ge_rawBenchmarkValue
      hn p (policy seed) G B R hu hcap cutoff
      hMartingaleStep hSuffixStep he hr
    simpa [lower, threshold, γ, base] using h
  have hseedAverage :
      lower ≤ Randomized.uniformAverage (fun seed =>
        Randomized.uniformAverage (normalizedRawCost u p (policy seed))) := by
    rw [show lower = Randomized.uniformAverage
      (fun _seed : Seeds => lower) by
        symm
        exact Randomized.uniformAverage_const lower]
    exact Randomized.uniformAverage_mono hseed
  have hjoint : lower ≤ Randomized.uniformAverage
      (fun σ : ObservedTrace.Placement n =>
        Randomized.uniformAverage fun seed =>
          normalizedRawCost u p (policy seed) σ) := by
    rw [RandomizedObligatory.uniformAverage_comm]
    exact hseedAverage
  obtain ⟨σ, hσ⟩ := RandomizedObligatory.finite_yao_select_fixed_input
    (fun σ : ObservedTrace.Placement n => fun seed =>
      normalizedRawCost u p (policy seed) σ) hjoint
  exact ⟨σ, by simpa [lower, threshold, γ, base] using hσ⟩

end

end ObservedAreaLower
end RevealingOptimization
end SchedulingPaper
