import SchedulingPaper.RevealingOptimizationInstanceBenchmark
import SchedulingPaper.RandomizedOptionalRoundedObservedEnvelope
import Mathlib.Tactic

/-!
# Operational raw-timing completion envelopes for revealing optimization

The adaptive first-touch bijection and all class-count identities are shared
with the optional observed runtime.  Raw execution has public duration `u`,
so its prefix work is exact and only upward rounding of known processing
requires one horizontal mesh.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace ObservedEnvelope

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.TraceBijection
open RandomizedOptional.ObservedEnvelope
open InstanceBenchmark

noncomputable section

theorem raw_operational_prefix_completion_le_greedy_rounded
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1)
    (selected : ι → Bool)
    {γ zeroMass τ u greedyModule greedyBlind pivotCost : ℝ}
    {mass completion greedyResidual : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hγ : 0 ≤ γ)
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
      ((RawObserved.rawElapsed u (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript) / n) +
          G.mesh ≤
        optionalKnapsackWork τ u greedyModule greedyBlind
          G.price greedyResidual)
    (hgreedyLow : ∀ item,
      optionalItemCost τ u G.price item < pivotCost →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item =
          optionalItemCapacity
            ((∑ k, compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)) / n)
            (RandomizedAnnounced.discoveryMass zeroMass
              (selectedPart selected mass))
            (residualPart selected mass) item)
    (hgreedyHigh : ∀ item,
      pivotCost < optionalItemCost τ u G.price item →
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
  have hblind0 := compiledBlindSelector_nonneg p policy
  have htestOperational := compiled_test_class_prefix_sum_eq_operational
    p policy σ (fun _ => true) hfuel cutoff hlength
  simp only [Bool.true_eq, if_true, testClassCount_true] at htestOperational
  have hblindCountOperational := compiled_blind_count_prefix_sum_eq_operational
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
  have ht0 : 0 ≤ t :=
    div_nonneg (Finset.sum_nonneg fun k _ => htest0 k reveal) hnR.le
  have hprefixTestLe : prefixTest ≤ totalTest :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _hk _hnot => htest0 k reveal)
  have htq : t ≤ q := div_le_div_of_nonneg_right hprefixTestLe hnR.le
  have hb0 : 0 ≤ b :=
    div_nonneg (Finset.sum_nonneg fun k _ => hblind0 k reveal) hnR.le
  have hsumBlind : (∑ k, selectBlind k reveal) = n - totalTest := by
    dsimp [selectBlind, compiledBlindSelector, totalTest, selectTest]
    rw [Finset.sum_sub_distrib]
    simp
  have hprefixBlindLe : prefixBlind ≤ ∑ k, selectBlind k reveal :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
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
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hzeroMass0 : 0 ≤ zeroMass := by
    rw [hzeroMassDef]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : zeroCategory (p occurrence) = true <;> simp [h])).1
  have hc0 : ∀ i, 0 ≤ c i := fun i =>
    div_nonneg (Nat.cast_nonneg _) hnR.le
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
    dsimp [c, t]
    rw [div_le_iff₀ hnR]
    calc
      (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ) ≤
          mass i * prefixTest + γ * n := by linarith
      _ = (mass i * (prefixTest / n) + γ) * n := by
        field_simp [hnR.ne']
  have hzApprox : z ≤ zeroMass * t + γ := by
    have hupper := (abs_le.mp hzeroGood).2
    rw [hzeroOperational] at hupper
    change (zeroTestCount transcript : ℝ) - zeroMass * prefixTest ≤
      γ * n at hupper
    dsimp [z, t]
    rw [div_le_iff₀ hnR]
    calc
      (zeroTestCount transcript : ℝ) ≤
          zeroMass * prefixTest + γ * n := by linarith
      _ = (zeroMass * (prefixTest / n) + γ) * n := by
        field_simp [hnR.ne']
  have hblindEq : prefixBlind = (blindCount transcript : ℝ) := by
    change (∑ k ∈ positionsThrough cutoff,
        compiledBlindSelector p policy k
          (revealOrder (touchTrace p policy) σ)) =
      (blindCount transcript : ℝ)
    simpa only [compiledBlindSelector] using hblindCountOperational
  have hactual : actual ≤ z + b + ∑ i, c i := by
    have hcount := completionCount_eq_operation_counts
      (placedProcessing p σ) transcript
    have hclasses :=
      (G.placed σ).sum_processedClassCount_eq_positiveProcessedCount transcript
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
      t + u * b + ∑ i, G.price i * c i ≤
        RawObserved.rawElapsed u (placedProcessing p σ) transcript / n + G.mesh := by
    have hknownWork :=
      (G.placed σ).sum_price_processedClassCount_le transcript
    change (∑ i, G.price i *
        (ObservedOnline.processedClassCount (placedProcessing p σ)
          (G.category i) transcript : ℝ)) ≤
      processedWork (placedProcessing p σ) transcript +
        G.mesh * positiveProcessedCount (placedProcessing p σ) transcript
      at hknownWork
    have hcompleted := completionCount_eq_operation_counts
      (placedProcessing p σ) transcript
    have hrunLe := run_completionCount_le_n
      (placedProcessing p σ) policy.strategy fuel
    change completionCount (placedProcessing p σ) transcript ≤ n at hrunLe
    rw [hcompleted] at hrunLe
    have hcountLe :
        (positiveProcessedCount (placedProcessing p σ) transcript : ℝ) ≤ n := by
      exact_mod_cast (show
        positiveProcessedCount (placedProcessing p σ) transcript ≤ n by omega)
    have hmeshCount :
        G.mesh *
            (positiveProcessedCount (placedProcessing p σ) transcript : ℝ) ≤
          G.mesh * n :=
      mul_le_mul_of_nonneg_left hcountLe G.mesh_nonneg
    have htestEq : prefixTest = transcript.testResults.length := by
      simpa [prefixTest, selectTest, reveal, transcript] using htestOperational
    rw [RawObserved.rawElapsed_eq_test_add_processed_add_raw]
    change prefixTest / n + u * (prefixBlind / n) +
        ∑ i, G.price i *
          ((ObservedOnline.processedClassCount (placedProcessing p σ)
            (G.category i) transcript : ℝ) / n) ≤
      ((transcript.testResults.length : ℝ) +
          processedWork (placedProcessing p σ) transcript +
          u * blindCount transcript) / n + G.mesh
    rw [htestEq, hblindEq]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    field_simp [hnR.ne']
    nlinarith
  change actual ≤ _
  exact optional_all_class_grid_prefix_completion_le_greedy selected
    hγ hzeroMass0 hmass0 G.price_nonneg hc0 ht0 htq hzApprox hclassApprox
    hb0 hbCap hactual hphysical hmax hmodulePositive hmoduleDensity hpivot
    hgreedyWork hgreedyLow hgreedyHigh

theorem raw_operational_prefix_completion_le_sortedEnvelope_rounded
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1)
    (selected : ι → Bool)
    {γ zeroMass τ u mean : ℝ} {mass : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hγ : 0 ≤ γ)
    (hτ : 0 < τ) (hu : 0 < u) (hprice : ∀ i, 0 < G.price i)
    (hpopulationMass : zeroMass + ∑ i, mass i = 1)
    (hmeanPartition :
      (∑ i, G.price i * selectedPart selected mass i) +
        ∑ i, G.price i * residualPart selected mass i = mean)
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
    (hcompletionLeOne :
      (completionCount (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤ 1) :
    let q := (∑ k, compiledTestSelector p policy k
      (revealOrder (touchTrace p policy) σ)) / n
    let a := RandomizedAnnounced.discoveryMass zeroMass
      (selectedPart selected mass)
    let residualMass := residualPart selected mass
    let work :=
      RawObserved.rawElapsed u (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript / n +
          G.mesh
    (completionCount (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤
      fluidBlocksCompleted
          (optionalSortedBlocks q a τ u G.price residualMass) work +
        (Fintype.card ι + 1) * γ := by
  dsimp
  let reveal := revealOrder (touchTrace p policy) σ
  let selectTest := compiledTestSelector p policy
  let q : ℝ := (∑ k, selectTest k reveal) / n
  let a := RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  let residualMass := residualPart selected mass
  let work := RawObserved.rawElapsed u (placedProcessing p σ)
      (run (placedProcessing p σ) policy.strategy fuel).config.transcript / n +
        G.mesh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Finset.sum_nonneg fun k _ =>
      compiledTestSelector_nonneg p policy k reveal) hnR.le
  have hsumTestLe : (∑ k, selectTest k reveal) ≤ n := by
    calc
      (∑ k, selectTest k reveal) ≤ ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          compiledTestSelector_le_one p policy k reveal
      _ = n := by simp
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hnR]
    exact hsumTestLe
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hresidual0 : ∀ i, 0 ≤ residualMass i := residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := hmodulePositive.le
  have hpartitionSelected : a + ∑ i, residualMass i = 1 := by
    dsimp [a, residualMass]
    unfold RandomizedAnnounced.discoveryMass
    have hsplit := sum_selectedPart_add_sum_residualPart selected mass
    linarith
  let lowWork := ∑ i, G.price i * selectedPart selected mass i
  have hmoduleWork : τ * a = 1 + lowWork := by
    simpa [a, lowWork, RandomizedAnnounced.discoveryWork] using hmoduleDensity
  have hmeanWork : lowWork + ∑ i, G.price i * residualMass i = mean := by
    simpa [lowWork, residualMass] using hmeanPartition
  have hterminal : fluidBlocksWork
      (optionalSortedBlocks q a τ u G.price residualMass) =
        q * (1 + mean) + u * (1 - q) := by
    rw [optionalSortedBlocks_work]
    linear_combination q * hmoduleWork + q * hmeanWork
  have hwork0 : 0 ≤ work := by
    dsimp [work]
    exact add_nonneg
      (div_nonneg
        (RawObserved.rawElapsed_nonneg (show 0 ≤ u from hu.le)
          (fun job => G.processing_nonneg (σ job)) _) hnR.le)
      G.mesh_nonneg
  by_cases hwithinTerminal : work ≤ q * (1 + mean) + u * (1 - q)
  · have hworkTerminal : work ≤ fluidBlocksWork
        (optionalSortedBlocks q a τ u G.price residualMass) := by
      rw [hterminal]
      exact hwithinTerminal
    have hcert := optionalSortedAllocation_certificate
      (q := q) (a := a) (τ := τ) (μ := u) (x := work)
      (p := G.price) (residualMass := residualMass)
      hτ hu hprice hq0 hq1 ha0 hresidual0 hwork0 hworkTerminal
    obtain ⟨hgreedyWork, hgreedyMass, pivotCost, hpivot,
        hgreedyLow, hgreedyHigh⟩ := hcert
    have hopen := raw_operational_prefix_completion_le_greedy_rounded hn p policy
      σ G hfuel cutoff hlength selected
      (γ := γ) (zeroMass := zeroMass) (τ := τ) (u := u)
      (mass := mass)
      (completion := fun _ => 0)
      (greedyModule := optionalSortedModule q a τ u work G.price residualMass)
      (greedyBlind := optionalSortedBlind q a τ u work G.price residualMass)
      (greedyResidual := optionalSortedResidual q a τ u work G.price residualMass)
      (pivotCost := pivotCost)
      hmassDef hzeroMassDef hγ hclassGood hzeroGood
      hmax hmodulePositive hmoduleDensity hpivot (by exact hgreedyWork.ge)
      hgreedyLow hgreedyHigh
    calc
      (completionCount (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤
          optionalKnapsackMass
              (optionalSortedModule q a τ u work G.price residualMass)
              (optionalSortedBlind q a τ u work G.price residualMass)
              (optionalSortedResidual q a τ u work G.price residualMass) +
            (Fintype.card ι + 1) * γ := hopen
      _ = fluidBlocksCompleted
            (optionalSortedBlocks q a τ u G.price residualMass) work +
            (Fintype.card ι + 1) * γ := by rw [hgreedyMass]
  · have hterminalLe : fluidBlocksWork
        (optionalSortedBlocks q a τ u G.price residualMass) ≤ work := by
      rw [hterminal]
      exact le_of_not_ge hwithinTerminal
    have hcurveOne := fluidBlocksCompleted_eq_mass_of_work_le
      (optionalSortedBlocks_cost_pos hτ hu hprice)
      (optionalSortedBlocks_mass_nonneg hq0 hq1 ha0 hresidual0)
      hterminalLe
    have hmassOne := optionalSortedBlocks_mass_eq_one
      q a τ u G.price residualMass hpartitionSelected
    rw [hcurveOne, hmassOne]
    have hslack0 : 0 ≤ (Fintype.card ι + 1 : ℝ) * γ := by positivity
    linarith

theorem raw_settled_prefix_completion_le_sortedEnvelope_rounded
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : RoundedPositiveGrid ι p) (selected : ι → Bool)
    {γ zeroMass τ u mean : ℝ} {mass : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hγ : 0 ≤ γ)
    (hτ : 0 < τ) (hu : 0 < u) (hprice : ∀ i, 0 < G.price i)
    (hpopulationMass : zeroMass + ∑ i, mass i = 1)
    (hmeanPartition :
      (∑ i, G.price i * selectedPart selected mass i) +
        ∑ i, G.price i * residualPart selected mass i = mean)
    (hclassGood : ∀ cutoff i,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        mass i *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hzeroGood : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if zeroCategory
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        zeroMass *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
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
    (pre : Transcript n)
    (hpre : pre <+:
      (settledRun p policy.strategy σ).config.transcript) :
    let q := (∑ k, compiledTestSelector p policy k
      (revealOrder (touchTrace p policy) σ)) / n
    let a := RandomizedAnnounced.discoveryMass zeroMass
      (selectedPart selected mass)
    let residualMass := residualPart selected mass
    (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
      fluidBlocksCompleted
          (optionalSortedBlocks q a τ u G.price residualMass)
          (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + G.mesh) +
        (Fintype.card ι + 1) * γ := by
  dsimp
  let full := (settledRun p policy.strategy σ).config.transcript
  let fuel := pre.length
  let reveal := revealOrder (touchTrace p policy) σ
  let q : ℝ := (∑ k, compiledTestSelector p policy k reveal) / n
  let a := RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  let residualMass := residualPart selected mass
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpreLength : pre.length ≤ full.length := hpre.length_le
  have hfullLength : full.length ≤ 2 * n + 1 := by
    dsimp [full, settledRun]
    rw [run_transcript_eq_runWord]
    exact runWord_length_le_fuel _ _ _ _
  have hfuel : fuel ≤ 2 * n + 1 := hpreLength.trans hfullLength
  have hrunTake := run_transcript_eq_take_of_le_length
    (placedProcessing p σ) policy.strategy hfuel hpreLength
  have hpreTake : pre = full.take pre.length := list_eq_take_of_prefix hpre
  have hrunPre :
      (run (placedProcessing p σ) policy.strategy fuel).config.transcript = pre := by
    simpa [fuel, full] using hrunTake.trans hpreTake.symm
  let touches := (touchChoices pre).length
  have htouchesLe : touches ≤ n := by
    have hprefChoices := touchChoices_prefix hpre
    have hlength := hprefChoices.length_le
    have hfullChoices : (touchChoices full).length = n := by
      have hchoices := touchTrace_choices_ofFn p policy σ
      dsimp [full]
      rw [← hchoices]
      simp
    simpa [touches, full, hfullChoices] using hlength
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
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn _
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hresidual0 : ∀ i, 0 ≤ residualMass i := residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := hmodulePositive.le
  by_cases htouches : touches = 0
  · have hcountLe := run_completionCount_le_startedLabels_length
      (placedProcessing p σ) policy.strategy fuel
    rw [hrunPre] at hcountLe
    have hstartedLength : pre.startedLabels.length = touches := by
      rw [← touchChoices_map_fst]
      simp [touches]
    have hcountZero : completionCount (placedProcessing p σ) pre = 0 := by
      rw [hstartedLength, htouches] at hcountLe
      omega
    have hcurve0 := fluidBlocksCompleted_nonneg
      (optionalSortedBlocks_mass_nonneg
        (q := q) (a := a) (τ := τ) (μ := u)
        (p := G.price) (residualMass := residualMass)
        hq0 hq1 ha0 hresidual0)
      (RawObserved.rawElapsed u (placedProcessing p σ) pre / n + G.mesh)
    have hslack0 : 0 ≤ (Fintype.card ι + 1 : ℝ) * γ := by positivity
    rw [hcountZero]
    norm_num
    linarith
  · let cutoff : Fin n := ⟨touches - 1, by omega⟩
    have hlength :
        (touchChoices
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
            cutoff.val + 1 := by
      rw [hrunPre]
      dsimp [cutoff, touches]
      omega
    have hcompletionLeOne :
        (completionCount (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) /
            n ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast run_completionCount_le_n
        (placedProcessing p σ) policy.strategy fuel
    have hopen := raw_operational_prefix_completion_le_sortedEnvelope_rounded
      hn p policy σ G hfuel cutoff hlength selected
      hmassDef hzeroMassDef hγ hτ hu hprice
      hpopulationMass hmeanPartition (hclassGood cutoff) (hzeroGood cutoff)
      hmax hmodulePositive hmoduleDensity hcompletionLeOne
    simpa [hrunPre, q, a, residualMass, reveal] using hopen


end

end ObservedEnvelope
end RevealingOptimization
end SchedulingPaper
