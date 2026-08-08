import SchedulingPaper.RandomizedOptionalObservedEnvelope
import SchedulingPaper.RandomizedOptionalKnapsackEnvelope
import Mathlib.Tactic

/-!
# Operational prefixes below the literal sorted greedy envelope

`ObservedEnvelope.operational_prefix_completion_le_greedy` deliberately
accepted an abstract greedy cut.  This file supplies that cut using the
executable sorted optional knapsack.  The result is the pointwise statement
needed before integrating a complete transcript.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedEnvelope

open ObservedOnline
open ObservedTrace
open TraceBijection
open Randomized

noncomputable section

theorem elapsed_nonneg_of_revealsMatch
    {n : ℕ} {processing : Fin n → ℝ} (transcript : Transcript n)
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hmatch : AllRevealsMatch processing transcript) :
    0 ≤ elapsed processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hrestMatch : AllRevealsMatch processing rest := by
        intro job value hmem
        exact hmatch job value (by
          cases observation <;>
            simp [Transcript.revealedResults, hmem])
      have hrest := ih hrestMatch
      cases observation with
      | testResult job value =>
          simp [elapsed, Observation.actualDuration]
          linarith
      | processed job =>
          simp [elapsed, Observation.actualDuration]
          exact add_nonneg (hprocessing job) hrest
      | blindCompleted job value =>
          have hvalue : value = processing job :=
            hmatch job value (by simp [Transcript.revealedResults])
          simp [elapsed, Observation.actualDuration, hvalue]
          exact add_nonneg (hprocessing job) hrest

/-- Every regulated operational prefix is dominated by the literal sorted
optional-knapsack completion curve.  Before the terminal work `q+μ` this is
the fractional-knapsack certificate; afterwards the curve is already one. -/
theorem operational_prefix_completion_le_sortedEnvelope
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : ExactPositiveGrid ι p) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1)
    (selected : ι → Bool)
    {γ zeroMass τ μ blindError : ℝ} {mass : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hμDef : μ = populationMean p)
    (hγ : 0 ≤ γ) (hblindError : 0 ≤ blindError)
    (hτ : 0 < τ) (hμ : 0 < μ) (hprice : ∀ i, 0 < G.price i)
    (hpopulationMass : zeroMass + ∑ i, mass i = 1)
    (hmeanPartition :
      (∑ i, G.price i * selectedPart selected mass i) +
        ∑ i, G.price i * residualPart selected mass i = μ)
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
    (hblindGood :
      |(∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            p (revealOrder (touchTrace p policy) σ k)) -
        μ *
          ∑ k ∈ positionsThrough cutoff,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ blindError * n)
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
      (elapsed (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript) / n +
          blindError
    (completionCount (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤
      fluidBlocksCompleted
          (optionalSortedBlocks q a τ μ G.price residualMass) work +
        (Fintype.card ι + 1) * γ := by
  dsimp
  let reveal := revealOrder (touchTrace p policy) σ
  let selectTest := compiledTestSelector p policy
  let q : ℝ := (∑ k, selectTest k reveal) / n
  let a := RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  let residualMass := residualPart selected mass
  let work :=
    elapsed (placedProcessing p σ)
      (run (placedProcessing p σ) policy.strategy fuel).config.transcript / n +
        blindError
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Finset.sum_nonneg fun k _ =>
      ObservedTrace.compiledTestSelector_nonneg p policy k reveal) hnR.le
  have hsumTestLe : (∑ k, selectTest k reveal) ≤ n := by
    calc
      (∑ k, selectTest k reveal) ≤ ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          ObservedTrace.compiledTestSelector_le_one p policy k reveal
      _ = n := by simp
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hnR]
    exact hsumTestLe
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn
      (fun occurrence => if G.category i (p occurrence) then 1 else 0)
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hresidual0 : ∀ i, 0 ≤ residualMass i :=
    residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := hmodulePositive.le
  have hpartitionSelected :
      a + ∑ i, residualMass i = 1 := by
    dsimp [a, residualMass]
    unfold RandomizedAnnounced.discoveryMass
    have hsplit := sum_selectedPart_add_sum_residualPart selected mass
    linarith
  let lowWork := ∑ i, G.price i * selectedPart selected mass i
  have hmoduleWork : τ * a = 1 + lowWork := by
    simpa [a, lowWork, RandomizedAnnounced.discoveryWork] using hmoduleDensity
  have hmeanWork : lowWork + ∑ i, G.price i * residualMass i = μ := by
    simpa [lowWork, residualMass] using hmeanPartition
  have hterminal : fluidBlocksWork
      (optionalSortedBlocks q a τ μ G.price residualMass) = q + μ :=
    optionalSortedBlocks_work_eq_q_add_mean q a τ μ lowWork G.price
      residualMass hmoduleWork hmeanWork
  have hwork0 : 0 ≤ work := by
    dsimp [work]
    have hrun := run_historyInvariant (placedProcessing p σ)
      policy.strategy fuel
    have helapsed : 0 ≤ elapsed (placedProcessing p σ)
        (run (placedProcessing p σ) policy.strategy fuel).config.transcript :=
      elapsed_nonneg_of_revealsMatch _
        (fun job => G.processing_nonneg (σ job)) hrun.revealsMatch
    exact add_nonneg
      (div_nonneg helapsed hnR.le)
      hblindError
  by_cases hwithinTerminal : work ≤ q + μ
  · have hworkTerminal : work ≤ fluidBlocksWork
        (optionalSortedBlocks q a τ μ G.price residualMass) := by
      rw [hterminal]
      exact hwithinTerminal
    have hcert := optionalSortedAllocation_certificate
      (q := q) (a := a) (τ := τ) (μ := μ) (x := work)
      (p := G.price) (residualMass := residualMass)
      hτ hμ hprice hq0 hq1 ha0 hresidual0 hwork0 hworkTerminal
    obtain ⟨hgreedyWork, hgreedyMass, pivotCost, hpivot,
        hgreedyLow, hgreedyHigh⟩ := hcert
    have hopen := operational_prefix_completion_le_greedy hn p policy σ G
      hfuel cutoff hlength selected
      (γ := γ) (zeroMass := zeroMass) (τ := τ) (μ := μ)
      (blindError := blindError) (mass := mass)
      (completion := fun _ => 0)
      (greedyModule := optionalSortedModule q a τ μ work G.price residualMass)
      (greedyBlind := optionalSortedBlind q a τ μ work G.price residualMass)
      (greedyResidual := optionalSortedResidual q a τ μ work G.price residualMass)
      (pivotCost := pivotCost)
      hmassDef hzeroMassDef hμDef hγ hblindError hclassGood hzeroGood hblindGood
      hmax hmodulePositive hmoduleDensity hpivot
      (by exact hgreedyWork.ge) hgreedyLow hgreedyHigh
    calc
      (completionCount (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) / n ≤
          optionalKnapsackMass
              (optionalSortedModule q a τ μ work G.price residualMass)
              (optionalSortedBlind q a τ μ work G.price residualMass)
              (optionalSortedResidual q a τ μ work G.price residualMass) +
            (Fintype.card ι + 1) * γ := hopen
      _ = fluidBlocksCompleted
            (optionalSortedBlocks q a τ μ G.price residualMass) work +
            (Fintype.card ι + 1) * γ := by rw [hgreedyMass]
  · have hterminalLe : fluidBlocksWork
        (optionalSortedBlocks q a τ μ G.price residualMass) ≤ work := by
      rw [hterminal]
      exact le_of_not_ge hwithinTerminal
    have hcurveOne := fluidBlocksCompleted_eq_mass_of_work_le
      (optionalSortedBlocks_cost_pos hτ hμ hprice)
      (optionalSortedBlocks_mass_nonneg hq0 hq1 ha0 hresidual0)
      hterminalLe
    have hmassOne := optionalSortedBlocks_mass_eq_one
      q a τ μ G.price residualMass hpartitionSelected
    rw [hcurveOne, hmassOne]
    have hslack0 : 0 ≤ (Fintype.card ι + 1 : ℝ) * γ := by positivity
    linarith

end

end ObservedEnvelope
end RandomizedOptional
end SchedulingPaper
