import SchedulingPaper.RandomizedOptionalObservedCompletionIntegral
import SchedulingPaper.RandomizedOptionalObservedFullWork
import Mathlib.Tactic

/-!
# From an observed completion envelope to a fluid area lower bound

This file closes the deterministic analytic bridge used in the optional-
testing lower bound.  Once every transcript prefix is dominated by a common
fluid completion curve and the terminal works agree, integration gives the
area of the fluid block schedule, up to the horizontal and vertical repair
errors.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedEnvelope

open ObservedOnline
open ObservedTrace
open TraceBijection
open Randomized

noncomputable section

/-- A pathwise prefix completion bound against a finite fluid block schedule
integrates to the corresponding fluid area lower bound. -/
theorem transcriptCost_ge_fluidBlocksArea
    {n : ℕ} (hn : 0 < n) {processing : Fin n → ℝ}
    (transcript : Transcript n) (blocks : List FluidBlock)
    (ζ ε : ℝ)
    (hζ : 0 ≤ ζ)
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hmatch : AllRevealsMatch processing transcript)
    (hcomplete : completionCount processing transcript = n)
    (hcost : ∀ b ∈ blocks, 0 < b.cost)
    (hmass : ∀ b ∈ blocks, 0 ≤ b.mass)
    (hmassOne : fluidBlocksMass blocks = 1)
    (hterminal : elapsed processing transcript / n = fluidBlocksWork blocks)
    (hprefix : ∀ pre, pre <+: transcript →
      (completionCount processing pre : ℝ) / n ≤
        fluidBlocksCompleted blocks (elapsed processing pre / n + ζ) + ε) :
    fluidBlocksArea blocks - ζ - ε * fluidBlocksWork blocks ≤
      completionCost processing transcript / (n : ℝ) ^ 2 := by
  let curve : ℝ → ℝ := fluidBlocksCompleted blocks
  let remaining : ℝ → ℝ := fun x => 1 - curve x
  let T := fluidBlocksWork blocks
  have hcurveContinuous : Continuous curve := by
    simpa [curve] using fluidBlocksCompleted_continuous blocks
  have hcurveMono : Monotone curve := by
    simpa [curve] using fluidBlocksCompleted_monotone hcost
  have hT : 0 ≤ T := by
    dsimp [T]
    exact fluidBlocksWork_nonneg hcost hmass
  have hremainingContinuous : Continuous remaining := by
    exact continuous_const.sub hcurveContinuous
  have hremainingInt :
      IntervalIntegrable remaining MeasureTheory.volume 0 (T + ζ) :=
    hremainingContinuous.intervalIntegrable 0 (T + ζ)
  have hremaining0 : ∀ x, 0 ≤ remaining x := by
    intro x
    dsimp [remaining, curve]
    exact sub_nonneg.mpr (by
      simpa [hmassOne] using fluidBlocksCompleted_le_mass hmass x)
  have hremaining1 : ∀ x, remaining x ≤ 1 := by
    intro x
    dsimp [remaining, curve]
    linarith [fluidBlocksCompleted_nonneg hmass x]
  have hshift := remainingMass_integral_shift hT hζ hremainingInt
    hremaining0 hremaining1
  have harea : (∫ x in 0..T, remaining x) = fluidBlocksArea blocks := by
    dsimp [remaining, curve, T]
    simpa [hmassOne] using
      fluidBlocks_remaining_integral_eq_area blocks hcost hmass
  have hintegral := transcriptCost_ge_remaining_integral hn transcript curve
    hcurveContinuous hcurveMono ζ ε hprocessing hmatch hcomplete hprefix
  have hintegralT :
      (∫ x in 0..T, (remaining (x + ζ) - ε)) ≤
        completionCost processing transcript / (n : ℝ) ^ 2 := by
    simpa [remaining, curve, T, hterminal] using hintegral
  have hshiftedInt : IntervalIntegrable (fun x => remaining (x + ζ))
      MeasureTheory.volume 0 T :=
    (hremainingContinuous.comp
      (continuous_id.add continuous_const)).intervalIntegrable 0 T
  have hconstantInt : IntervalIntegrable (fun _x : ℝ => ε)
      MeasureTheory.volume 0 T :=
    continuous_const.intervalIntegrable 0 T
  have hvertical :
      (∫ x in 0..T, (remaining (x + ζ) - ε)) =
        (∫ x in 0..T, remaining (x + ζ)) - ε * T := by
    rw [intervalIntegral.integral_sub hshiftedInt hconstantInt]
    simp
    ring
  rw [hvertical] at hintegralT
  rw [harea] at hshift
  linarith

/-- The complete deterministic lower-bound bridge for one good hidden
placement.  The tested fraction `q` is the fraction realized by the adaptive
policy itself.  It is substituted only after the simultaneous prefix event
has been fixed. -/
theorem settled_cost_ge_sortedBlocksArea
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : ExactPositiveGrid ι p) (selected : ι → Bool)
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
    (hblindGood : ∀ cutoff,
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
          (selectedPart selected mass)) :
    let q := (∑ k, compiledTestSelector p policy k
      (revealOrder (touchTrace p policy) σ)) / n
    let a := RandomizedAnnounced.discoveryMass zeroMass
      (selectedPart selected mass)
    let residualMass := residualPart selected mass
    fluidBlocksArea
          (optionalSortedBlocks q a τ μ G.price residualMass) -
        blindError - (Fintype.card ι + 1) * γ * (q + μ) ≤
      completionCost (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript /
        (n : ℝ) ^ 2 := by
  dsimp
  let reveal := revealOrder (touchTrace p policy) σ
  let q : ℝ := (∑ k, compiledTestSelector p policy k reveal) / n
  let a := RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  let residualMass := residualPart selected mass
  let blocks := optionalSortedBlocks q a τ μ G.price residualMass
  let transcript := (settledRun p policy.strategy σ).config.transcript
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
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn
      (fun occurrence => if G.category i (p occurrence) then 1 else 0)
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
  have hmeanWork : lowWork + ∑ i, G.price i * residualMass i = μ := by
    simpa [lowWork, residualMass] using hmeanPartition
  have hblocksMass : fluidBlocksMass blocks = 1 := by
    dsimp [blocks]
    exact optionalSortedBlocks_mass_eq_one q a τ μ G.price residualMass
      hpartitionSelected
  have hblocksWork : fluidBlocksWork blocks = q + μ := by
    dsimp [blocks]
    exact optionalSortedBlocks_work_eq_q_add_mean q a τ μ lowWork G.price
      residualMass hmoduleWork hmeanWork
  have hblocksCost : ∀ b ∈ blocks, 0 < b.cost := by
    dsimp [blocks]
    exact optionalSortedBlocks_cost_pos hτ hμ hprice
  have hblocksMass0 : ∀ b ∈ blocks, 0 ≤ b.mass := by
    dsimp [blocks]
    exact optionalSortedBlocks_mass_nonneg hq0 hq1 ha0 hresidual0
  have hprocessing : ∀ job, 0 ≤ placedProcessing p σ job := by
    intro job
    exact G.processing_nonneg (σ job)
  have hmatch : AllRevealsMatch (placedProcessing p σ) transcript := by
    dsimp [transcript, settledRun]
    exact (run_historyInvariant (placedProcessing p σ) policy.strategy
      (2 * n + 1)).revealsMatch
  have hcomplete : completionCount (placedProcessing p σ) transcript = n := by
    dsimp [transcript, settledRun]
    exact run_completionCount_eq_n_of_done (placedProcessing p σ)
      policy.strategy (2 * n + 1) (policy.completes σ)
  have hterminal : elapsed (placedProcessing p σ) transcript / n =
      fluidBlocksWork blocks := by
    have hrun := settled_elapsed_div_eq_testFraction_add_mean hn p policy σ hμDef
    rw [hblocksWork]
    simpa [transcript, q, reveal] using hrun
  have hprefix : ∀ pre, pre <+: transcript →
      (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
        fluidBlocksCompleted blocks
            (elapsed (placedProcessing p σ) pre / n + blindError) +
          (Fintype.card ι + 1) * γ := by
    intro pre hpre
    have hpref := settled_prefix_completion_le_sortedEnvelope
      hn p policy σ G selected hmassDef hzeroMassDef hμDef hγ hblindError
      hτ hμ hprice hpopulationMass hmeanPartition hclassGood hzeroGood
      hblindGood hmax hmodulePositive hmoduleDensity pre
      (by simpa [transcript] using hpre)
    simpa [q, a, residualMass, blocks, reveal] using hpref
  have harea := transcriptCost_ge_fluidBlocksArea hn transcript blocks
    blindError ((Fintype.card ι + 1) * γ) hblindError hprocessing hmatch
    hcomplete hblocksCost hblocksMass0 hblocksMass hterminal hprefix
  rw [hblocksWork] at harea
  simpa [transcript, blocks, q, a, residualMass, reveal, mul_assoc] using harea

/-- A placement-independent version of the preceding theorem.  Any fixed
minimizing fraction `qStar` may replace the run's adaptive fraction, while
the vertical repair horizon is bounded by `1+μ`. -/
theorem settled_cost_ge_fixedFluidMinimum
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : ExactPositiveGrid ι p) (selected : ι → Bool)
    {qStar γ zeroMass τ μ blindError : ℝ} {mass : ι → ℝ}
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
    (hblindGood : ∀ cutoff,
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
    (hmin : ∀ q, 0 ≤ q → q ≤ 1 →
      fluidBlocksArea (optionalSortedBlocks qStar
          (RandomizedAnnounced.discoveryMass zeroMass
            (selectedPart selected mass)) τ μ G.price
          (residualPart selected mass)) ≤
        fluidBlocksArea (optionalSortedBlocks q
          (RandomizedAnnounced.discoveryMass zeroMass
            (selectedPart selected mass)) τ μ G.price
          (residualPart selected mass))) :
    fluidBlocksArea (optionalSortedBlocks qStar
          (RandomizedAnnounced.discoveryMass zeroMass
            (selectedPart selected mass)) τ μ G.price
          (residualPart selected mass)) -
        blindError - (Fintype.card ι + 1) * γ * (1 + μ) ≤
      completionCost (placedProcessing p σ)
          (settledRun p policy.strategy σ).config.transcript /
        (n : ℝ) ^ 2 := by
  let reveal := revealOrder (touchTrace p policy) σ
  let q : ℝ := (∑ k, compiledTestSelector p policy k reveal) / n
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
  have hrun := settled_cost_ge_sortedBlocksArea hn p policy σ G selected
    hmassDef hzeroMassDef hμDef hγ hblindError hτ hμ hprice
    hpopulationMass hmeanPartition hclassGood hzeroGood hblindGood hmax
    hmodulePositive hmoduleDensity
  have hminimum := hmin q hq0 hq1
  have hcoefficient : 0 ≤ (Fintype.card ι + 1 : ℝ) * γ := by
    positivity
  have hhorizon :
      (Fintype.card ι + 1 : ℝ) * γ * (q + μ) ≤
        (Fintype.card ι + 1 : ℝ) * γ * (1 + μ) := by
    apply mul_le_mul_of_nonneg_left _ hcoefficient
    simpa [add_comm] using add_le_add_right hq1 μ
  dsimp at hrun
  simpa [q, reveal] using (show
      fluidBlocksArea (optionalSortedBlocks qStar
            (RandomizedAnnounced.discoveryMass zeroMass
              (selectedPart selected mass)) τ μ G.price
            (residualPart selected mass)) -
          blindError - (Fintype.card ι + 1) * γ * (1 + μ) ≤
        completionCost (placedProcessing p σ)
            (settledRun p policy.strategy σ).config.transcript /
          (n : ℝ) ^ 2 by linarith)

end

end ObservedEnvelope
end RandomizedOptional
end SchedulingPaper
