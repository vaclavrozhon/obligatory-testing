import SchedulingPaper.GeneralRandomization
import SchedulingPaper.PrivateShuffleCorollaries
import SchedulingPaper.RandomizedOnlineBinaryCompiler
import SchedulingPaper.BlindOptimizationRandomizedCompiler
import SchedulingPaper.BlindOptimizationInstanceLower
import SchedulingPaper.RevealingOptimizationOperationalCompiler
import SchedulingPaper.RandomizedOptionalUnknownRates
import SchedulingPaper.BlindOptionalUnboundedOperational
import SchedulingPaper.ObligatoryUnboundedOperational
import Mathlib.Tactic

/-!
# Paper conclusions for arbitrary private probability spaces

The algorithms constructed in the development have finite uniform seeds.
The competing randomized algorithms in the paper are allowed arbitrary
private probability spaces.  The corollaries below close that quantifier
gap.  Expected run costs are required to be integrable; this is the usual
well-formedness condition for an expected-cost guarantee.
-/

namespace SchedulingPaper

open MeasureTheory

noncomputable section

namespace RandomizedObligatory

open Randomized
open Online

/-- Operational obligatory-testing lower bound for an arbitrary private
probability space, with the independent private label shuffle displayed
literally. -/
theorem oblivious_iid_binary_lower_online_general_privateShuffle_actualOPT
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ seed order input job,
      (Online.run .infinite
        (Online.fixedOracle (iidBinaryProcessingTime input))
        ((strategy seed).relabel order) fuel).config.jobs job = .done)
    (hcost : ∀ input, Integrable (fun seed =>
      uniformAverage fun order : Equiv.Perm (Fin n) =>
        Online.runCompletionCost .infinite
          (iidBinaryProcessingTime input)
          (Online.run .infinite
            (Online.fixedOracle (iidBinaryProcessingTime input))
            ((strategy seed).relabel order) fuel)) μ) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) *
          finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
        generalExpectation μ fun seed =>
          uniformAverage fun order : Equiv.Perm (Fin n) =>
            Online.runCompletionCost .infinite
              (iidBinaryProcessingTime input)
              (Online.run .infinite
                (Online.fixedOracle (iidBinaryProcessingTime input))
                ((strategy seed).relabel order) fuel) := by
  let cost : BinaryInput n → Ω → ℝ := fun input seed =>
    uniformAverage fun order : Equiv.Perm (Fin n) =>
      Online.runCompletionCost .infinite
        (iidBinaryProcessingTime input)
        (Online.run .infinite
          (Online.fixedOracle (iidBinaryProcessingTime input))
          ((strategy seed).relabel order) fuel)
  have hseed : ∀ seed, (n : ℝ) ^ 2 ≤
      uniformAverage fun input : BinaryInput n => cost input seed := by
    intro seed
    rw [RandomizedObligatory.uniformAverage_comm]
    calc
      (n : ℝ) ^ 2 = uniformAverage
          (fun _order : Equiv.Perm (Fin n) => (n : ℝ) ^ 2) :=
        (uniformAverage_const _).symm
      _ ≤ uniformAverage (fun order : Equiv.Perm (Fin n) =>
          uniformAverage fun input : BinaryInput n =>
            Online.runCompletionCost .infinite
              (iidBinaryProcessingTime input)
              (Online.run .infinite
                (Online.fixedOracle (iidBinaryProcessingTime input))
                ((strategy seed).relabel order) fuel)) := by
        apply uniformAverage_mono
        intro order
        exact onlineStrategy_iidBinary_uniformAverage_lower
          ((strategy seed).relabel order) fuel (hdone seed order)
  have hjoint : (n : ℝ) ^ 2 ≤ uniformAverage
      (fun input : BinaryInput n => generalExpectation μ (cost input)) := by
    rw [← generalExpectation_uniformAverage_comm μ cost hcost]
    rw [← generalExpectation_const μ ((n : ℝ) ^ 2)]
    exact generalExpectation_mono μ (integrable_const _)
      (integrable_uniformAverage μ cost hcost) hseed
  apply general_yao_select_uniform_ratio μ cost hcost
    (fun input => finiteObligatoryOPT (iidBinaryProcessingTime input))
      (L := (n : ℝ) ^ 2)
      (O := (3 * (n : ℝ) ^ 2 + 5 * n) / 4)
  · exact hjoint
  · calc
      uniformAverage (fun input : BinaryInput n =>
          finiteObligatoryOPT (iidBinaryProcessingTime input)) =
          uniformAverage (iidBinaryOfflineCost n) := by
            apply congrArg uniformAverage
            funext input
            exact (iidBinaryOfflineCost_eq_finiteObligatoryOPT hn input).symm
      _ = (3 * (n : ℝ) ^ 2 + 5 * n) / 4 :=
        uniformAverage_iidBinaryOfflineCost n
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    field_simp
    norm_num

end RandomizedObligatory

namespace BlindOptimization
namespace RandomizedCompiler

open Randomized
open RandomizedLower
open Online

/-- Exact finite blind-optimization Yao ratio for arbitrary private
randomness. -/
theorem operational_binary_general_expected_ratio
    {n : ℕ} (hn : 0 < n) {u b : ℝ} (hu : 1 < u)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Strategy n)
    (hcomplete : ∀ seed, CompletesAll u (strategy seed))
    (hcost : ∀ input : BinaryInput n, Integrable (fun seed =>
      runCost u (binaryProcessing u input) (strategy seed) n) μ) :
    ∃ input : BinaryInput n,
      binaryFiniteYaoRatio n u b *
          offlineCost u (binaryProcessing u input) ≤
        generalExpectation μ fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n := by
  let cost : BinaryInput n → Ω → ℝ := fun input seed =>
    runCost u (binaryProcessing u input) (strategy seed) n
  let numerator := triangularCount n * min u (1 + b * u)
  let denominator := binaryExpectedOfflineCost n u b
  have hseed : ∀ seed, numerator ≤
      finiteExpectation (bernoulliWeight n b) fun input => cost input seed := by
    intro seed
    exact operational_binary_finiteExpectation_lower (strategy seed)
      (by linarith) hb0 hb1 (hcomplete seed)
  have hlower : numerator ≤ finiteExpectation (bernoulliWeight n b)
      (fun input => generalExpectation μ (cost input)) := by
    rw [finiteExpectation_generalExpectation_comm μ
      (bernoulliWeight n b) cost hcost]
    rw [← generalExpectation_const μ numerator]
    exact generalExpectation_mono μ (integrable_const _)
      (integrable_finiteExpectation μ (bernoulliWeight n b) cost hcost) hseed
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hpair : 0 < 1 + (u - 1) * b ^ 2 := by
    have hnonneg : 0 ≤ (u - 1) * b ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg b)
    linarith
  have hdiagonal : 0 < 1 + (u - 1) * b := by
    have hnonneg : 0 ≤ (u - 1) * b :=
      mul_nonneg (by linarith) hb0
    linarith
  have hdenRewrite : denominator =
      (n : ℝ) * ((n : ℝ) - 1) / 2 * (1 + (u - 1) * b ^ 2) +
        (n : ℝ) * (1 + (u - 1) * b) := by
    dsimp [denominator]
    unfold binaryExpectedOfflineCost
    ring
  have hden : 0 < denominator := by
    rw [hdenRewrite]
    have hcoeff : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by positivity
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hcoeff hpair.le)
      (mul_pos hnR hdiagonal)
  apply general_yao_select_ratio μ (bernoulliWeight n b)
    (bernoulliWeight_nonneg hb0 hb1)
    (bernoulliWeight_mass n b) cost hcost
    (fun input => offlineCost u (binaryProcessing u input))
      (L := numerator) (O := denominator)
  · exact hlower
  · exact finiteExpectation_binary_offlineCost hu
  · unfold binaryFiniteYaoRatio
    exact le_of_eq (div_mul_cancel₀ _ hden.ne')

/-- At a curve-maximizing binary mass, the general-private-randomness finite
ratios converge to the blind-optimization curve. -/
theorem exists_binary_mass_operational_ratio_tendsto_curve_general
    {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => binaryFiniteYaoRatio n u b)
        Filter.atTop (nhds (randomizedCurve u)) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω],
        ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
        0 < n → ∀ strategy : Ω → Strategy n,
          (∀ seed, CompletesAll u (strategy seed)) →
          (∀ input : BinaryInput n, Integrable (fun seed =>
            runCost u (binaryProcessing u input) (strategy seed) n) μ) →
          ∃ input : BinaryInput n,
            binaryFiniteYaoRatio n u b *
                offlineCost u (binaryProcessing u input) ≤
              generalExpectation μ fun seed =>
                runCost u (binaryProcessing u input) (strategy seed) n := by
  obtain ⟨b, hb, hlimit⟩ := exists_binary_mass_finite_ratio_tendsto_curve hu
  refine ⟨b, hb, hlimit, ?_⟩
  intro n Ω _ μ _ hn strategy hcomplete hcost
  exact operational_binary_general_expected_ratio hn hu hb.1 hb.2
    μ strategy hcomplete hcost

end RandomizedCompiler

namespace InstanceLower

open Randomized
open Online
open RandomizedOptional

/-- Blind-optimization arbitrary-input lower bound for an arbitrary private
probability space. -/
theorem generalExpectedCost_ge_instanceBenchmark_nsq
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp : ∀ job, p job ∈ Set.Icc (0 : ℝ) u)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Online.Strategy n)
    (hcompletes : ∀ seed placement,
      Online.Completes (ObservedTrace.placedProcessing p placement)
        (strategy seed))
    (hcost : Integrable (fun seed =>
      uniformAverage (fun placement : Equiv.Perm (Fin n) =>
        Online.runCost u (ObservedTrace.placedProcessing p placement)
          (strategy seed) n)) μ) :
    (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
        n * u * Real.sqrt (2 * n) ≤
      generalExpectation μ fun seed =>
        uniformAverage (fun placement : Equiv.Perm (Fin n) =>
          Online.runCost u (ObservedTrace.placedProcessing p placement)
            (strategy seed) n) := by
  let lower := (n : ℝ) ^ 2 / 2 * min u (1 + populationMean p) -
    n * u * Real.sqrt (2 * n)
  have hpoint : ∀ seed, lower ≤
      uniformAverage (fun placement : Equiv.Perm (Fin n) =>
        Online.runCost u (ObservedTrace.placedProcessing p placement)
          (strategy seed) n) := by
    intro seed
    let policy : ObservedTrace.CompletePolicy p :=
      ⟨strategy seed, hcompletes seed⟩
    exact completePolicy_expectedCost_ge_instanceBenchmark_nsq
      hn hu p hp policy
  change lower ≤ _
  rw [← generalExpectation_const μ lower]
  exact generalExpectation_mono μ (integrable_const _) hcost hpoint

end InstanceLower
end BlindOptimization

namespace RevealingOptimization
namespace OperationalCompiler

open Randomized
open RandomizedYao
open BlindOptimization.RandomizedLower

/-- Family-B operational Yao lower bound for arbitrary private randomness. -/
theorem familyB_operational_general_yao_ratio
    {n : ℕ} (hn : 0 < n) {u τ : ℝ}
    (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Online.Strategy n)
    (hcomplete : ∀ seed, CompletesBinary u u (strategy seed))
    (hcost : ∀ input : RandomizedYao.BinaryInput n, Integrable
      (fun seed => binaryRunCost u u (strategy seed) input) μ) :
    ∃ input : RandomizedYao.BinaryInput n,
      familyBFiniteYaoRatio n u τ *
          empiricalRevealingOfflineCost u
            (RandomizedYao.binaryProcessing u input) ≤
        generalExpectation μ fun seed =>
          binaryRunCost u u (strategy seed) input := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  let weight := RandomizedYao.bernoulliWeight n (survivalMass τ)
  let cost : RandomizedYao.BinaryInput n → Ω → ℝ := fun input seed =>
    binaryRunCost u u (strategy seed) input
  let numerator := (n : ℝ) ^ 2 / 2 *
    (familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2))
  let denominator := BlindOptimization.RandomizedLower.binaryExpectedOfflineCost
    n u (survivalMass τ)
  have hseed : ∀ seed, numerator ≤
      finiteExpectation weight fun input => cost input seed := by
    intro seed
    calc
      numerator ≤ finiteExpectation weight
          ((compileInitial (strategy seed) u).cost u u) := by
        simpa [numerator, weight] using
          (compileInitial (strategy seed) u).familyB_le_finiteExpectation
            hu hτ hτu
      _ = finiteExpectation weight (cost · seed) := by
        apply congrArg (finiteExpectation weight)
        funext input
        exact compileInitial_cost_eq_binaryRunCost (strategy seed)
          (by linarith : u ≠ 0) input (hcomplete seed)
  have hlower : numerator ≤ finiteExpectation weight
      (fun input => generalExpectation μ (cost input)) := by
    rw [finiteExpectation_generalExpectation_comm μ weight cost hcost]
    rw [← generalExpectation_const μ numerator]
    exact generalExpectation_mono μ (integrable_const _)
      (integrable_finiteExpectation μ weight cost hcost) hseed
  have hden := binaryExpectedOfflineCost_pos hn hu hx0
  apply general_yao_select_ratio μ weight
    (BlindOptimization.RandomizedLower.bernoulliWeight_nonneg hx0 hx1)
    (BlindOptimization.RandomizedLower.bernoulliWeight_mass n _)
    cost hcost
    (fun input => empiricalRevealingOfflineCost u
      (RandomizedYao.binaryProcessing u input))
      (L := numerator) (O := denominator)
  · exact hlower
  · simpa [weight, denominator] using
      (finiteExpectation_empiricalOfflineCost_binary
        (n := n) (x := survivalMass τ) hu (by linarith : 0 < u))
  · unfold familyBFiniteYaoRatio
    exact le_of_eq (div_mul_cancel₀ _ hden.ne')

/-- Family-A operational Yao lower bound for arbitrary private randomness. -/
theorem familyA_operational_general_yao_ratio
    {n : ℕ} (hn : 0 < n) {u τ : ℝ}
    (hu : 1 < u) (hτ : 1 ≤ τ) (hτcap : τ ≤ u - 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Online.Strategy n)
    (hcomplete : ∀ seed, CompletesBinary u τ (strategy seed))
    (hcost : ∀ input : RandomizedYao.BinaryInput n, Integrable
      (fun seed => binaryRunCost u τ (strategy seed) input) μ) :
    ∃ input : RandomizedYao.BinaryInput n,
      familyAFiniteYaoRatio n τ *
          empiricalRevealingOfflineCost u
            (RandomizedYao.binaryProcessing τ input) ≤
        generalExpectation μ fun seed =>
          binaryRunCost u τ (strategy seed) input := by
  have hτ0 : 0 < τ := by linarith
  have hτu : τ ≤ u := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  let weight := RandomizedYao.bernoulliWeight n (survivalMass τ)
  let cost : RandomizedYao.BinaryInput n → Ω → ℝ := fun input seed =>
    binaryRunCost u τ (strategy seed) input
  let numerator := (n : ℝ) ^ 2 / 2 *
    (familyA τ * (1 + τ * survivalMass τ ^ 2))
  let denominator := BlindOptimization.RandomizedLower.binaryExpectedOfflineCost
    n (1 + τ) (survivalMass τ)
  have hseed : ∀ seed, numerator ≤
      finiteExpectation weight fun input => cost input seed := by
    intro seed
    calc
      numerator ≤ finiteExpectation weight
          ((compileInitial (strategy seed) τ).cost u τ) := by
        simpa [numerator, weight] using
          (compileInitial (strategy seed) τ).familyA_le_finiteExpectation
            hu hτ hτu
      _ = finiteExpectation weight (cost · seed) := by
        apply congrArg (finiteExpectation weight)
        funext input
        exact compileInitial_cost_eq_binaryRunCost (strategy seed)
          (by linarith : τ ≠ 0) input (hcomplete seed)
  have hlower : numerator ≤ finiteExpectation weight
      (fun input => generalExpectation μ (cost input)) := by
    rw [finiteExpectation_generalExpectation_comm μ weight cost hcost]
    rw [← generalExpectation_const μ numerator]
    exact generalExpectation_mono μ (integrable_const _)
      (integrable_finiteExpectation μ weight cost hcost) hseed
  have hhigh : 1 < 1 + τ := by linarith
  have hden := binaryExpectedOfflineCost_pos hn hhigh hx0
  apply general_yao_select_ratio μ weight
    (BlindOptimization.RandomizedLower.bernoulliWeight_nonneg hx0 hx1)
    (BlindOptimization.RandomizedLower.bernoulliWeight_mass n _)
    cost hcost
    (fun input => empiricalRevealingOfflineCost u
      (RandomizedYao.binaryProcessing τ input))
      (L := numerator) (O := denominator)
  · exact hlower
  · rw [show finiteExpectation weight
        (fun input => empiricalRevealingOfflineCost u
          (RandomizedYao.binaryProcessing τ input)) =
        BlindOptimization.RandomizedLower.binaryExpectedOfflineCost n
          (binaryEffectiveHigh u τ) (survivalMass τ) by
      simpa [weight] using
        (finiteExpectation_empiricalOfflineCost_binary
          (n := n) (x := survivalMass τ) hu hτ0)]
    rw [binaryEffectiveHigh_eq_add_one hτcap]
  · unfold familyAFiniteYaoRatio
    exact le_of_eq (div_mul_cancel₀ _ hden.ne')

/-- Quantifier-ordered revealing-optimization lower theorem for arbitrary
private probability spaces. -/
theorem exists_operational_binary_family_ratio_tendsto_curve_general
    {u : ℝ} (hu : 1 < u) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u,
      familyB u τ = randomizedCurve u ∧
      Filter.Tendsto (fun n : ℕ => familyBFiniteYaoRatio n u τ)
        Filter.atTop (nhds (randomizedCurve u)) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω],
        ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
        0 < n → ∀ strategy : Ω → Online.Strategy n,
          (∀ seed, CompletesBinary u u (strategy seed)) →
          (∀ input : RandomizedYao.BinaryInput n, Integrable
            (fun seed => binaryRunCost u u (strategy seed) input) μ) →
          ∃ input : RandomizedYao.BinaryInput n,
            familyBFiniteYaoRatio n u τ *
                empiricalRevealingOfflineCost u
                  (RandomizedYao.binaryProcessing u input) ≤
              generalExpectation μ fun seed =>
                binaryRunCost u u (strategy seed) input) ∨
    (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1),
      familyA τ = randomizedCurve u ∧
      Filter.Tendsto (fun n : ℕ => familyAFiniteYaoRatio n τ)
        Filter.atTop (nhds (randomizedCurve u)) ∧
      ∀ (n : ℕ) (Ω : Type) [MeasurableSpace Ω],
        ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
        0 < n → ∀ strategy : Ω → Online.Strategy n,
          (∀ seed, CompletesBinary u τ (strategy seed)) →
          (∀ input : RandomizedYao.BinaryInput n, Integrable
            (fun seed => binaryRunCost u τ (strategy seed) input) μ) →
          ∃ input : RandomizedYao.BinaryInput n,
            familyAFiniteYaoRatio n τ *
                empiricalRevealingOfflineCost u
                  (RandomizedYao.binaryProcessing τ input) ≤
              generalExpectation μ fun seed =>
                binaryRunCost u τ (strategy seed) input) := by
  rcases binaryFamilies_attain_curve hu with hB | hA
  · left
    rcases hB with ⟨τ, hτ, hattain⟩
    refine ⟨τ, hτ, hattain, ?_, ?_⟩
    · simpa [hattain] using familyBFiniteYaoRatio_tendsto (τ := τ) hu
    · intro n Ω _ μ _ hn strategy hcomplete hcost
      exact familyB_operational_general_yao_ratio hn hu hτ.1 hτ.2
        μ strategy hcomplete hcost
  · right
    rcases hA with ⟨τ, hτ, hattain⟩
    have hτpos : 0 < τ := by linarith [hτ.1]
    refine ⟨τ, hτ, hattain, ?_, ?_⟩
    · simpa [hattain] using familyAFiniteYaoRatio_tendsto hτpos
    · intro n Ω _ μ _ hn strategy hcomplete hcost
      exact familyA_operational_general_yao_ratio hn hu hτ.1 hτ.2
        μ strategy hcomplete hcost

end OperationalCompiler
end RevealingOptimization

namespace ObligatoryPaper

open Randomized
open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower
open ObligatoryInstance

/-- Bounded obligatory-testing instance comparison against a competitor with
an arbitrary private probability space. -/
theorem privateShuffle_paperGrowingPolicy_general_concrete_rate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hCoarseCover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (policy : Ω → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (hcost : Integrable (fun seed =>
      uniformAverage (normalizedCost p (policy seed))) μ) :
    uniformAverage
        (physicalGrowingRunCost
          (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
          (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
      (paperPilotSize n + paperRest n : ℝ) ^ 2 *
        (generalExpectation μ (fun seed =>
            uniformAverage (normalizedCost p (policy seed))) +
          paperInstanceError L n) := by
  let learned := uniformAverage
    (physicalGrowingRunCost
      (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
      (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p)
  let scale := (paperPilotSize n + paperRest n : ℝ) ^ 2
  let error := paperInstanceError L n
  let competitor : Ω → ℝ := fun seed =>
    uniformAverage (normalizedCost p (policy seed))
  have hpoint : ∀ seed, learned ≤ scale * (competitor seed + error) := by
    intro seed
    have hfinite := privateShuffle_paperGrowingPolicy_concrete_rate
      (Seeds := Unit) hR hroot hL hCoarseCover hFineCover p hp0 hpL
      (fun _ => policy seed) (fun _ => htest seed)
    simpa [learned, scale, error, competitor] using hfinite
  have hrightInt : Integrable (fun seed => scale * (competitor seed + error)) μ :=
    (hcost.add (integrable_const error)).const_mul scale
  have havg := generalExpectation_mono μ (integrable_const learned)
    hrightInt hpoint
  simpa [learned, scale, error, competitor, generalExpectation,
    integral_const_mul, integral_add hcost (integrable_const error)] using havg

end ObligatoryPaper

namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open AnnouncedRoundedLower

/-- Bounded blind-execution comparison against arbitrary private
randomness. -/
theorem boundedUniform_blindPilot_general_concrete_rate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {n : ℕ} (hroot : 2 ≤ sixteenthRoot n)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (policy : Ω → ObservedTrace.CompletePolicy p)
    (hcost : Integrable (fun seed =>
      uniformAverage (normalizedCost p (policy seed))) μ) :
    let m := concreteUnknownParameter n
    let hscales := concreteUnknownParameter_bounds n hroot
    let pilot := inverseSquarePilotPositions n m
      (parameter_scales hscales.1 hscales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      generalExpectation μ (fun seed =>
        uniformAverage (normalizedCost p (policy seed))) +
        7830 * (L + 1) ^ 2 / m := by
  dsimp only
  let m := concreteUnknownParameter n
  let hscales := concreteUnknownParameter_bounds n hroot
  let pilot := inverseSquarePilotPositions n m
    (parameter_scales hscales.1 hscales.2).2.1
  let G := boundedUniformRoundedGrid
    (show 0 < m by omega) hL p hp0 hpL
  let learned := uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
    uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) / (n : ℝ) ^ 2
  let error := 7830 * (L + 1) ^ 2 / (m : ℝ)
  let competitor : Ω → ℝ := fun seed =>
    uniformAverage (normalizedCost p (policy seed))
  have hpoint : ∀ seed, learned ≤ competitor seed + error := by
    intro seed
    simpa [learned, error, competitor, m, hscales, pilot, G] using
      (boundedUniform_blindPilot_concrete_rate
        hroot hL p hp0 hpL (policy seed))
  have havg := generalExpectation_mono μ (integrable_const learned)
    (hcost.add (integrable_const error)) hpoint
  simpa [learned, error, competitor, m, hscales, pilot, G,
    generalExpectation, integral_add hcost (integrable_const error)] using havg

end RandomizedOptional

namespace RandomizedOptional
namespace Unbounded

open Randomized

/-- The one-long-job selection argument for an arbitrary private probability
space. -/
theorem exists_oblivious_long_label_general
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool)
    (H zeroCost : ℝ) (longCost : Fin n → ℝ)
    (hH : 0 ≤ H)
    (htestedInt : Integrable (fun seed => testedArea (tested seed)) μ)
    (hblindInt : Integrable (fun seed => blindArea (tested seed)) μ)
    (hchargeInt : ∀ label, Integrable (fun seed =>
      exceptionalCharge (order seed) (tested seed) H label) μ)
    (hzero : generalExpectation μ (fun seed => testedArea (tested seed)) ≤
      zeroCost)
    (hlong : ∀ label,
      generalExpectation μ (fun seed =>
        exceptionalCharge (order seed) (tested seed) H label) ≤
          longCost label) :
    ∃ label, H / n * ((n : ℝ) * (n + 1) / 2 - zeroCost) ≤
      longCost label := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let target := H / n * ((n : ℝ) * (n + 1) / 2 - zeroCost)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hblind :
      (n : ℝ) * (n + 1) / 2 - zeroCost ≤
        generalExpectation μ (fun seed => blindArea (tested seed)) := by
    have hpartition :
        generalExpectation μ (fun seed => testedArea (tested seed)) +
          generalExpectation μ (fun seed => blindArea (tested seed)) =
            (n : ℝ) * (n + 1) / 2 := by
      rw [← generalExpectation_add μ htestedInt hblindInt]
      calc
        generalExpectation μ (fun seed =>
            testedArea (tested seed) + blindArea (tested seed)) =
            generalExpectation μ
              (fun _seed : Ω => ∑ rank, rankWeight n rank) := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun seed =>
                  testedArea_add_blindArea (tested seed)
        _ = ∑ rank, rankWeight n rank := generalExpectation_const μ _
        _ = (n : ℝ) * (n + 1) / 2 := sum_rankWeight n
    linarith
  have hcharges :
      H * generalExpectation μ (fun seed => blindArea (tested seed)) ≤
        ∑ label, longCost label := by
    have hsum :
        (∑ label, generalExpectation μ (fun seed =>
          exceptionalCharge (order seed) (tested seed) H label)) =
        H * generalExpectation μ (fun seed => blindArea (tested seed)) := by
      calc
        (∑ label, generalExpectation μ (fun seed =>
            exceptionalCharge (order seed) (tested seed) H label)) =
            generalExpectation μ (fun seed => ∑ label,
              exceptionalCharge (order seed) (tested seed) H label) := by
                unfold generalExpectation
                rw [integral_finsetSum Finset.univ]
                exact fun label _ => hchargeInt label
        _ = generalExpectation μ (fun seed =>
            H * blindArea (tested seed)) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun seed =>
                exceptionalCharge_sum_labels (order seed) (tested seed) H
        _ = H * generalExpectation μ
            (fun seed => blindArea (tested seed)) := by
              exact integral_const_mul H _
    rw [← hsum]
    exact Finset.sum_le_sum fun label _ => hlong label
  have hsumLower : (n : ℝ) * target ≤ ∑ label, longCost label := by
    have htarget : (n : ℝ) * target =
        H * ((n : ℝ) * (n + 1) / 2 - zeroCost) := by
      dsimp [target]
      field_simp
    rw [htarget]
    exact (mul_le_mul_of_nonneg_left hblind hH).trans hcharges
  by_contra hexists
  push Not at hexists
  have hsumUpper : (∑ label, longCost label) < (n : ℝ) * target := by
    calc
      (∑ label, longCost label) < ∑ _label : Fin n, target :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun label _ => hexists label)
      _ = (n : ℝ) * target := by simp
  linarith

/-- General-private-randomness form of the finite-scale unbounded blind
execution contradiction. -/
theorem no_finite_ratio_at_quadratic_scale_general
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (order : Ω → Equiv.Perm (Fin n))
    (tested : Ω → Fin n → Bool)
    (R η zeroCost : ℝ) (longCost : Fin n → ℝ)
    (_hR : 0 ≤ R) (hη : η ≤ 1 / 8)
    (hnlarge : 8 * R + 1 < 3 * n)
    (htestedInt : Integrable (fun seed => testedArea (tested seed)) μ)
    (hblindInt : Integrable (fun seed => blindArea (tested seed)) μ)
    (hchargeInt : ∀ label, Integrable (fun seed =>
      exceptionalCharge (order seed) (tested seed) ((n : ℝ) ^ 2) label) μ)
    (hzeroArea : generalExpectation μ
      (fun seed => testedArea (tested seed)) ≤ zeroCost)
    (hzeroCost : zeroCost ≤ η * n ^ 2)
    (hlong : ∀ label,
      generalExpectation μ (fun seed => exceptionalCharge (order seed)
        (tested seed) ((n : ℝ) ^ 2) label) ≤ longCost label)
    (hcompetitive : ∀ label,
      longCost label ≤ R * (n : ℝ) ^ 2 + η * n ^ 2) : False := by
  obtain ⟨label, hlower⟩ := exists_oblivious_long_label_general hn μ
    order tested ((n : ℝ) ^ 2) zeroCost longCost (sq_nonneg _)
    htestedInt hblindInt hchargeInt hzeroArea hlong
  have hlower' : (n : ℝ) ^ 2 * ((n + 1 : ℝ) / 2 - η * n) ≤
      longCost label := by
    calc
      (n : ℝ) ^ 2 * ((n + 1 : ℝ) / 2 - η * n) =
          (n : ℝ) ^ 2 / n *
            ((n : ℝ) * (n + 1) / 2 - η * n ^ 2) := by
              have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
              field_simp [hnR]
      _ ≤ (n : ℝ) ^ 2 / n *
            ((n : ℝ) * (n + 1) / 2 - zeroCost) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              linarith
      _ ≤ longCost label := hlower
  have hupper := hcompetitive label
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlargeReal : 8 * R + 1 < 3 * (n : ℝ) := by exact hnlarge
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnreal
  have hdivided : (n + 1 : ℝ) / 2 - η * n ≤ R + η := by
    apply le_of_mul_le_mul_left (a := (n : ℝ) ^ 2) _ hn2
    calc
      (n : ℝ) ^ 2 * ((n + 1 : ℝ) / 2 - η * n) ≤ longCost label := hlower'
      _ ≤ R * (n : ℝ) ^ 2 + η * n ^ 2 := hupper
      _ = (n : ℝ) ^ 2 * (R + η) := by ring
  have hηscaled : η * (n : ℝ) ≤ (n : ℝ) / 8 := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hη (le_of_lt hnreal)
  linarith

end Unbounded

namespace UnboundedOperational

open Randomized
open Unbounded
open ObservedOnline
open ObservedTrace

/-- Fully operational unbounded blind-execution impossibility theorem for an
arbitrary private probability space.  Besides run-cost integrability it asks
for integrability of the finite trace charge; this is exactly the
measurability condition on the algorithm's first-touch decisions. -/
theorem no_finite_ratio_at_quadratic_scale_operational_general
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Strategy n)
    (hcomplete : ∀ seed, CompletesAllNonnegative (strategy seed))
    (R η : ℝ) (hR : 0 ≤ R) (hη : η ≤ 1 / 8)
    (hnlarge : 8 * R + 1 < 3 * n)
    (hzeroInt : Integrable (fun seed =>
      settledCost (zeroProcessing n) (strategy seed)) μ)
    (hlongInt : ∀ label, Integrable (fun seed =>
      settledCost (oneLongProcessing ((n : ℝ) ^ 2) label)
        (strategy seed)) μ)
    (hchargeInt : ∀ label, Integrable (fun seed =>
      let zeroPolicy := asCompletePolicy (zeroProcessing n)
        (by simp [zeroProcessing]) (strategy seed) (hcomplete seed)
      let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
      let zeroTrace := touchTrace (zeroProcessing n) zeroPolicy placement
      exceptionalCharge zeroTrace.label (traceTested zeroTrace)
        ((n : ℝ) ^ 2) label) μ)
    (hzeroCost : generalExpectation μ (fun seed =>
      settledCost (zeroProcessing n) (strategy seed)) ≤ η * (n : ℝ) ^ 2)
    (hcompetitive : ∀ label,
      generalExpectation μ (fun seed =>
        settledCost (oneLongProcessing ((n : ℝ) ^ 2) label)
          (strategy seed)) ≤
        R * (n : ℝ) ^ 2 + η * (n : ℝ) ^ 2) : False := by
  let zeroPolicy (seed : Ω) := asCompletePolicy (zeroProcessing n)
    (by simp [zeroProcessing]) (strategy seed) (hcomplete seed)
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let zeroTrace (seed : Ω) :=
    touchTrace (zeroProcessing n) (zeroPolicy seed) placement
  let order (seed : Ω) : Equiv.Perm (Fin n) := (zeroTrace seed).label
  let tested (seed : Ω) : Fin n → Bool := traceTested (zeroTrace seed)
  let zeroCost := generalExpectation μ (fun seed =>
    settledCost (zeroProcessing n) (strategy seed))
  let longCost (label : Fin n) := generalExpectation μ (fun seed =>
    settledCost (oneLongProcessing ((n : ℝ) ^ 2) label) (strategy seed))
  have htestedEq : (fun seed => testedArea (tested seed)) =
      (fun seed => settledCost (zeroProcessing n) (strategy seed)) := by
    funext seed
    simpa [tested, order, zeroTrace, zeroPolicy, placement] using
      zero_testedArea_eq_settledCost (strategy seed) (hcomplete seed)
  have htestedInt : Integrable (fun seed => testedArea (tested seed)) μ := by
    rw [htestedEq]
    exact hzeroInt
  have hblindEq : (fun seed => Unbounded.blindArea (tested seed)) =
      (fun seed => (n : ℝ) * (n + 1) / 2 - testedArea (tested seed)) := by
    funext seed
    have hsum := testedArea_add_blindArea (tested seed)
    rw [sum_rankWeight] at hsum
    linarith
  have hblindInt : Integrable
      (fun seed => Unbounded.blindArea (tested seed)) μ := by
    rw [hblindEq]
    exact (integrable_const _).sub htestedInt
  apply no_finite_ratio_at_quadratic_scale_general hn μ order tested
    R η zeroCost longCost hR hη hnlarge htestedInt hblindInt
  · intro label
    simpa [order, tested, zeroTrace, zeroPolicy, placement] using hchargeInt label
  · rw [htestedEq]
  · exact hzeroCost
  · intro label
    have hpoint : ∀ seed,
        exceptionalCharge (order seed) (tested seed) ((n : ℝ) ^ 2) label ≤
          settledCost (oneLongProcessing ((n : ℝ) ^ 2) label)
            (strategy seed) := by
      intro seed
      simpa [order, tested, zeroTrace, zeroPolicy, placement] using
        exceptionalCharge_le_oneLong_settledCost
          (strategy seed) (hcomplete seed) (sq_nonneg (n : ℝ)) label
    exact generalExpectation_mono μ
      (by simpa [order, tested, zeroTrace, zeroPolicy, placement] using
        hchargeInt label)
      (hlongInt label) hpoint
  · exact hcompetitive

end UnboundedOperational
end RandomizedOptional

namespace RevealingOptimization
namespace InstanceOptimal

open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower
open ObservedAreaLower

/-- Bounded revealing-optimization comparison against arbitrary private
randomness. -/
theorem privateShuffle_compiled_le_generalCompetitor_concrete_rate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {n : ℕ}
    (hroot : 2 ≤ RandomizedOptional.sixteenthRoot n)
    {u : ℝ} (hu : 0 < u)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpu : ∀ job, p job ≤ u)
    (policy : Ω → CompletePolicy p)
    (hcost : Integrable (fun seed =>
      uniformAverage (normalizedRawCost u p (policy seed))) μ) :
    let m := RandomizedOptional.concreteUnknownParameter n
    let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
    let pilot := RandomizedOptional.inverseSquarePilotPositions n m
      (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hu p hp0 hpu
    compiledExpectedNormalizedCost G pilot u ≤
      generalExpectation μ (fun seed =>
        uniformAverage (normalizedRawCost u p (policy seed))) +
        concreteRevealingComparisonError u n := by
  dsimp only
  let m := RandomizedOptional.concreteUnknownParameter n
  let scales := RandomizedOptional.concreteUnknownParameter_bounds n hroot
  let pilot := RandomizedOptional.inverseSquarePilotPositions n m
    (RandomizedOptional.parameter_scales scales.1 scales.2).2.1
  let G := boundedUniformRoundedGrid
    (show 0 < m by omega) hu p hp0 hpu
  let learned := compiledExpectedNormalizedCost G pilot u
  let error := concreteRevealingComparisonError u n
  let competitor : Ω → ℝ := fun seed =>
    uniformAverage (normalizedRawCost u p (policy seed))
  have hpoint : ∀ seed, learned ≤ competitor seed + error := by
    intro seed
    have hfinite := privateShuffle_compiled_le_randomizedCompetitor_concrete_rate
      (Seeds := Unit) hroot hu p hp0 hpu (fun _ => policy seed)
    simpa [learned, error, competitor, m, scales, pilot, G] using hfinite
  have havg := generalExpectation_mono μ (integrable_const learned)
    (hcost.add (integrable_const error)) hpoint
  simpa [learned, error, competitor, m, scales, pilot, G,
    generalExpectation, integral_add hcost (integrable_const error)] using havg

end InstanceOptimal
end RevealingOptimization

namespace ObligatoryUnboundedOperational

open Randomized
open ObligatoryUnbounded

/-- The all-long/one-zero operational dichotomy for an arbitrary private
probability space.  Thus the unbounded obligatory-testing
instance-optimality impossibility does not rely on a finite seed model. -/
theorem exists_operational_quadratic_gap_general
    {n : ℕ} (hn : 7 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (strategy : Ω → Online.Strategy n) (fuel : ℕ)
    (hdoneHigh : ∀ seed job,
      (Online.run .infinite
        (Online.fixedOracle (allHighProcessing ((n : ℝ) ^ 2)))
        (strategy seed) fuel).config.jobs job = .done)
    (hdoneZero : ∀ seed label job,
      (Online.run .infinite
        (Online.fixedOracle
          (oneZeroProcessing ((n : ℝ) ^ 2) label))
        (strategy seed) fuel).config.jobs job = .done)
    (hhighCost : Integrable (fun seed ↦
      operationalCost (allHighProcessing ((n : ℝ) ^ 2))
        (strategy seed) fuel) μ)
    (hzeroCost : ∀ label, Integrable (fun seed ↦
      operationalCost (oneZeroProcessing ((n : ℝ) ^ 2) label)
        (strategy seed) fuel) μ)
    (hcompleted : Integrable (fun seed ↦
      ∑ rank, (runCompletedBefore
        (allHighProcessing ((n : ℝ) ^ 2)) (strategy seed) fuel
          (hdoneHigh seed) rank : ℝ)) μ)
    (hcharge : ∀ label, Integrable (fun seed ↦
      exceptionalZeroCharge
        (runTestOrder (allHighProcessing ((n : ℝ) ^ 2))
          (strategy seed) fuel (hdoneHigh seed))
        (runCompletedBefore (allHighProcessing ((n : ℝ) ^ 2))
          (strategy seed) fuel (hdoneHigh seed))
        ((n : ℝ) ^ 2) label) μ) :
    (n : ℝ) ^ 2 / 8 ≤
        generalExpectation μ (fun seed ↦
          operationalCost (allHighProcessing ((n : ℝ) ^ 2))
            (strategy seed) fuel) -
          allHighImmediateComparisonCost n ((n : ℝ) ^ 2) ∨
      ∃ label,
        (n : ℝ) ^ 2 / 8 <
          generalExpectation μ (fun seed ↦
            operationalCost (oneZeroProcessing ((n : ℝ) ^ 2) label)
              (strategy seed) fuel) -
            oneZeroRandomOrderComparisonUpper n ((n : ℝ) ^ 2) := by
  let H : ℝ := (n : ℝ) ^ 2
  let order : Ω → Equiv.Perm (Fin n) := fun seed ↦
    runTestOrder (allHighProcessing H) (strategy seed) fuel
      (by simpa [H] using hdoneHigh seed)
  let completedBefore : Ω → Fin n → ℕ := fun seed ↦
    runCompletedBefore (allHighProcessing H) (strategy seed) fuel
      (by simpa [H] using hdoneHigh seed)
  let highGap : Ω → ℝ := fun seed ↦
    operationalCost (allHighProcessing H) (strategy seed) fuel -
      allHighImmediateComparisonCost n H
  let zeroGap : Fin n → Ω → ℝ := fun label seed ↦
    operationalCost (oneZeroProcessing H label) (strategy seed) fuel -
      oneZeroRandomOrderComparisonUpper n H
  have hH : 0 < H := by dsimp [H]; positivity
  have hcompleted' : Integrable (fun seed ↦
      ∑ rank, (completedBefore seed rank : ℝ)) μ := by
    simpa [completedBefore, H] using hcompleted
  have hhighGapInt : Integrable highGap μ := by
    exact (by simpa [highGap, H] using
      hhighCost.sub (integrable_const
        (allHighImmediateComparisonCost n ((n : ℝ) ^ 2))))
  have hzeroGapInt : ∀ label, Integrable (zeroGap label) μ := by
    intro label
    exact (by simpa [zeroGap, H] using
      (hzeroCost label).sub (integrable_const
        (oneZeroRandomOrderComparisonUpper n ((n : ℝ) ^ 2))))
  have hcharge' : ∀ label, Integrable (fun seed ↦
      exceptionalZeroCharge (order seed) (completedBefore seed) H label) μ := by
    intro label
    simpa [order, completedBefore, H] using hcharge label
  have hhighPoint : ∀ seed, highGap seed =
      ∑ rank, rankGap (completedBefore seed) rank := by
    intro seed
    simpa [highGap, operationalCost, allHighImmediateComparisonCost,
      completedBefore]
      using allHigh_operational_gap_eq_rankGaps hH (strategy seed) fuel
        (by simpa [H] using hdoneHigh seed)
  have hhighIdentity :
      generalExpectation μ highGap +
          generalExpectation μ (fun seed ↦
            ∑ rank, (completedBefore seed rank : ℝ)) =
        (n : ℝ) * (n - 1) / 2 := by
    rw [← generalExpectation_add μ hhighGapInt hcompleted']
    calc
      generalExpectation μ (fun seed ↦
          highGap seed + ∑ rank, (completedBefore seed rank : ℝ)) =
          generalExpectation μ
            (fun _seed : Ω ↦ ∑ rank : Fin n, rankValue rank) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun seed ↦ by
          change highGap seed + ∑ rank, (completedBefore seed rank : ℝ) = _
          rw [hhighPoint seed, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro rank _
          simp [rankGap]
      _ = ∑ rank : Fin n, rankValue rank := generalExpectation_const μ _
      _ = (n : ℝ) * (n - 1) / 2 := sum_rankValues n
  by_cases hhigh : (n : ℝ) ^ 2 / 8 ≤ generalExpectation μ highGap
  · left
    have hhighEq : generalExpectation μ highGap =
        generalExpectation μ (fun seed ↦
          operationalCost (allHighProcessing ((n : ℝ) ^ 2))
            (strategy seed) fuel) -
          allHighImmediateComparisonCost n ((n : ℝ) ^ 2) := by
      unfold highGap
      rw [generalExpectation_sub μ hhighCost
        (integrable_const (allHighImmediateComparisonCost n H)),
        generalExpectation_const]
    rw [← hhighEq]
    exact hhigh
  · right
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    have hmany :
        (n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8 <
          generalExpectation μ (fun seed ↦
            ∑ rank, (completedBefore seed rank : ℝ)) := by
      linarith
    have hchargeSum :
        (n : ℝ) ^ 2 *
            ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) <
          ∑ label, generalExpectation μ (fun seed ↦
            exceptionalZeroCharge (order seed) (completedBefore seed)
              H label) := by
      calc
        (n : ℝ) ^ 2 *
            ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) <
            H * generalExpectation μ (fun seed ↦
              ∑ rank, (completedBefore seed rank : ℝ)) := by
          simpa [H] using mul_lt_mul_of_pos_left hmany hH
        _ = ∑ label, generalExpectation μ (fun seed ↦
              exceptionalZeroCharge (order seed) (completedBefore seed)
                H label) := by
          calc
            H * generalExpectation μ (fun seed ↦
                ∑ rank, (completedBefore seed rank : ℝ)) =
                generalExpectation μ (fun seed ↦ H *
                  ∑ rank, (completedBefore seed rank : ℝ)) := by
                    exact (integral_const_mul H _).symm
            _ = generalExpectation μ (fun seed ↦ ∑ label,
                  exceptionalZeroCharge (order seed) (completedBefore seed)
                    H label) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun seed ↦
                (exceptionalZeroCharge_sum_labels
                  (order seed) (completedBefore seed) H).symm
            _ = ∑ label, generalExpectation μ (fun seed ↦
                  exceptionalZeroCharge (order seed) (completedBefore seed)
                    H label) := by
              unfold generalExpectation
              rw [integral_finsetSum Finset.univ]
              exact fun label _ ↦ hcharge' label
    have honePoint : ∀ label seed,
        exceptionalZeroCharge (order seed) (completedBefore seed) H label -
            2 * n ^ 2 ≤ zeroGap label seed := by
      intro label seed
      have hsame := allHigh_oneZero_same_rank_completed
        (strategy seed) fuel label
        (by simpa [H] using hdoneHigh seed)
        (by simpa [H] using hdoneZero seed label)
      have hcost := oneZero_operational_cost_ge
        hH.le hH.ne' (strategy seed) fuel label (by omega)
        (by simpa [H] using hdoneZero seed label)
      dsimp at hsame hcost
      dsimp [exceptionalZeroCharge, order, completedBefore, zeroGap,
        operationalCost, oneZeroRandomOrderComparisonUpper]
      rw [hsame.2]
      dsimp [H, Online.runCompletionCost] at hcost ⊢
      nlinarith
    have hone : ∀ label,
        generalExpectation μ (fun seed ↦
            exceptionalZeroCharge (order seed) (completedBefore seed) H label) -
            2 * n ^ 2 ≤ generalExpectation μ (zeroGap label) := by
      intro label
      calc
        generalExpectation μ (fun seed ↦
              exceptionalZeroCharge (order seed) (completedBefore seed)
                H label) - 2 * n ^ 2 =
            generalExpectation μ (fun seed ↦
              exceptionalZeroCharge (order seed) (completedBefore seed)
                H label - 2 * n ^ 2) := by
          rw [generalExpectation_sub μ (hcharge' label)
            (integrable_const (2 * (n : ℝ) ^ 2)),
            generalExpectation_const]
        _ ≤ generalExpectation μ (zeroGap label) :=
          generalExpectation_mono μ
            ((hcharge' label).sub (integrable_const (2 * (n : ℝ) ^ 2)))
            (hzeroGapInt label) (honePoint label)
    have hsumGap :
        (n : ℝ) ^ 2 *
              ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) -
            (n : ℝ) * (2 * n ^ 2) <
          ∑ label, generalExpectation μ (zeroGap label) := by
      have hsumLe :
          (∑ label, (generalExpectation μ (fun seed ↦
                exceptionalZeroCharge (order seed) (completedBefore seed)
                  H label) - 2 * n ^ 2)) ≤
            ∑ label, generalExpectation μ (zeroGap label) :=
        Finset.sum_le_sum fun label _ ↦ hone label
      have hrewrite :
          (∑ label : Fin n, (generalExpectation μ (fun seed ↦
                exceptionalZeroCharge (order seed) (completedBefore seed)
                  H label) - 2 * n ^ 2)) =
            (∑ label, generalExpectation μ (fun seed ↦
              exceptionalZeroCharge (order seed) (completedBefore seed)
                H label)) - (n : ℝ) * (2 * n ^ 2) := by
        rw [Finset.sum_sub_distrib]
        simp
      rw [hrewrite] at hsumLe
      linarith
    have htarget : (n : ℝ) * ((n : ℝ) ^ 2 / 8) ≤
        (n : ℝ) ^ 2 *
              ((n : ℝ) * (n - 1) / 2 - (n : ℝ) ^ 2 / 8) -
            (n : ℝ) * (2 * n ^ 2) := by
      have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 7), sq_nonneg (n : ℝ)]
    by_contra hexists
    push Not at hexists
    have hsumUpper : (∑ label, generalExpectation μ (zeroGap label)) ≤
        (n : ℝ) * ((n : ℝ) ^ 2 / 8) := by
      have hexists' : ∀ label,
          generalExpectation μ (zeroGap label) ≤ (n : ℝ) ^ 2 / 8 := by
        intro label
        have hzeroEq : generalExpectation μ (zeroGap label) =
            generalExpectation μ (fun seed ↦
              operationalCost (oneZeroProcessing ((n : ℝ) ^ 2) label)
                (strategy seed) fuel) -
              oneZeroRandomOrderComparisonUpper n ((n : ℝ) ^ 2) := by
          unfold zeroGap
          rw [generalExpectation_sub μ (hzeroCost label)
            (integrable_const
              (oneZeroRandomOrderComparisonUpper n ((n : ℝ) ^ 2))),
            generalExpectation_const]
        rw [hzeroEq]
        exact hexists label
      calc
        (∑ label, generalExpectation μ (zeroGap label)) ≤
            ∑ _label : Fin n, ((n : ℝ) ^ 2 / 8) :=
          Finset.sum_le_sum fun label _ ↦ hexists' label
        _ = (n : ℝ) * ((n : ℝ) ^ 2 / 8) := by simp
    linarith

end ObligatoryUnboundedOperational

end

end SchedulingPaper
