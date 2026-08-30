import SchedulingPaper.ObligatoryPaperAlgorithm
import SchedulingPaper.RevealingOptimizationInstanceOptimal
import SchedulingPaper.RandomizedFourThirds
import SchedulingPaper.RandomizedRelabelRun
import Mathlib.Tactic

/-!
# Finite private-shuffle corollaries

This file closes the finite-seed symmetrization step used by the paper-level
randomized statements.  A completing observed policy can be relabelled by an
independent uniform permutation.  Its cost on a fixed hidden placement is
then its original cost on the composed placement, whose uniform average is
independent of the fixed placement.
-/

namespace SchedulingPaper

open Randomized

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A uniform average over a product seed is the iterated uniform average. -/
theorem uniformAverage_prod
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A → B → ℝ) :
    uniformAverage (fun z : A × B ↦ f z.1 z.2) =
      uniformAverage (fun a ↦ uniformAverage (f a)) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformAverage
  simp only [Fintype.sum_prod_type, Fintype.card_prod]
  rw [Finset.sum_div]
  push_cast
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  field_simp

namespace RandomizedOptional
namespace ObservedTrace

open ObservedOnline

/-- Relabel a completing observed policy by a public-label permutation. -/
def CompletePolicy.relabel {n : ℕ} {p : Fin n → ℝ}
    (policy : CompletePolicy p) (order : Placement n) : CompletePolicy p where
  strategy := policy.strategy.relabel order
  completes := by
    intro σ job
    have h := policy.completes (order.trans σ) (order.symm job)
    change
      (ObservedOnline.run (placedProcessing p σ)
        (policy.strategy.relabel order) (2 * n + 1)).config.jobs job = .done
    rw [ObservedOnline.run_relabel_config]
    simpa [ObservedOnline.Config.relabel, placedProcessing, settledRun] using h

theorem touchChoices_map_relabel {n : ℕ}
    (order : Placement n) (transcript : ObservedOnline.Transcript n) :
    touchChoices
        (transcript.map (ObservedOnline.Observation.relabel order)) =
      (touchChoices transcript).map fun choice ↦ (order choice.1, choice.2) := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [touchChoices, observationTouchChoice?,
          ObservedOnline.Observation.relabel, ih]

/-- Relabelling changes only public labels, not whether each first touch is a
test or a blind execution. -/
theorem CompletePolicy.relabel_firstTouchesAreTests
    {n : ℕ} {p : Fin n → ℝ} (policy : CompletePolicy p)
    (htest : ObligatoryInstance.FirstTouchesAreTests policy)
    (order : Placement n) :
    ObligatoryInstance.FirstTouchesAreTests (policy.relabel order) := by
  intro σ k
  let oldσ : Placement n := order.trans σ
  have hold : ∀ choice ∈
      touchChoices (settledRun p policy.strategy oldσ).config.transcript,
      choice.2 = .test := by
    intro choice hchoice
    rw [← touchTrace_choices_ofFn p policy oldσ] at hchoice
    simp only [List.mem_ofFn] at hchoice
    obtain ⟨j, rfl⟩ := hchoice
    exact htest oldσ j
  have hrun :
      (settledRun p (policy.relabel order).strategy σ).config.transcript =
        (settledRun p policy.strategy oldσ).config.transcript.map
          (ObservedOnline.Observation.relabel order) := by
    dsimp [CompletePolicy.relabel, settledRun, oldσ]
    rw [ObservedOnline.run_relabel_config]
    rfl
  have hnew : ∀ choice ∈
      touchChoices
        (settledRun p (policy.relabel order).strategy σ).config.transcript,
      choice.2 = .test := by
    intro choice hchoice
    rw [hrun, touchChoices_map_relabel] at hchoice
    obtain ⟨oldChoice, holdChoice, rfl⟩ := List.mem_map.mp hchoice
    exact hold oldChoice holdChoice
  have hmember :
      ((touchTrace p (policy.relabel order) σ).label k,
        (touchTrace p (policy.relabel order) σ).kind k) ∈
      touchChoices
        (settledRun p (policy.relabel order).strategy σ).config.transcript := by
    rw [← touchTrace_choices_ofFn p (policy.relabel order) σ]
    exact List.mem_ofFn.mpr ⟨k, rfl⟩
  have hk := hnew
    ((touchTrace p (policy.relabel order) σ).label k,
      (touchTrace p (policy.relabel order) σ).kind k) hmember
  exact hk

theorem normalizedCost_relabel
    {n : ℕ} {p : Fin n → ℝ} (policy : CompletePolicy p)
    (order σ : Placement n) :
    RandomizedOptional.AnnouncedExactLower.normalizedCost p
        (policy.relabel order) σ =
      RandomizedOptional.AnnouncedExactLower.normalizedCost p policy
        (order.trans σ) := by
  unfold RandomizedOptional.AnnouncedExactLower.normalizedCost
  dsimp [CompletePolicy.relabel, settledRun]
  rw [ObservedOnline.run_relabel_config]
  change
    ObservedOnline.completionCost (placedProcessing p σ)
        ((ObservedOnline.run
          (fun virtual ↦ placedProcessing p σ (order virtual))
          policy.strategy (2 * n + 1)).config.transcript.map
            (ObservedOnline.Observation.relabel order)) / (n : ℝ) ^ 2 = _
  rw [ObservedOnline.completionCost_map_relabel]
  rfl

/-- Postcomposition by a fixed placement permutes the finite placement
space. -/
def postcomposePlacement {n : ℕ} (σ : Placement n) :
    Placement n ≃ Placement n where
  toFun order := order.trans σ
  invFun τ := τ.trans σ.symm
  left_inv order := by ext job; simp
  right_inv τ := by ext job; simp

theorem uniformAverage_normalizedCost_relabel
    {n : ℕ} {p : Fin n → ℝ} (policy : CompletePolicy p)
    (σ : Placement n) :
    uniformAverage (fun order : Placement n ↦
        RandomizedOptional.AnnouncedExactLower.normalizedCost p
          (policy.relabel order) σ) =
      uniformAverage
        (RandomizedOptional.AnnouncedExactLower.normalizedCost p policy) := by
  rw [show (fun order : Placement n ↦
      RandomizedOptional.AnnouncedExactLower.normalizedCost p
        (policy.relabel order) σ) =
      (RandomizedOptional.AnnouncedExactLower.normalizedCost p policy) ∘
        postcomposePlacement σ by
    funext order
    exact normalizedCost_relabel policy order σ]
  exact uniformAverage_comp_equiv (postcomposePlacement σ)
    (RandomizedOptional.AnnouncedExactLower.normalizedCost p policy)

theorem normalizedRoundedCost_relabel
    {n : ℕ} {p : Fin n → ℝ} (policy : CompletePolicy p)
    (order σ : Placement n) :
    RandomizedOptional.AnnouncedRoundedLower.normalizedCost p
        (policy.relabel order) σ =
      RandomizedOptional.AnnouncedRoundedLower.normalizedCost p policy
        (order.trans σ) := by
  unfold RandomizedOptional.AnnouncedRoundedLower.normalizedCost
  dsimp [CompletePolicy.relabel, settledRun]
  rw [ObservedOnline.run_relabel_config]
  change
    ObservedOnline.completionCost (placedProcessing p σ)
        ((ObservedOnline.run
          (fun virtual ↦ placedProcessing p σ (order virtual))
          policy.strategy (2 * n + 1)).config.transcript.map
            (ObservedOnline.Observation.relabel order)) / (n : ℝ) ^ 2 = _
  rw [ObservedOnline.completionCost_map_relabel]
  rfl

theorem uniformAverage_normalizedRoundedCost_relabel
    {n : ℕ} {p : Fin n → ℝ} (policy : CompletePolicy p)
    (σ : Placement n) :
    uniformAverage (fun order : Placement n ↦
        RandomizedOptional.AnnouncedRoundedLower.normalizedCost p
          (policy.relabel order) σ) =
      uniformAverage
        (RandomizedOptional.AnnouncedRoundedLower.normalizedCost p policy) := by
  rw [show (fun order : Placement n ↦
      RandomizedOptional.AnnouncedRoundedLower.normalizedCost p
        (policy.relabel order) σ) =
      (RandomizedOptional.AnnouncedRoundedLower.normalizedCost p policy) ∘
        postcomposePlacement σ by
    funext order
    exact normalizedRoundedCost_relabel policy order σ]
  exact uniformAverage_comp_equiv (postcomposePlacement σ)
    (RandomizedOptional.AnnouncedRoundedLower.normalizedCost p policy)

end ObservedTrace
end RandomizedOptional

namespace RevealingOptimization

open RandomizedOptional
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open RandomizedOptional.ObservedEnvelope
open RawObserved
open ObservedAreaLower

theorem rawCompletionCost_map_relabel
    {n : ℕ} (u : ℝ) (processing : Fin n → ℝ)
    (order : Placement n) (transcript : Transcript n) :
    rawCompletionCost u processing
        (transcript.map (Observation.relabel order)) =
      rawCompletionCost u (fun virtual ↦ processing (order virtual))
        transcript := by
  unfold rawCompletionCost rawTranscriptCompletionSteps
  apply congrArg completionStepsCost
  rw [List.map_map]
  apply List.map_congr_left
  intro observation _
  cases observation <;>
    simp [rawObservationDuration, observationCompletionCount,
      Observation.relabel, Observation.completionLabel]

theorem normalizedRawCost_relabel
    {n : ℕ} (u : ℝ) {p : Fin n → ℝ} (policy : CompletePolicy p)
    (order σ : Placement n) :
    normalizedRawCost u p (policy.relabel order) σ =
      normalizedRawCost u p policy (order.trans σ) := by
  unfold normalizedRawCost
  dsimp [CompletePolicy.relabel, settledRun]
  rw [ObservedOnline.run_relabel_config]
  change
    rawCompletionCost u (placedProcessing p σ)
        ((ObservedOnline.run
          (fun virtual ↦ placedProcessing p σ (order virtual))
          policy.strategy (2 * n + 1)).config.transcript.map
            (Observation.relabel order)) / (n : ℝ) ^ 2 = _
  rw [rawCompletionCost_map_relabel]
  rfl

theorem uniformAverage_normalizedRawCost_relabel
    {n : ℕ} (u : ℝ) {p : Fin n → ℝ} (policy : CompletePolicy p)
    (σ : Placement n) :
    uniformAverage (fun order : Placement n ↦
        normalizedRawCost u p (policy.relabel order) σ) =
      uniformAverage (normalizedRawCost u p policy) := by
  rw [show (fun order : Placement n ↦
      normalizedRawCost u p (policy.relabel order) σ) =
      (normalizedRawCost u p policy) ∘
        RandomizedOptional.ObservedTrace.postcomposePlacement σ by
    funext order
    exact normalizedRawCost_relabel u policy order σ]
  exact uniformAverage_comp_equiv
    (RandomizedOptional.ObservedTrace.postcomposePlacement σ)
    (normalizedRawCost u p policy)

end RevealingOptimization

namespace ObligatoryPaper

open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower
open ObligatoryInstance

/-- Public finite-seed obligatory instance comparison with the competitor's
private-shuffle average present literally in the conclusion. -/
theorem privateShuffle_paperGrowingPolicy_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hCoarseCover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    uniformAverage
        (physicalGrowingRunCost
          (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
          (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
      (paperPilotSize n + paperRest n : ℝ) ^ 2 *
        (uniformAverage (fun seed ↦
            uniformAverage (normalizedCost p (policy seed))) +
          paperInstanceError L n) := by
  let symPolicy :
      Seeds × Placement (paperPilotSize n + paperRest n) → CompletePolicy p :=
    fun seed ↦ (policy seed.1).relabel seed.2
  have hsymTest : ∀ seed, FirstTouchesAreTests (symPolicy seed) := by
    intro seed
    exact (policy seed.1).relabel_firstTouchesAreTests (htest seed.1) seed.2
  obtain ⟨σ, hσ⟩ := exists_fixedPlacement_paperGrowingPolicy_concrete_rate
    (Seeds := Seeds × Placement (paperPilotSize n + paperRest n))
    hR hroot hL hCoarseCover hFineCover p hp0 hpL symPolicy hsymTest
  have havg :
      uniformAverage (fun seed => normalizedCost p (symPolicy seed) σ) =
        uniformAverage (fun seed ↦
          uniformAverage (normalizedCost p (policy seed))) := by
    change uniformAverage (fun seed :
        Seeds × Placement (paperPilotSize n + paperRest n) =>
          normalizedCost p ((policy seed.1).relabel seed.2) σ) = _
    calc
      _ = uniformAverage (fun seed : Seeds =>
          uniformAverage (fun order :
            Placement (paperPilotSize n + paperRest n) =>
              normalizedCost p ((policy seed).relabel order) σ)) :=
        uniformAverage_prod (fun seed order =>
          normalizedCost p ((policy seed).relabel order) σ)
      _ = _ := by
        apply congrArg uniformAverage
        funext seed
        exact uniformAverage_normalizedRoundedCost_relabel (policy seed) σ
  rw [havg] at hσ
  exact hσ

end ObligatoryPaper

namespace RevealingOptimization
namespace InstanceOptimal

open RandomizedOptional
open RandomizedOptional.ObservedTrace
open RandomizedOptional.AnnouncedRoundedLower
open ObservedAreaLower

/-- Public finite-seed revealing instance comparison with the competitor's
private-shuffle average present literally in the conclusion. -/
theorem privateShuffle_compiled_le_randomizedCompetitor_concrete_rate
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
    compiledExpectedNormalizedCost G pilot u ≤
      (uniformAverage fun seed ↦
        uniformAverage (normalizedRawCost u p (policy seed))) +
        concreteRevealingComparisonError u n := by
  dsimp
  let symPolicy : Seeds × Placement n → CompletePolicy p :=
    fun seed ↦ (policy seed.1).relabel seed.2
  obtain ⟨σ, hσ⟩ :=
    exists_fixedPlacement_compiled_le_randomizedCompetitor_concrete_rate
      (Seeds := Seeds × Placement n) hroot hu p hp0 hpu symPolicy
  have havg :
      uniformAverage (fun seed =>
          normalizedRawCost u p (symPolicy seed) σ) =
        uniformAverage (fun seed ↦
          uniformAverage (normalizedRawCost u p (policy seed))) := by
    change uniformAverage (fun seed : Seeds × Placement n =>
      normalizedRawCost u p ((policy seed.1).relabel seed.2) σ) = _
    calc
      _ = uniformAverage (fun seed : Seeds =>
          uniformAverage (fun order : Placement n =>
            normalizedRawCost u p ((policy seed).relabel order) σ)) :=
        uniformAverage_prod (fun seed order =>
          normalizedRawCost u p ((policy seed).relabel order) σ)
      _ = _ := by
        apply congrArg uniformAverage
        funext seed
        exact uniformAverage_normalizedRawCost_relabel u (policy seed) σ
  rw [havg] at hσ
  exact hσ

end InstanceOptimal
end RevealingOptimization

namespace RandomizedObligatory

/-- The operational binary lower bound with an independent uniform private
label shuffle displayed as a separate finite random seed. -/
theorem oblivious_iid_binary_lower_online_privateShuffle_actualOPT
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ seed input job,
      (Online.run .infinite
        (Online.fixedOracle (iidBinaryProcessingTime input))
        (strategy seed) fuel).config.jobs job = .done) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) *
          finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
        uniformAverage fun seed ↦
          uniformAverage fun order : Equiv.Perm (Fin n) ↦
            Online.runCompletionCost .infinite
              (iidBinaryProcessingTime input)
              (Online.run .infinite
                (Online.fixedOracle (iidBinaryProcessingTime input))
                ((strategy seed).relabel order) fuel) := by
  let shuffledStrategy : Seeds × Equiv.Perm (Fin n) → Online.Strategy n :=
    fun seed ↦ (strategy seed.1).relabel seed.2
  have hshuffledDone : ∀ seed input job,
      (Online.run .infinite
        (Online.fixedOracle (iidBinaryProcessingTime input))
        (shuffledStrategy seed) fuel).config.jobs job = .done := by
    intro seed input job
    let shuffledInput : BinaryInput n := fun i ↦ input (seed.2 i)
    have h := hdone seed.1 shuffledInput (seed.2.symm job)
    dsimp [shuffledStrategy]
    rw [Online.run_relabel_config]
    simpa [Online.Config.relabel, iidBinaryProcessingTime, shuffledInput] using h
  obtain ⟨input, hinput⟩ := oblivious_iid_binary_lower_online_actualOPT
    hn shuffledStrategy fuel hshuffledDone
  refine ⟨input, ?_⟩
  dsimp [shuffledStrategy] at hinput
  change
    (4 * n / (3 * n + 5)) *
        finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
      uniformAverage (fun seed : Seeds × Equiv.Perm (Fin n) =>
        Online.runCompletionCost .infinite
          (iidBinaryProcessingTime input)
          (Online.run .infinite
            (Online.fixedOracle (iidBinaryProcessingTime input))
            ((strategy seed.1).relabel seed.2) fuel)) at hinput
  exact hinput.trans_eq (uniformAverage_prod (fun seed order =>
    Online.runCompletionCost .infinite
      (iidBinaryProcessingTime input)
      (Online.run .infinite
        (Online.fixedOracle (iidBinaryProcessingTime input))
        ((strategy seed).relabel order) fuel)))

end RandomizedObligatory

end
end SchedulingPaper
