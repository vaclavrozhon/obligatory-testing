import SchedulingPaper.ObligatoryGrowingCutoffConditionalOrder
import SchedulingPaper.ObligatoryMaximumDensityTemplate
import SchedulingPaper.RandomizedOperationalAnalytic

/-!
# Analytic comparator for the growing-cutoff obligatory policy

The conditional sample-first scalar cost is bounded by the stationary
population comparator of the learned maximum-density threshold, with the
cutoff-parametric cross-block overhead.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

theorem growing_baseClassifiedJobs_split_eq
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) :
    baseClassifiedJobs
        (splitSampleProcessing k r p)
        (growingSplitSampleEarly k r d B η hη p) ++
      baseClassifiedJobs
        (splitRestProcessing k r p)
        (growingSplitRestEarly k r d B η hη p) =
      baseClassifiedJobs p (growingLearnedEarlyFor k r d B η hη p) := by
  unfold baseClassifiedJobs
  rw [← List.ofFn_fin_append]
  apply congrArg List.ofFn
  funext job
  obtain ⟨location, rfl⟩ := finSumFinEquiv.surjective job
  cases location with
  | inl i =>
      change Fin.append _ _ (Fin.castAdd r i) = _
      rw [Fin.append_left]
      rfl
  | inr i =>
      change Fin.append _ _ (Fin.natAdd k i) = _
      rw [Fin.append_right]
      rfl

theorem growing_uniformStationaryScalarCost_learnedSplit_eq
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) :
    uniformStationaryScalarCost
        (earlyMassCount (growingSplitSampleEarly k r d B η hη p))
        (earlyMassCount (growingSplitRestEarly k r d B η hη p))
        (∑ i, discoveryBlock
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) i)
        (∑ i, discoveryBlock
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p) i)
        (earlySelfWork
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p))
        (earlySelfWork
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p))
        (classifiedLateCost
          (baseClassifiedJobs
              (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) ++
            baseClassifiedJobs
              (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p))) =
      stationaryScalarCost (k + r)
        (earlyMassCount (growingLearnedEarlyFor k r d B η hη p))
        ((∑ i, discoveryBlock p (growingLearnedEarlyFor k r d B η hη p) i) -
          (k + r))
        (classifiedLateWork
          (baseClassifiedJobs p (growingLearnedEarlyFor k r d B η hη p)))
        (classifiedLatePairMin
          (baseClassifiedJobs p (growingLearnedEarlyFor k r d B η hη p))) := by
  rw [uniformStationaryScalarCost_split_eq]
  have hjobs := growing_baseClassifiedJobs_split_eq k r d B η hη p
  have hearly :
      earlyMassCount (growingSplitSampleEarly k r d B η hη p) +
          earlyMassCount (growingSplitRestEarly k r d B η hη p) =
        earlyMassCount (growingLearnedEarlyFor k r d B η hη p) := by
    rw [← classifiedEarlyCount_ofFn_eq_massCount
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p),
      ← classifiedEarlyCount_ofFn_eq_massCount
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p),
      ← classifiedEarlyCount_append, hjobs,
      classifiedEarlyCount_ofFn_eq_massCount]
  have hwork :
      (∑ i, discoveryBlock
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) i) +
          (∑ i, discoveryBlock
            (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p) i) =
        ∑ i, discoveryBlock p (growingLearnedEarlyFor k r d B η hη p) i := by
    rw [← classifiedDiscoveryWork_ofFn
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p),
      ← classifiedDiscoveryWork_ofFn
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p),
      ← classifiedDiscoveryWork_append, hjobs,
      classifiedDiscoveryWork_ofFn]
  rw [hearly, hwork, hjobs]

theorem growingLearnedSample_discoveryWork_le
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (hB : 0 ≤ B) (hBgrid : B ≤ (d : ℝ) * η)
    (p : Online.Label (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, discoveryBlock
      (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) i) ≤
      (B + 1) * k := by
  calc
    (∑ i, discoveryBlock
        (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) i) ≤
        ∑ _i : Fin k, (B + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold discoveryBlock
      cases hearly : growingSplitSampleEarly k r d B η hη p i
      · simp
        linarith
      · have hle : splitSampleProcessing k r p i ≤ B := by
          apply Online.growingLearnedClassifiesEarly_processing_le
            B d η hη _ _ (hp (Fin.castAdd r i)) hBgrid
          simpa [growingSplitSampleEarly, splitSampleProcessing, growingLearnedEarlyFor]
            using hearly
        simp [hearly]
        linarith
    _ = (B + 1) * k := by simp; ring

/-- The exact conditional sample-first scalar is at most the normalized
stationary comparator plus the cross-block implementation overhead. -/
theorem growingLearnedSampleFirstScalarCost_le_stationary_add
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (hB : 0 ≤ B) (hBgrid : B ≤ (d : ℝ) * η)
    (p : Online.Label (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    growingLearnedSampleFirstScalarCost k r d B η hη p ≤
      stationaryScalarCost (k + r)
        (earlyMassCount (growingLearnedEarlyFor k r d B η hη p))
        ((∑ i, discoveryBlock p (growingLearnedEarlyFor k r d B η hη p) i) -
          (k + r))
        (classifiedLateWork
          (baseClassifiedJobs p (growingLearnedEarlyFor k r d B η hη p)))
        (classifiedLatePairMin
          (baseClassifiedJobs p (growingLearnedEarlyFor k r d B η hη p))) +
        (B + 1) * (k + r : ℝ) * k / 2 := by
  let eSample := earlyMassCount (growingSplitSampleEarly k r d B η hη p)
  let eRest := earlyMassCount (growingSplitRestEarly k r d B η hη p)
  let workSample := ∑ i, discoveryBlock
    (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) i
  let workRest := ∑ i, discoveryBlock
    (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p) i
  have hsampleUniform := sampleFirstScalarCost_le_uniform_add
    (eSample := eSample) (eRest := eRest)
    (workSample := workSample) (workRest := workRest)
    (selfSample := earlySelfWork
      (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p))
    (selfRest := earlySelfWork
      (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p))
    (lateCost := classifiedLateCost
      (baseClassifiedJobs
          (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p) ++
        baseClassifiedJobs
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p)))
    (earlyMassCount_nonneg _) (discoveryWork_nonneg _ _
      (fun i => hp (Fin.natAdd k i)))
  have heRest0 : 0 ≤ eRest := earlyMassCount_nonneg _
  have heRest : eRest ≤ (k + r : ℝ) :=
    (earlyMassCount_le_card (growingSplitRestEarly k r d B η hη p) |>.trans
      (by exact_mod_cast Nat.le_add_left r k))
  have hwork0 : 0 ≤ workSample :=
    discoveryWork_nonneg _ _ (fun i => hp (Fin.castAdd r i))
  have hwork : workSample ≤ (B + 1) * k :=
    growingLearnedSample_discoveryWork_le
      k r d B η hη hB hBgrid p hp
  have hcross : eRest * workSample / 2 ≤
      (B + 1) * (k + r : ℝ) * k / 2 := by
    have hprod := mul_le_mul heRest hwork hwork0 (by positivity)
    nlinarith
  dsimp [growingLearnedSampleFirstScalarCost, eSample, eRest,
    workSample, workRest] at hsampleUniform hcross ⊢
  rw [growing_uniformStationaryScalarCost_learnedSplit_eq] at hsampleUniform
  linarith

end

end RandomizedObligatory
end SchedulingPaper
