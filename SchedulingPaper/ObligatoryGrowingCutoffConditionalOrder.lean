import SchedulingPaper.RandomizedConditionalOrder
import SchedulingPaper.ObligatoryGrowingCutoffOperationalUpper

/-!
# Conditional averaging for the growing-cutoff obligatory policy

The growing learner depends only on the unordered pilot histogram.  This
module transports the operational upper bound through independent pilot/rest
orders and through the public random relabelling.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

theorem growingLearnedThresholdFromResults_eq_of_perm
    {n d : ℕ} {B η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : results.Perm results') :
    Online.growingLearnedThresholdFromResults? B d η hη results =
      Online.growingLearnedThresholdFromResults? B d η hη results' := by
  have hmu := resultCategoryFraction_eq_of_perm (d := d) hη hperm
  unfold Online.growingLearnedThresholdFromResults?
  unfold Online.growingResultMaximumDensitySet
  rw [hmu]

theorem growingLearnedThresholdFromResults_eq_of_value_perm
    {n d : ℕ} {B η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : (results.map Prod.snd).Perm (results'.map Prod.snd)) :
    Online.growingLearnedThresholdFromResults? B d η hη results =
      Online.growingLearnedThresholdFromResults? B d η hη results' := by
  have hmu := resultCategoryFraction_eq_of_value_perm (d := d) hη hperm
  unfold Online.growingLearnedThresholdFromResults?
  unfold Online.growingResultMaximumDensitySet
  rw [hmu]

theorem growingLearnedClassifiesEarly_eq_of_perm
    {n d : ℕ} {B η p : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : results.Perm results') :
    Online.growingLearnedClassifiesEarly B d η hη results p =
      Online.growingLearnedClassifiesEarly B d η hη results' p := by
  unfold Online.growingLearnedClassifiesEarly
  rw [growingLearnedThresholdFromResults_eq_of_perm hη hperm]

theorem growingLearnedClassifiesEarly_eq_of_value_perm
    {n d : ℕ} {B η p : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : (results.map Prod.snd).Perm (results'.map Prod.snd)) :
    Online.growingLearnedClassifiesEarly B d η hη results p =
      Online.growingLearnedClassifiesEarly B d η hη results' p := by
  unfold Online.growingLearnedClassifiesEarly
  rw [growingLearnedThresholdFromResults_eq_of_value_perm hη hperm]

def growingLearnedEarlyFor
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Online.Label (k + r) → Bool :=
  fun job => Online.growingLearnedClassifiesEarly B d η hη
    ((Online.fixedTestResults p).take k) (p job)

def growingSplitSampleEarly
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Fin k → Bool :=
  fun i => growingLearnedEarlyFor k r d B η hη p (Fin.castAdd r i)

def growingSplitRestEarly
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Fin r → Bool :=
  fun i => growingLearnedEarlyFor k r d B η hη p (Fin.natAdd k i)

theorem growingLearnedEarlyFor_blockInternalOrder
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) (job : Online.Label (k + r)) :
    growingLearnedEarlyFor k r d B η hη
        (p ∘ blockInternalOrder k r sampleOrder restOrder) job =
      growingLearnedEarlyFor k r d B η hη p
        (blockInternalOrder k r sampleOrder restOrder job) := by
  unfold growingLearnedEarlyFor
  exact growingLearnedClassifiesEarly_eq_of_value_perm hη
    (sampleValues_perm_blockInternalOrder k r p sampleOrder restOrder)

/-- The finite ideal objective for a block-internally permuted run is exactly
the two ordered classified lists used by the conditional expectation lemma. -/
theorem growing_finiteIdealPairCost_blockInternalOrder_eq
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) :
    finiteIdealPairCost
        (p ∘ blockInternalOrder k r sampleOrder restOrder)
        (growingLearnedEarlyFor k r d B η hη
          (p ∘ blockInternalOrder k r sampleOrder restOrder)) =
      classifiedPairCost
        (orderedClassifiedJobs
            (splitSampleProcessing k r p)
            (growingSplitSampleEarly k r d B η hη p) sampleOrder ++
          orderedClassifiedJobs
            (splitRestProcessing k r p)
            (growingSplitRestEarly k r d B η hη p) restOrder) := by
  rw [← classifiedPairCost_ofFn]
  apply congrArg classifiedPairCost
  unfold orderedClassifiedJobs
  rw [← List.ofFn_fin_append]
  apply congrArg List.ofFn
  funext job
  obtain ⟨location, rfl⟩ := finSumFinEquiv.surjective job
  cases location with
  | inl i =>
      change
        ((p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.castAdd r i),
          growingLearnedEarlyFor k r d B η hη
            (p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.castAdd r i)) =
          Fin.append
            ((fun i =>
                (splitSampleProcessing k r p i,
                  growingSplitSampleEarly k r d B η hη p i)) ∘
              linearizedFinOrder k sampleOrder)
            ((fun i =>
                (splitRestProcessing k r p i,
                  growingSplitRestEarly k r d B η hη p i)) ∘
              linearizedFinOrder r restOrder)
            (Fin.castAdd r i)
      rw [Fin.append_left]
      simp only [Function.comp_apply]
      have hblock :
          blockInternalOrder k r sampleOrder restOrder (Fin.castAdd r i) =
            Fin.castAdd r (linearizedFinOrder k sampleOrder i) := by
        exact blockInternalOrder_sample k r sampleOrder restOrder i
      apply Prod.ext
      · simp [splitSampleProcessing, hblock]
      · simpa [growingSplitSampleEarly, hblock] using
          growingLearnedEarlyFor_blockInternalOrder
            k r d B η hη p sampleOrder restOrder (Fin.castAdd r i)
  | inr i =>
      change
        ((p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.natAdd k i),
          growingLearnedEarlyFor k r d B η hη
            (p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.natAdd k i)) =
          Fin.append
            ((fun i =>
                (splitSampleProcessing k r p i,
                  growingSplitSampleEarly k r d B η hη p i)) ∘
              linearizedFinOrder k sampleOrder)
            ((fun i =>
                (splitRestProcessing k r p i,
                  growingSplitRestEarly k r d B η hη p i)) ∘
              linearizedFinOrder r restOrder)
            (Fin.natAdd k i)
      rw [Fin.append_right]
      simp only [Function.comp_apply]
      have hblock :
          blockInternalOrder k r sampleOrder restOrder (Fin.natAdd k i) =
            Fin.natAdd k (linearizedFinOrder r restOrder i) := by
        exact blockInternalOrder_rest k r sampleOrder restOrder i
      apply Prod.ext
      · simp [splitRestProcessing, hblock]
      · simpa [growingSplitRestEarly, hblock] using
          growingLearnedEarlyFor_blockInternalOrder
            k r d B η hη p sampleOrder restOrder (Fin.natAdd k i)

def growingLearnedSampleFirstScalarCost
    (k r d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : ℝ :=
  sampleFirstScalarCost
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
          (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p)))

theorem growing_uniformAverage_finiteIdeal_blockInternalOrder
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (p : Online.Label (k + r) → ℝ) :
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          finiteIdealPairCost
            (p ∘ blockInternalOrder k r orders.1 orders.2)
            (growingLearnedEarlyFor k r d B η hη
              (p ∘ blockInternalOrder k r orders.1 orders.2))) =
      growingLearnedSampleFirstScalarCost k r d B η hη p := by
  have hfunctions :
      (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
        finiteIdealPairCost
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (growingLearnedEarlyFor k r d B η hη
            (p ∘ blockInternalOrder k r orders.1 orders.2))) =
      (fun orders =>
        classifiedPairCost
          (orderedClassifiedJobs
              (splitSampleProcessing k r p)
              (growingSplitSampleEarly k r d B η hη p) orders.1 ++
            orderedClassifiedJobs
              (splitRestProcessing k r p)
              (growingSplitRestEarly k r d B η hη p) orders.2)) := by
    funext orders
    exact growing_finiteIdealPairCost_blockInternalOrder_eq
      k r d B η hη p orders.1 orders.2
  rw [hfunctions]
  exact uniformAverage_classifiedPairCost_ordered_append hk hr
    (splitSampleProcessing k r p) (growingSplitSampleEarly k r d B η hη p)
    (splitRestProcessing k r p) (growingSplitRestEarly k r d B η hη p)

/-- Conditional operational upper bound: after fixing the unordered sample,
averaging only the two internal orders costs the exact sample-first scalar
comparator plus the deterministic delayed-sample budget. -/
theorem growing_uniformAverage_run_blockInternalOrder_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η) (p : Online.Label (k + r) → ℝ)
    (hp : ∀ job, 0 ≤ p job) :
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          Online.runCompletionCost .infinite
            (p ∘ blockInternalOrder k r orders.1 orders.2)
            (Online.run .infinite
              (Online.fixedOracle
                (p ∘ blockInternalOrder k r orders.1 orders.2))
              (Online.growingObligatoryStrategy (k + r) k d B η hη)
              (2 * (k + r) + 1))) ≤
      growingLearnedSampleFirstScalarCost k r d B η hη p + (B + 1) * (k : ℝ) ^ 2 := by
  have hklt : k < k + r := Nat.lt_add_of_pos_right hr
  have hpoint : ∀ orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r),
      Online.runCompletionCost .infinite
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (Online.run .infinite
            (Online.fixedOracle
              (p ∘ blockInternalOrder k r orders.1 orders.2))
            (Online.growingObligatoryStrategy (k + r) k d B η hη)
            (2 * (k + r) + 1)) ≤
        finiteIdealPairCost
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (growingLearnedEarlyFor k r d B η hη
            (p ∘ blockInternalOrder k r orders.1 orders.2)) +
          (B + 1) * (k : ℝ) ^ 2 := by
    intro orders
    simpa [growingLearnedEarlyFor] using
      Online.run_growingObligatoryStrategy_cost_le_finiteIdeal_add
        (k + r) k d B η hη hklt hB hBgrid
        (p ∘ blockInternalOrder k r orders.1 orders.2)
        (fun job => hp (blockInternalOrder k r orders.1 orders.2 job))
  calc
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          Online.runCompletionCost .infinite
            (p ∘ blockInternalOrder k r orders.1 orders.2)
            (Online.run .infinite
              (Online.fixedOracle
                (p ∘ blockInternalOrder k r orders.1 orders.2))
              (Online.growingObligatoryStrategy (k + r) k d B η hη)
              (2 * (k + r) + 1))) ≤
        uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            finiteIdealPairCost
              (p ∘ blockInternalOrder k r orders.1 orders.2)
              (growingLearnedEarlyFor k r d B η hη
                (p ∘ blockInternalOrder k r orders.1 orders.2)) +
            (B + 1) * (k : ℝ) ^ 2) := uniformAverage_mono hpoint
    _ = uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            finiteIdealPairCost
              (p ∘ blockInternalOrder k r orders.1 orders.2)
              (growingLearnedEarlyFor k r d B η hη
                (p ∘ blockInternalOrder k r orders.1 orders.2))) +
          (B + 1) * (k : ℝ) ^ 2 := by
        rw [uniformAverage_add, uniformAverage_const]
    _ = growingLearnedSampleFirstScalarCost k r d B η hη p +
          (B + 1) * (k : ℝ) ^ 2 := by
        rw [growing_uniformAverage_finiteIdeal_blockInternalOrder
          k r d hk hr B η hη p]
def physicalGrowingRunCost
    (n k d : ℕ) (B η : ℝ) (hη : 0 < η)
    (p : Online.Label n → ℝ) (order : Equiv.Perm (Online.Label n)) : ℝ :=
  Online.runCompletionCost .infinite p
    (Online.run .infinite (Online.fixedOracle p)
      (Online.randomizedGrowingObligatoryStrategy n k d B η hη order)
      (2 * n + 1))

/-- Operational expectation after the random physical relabelling is bounded
by the outer average of the exact conditional sample-first scalar costs. -/
theorem uniformAverage_physicalGrowingRunCost_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (B η : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (hBgrid : B ≤ (d : ℝ) * η) (p : Online.Label (k + r) → ℝ)
    (hp : ∀ job, 0 ≤ p job) :
    uniformAverage (physicalGrowingRunCost (k + r) k d B η hη p) ≤
      uniformAverage (fun outer : Equiv.Perm (Fin (k + r)) =>
        growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ outer)) +
        (B + 1) * (k : ℝ) ^ 2 := by
  let f := physicalGrowingRunCost (k + r) k d B η hη p
  rw [uniformAverage_eq_blockConditionalAverage k r f]
  have houter : ∀ outer : Equiv.Perm (Fin (k + r)),
      uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            f ((blockInternalOrder k r orders.1 orders.2).trans
              outer)) ≤
        growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ outer) +
          (B + 1) * (k : ℝ) ^ 2 := by
    intro outer
    have hfunctions :
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          f ((blockInternalOrder k r orders.1 orders.2).trans
            outer)) =
        (fun orders =>
          Online.runCompletionCost .infinite
            ((p ∘ outer) ∘ blockInternalOrder k r orders.1 orders.2)
            (Online.run .infinite
              (Online.fixedOracle
                ((p ∘ outer) ∘ blockInternalOrder k r orders.1 orders.2))
              (Online.growingObligatoryStrategy (k + r) k d B η hη)
              (2 * (k + r) + 1))) := by
      funext orders
      unfold f physicalGrowingRunCost
      unfold Online.randomizedGrowingObligatoryStrategy
      simpa [Function.comp_def, Equiv.trans_apply] using
        Online.runCompletionCost_relabel .infinite p
          ((blockInternalOrder k r orders.1 orders.2).trans outer)
          (Online.growingObligatoryStrategy (k + r) k d B η hη)
          (2 * (k + r) + 1)
    rw [hfunctions]
    exact growing_uniformAverage_run_blockInternalOrder_le
      k r d hk hr B η hη hB hBgrid (p ∘ outer)
        (fun job => hp (outer job))
  calc
    uniformAverage
        (fun outer : Equiv.Perm (Fin (k + r)) =>
          uniformAverage
            (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
              f ((blockInternalOrder k r orders.1 orders.2).trans
                outer))) ≤
      uniformAverage
        (fun outer : Equiv.Perm (Fin (k + r)) =>
          growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ outer) +
            (B + 1) * (k : ℝ) ^ 2) := uniformAverage_mono houter
    _ = uniformAverage (fun outer : Equiv.Perm (Fin (k + r)) =>
          growingLearnedSampleFirstScalarCost k r d B η hη (p ∘ outer)) +
          (B + 1) * (k : ℝ) ^ 2 := by
        rw [uniformAverage_add, uniformAverage_const]


end

end RandomizedObligatory
end SchedulingPaper
