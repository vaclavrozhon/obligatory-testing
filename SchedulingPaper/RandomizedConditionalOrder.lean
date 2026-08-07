import SchedulingPaper.RandomizedOperationalUpper
import SchedulingPaper.RandomizedRelabelRun
import SchedulingPaper.RandomizedObligatoryLower
import Mathlib.Tactic

/-!
# Conditional block-order averaging

A uniform permutation is refined by independently permuting its first `k`
positions and its remaining `r` positions.  Right multiplication by any such
block permutation is a bijection of the full permutation space, so inserting
this conditional average does not change the algorithm's expectation.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

/-! ## The learner only sees the unordered sample -/

theorem resultCategoryFraction_eq_of_perm
    {n d : ℕ} {η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : results.Perm results') :
    Online.resultCategoryFraction d η hη results =
      Online.resultCategoryFraction d η hη results' := by
  funext b
  unfold Online.resultCategoryFraction
  rw [hperm.length_eq]
  congr 1
  exact_mod_cast (hperm.filter fun result =>
    quantizedCategory d η result.2 hη = b).length_eq

theorem resultCategoryFraction_eq_of_value_perm
    {n d : ℕ} {η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : (results.map Prod.snd).Perm (results'.map Prod.snd)) :
    Online.resultCategoryFraction d η hη results =
      Online.resultCategoryFraction d η hη results' := by
  funext b
  unfold Online.resultCategoryFraction
  have hlength : results.length = results'.length := by
    simpa using hperm.length_eq
  rw [hlength]
  congr 1
  have hfilter (xs : List (Online.Label n × ℝ)) :
      (xs.filter fun result =>
          quantizedCategory d η result.2 hη = b).length =
        ((xs.map Prod.snd).filter fun p =>
          quantizedCategory d η p hη = b).length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.filter_cons, List.map_cons]; split <;> simp_all
  exact_mod_cast (by
    rw [hfilter results, hfilter results']
    exact (hperm.filter fun p =>
      quantizedCategory d η p hη = b).length_eq)

theorem learnedThresholdFromResults_eq_of_perm
    {n d : ℕ} {η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : results.Perm results') :
    Online.learnedThresholdFromResults? d η hη results =
      Online.learnedThresholdFromResults? d η hη results' := by
  have hmu := resultCategoryFraction_eq_of_perm (d := d) hη hperm
  unfold Online.learnedThresholdFromResults?
  unfold Online.resultMaximumDensitySet
  rw [hmu]

theorem learnedThresholdFromResults_eq_of_value_perm
    {n d : ℕ} {η : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : (results.map Prod.snd).Perm (results'.map Prod.snd)) :
    Online.learnedThresholdFromResults? d η hη results =
      Online.learnedThresholdFromResults? d η hη results' := by
  have hmu := resultCategoryFraction_eq_of_value_perm (d := d) hη hperm
  unfold Online.learnedThresholdFromResults?
  unfold Online.resultMaximumDensitySet
  rw [hmu]

theorem learnedClassifiesEarly_eq_of_perm
    {n d : ℕ} {η p : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : results.Perm results') :
    Online.learnedClassifiesEarly d η hη results p =
      Online.learnedClassifiesEarly d η hη results' p := by
  unfold Online.learnedClassifiesEarly
  rw [learnedThresholdFromResults_eq_of_perm hη hperm]

theorem learnedClassifiesEarly_eq_of_value_perm
    {n d : ℕ} {η p : ℝ} (hη : 0 < η)
    {results results' : List (Online.Label n × ℝ)}
    (hperm : (results.map Prod.snd).Perm (results'.map Prod.snd)) :
    Online.learnedClassifiesEarly d η hη results p =
      Online.learnedClassifiesEarly d η hη results' p := by
  unfold Online.learnedClassifiesEarly
  rw [learnedThresholdFromResults_eq_of_value_perm hη hperm]

def blockInternalOrder
    (k r : ℕ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (k + r)) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (linearizedFinOrder k sampleOrder)
      (linearizedFinOrder r restOrder) |>.trans finSumFinEquiv)

@[simp] theorem blockInternalOrder_sample
    (k r : ℕ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) (i : Fin k) :
    blockInternalOrder k r sampleOrder restOrder
        (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv
        (Sum.inl (linearizedFinOrder k sampleOrder i)) := by
  simp [blockInternalOrder]

@[simp] theorem blockInternalOrder_rest
    (k r : ℕ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) (i : Fin r) :
    blockInternalOrder k r sampleOrder restOrder
        (finSumFinEquiv (Sum.inr i)) =
      finSumFinEquiv
        (Sum.inr (linearizedFinOrder r restOrder i)) := by
  simp [blockInternalOrder]

theorem map_snd_fixedTestResults_take_add
    (k r : ℕ) (p : Online.Label (k + r) → ℝ) :
    ((Online.fixedTestResults p).take k).map Prod.snd =
      List.ofFn fun i : Fin k => p (Fin.castAdd r i) := by
  unfold Online.fixedTestResults
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_add_right k r)]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rfl

/-- Permuting inside the first block preserves the unordered list of sample
values seen by the learner. -/
theorem sampleValues_perm_blockInternalOrder
    (k r : ℕ) (p : Online.Label (k + r) → ℝ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) :
    (((Online.fixedTestResults
        (p ∘ blockInternalOrder k r sampleOrder restOrder)).take k).map
          Prod.snd).Perm
      (((Online.fixedTestResults p).take k).map Prod.snd) := by
  rw [map_snd_fixedTestResults_take_add, map_snd_fixedTestResults_take_add]
  have hpoint : (fun i : Fin k =>
      (p ∘ blockInternalOrder k r sampleOrder restOrder)
        (Fin.castAdd r i)) =
      (fun i => p (Fin.castAdd r (linearizedFinOrder k sampleOrder i))) := by
    funext i
    apply congrArg p
    change blockInternalOrder k r sampleOrder restOrder
        (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv
        (Sum.inl (linearizedFinOrder k sampleOrder i))
    exact blockInternalOrder_sample k r sampleOrder restOrder i
  rw [hpoint]
  exact Equiv.Perm.ofFn_comp_perm (linearizedFinOrder k sampleOrder)
    (fun i : Fin k => p (Fin.castAdd r i))

def splitSampleProcessing
    (k r : ℕ) (p : Online.Label (k + r) → ℝ) : Fin k → ℝ :=
  fun i => p (Fin.castAdd r i)

def splitRestProcessing
    (k r : ℕ) (p : Online.Label (k + r) → ℝ) : Fin r → ℝ :=
  fun i => p (Fin.natAdd k i)

def learnedEarlyFor
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Online.Label (k + r) → Bool :=
  fun job => Online.learnedClassifiesEarly d η hη
    ((Online.fixedTestResults p).take k) (p job)

def splitSampleEarly
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Fin k → Bool :=
  fun i => learnedEarlyFor k r d η hη p (Fin.castAdd r i)

def splitRestEarly
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : Fin r → Bool :=
  fun i => learnedEarlyFor k r d η hη p (Fin.natAdd k i)

theorem learnedEarlyFor_blockInternalOrder
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) (job : Online.Label (k + r)) :
    learnedEarlyFor k r d η hη
        (p ∘ blockInternalOrder k r sampleOrder restOrder) job =
      learnedEarlyFor k r d η hη p
        (blockInternalOrder k r sampleOrder restOrder job) := by
  unfold learnedEarlyFor
  exact learnedClassifiesEarly_eq_of_value_perm hη
    (sampleValues_perm_blockInternalOrder k r p sampleOrder restOrder)

/-- The finite ideal objective for a block-internally permuted run is exactly
the two ordered classified lists used by the conditional expectation lemma. -/
theorem finiteIdealPairCost_blockInternalOrder_eq
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ)
    (sampleOrder : Equiv.Perm (Fin k))
    (restOrder : Equiv.Perm (Fin r)) :
    finiteIdealPairCost
        (p ∘ blockInternalOrder k r sampleOrder restOrder)
        (learnedEarlyFor k r d η hη
          (p ∘ blockInternalOrder k r sampleOrder restOrder)) =
      classifiedPairCost
        (orderedClassifiedJobs
            (splitSampleProcessing k r p)
            (splitSampleEarly k r d η hη p) sampleOrder ++
          orderedClassifiedJobs
            (splitRestProcessing k r p)
            (splitRestEarly k r d η hη p) restOrder) := by
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
          learnedEarlyFor k r d η hη
            (p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.castAdd r i)) =
          Fin.append
            ((fun i =>
                (splitSampleProcessing k r p i,
                  splitSampleEarly k r d η hη p i)) ∘
              linearizedFinOrder k sampleOrder)
            ((fun i =>
                (splitRestProcessing k r p i,
                  splitRestEarly k r d η hη p i)) ∘
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
      · simpa [splitSampleEarly, hblock] using
          learnedEarlyFor_blockInternalOrder
            k r d η hη p sampleOrder restOrder (Fin.castAdd r i)
  | inr i =>
      change
        ((p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.natAdd k i),
          learnedEarlyFor k r d η hη
            (p ∘ blockInternalOrder k r sampleOrder restOrder)
            (Fin.natAdd k i)) =
          Fin.append
            ((fun i =>
                (splitSampleProcessing k r p i,
                  splitSampleEarly k r d η hη p i)) ∘
              linearizedFinOrder k sampleOrder)
            ((fun i =>
                (splitRestProcessing k r p i,
                  splitRestEarly k r d η hη p i)) ∘
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
      · simpa [splitRestEarly, hblock] using
          learnedEarlyFor_blockInternalOrder
            k r d η hη p sampleOrder restOrder (Fin.natAdd k i)

def learnedSampleFirstScalarCost
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) : ℝ :=
  sampleFirstScalarCost
    (earlyMassCount (splitSampleEarly k r d η hη p))
    (earlyMassCount (splitRestEarly k r d η hη p))
    (∑ i, discoveryBlock
      (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) i)
    (∑ i, discoveryBlock
      (splitRestProcessing k r p) (splitRestEarly k r d η hη p) i)
    (earlySelfWork
      (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p))
    (earlySelfWork
      (splitRestProcessing k r p) (splitRestEarly k r d η hη p))
    (classifiedLateCost
      (baseClassifiedJobs
          (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) ++
        baseClassifiedJobs
          (splitRestProcessing k r p) (splitRestEarly k r d η hη p)))

theorem uniformAverage_finiteIdeal_blockInternalOrder
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (p : Online.Label (k + r) → ℝ) :
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          finiteIdealPairCost
            (p ∘ blockInternalOrder k r orders.1 orders.2)
            (learnedEarlyFor k r d η hη
              (p ∘ blockInternalOrder k r orders.1 orders.2))) =
      learnedSampleFirstScalarCost k r d η hη p := by
  have hfunctions :
      (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
        finiteIdealPairCost
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (learnedEarlyFor k r d η hη
            (p ∘ blockInternalOrder k r orders.1 orders.2))) =
      (fun orders =>
        classifiedPairCost
          (orderedClassifiedJobs
              (splitSampleProcessing k r p)
              (splitSampleEarly k r d η hη p) orders.1 ++
            orderedClassifiedJobs
              (splitRestProcessing k r p)
              (splitRestEarly k r d η hη p) orders.2)) := by
    funext orders
    exact finiteIdealPairCost_blockInternalOrder_eq
      k r d η hη p orders.1 orders.2
  rw [hfunctions]
  exact uniformAverage_classifiedPairCost_ordered_append hk hr
    (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p)
    (splitRestProcessing k r p) (splitRestEarly k r d η hη p)

/-- Conditional operational upper bound: after fixing the unordered sample,
averaging only the two internal orders costs the exact sample-first scalar
comparator plus the deterministic delayed-sample budget. -/
theorem uniformAverage_run_blockInternalOrder_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (p : Online.Label (k + r) → ℝ)
    (hp : ∀ job, 0 ≤ p job) :
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          Online.runCompletionCost .infinite
            (p ∘ blockInternalOrder k r orders.1 orders.2)
            (Online.run .infinite
              (Online.fixedOracle
                (p ∘ blockInternalOrder k r orders.1 orders.2))
              (Online.sampledObligatoryStrategy (k + r) k d η hη)
              (2 * (k + r) + 1))) ≤
      learnedSampleFirstScalarCost k r d η hη p + 17 * (k : ℝ) ^ 2 := by
  have hklt : k < k + r := Nat.lt_add_of_pos_right hr
  have hpoint : ∀ orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r),
      Online.runCompletionCost .infinite
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (Online.run .infinite
            (Online.fixedOracle
              (p ∘ blockInternalOrder k r orders.1 orders.2))
            (Online.sampledObligatoryStrategy (k + r) k d η hη)
            (2 * (k + r) + 1)) ≤
        finiteIdealPairCost
          (p ∘ blockInternalOrder k r orders.1 orders.2)
          (learnedEarlyFor k r d η hη
            (p ∘ blockInternalOrder k r orders.1 orders.2)) +
          17 * (k : ℝ) ^ 2 := by
    intro orders
    simpa [learnedEarlyFor] using
      Online.run_sampledObligatoryStrategy_cost_le_finiteIdeal_add
        (k + r) k d η hη hklt
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
              (Online.sampledObligatoryStrategy (k + r) k d η hη)
              (2 * (k + r) + 1))) ≤
        uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            finiteIdealPairCost
              (p ∘ blockInternalOrder k r orders.1 orders.2)
              (learnedEarlyFor k r d η hη
                (p ∘ blockInternalOrder k r orders.1 orders.2)) +
            17 * (k : ℝ) ^ 2) := uniformAverage_mono hpoint
    _ = uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            finiteIdealPairCost
              (p ∘ blockInternalOrder k r orders.1 orders.2)
              (learnedEarlyFor k r d η hη
                (p ∘ blockInternalOrder k r orders.1 orders.2))) +
          17 * (k : ℝ) ^ 2 := by
        rw [uniformAverage_add, uniformAverage_const]
    _ = learnedSampleFirstScalarCost k r d η hη p +
          17 * (k : ℝ) ^ 2 := by
        rw [uniformAverage_finiteIdeal_blockInternalOrder k r d hk hr η hη p]

/-- Inserting independent random orders inside the two blocks leaves a
uniform full permutation uniform. -/
theorem uniformAverage_eq_blockConditionalAverage
    (k r : ℕ) (f : Equiv.Perm (Fin (k + r)) → ℝ) :
    uniformAverage f =
      uniformAverage fun outer : Equiv.Perm (Fin (k + r)) =>
        uniformAverage fun orders :
            Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          f ((blockInternalOrder k r orders.1 orders.2).trans outer) := by
  rw [uniformAverage_comm]
  rw [show (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
      uniformAverage fun outer : Equiv.Perm (Fin (k + r)) =>
        f ((blockInternalOrder k r orders.1 orders.2).trans outer)) =
      (fun _orders => uniformAverage f) by
    funext orders
    let block := blockInternalOrder k r orders.1 orders.2
    let e : Equiv.Perm (Equiv.Perm (Fin (k + r))) :=
      { toFun := fun outer => block.trans outer
        invFun := fun outer => block.symm.trans outer
        left_inv := by intro outer; ext i; simp
        right_inv := by intro outer; ext i; simp }
    have h := uniformAverage_comp_equiv e f
    simpa [e] using h]
  simp

def physicalSampledRunCost
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label n → ℝ) (order : Equiv.Perm (Online.Label n)) : ℝ :=
  Online.runCompletionCost .infinite p
    (Online.run .infinite (Online.fixedOracle p)
      (Online.randomizedSampledObligatoryStrategy n k d η hη order)
      (2 * n + 1))

/-- Operational expectation after the random physical relabelling is bounded
by the outer average of the exact conditional sample-first scalar costs. -/
theorem uniformAverage_physicalSampledRunCost_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (p : Online.Label (k + r) → ℝ)
    (hp : ∀ job, 0 ≤ p job) :
    uniformAverage (physicalSampledRunCost (k + r) k d η hη p) ≤
      uniformAverage (fun outer : Equiv.Perm (Fin (k + r)) =>
        learnedSampleFirstScalarCost k r d η hη (p ∘ outer)) +
        17 * (k : ℝ) ^ 2 := by
  let f := physicalSampledRunCost (k + r) k d η hη p
  rw [uniformAverage_eq_blockConditionalAverage k r f]
  have houter : ∀ outer : Equiv.Perm (Fin (k + r)),
      uniformAverage
          (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
            f ((blockInternalOrder k r orders.1 orders.2).trans
              outer)) ≤
        learnedSampleFirstScalarCost k r d η hη (p ∘ outer) +
          17 * (k : ℝ) ^ 2 := by
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
              (Online.sampledObligatoryStrategy (k + r) k d η hη)
              (2 * (k + r) + 1))) := by
      funext orders
      unfold f physicalSampledRunCost
      unfold Online.randomizedSampledObligatoryStrategy
      simpa [Function.comp_def, Equiv.trans_apply] using
        Online.runCompletionCost_relabel .infinite p
          ((blockInternalOrder k r orders.1 orders.2).trans outer)
          (Online.sampledObligatoryStrategy (k + r) k d η hη)
          (2 * (k + r) + 1)
    rw [hfunctions]
    exact uniformAverage_run_blockInternalOrder_le
      k r d hk hr η hη (p ∘ outer) (fun job => hp (outer job))
  calc
    uniformAverage
        (fun outer : Equiv.Perm (Fin (k + r)) =>
          uniformAverage
            (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
              f ((blockInternalOrder k r orders.1 orders.2).trans
                outer))) ≤
      uniformAverage
        (fun outer : Equiv.Perm (Fin (k + r)) =>
          learnedSampleFirstScalarCost k r d η hη (p ∘ outer) +
            17 * (k : ℝ) ^ 2) := uniformAverage_mono houter
    _ = uniformAverage (fun outer : Equiv.Perm (Fin (k + r)) =>
          learnedSampleFirstScalarCost k r d η hη (p ∘ outer)) +
          17 * (k : ℝ) ^ 2 := by
        rw [uniformAverage_add, uniformAverage_const]

end

end RandomizedObligatory
end SchedulingPaper
