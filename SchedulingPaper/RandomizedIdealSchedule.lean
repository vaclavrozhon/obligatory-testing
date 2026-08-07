import SchedulingPaper.RandomizedBlockOrder
import SchedulingPaper.OfflineOptimal
import Mathlib.Tactic

/-!
# Algebra of the ideal immediate/deferred schedule

A job is represented by `(p, early)`.  Every job is tested, an early job is
processed immediately, and all late jobs are processed in SPT order after
discovery.  The identities below are finite and exact, including zero jobs.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

abbrev ClassifiedJob := ℝ × Bool

def classifiedBlock (job : ClassifiedJob) : ℝ :=
  1 + if job.2 then job.1 else 0

def classifiedEarlyCount : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs => (if job.2 then 1 else 0) + classifiedEarlyCount jobs

def classifiedLateCount : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs => (if job.2 then 0 else 1) + classifiedLateCount jobs

def classifiedDiscoveryWork : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs => classifiedBlock job + classifiedDiscoveryWork jobs

/-- Sum of completion times of the early jobs in the literal discovery
order. -/
def classifiedEarlyCost : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs =>
      (if job.2 then classifiedBlock job else 0) +
        classifiedEarlyCount jobs * classifiedBlock job +
        classifiedEarlyCost jobs

def classifiedLateWork : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs =>
      (if job.2 then 0 else job.1) + classifiedLateWork jobs

def classifiedLatePairMin : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs =>
      (if job.2 then 0 else
        (jobs.map fun other => if other.2 then 0
          else min job.1 other.1).sum) +
        classifiedLatePairMin jobs

def classifiedLateValues (jobs : List ClassifiedJob) : List ℝ :=
  jobs.filterMap fun job => if job.2 then none else some job.1

theorem classifiedLateCount_eq_length_lateValues
    (jobs : List ClassifiedJob) :
    classifiedLateCount jobs = (classifiedLateValues jobs).length := by
  induction jobs with
  | nil => simp [classifiedLateCount, classifiedLateValues]
  | cons job jobs ih =>
      rw [classifiedLateCount]
      unfold classifiedLateValues at ih ⊢
      simp only [List.filterMap_cons]
      cases job.2 <;> simp [ih] <;> ring

theorem classifiedLateWork_eq_sum_lateValues
    (jobs : List ClassifiedJob) :
    classifiedLateWork jobs = (classifiedLateValues jobs).sum := by
  induction jobs with
  | nil => simp [classifiedLateWork, classifiedLateValues]
  | cons job jobs ih =>
      rw [classifiedLateWork]
      unfold classifiedLateValues at ih ⊢
      simp only [List.filterMap_cons]
      cases job.2 <;> simp [ih]

theorem classifiedLatePairMin_eq_pairMinCost_lateValues
    (jobs : List ClassifiedJob) :
    classifiedLatePairMin jobs = pairMinCost (classifiedLateValues jobs) := by
  induction jobs with
  | nil => simp [classifiedLatePairMin, classifiedLateValues, pairMinCost]
  | cons job jobs ih =>
      rcases job with ⟨p, early⟩
      cases early
      · simp only [classifiedLatePairMin, Bool.false_eq_true, if_false,
          classifiedLateValues, List.filterMap_cons, pairMinCost_cons]
        rw [ih]
        congr 1
        clear ih
        induction jobs with
        | nil => simp [classifiedLateValues]
        | cons other jobs ihJobs =>
            rcases other with ⟨q, otherEarly⟩
            cases otherEarly <;>
              simp [classifiedLateValues, ihJobs]
      · simp [classifiedLatePairMin, classifiedLateValues, ih]

/-- Common discovery offset plus the final SPT late tail. -/
def classifiedLateCost (jobs : List ClassifiedJob) : ℝ :=
  classifiedLateCount jobs * classifiedDiscoveryWork jobs +
    classifiedLateWork jobs + classifiedLatePairMin jobs

theorem classifiedDiscoveryWork_perm
    {left right : List ClassifiedJob} (hperm : left.Perm right) :
    classifiedDiscoveryWork left = classifiedDiscoveryWork right := by
  induction hperm with
  | nil => rfl
  | cons job hperm ih =>
      simp only [classifiedDiscoveryWork]
      rw [ih]
  | swap first second jobs =>
      simp only [classifiedDiscoveryWork]
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem classifiedLateCost_perm
    {left right : List ClassifiedJob} (hperm : left.Perm right) :
    classifiedLateCost left = classifiedLateCost right := by
  have hvalues : (classifiedLateValues left).Perm
      (classifiedLateValues right) :=
    by
      unfold classifiedLateValues
      exact hperm.filterMap fun job => if job.2 then none else some job.1
  unfold classifiedLateCost
  rw [classifiedLateCount_eq_length_lateValues,
    classifiedLateCount_eq_length_lateValues,
    classifiedLateWork_eq_sum_lateValues,
    classifiedLateWork_eq_sum_lateValues,
    classifiedLatePairMin_eq_pairMinCost_lateValues,
    classifiedLatePairMin_eq_pairMinCost_lateValues,
    hvalues.length_eq, hvalues.sum_eq, pairMinCost_perm hvalues,
    classifiedDiscoveryWork_perm hperm]

def idealPairCharge (left right : ClassifiedJob) : ℝ :=
  if left.2 then 1 + left.1
  else if right.2 then 2 + right.1
  else 2 + min left.1 right.1

/-- Diagonal plus unordered-pair form of the same ideal schedule. -/
def classifiedPairCost : List ClassifiedJob → ℝ
  | [] => 0
  | job :: jobs =>
      (1 + job.1) + (jobs.map (idealPairCharge job)).sum +
        classifiedPairCost jobs

def finiteIdealPairCost
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool) : ℝ :=
  (∑ i : Fin n, (1 + p i)) +
    ∑ left : Fin n, ∑ right ∈ Finset.univ.filter (fun right => left < right),
      idealPairCharge (p left, early left) (p right, early right)

theorem classifiedPairCost_ofFn
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool) :
    classifiedPairCost (List.ofFn fun i => (p i, early i)) =
      finiteIdealPairCost p early := by
  induction n with
  | zero =>
      simp [classifiedPairCost, finiteIdealPairCost]
  | succ n ih =>
      rw [List.ofFn_succ, classifiedPairCost]
      unfold finiteIdealPairCost
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Finset.sum_filter]
      rw [Fin.sum_univ_succ]
      simp only [lt_self_iff_false, if_false, zero_add, Fin.succ_pos, if_true,
        Fin.succ_lt_succ_iff]
      rw [show
          (List.ofFn fun i : Fin n => (p i.succ, early i.succ)).map
              (idealPairCharge (p 0, early 0)) =
            List.ofFn (fun i : Fin n =>
              idealPairCharge (p 0, early 0) (p i.succ, early i.succ)) by
        rw [List.map_ofFn]
        rfl,
        List.sum_ofFn]
      rw [ih (fun i => p i.succ) (fun i => early i.succ)]
      unfold finiteIdealPairCost
      have hrow : ∀ left : Fin n,
          (∑ right : Fin (n + 1), if left.succ < right then
              idealPairCharge (p left.succ, early left.succ)
                (p right, early right) else 0) =
            ∑ right : Fin n, if left < right then
              idealPairCharge (p left.succ, early left.succ)
                (p right.succ, early right.succ) else 0 := by
        intro left
        rw [Fin.sum_univ_succ]
        simp only [Fin.not_lt_zero, if_false, zero_add,
          Fin.succ_lt_succ_iff]
      simp_rw [hrow]
      simp_rw [Finset.sum_filter]
      ring

@[simp] theorem classifiedEarlyCount_cons (job : ClassifiedJob)
    (jobs : List ClassifiedJob) :
    classifiedEarlyCount (job :: jobs) =
      (if job.2 then 1 else 0) + classifiedEarlyCount jobs := rfl

@[simp] theorem classifiedLateCount_cons (job : ClassifiedJob)
    (jobs : List ClassifiedJob) :
    classifiedLateCount (job :: jobs) =
      (if job.2 then 0 else 1) + classifiedLateCount jobs := rfl

theorem classifiedEarlyCount_add_lateCount
    (jobs : List ClassifiedJob) :
    classifiedEarlyCount jobs + classifiedLateCount jobs = jobs.length := by
  induction jobs with
  | nil => simp [classifiedEarlyCount, classifiedLateCount]
  | cons job jobs ih =>
      simp only [classifiedEarlyCount, classifiedLateCount, List.length_cons]
      cases job.2 <;> simp <;> linarith

theorem classifiedDiscoveryWork_eq_earlyWork_add_lateCount
    (jobs : List ClassifiedJob) :
    classifiedDiscoveryWork jobs =
      classifiedLateCount jobs +
        (jobs.map fun job => if job.2 then 1 + job.1 else 0).sum := by
  induction jobs with
  | nil => simp [classifiedDiscoveryWork, classifiedLateCount]
  | cons job jobs ih =>
      rcases job with ⟨p, early⟩
      simp only [classifiedDiscoveryWork, classifiedLateCount,
        List.map_cons, List.sum_cons]
      rw [ih]
      cases early <;> simp [classifiedBlock] <;> ring

private theorem map_idealPairCharge_sum_early
    (p : ℝ) (jobs : List ClassifiedJob) :
    (jobs.map (idealPairCharge (p, true))).sum =
      jobs.length * (1 + p) := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      simp [idealPairCharge, ih]
      push_cast
      ring

private theorem map_idealPairCharge_sum_late
    (p : ℝ) (jobs : List ClassifiedJob) :
    (jobs.map (idealPairCharge (p, false))).sum =
      classifiedEarlyCount jobs +
        (jobs.map fun job => if job.2 then 1 + job.1 else 0).sum +
        2 * classifiedLateCount jobs +
        (jobs.map fun job => if job.2 then 0 else min p job.1).sum := by
  induction jobs with
  | nil =>
      simp [classifiedEarlyCount, classifiedLateCount]
  | cons job jobs ih =>
      rcases job with ⟨q, early⟩
      simp only [List.map_cons, List.sum_cons, classifiedEarlyCount,
        classifiedLateCount]
      rw [ih]
      cases early <;> simp [idealPairCharge] <;> ring

/-- Exact diagonal-plus-pairs decomposition of the ideal schedule. -/
theorem classifiedPairCost_eq_early_add_late
    (jobs : List ClassifiedJob) :
    classifiedPairCost jobs =
      classifiedEarlyCost jobs + classifiedLateCost jobs := by
  induction jobs with
  | nil =>
      simp [classifiedPairCost, classifiedEarlyCost, classifiedLateCost,
        classifiedLateCount, classifiedDiscoveryWork, classifiedLateWork,
        classifiedLatePairMin]
  | cons job jobs ih =>
      rcases job with ⟨p, early⟩
      unfold classifiedPairCost classifiedEarlyCost classifiedLateCost
      simp only [classifiedLateCount, classifiedDiscoveryWork,
        classifiedLateWork, classifiedLatePairMin]
      rw [ih]
      rw [classifiedLateCost]
      cases early
      · rw [map_idealPairCharge_sum_late]
        have hwork := classifiedDiscoveryWork_eq_earlyWork_add_lateCount jobs
        simp only [Bool.false_eq_true, if_false, zero_add]
        rw [hwork]
        simp [classifiedBlock]
        ring
      · rw [map_idealPairCharge_sum_early]
        have hcount := classifiedEarlyCount_add_lateCount jobs
        simp only [if_true, zero_add]
        push_cast at hcount ⊢
        simp [classifiedBlock]
        linear_combination -(1 + p) * hcount

theorem classifiedEarlyCount_append
    (sample rest : List ClassifiedJob) :
    classifiedEarlyCount (sample ++ rest) =
      classifiedEarlyCount sample + classifiedEarlyCount rest := by
  induction sample with
  | nil => simp [classifiedEarlyCount]
  | cons job sample ih =>
      simp only [List.cons_append, classifiedEarlyCount]
      rw [ih]
      ring

theorem classifiedEarlyCount_perm
    {left right : List ClassifiedJob} (hperm : left.Perm right) :
    classifiedEarlyCount left = classifiedEarlyCount right := by
  induction hperm with
  | nil => rfl
  | cons job hperm ih =>
      simp only [classifiedEarlyCount]
      rw [ih]
  | swap first second jobs =>
      simp only [classifiedEarlyCount]
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Early cost of concatenated discovery blocks. -/
theorem classifiedEarlyCost_append
    (sample rest : List ClassifiedJob) :
    classifiedEarlyCost (sample ++ rest) =
      classifiedEarlyCost sample +
        classifiedEarlyCount rest * classifiedDiscoveryWork sample +
        classifiedEarlyCost rest := by
  induction sample with
  | nil => simp [classifiedEarlyCost, classifiedDiscoveryWork]
  | cons job sample ih =>
      simp only [List.cons_append, classifiedEarlyCost,
        classifiedDiscoveryWork]
      rw [ih]
      rw [classifiedEarlyCount_append]
      ring

theorem classifiedEarlyCount_ofFn
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) :
    classifiedEarlyCount (List.ofFn fun i => (p i, early i)) =
      ∑ i, if early i then 1 else 0 := by
  induction k with
  | zero =>
      simp [classifiedEarlyCount]
  | succ k ih =>
      rw [List.ofFn_succ, classifiedEarlyCount, Fin.sum_univ_succ]
      rw [ih (fun i => p i.succ) (fun i => early i.succ)]

/-- `positionEarlyCost` is the `List.ofFn` presentation of the recursive
early cost. -/
theorem classifiedEarlyCost_ofFn
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) :
    classifiedEarlyCost (List.ofFn fun i => (p i, early i)) =
      positionEarlyCost p early := by
  induction k with
  | zero =>
      simp [classifiedEarlyCost, positionEarlyCost]
  | succ k ih =>
      let pTail : Fin k → ℝ := fun i => p i.succ
      let earlyTail : Fin k → Bool := fun i => early i.succ
      have hprefix : ∀ i : Fin k,
          (∑ j : Fin (k + 1), if j < i.succ then
              discoveryBlock p early j else 0) =
            discoveryBlock p early 0 +
              ∑ j : Fin k, if j < i then
                discoveryBlock pTail earlyTail j else 0 := by
        intro i
        rw [Fin.sum_univ_succ]
        simp only [Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]
        rfl
      rw [List.ofFn_succ, classifiedEarlyCost]
      rw [ih pTail earlyTail]
      unfold positionEarlyCost
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero, if_false, Finset.sum_const_zero, add_zero]
      simp_rw [hprefix]
      have hsplit : ∀ i : Fin k,
          (if early i.succ then
              discoveryBlock p early i.succ +
                (discoveryBlock p early 0 +
                  ∑ j, if j < i then discoveryBlock pTail earlyTail j else 0)
            else 0) =
          (if earlyTail i then 1 else 0) *
              discoveryBlock p early 0 +
            (if earlyTail i then
              discoveryBlock pTail earlyTail i +
                ∑ j, if j < i then discoveryBlock pTail earlyTail j else 0
            else 0) := by
        intro i
        cases h : early i.succ <;>
          simp [earlyTail, pTail, discoveryBlock, h] <;> ring
      simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [← classifiedEarlyCount_ofFn pTail earlyTail]
      simp [classifiedBlock, discoveryBlock, pTail, earlyTail,
        Fin.not_lt_zero]
      ring

def orderedClassifiedJobs
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool)
    (order : Equiv.Perm (Fin k)) : List ClassifiedJob :=
  List.ofFn ((fun i => (p i, early i)) ∘ linearizedFinOrder k order)

def baseClassifiedJobs
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) :
    List ClassifiedJob :=
  List.ofFn fun i => (p i, early i)

theorem orderedClassifiedJobs_perm_base
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool)
    (order : Equiv.Perm (Fin k)) :
    (orderedClassifiedJobs p early order).Perm
      (baseClassifiedJobs p early) := by
  exact Equiv.Perm.ofFn_comp_perm (linearizedFinOrder k order)
    (fun i => (p i, early i))

theorem classifiedDiscoveryWork_ofFn
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) :
    classifiedDiscoveryWork (baseClassifiedJobs p early) =
      ∑ i, discoveryBlock p early i := by
  induction k with
  | zero => simp [baseClassifiedJobs, classifiedDiscoveryWork]
  | succ k ih =>
      unfold baseClassifiedJobs
      rw [List.ofFn_succ, classifiedDiscoveryWork, Fin.sum_univ_succ]
      change classifiedBlock (p 0, early 0) +
          classifiedDiscoveryWork
            (baseClassifiedJobs (fun i => p i.succ) (fun i => early i.succ)) =
        discoveryBlock p early 0 +
          ∑ i : Fin k, discoveryBlock p early i.succ
      rw [ih]
      rfl

theorem classifiedEarlyCount_ofFn_eq_massCount
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool) :
    classifiedEarlyCount (baseClassifiedJobs p early) =
      earlyMassCount early := by
  unfold baseClassifiedJobs earlyMassCount
  exact classifiedEarlyCount_ofFn p early

theorem classifiedEarlyCost_ordered_eq_stationary
    {k : ℕ} (p : Fin k → ℝ) (early : Fin k → Bool)
    (order : Equiv.Perm (Fin k)) :
    classifiedEarlyCost (orderedClassifiedJobs p early order) =
      stationaryEarlyCost p early order := by
  unfold orderedClassifiedJobs
  rw [classifiedEarlyCost_ofFn]
  exact positionEarlyCost_comp_linearized_eq_stationary k p early order

/-- Exact conditional cost of the ideal sample-first schedule, now in the
same diagonal-plus-pairs form used by the operational trace. -/
theorem uniformAverage_classifiedPairCost_ordered_append
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (pSample : Fin k → ℝ) (earlySample : Fin k → Bool)
    (pRest : Fin r → ℝ) (earlyRest : Fin r → Bool) :
    uniformAverage
        (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
          classifiedPairCost
            (orderedClassifiedJobs pSample earlySample orders.1 ++
              orderedClassifiedJobs pRest earlyRest orders.2)) =
      sampleFirstScalarCost
        (earlyMassCount earlySample) (earlyMassCount earlyRest)
        (∑ i, discoveryBlock pSample earlySample i)
        (∑ i, discoveryBlock pRest earlyRest i)
        (earlySelfWork pSample earlySample)
        (earlySelfWork pRest earlyRest)
        (classifiedLateCost
          (baseClassifiedJobs pSample earlySample ++
            baseClassifiedJobs pRest earlyRest)) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hpoint : ∀ orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r),
      classifiedPairCost
          (orderedClassifiedJobs pSample earlySample orders.1 ++
            orderedClassifiedJobs pRest earlyRest orders.2) =
        blockOrderedEarlyCost pSample earlySample pRest earlyRest
            orders.1 orders.2 +
          classifiedLateCost
            (baseClassifiedJobs pSample earlySample ++
              baseClassifiedJobs pRest earlyRest) := by
    intro orders
    rw [classifiedPairCost_eq_early_add_late,
      classifiedEarlyCost_append,
      classifiedEarlyCost_ordered_eq_stationary,
      classifiedEarlyCost_ordered_eq_stationary]
    have hSample := orderedClassifiedJobs_perm_base
      pSample earlySample orders.1
    have hRest := orderedClassifiedJobs_perm_base
      pRest earlyRest orders.2
    have hAppend :
        (orderedClassifiedJobs pSample earlySample orders.1 ++
          orderedClassifiedJobs pRest earlyRest orders.2).Perm
        (baseClassifiedJobs pSample earlySample ++
          baseClassifiedJobs pRest earlyRest) :=
      hSample.append hRest
    rw [classifiedLateCost_perm hAppend,
      classifiedEarlyCount_perm hRest,
      classifiedEarlyCount_ofFn_eq_massCount,
      classifiedDiscoveryWork_perm hSample,
      classifiedDiscoveryWork_ofFn]
    rfl
  rw [show (fun orders : Equiv.Perm (Fin k) × Equiv.Perm (Fin r) =>
      classifiedPairCost
        (orderedClassifiedJobs pSample earlySample orders.1 ++
          orderedClassifiedJobs pRest earlyRest orders.2)) =
      (fun orders =>
        blockOrderedEarlyCost pSample earlySample pRest earlyRest
            orders.1 orders.2 +
          classifiedLateCost
            (baseClassifiedJobs pSample earlySample ++
              baseClassifiedJobs pRest earlyRest)) by
        funext orders
        exact hpoint orders]
  exact uniformAverage_blockOrderedEarlyCost_add_late
    pSample earlySample pRest earlyRest _

end

end RandomizedObligatory
end SchedulingPaper
