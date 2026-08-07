import SchedulingPaper.RandomizedConditionalOrder
import SchedulingPaper.RandomizedGoodLearned
import Mathlib.Tactic

/-!
# Analytic bounds for the operational sampled policy

This module rewrites the conditional scalar cost extracted from the literal
online transcript as the normalized stationary objective used by the sharp
`4/3` certificate.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

theorem earlySelfWork_eq_mass_add_work_sub_card
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool) :
    earlySelfWork p early =
      earlyMassCount early + (∑ i, discoveryBlock p early i) - n := by
  unfold earlySelfWork earlyMassCount discoveryBlock
  calc
    (∑ i : Fin n,
        if early i then 1 + (if early i then p i else 0) else 0) =
        ∑ i : Fin n, ((if early i then 1 else 0) +
          (1 + if early i then p i else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases early i <;> simp
    _ = (∑ i : Fin n, if early i then 1 else 0) +
        ∑ i : Fin n, (1 + if early i then p i else 0) - n := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp

theorem classifiedDiscoveryWork_append
    (left right : List ClassifiedJob) :
    classifiedDiscoveryWork (left ++ right) =
      classifiedDiscoveryWork left + classifiedDiscoveryWork right := by
  induction left with
  | nil => simp [classifiedDiscoveryWork]
  | cons job left ih =>
      simp only [List.cons_append, classifiedDiscoveryWork]
      rw [ih]
      ring

/-- The fully uniform scalar comparator for two blocks is the ordinary
stationary scalar cost of their union. -/
theorem uniformStationaryScalarCost_split_eq
    {k r : ℕ}
    (pSample : Fin k → ℝ) (earlySample : Fin k → Bool)
    (pRest : Fin r → ℝ) (earlyRest : Fin r → Bool) :
    uniformStationaryScalarCost
        (earlyMassCount earlySample) (earlyMassCount earlyRest)
        (∑ i, discoveryBlock pSample earlySample i)
        (∑ i, discoveryBlock pRest earlyRest i)
        (earlySelfWork pSample earlySample)
        (earlySelfWork pRest earlyRest)
        (classifiedLateCost
          (baseClassifiedJobs pSample earlySample ++
            baseClassifiedJobs pRest earlyRest)) =
      stationaryScalarCost (k + r)
        (earlyMassCount earlySample + earlyMassCount earlyRest)
        ((∑ i, discoveryBlock pSample earlySample i) +
          (∑ i, discoveryBlock pRest earlyRest i) - (k + r))
        (classifiedLateWork
          (baseClassifiedJobs pSample earlySample ++
            baseClassifiedJobs pRest earlyRest))
        (classifiedLatePairMin
          (baseClassifiedJobs pSample earlySample ++
            baseClassifiedJobs pRest earlyRest)) := by
  let sample := baseClassifiedJobs pSample earlySample
  let rest := baseClassifiedJobs pRest earlyRest
  let jobs := sample ++ rest
  have hcountSample : classifiedEarlyCount sample =
      earlyMassCount earlySample :=
    classifiedEarlyCount_ofFn_eq_massCount pSample earlySample
  have hcountRest : classifiedEarlyCount rest =
      earlyMassCount earlyRest :=
    classifiedEarlyCount_ofFn_eq_massCount pRest earlyRest
  have hworkSample : classifiedDiscoveryWork sample =
      ∑ i, discoveryBlock pSample earlySample i :=
    classifiedDiscoveryWork_ofFn pSample earlySample
  have hworkRest : classifiedDiscoveryWork rest =
      ∑ i, discoveryBlock pRest earlyRest i :=
    classifiedDiscoveryWork_ofFn pRest earlyRest
  have hlengthSample : sample.length = k := by simp [sample, baseClassifiedJobs]
  have hlengthRest : rest.length = r := by simp [rest, baseClassifiedJobs]
  have hlateCount : classifiedLateCount jobs =
      (k + r : ℝ) -
        (earlyMassCount earlySample + earlyMassCount earlyRest) := by
    have htotal := classifiedEarlyCount_add_lateCount jobs
    have hearly : classifiedEarlyCount jobs =
        earlyMassCount earlySample + earlyMassCount earlyRest := by
      dsimp [jobs]
      rw [classifiedEarlyCount_append, hcountSample, hcountRest]
    rw [hearly] at htotal
    simp [jobs, hlengthSample, hlengthRest] at htotal
    linarith
  have hwork : classifiedDiscoveryWork jobs =
      (∑ i, discoveryBlock pSample earlySample i) +
        (∑ i, discoveryBlock pRest earlyRest i) := by
    dsimp [jobs]
    rw [classifiedDiscoveryWork_append, hworkSample, hworkRest]
  have hselfSample :=
    earlySelfWork_eq_mass_add_work_sub_card pSample earlySample
  have hselfRest :=
    earlySelfWork_eq_mass_add_work_sub_card pRest earlyRest
  unfold uniformStationaryScalarCost Randomized.uniformEarlyCost
  unfold stationaryScalarCost classifiedLateCost
  dsimp only
  change _ +
      (classifiedLateCount jobs * classifiedDiscoveryWork jobs +
        classifiedLateWork jobs + classifiedLatePairMin jobs) = _
  rw [hlateCount, hwork]
  nlinarith

theorem map_classifiedLateValues_sum
    (f : ℝ → ℝ) (jobs : List ClassifiedJob) :
    ((classifiedLateValues jobs).map f).sum =
      (jobs.map fun job => if job.2 then 0 else f job.1).sum := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      rcases job with ⟨p, early⟩
      unfold classifiedLateValues at ih ⊢
      cases early <;> simp [ih]

@[simp] theorem classifiedLateValues_cons
    (job : ClassifiedJob) (jobs : List ClassifiedJob) :
    classifiedLateValues (job :: jobs) =
      if job.2 then classifiedLateValues jobs
      else job.1 :: classifiedLateValues jobs := by
  rcases job with ⟨p, early⟩
  cases early <;> rfl

theorem listFullMinCost_cons (x : ℝ) (xs : List ℝ) :
    listFullMinCost (x :: xs) =
      x + 2 * (xs.map (min x)).sum + listFullMinCost xs := by
  unfold listFullMinCost
  simp only [List.map_cons, List.sum_cons, min_self]
  have hsym : (xs.map fun y => min y x).sum =
      (xs.map (min x)).sum := by
    congr 1
    exact List.map_congr_left fun y _ => min_comm y x
  rw [List.sum_map_add, hsym]
  ring

theorem listFullMinCost_lateValues_ofFn
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool) :
    listFullMinCost
        (classifiedLateValues (baseClassifiedJobs p early)) =
      ∑ i : Fin n, ∑ j : Fin n,
        if early i then 0 else if early j then 0 else min (p i) (p j) := by
  induction n with
  | zero => simp [baseClassifiedJobs, classifiedLateValues, listFullMinCost]
  | succ n ih =>
      let pTail : Fin n → ℝ := fun i => p i.succ
      let earlyTail : Fin n → Bool := fun i => early i.succ
      have hrow :
          ((classifiedLateValues
              (baseClassifiedJobs pTail earlyTail)).map (min (p 0))).sum =
            ∑ j : Fin n,
              if early j.succ then 0 else min (p 0) (p j.succ) := by
        rw [map_classifiedLateValues_sum]
        unfold baseClassifiedJobs
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      unfold baseClassifiedJobs
      rw [List.ofFn_succ]
      change
        listFullMinCost
          (classifiedLateValues
            ((p 0, early 0) ::
              baseClassifiedJobs pTail earlyTail)) = _
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_succ]
      have htailRows :
          (∑ i : Fin n, ∑ j : Fin (n + 1),
            if early i.succ then 0
            else if early j then 0 else min (p i.succ) (p j)) =
          (∑ i : Fin n,
              (if early i.succ then 0
                else if early 0 then 0 else min (p i.succ) (p 0))) +
            ∑ i : Fin n, ∑ j : Fin n,
              if early i.succ then 0
              else if early j.succ then 0
              else min (p i.succ) (p j.succ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_succ]
      rw [htailRows]
      cases hzero : early 0
      · simp only [classifiedLateValues, List.filterMap_cons, hzero,
          Bool.false_eq_true, ↓reduceIte, listFullMinCost_cons]
        change p 0 +
            2 * ((classifiedLateValues
              (baseClassifiedJobs pTail earlyTail)).map (min (p 0))).sum +
              listFullMinCost
                (classifiedLateValues
                  (baseClassifiedJobs pTail earlyTail)) = _
        rw [hrow]
        rw [ih pTail earlyTail]
        simp only [earlyTail, pTail]
        simp_rw [min_comm (p _ ) (p 0)]
        simp
        ring
      · simp only [classifiedLateValues, List.filterMap_cons, hzero,
          ↓reduceIte]
        change listFullMinCost
            (classifiedLateValues
              (baseClassifiedJobs pTail earlyTail)) = _
        rw [ih pTail earlyTail]
        simp only [earlyTail, pTail]
        simp

theorem earlyMassCount_div_eq_weightedMass
    {n : ℕ} (hn : 0 < n) (early : Fin n → Bool) :
    earlyMassCount early / n = weightedMass (earlyJobWeight early) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold earlyMassCount weightedMass earlyJobWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases early i <;> simp

theorem discoveryWork_sub_card_div_eq_weightedMoment
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (early : Fin n → Bool) :
    ((∑ i, discoveryBlock p early i) - n) / n =
      weightedMoment (earlyJobWeight early) p := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold weightedMoment earlyJobWeight discoveryBlock
  have hsum :
      (∑ i : Fin n, (1 + if early i then p i else 0)) - n =
        ∑ i : Fin n, if early i then p i else 0 := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases early i <;> simp <;> field_simp [hnR]

theorem classifiedLateWork_base_add_earlyWork
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool) :
    classifiedLateWork (baseClassifiedJobs p early) +
        ((∑ i, discoveryBlock p early i) - n) =
      ∑ i, p i := by
  induction n with
  | zero => simp [baseClassifiedJobs, classifiedLateWork]
  | succ n ih =>
      rw [show baseClassifiedJobs p early =
          (p 0, early 0) ::
            baseClassifiedJobs (fun i => p i.succ) (fun i => early i.succ) by
        unfold baseClassifiedJobs
        rw [List.ofFn_succ]]
      rw [classifiedLateWork, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have htail := ih (fun i => p i.succ) (fun i => early i.succ)
      cases h : early 0 <;> simp [baseClassifiedJobs, discoveryBlock, h] at htail ⊢ <;>
        linarith

theorem weightedMinPair_lateJobWeight_eq
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (early : Fin n → Bool) :
    weightedMinPair (lateJobWeight early) p =
      (classifiedLateWork (baseClassifiedJobs p early) +
          2 * classifiedLatePairMin (baseClassifiedJobs p early)) /
        (n : ℝ) ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfull := listFullMinCost_lateValues_ofFn p early
  rw [listFullMinCost_eq_sum_add_two_pairMinCost,
    ← classifiedLateWork_eq_sum_lateValues,
    ← classifiedLatePairMin_eq_pairMinCost_lateValues] at hfull
  unfold weightedMinPair lateJobWeight
  rw [show (fun i : Fin n => ∑ j : Fin n,
      (if early i then 0 else 1 / (n : ℝ)) *
        (if early j then 0 else 1 / (n : ℝ)) * min (p i) (p j)) =
    (fun i => (∑ j : Fin n,
      if early i then 0 else if early j then 0 else min (p i) (p j)) /
        (n : ℝ) ^ 2) by
      funext i
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      cases hi : early i <;> cases hj : early j <;>
        simp [hi, hj, hnR] <;> field_simp [hnR]]
  rw [← Finset.sum_div, ← hfull]

theorem stationaryScalarCost_eq_finiteFluid
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (early : Fin n → Bool)
    (haPos : 0 < weightedMass (earlyJobWeight early)) :
    stationaryScalarCost n
        (earlyMassCount early)
        ((∑ i, discoveryBlock p early i) - n)
        (classifiedLateWork (baseClassifiedJobs p early))
        (classifiedLatePairMin (baseClassifiedJobs p early)) =
      (n : ℝ) ^ 2 *
          stationaryFluidCost
            ((1 + weightedMoment (earlyJobWeight early) p) /
              weightedMass (earlyJobWeight early))
            (weightedMass (earlyJobWeight early))
            (weightedMinPair (lateJobWeight early) p) +
        (earlyMassCount early + ∑ i, p i) / 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [stationaryScalarCost_eq_normalized hnR]
  have ha := earlyMassCount_div_eq_weightedMass hn early
  have hm := discoveryWork_sub_card_div_eq_weightedMoment hn p early
  have hlate := weightedMinPair_lateJobWeight_eq hn p early
  have hsum := classifiedLateWork_base_add_earlyWork p early
  have hePos : 0 < earlyMassCount early := by
    have hdiv : 0 < earlyMassCount early / (n : ℝ) := by
      rw [ha]
      exact haPos
    exact (div_pos_iff_of_pos_right (show 0 < (n : ℝ) by positivity)).mp hdiv
  unfold stationaryFluidCost
  rw [← ha, ← hm, hlate]
  field_simp [hnR, hePos.ne']
  nlinarith

theorem baseClassifiedJobs_split_eq
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) :
    baseClassifiedJobs
        (splitSampleProcessing k r p)
        (splitSampleEarly k r d η hη p) ++
      baseClassifiedJobs
        (splitRestProcessing k r p)
        (splitRestEarly k r d η hη p) =
      baseClassifiedJobs p (learnedEarlyFor k r d η hη p) := by
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

theorem uniformStationaryScalarCost_learnedSplit_eq
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) :
    uniformStationaryScalarCost
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
              (splitRestProcessing k r p) (splitRestEarly k r d η hη p))) =
      stationaryScalarCost (k + r)
        (earlyMassCount (learnedEarlyFor k r d η hη p))
        ((∑ i, discoveryBlock p (learnedEarlyFor k r d η hη p) i) -
          (k + r))
        (classifiedLateWork
          (baseClassifiedJobs p (learnedEarlyFor k r d η hη p)))
        (classifiedLatePairMin
          (baseClassifiedJobs p (learnedEarlyFor k r d η hη p))) := by
  rw [uniformStationaryScalarCost_split_eq]
  have hjobs := baseClassifiedJobs_split_eq k r d η hη p
  have hearly :
      earlyMassCount (splitSampleEarly k r d η hη p) +
          earlyMassCount (splitRestEarly k r d η hη p) =
        earlyMassCount (learnedEarlyFor k r d η hη p) := by
    rw [← classifiedEarlyCount_ofFn_eq_massCount
          (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p),
      ← classifiedEarlyCount_ofFn_eq_massCount
          (splitRestProcessing k r p) (splitRestEarly k r d η hη p),
      ← classifiedEarlyCount_append, hjobs,
      classifiedEarlyCount_ofFn_eq_massCount]
  have hwork :
      (∑ i, discoveryBlock
          (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) i) +
          (∑ i, discoveryBlock
            (splitRestProcessing k r p) (splitRestEarly k r d η hη p) i) =
        ∑ i, discoveryBlock p (learnedEarlyFor k r d η hη p) i := by
    rw [← classifiedDiscoveryWork_ofFn
          (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p),
      ← classifiedDiscoveryWork_ofFn
          (splitRestProcessing k r p) (splitRestEarly k r d η hη p),
      ← classifiedDiscoveryWork_append, hjobs,
      classifiedDiscoveryWork_ofFn]
  rw [hearly, hwork, hjobs]

theorem earlyMassCount_nonneg
    {n : ℕ} (early : Fin n → Bool) : 0 ≤ earlyMassCount early := by
  unfold earlyMassCount
  positivity

theorem earlyMassCount_le_card
    {n : ℕ} (early : Fin n → Bool) : earlyMassCount early ≤ n := by
  unfold earlyMassCount
  calc
    (∑ i : Fin n, if early i then (1 : ℝ) else 0) ≤
        ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases early i <;> simp
    _ = n := by simp

theorem discoveryWork_nonneg
    {n : ℕ} (p : Fin n → ℝ) (early : Fin n → Bool)
    (hp : ∀ i, 0 ≤ p i) :
    0 ≤ ∑ i, discoveryBlock p early i := by
  apply Finset.sum_nonneg
  intro i _
  unfold discoveryBlock
  cases early i
  · simp
  · simp
    linarith [hp i]

theorem learnedSample_discoveryWork_le
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, discoveryBlock
      (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) i) ≤
      17 * k := by
  calc
    (∑ i, discoveryBlock
        (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) i) ≤
        ∑ _i : Fin k, (17 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold discoveryBlock
      cases hearly : splitSampleEarly k r d η hη p i
      · norm_num
      · have hle : splitSampleProcessing k r p i ≤ 16 := by
          apply Online.learnedClassifiesEarly_processing_le_sixteen hη
            (hp (Fin.castAdd r i))
          simpa [splitSampleEarly, splitSampleProcessing, learnedEarlyFor]
            using hearly
        simp [hearly]
        linarith
    _ = 17 * k := by simp; ring

/-- The exact conditional sample-first scalar is at most the normalized
stationary comparator plus the cross-block implementation overhead. -/
theorem learnedSampleFirstScalarCost_le_stationary_add
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Online.Label (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    learnedSampleFirstScalarCost k r d η hη p ≤
      stationaryScalarCost (k + r)
        (earlyMassCount (learnedEarlyFor k r d η hη p))
        ((∑ i, discoveryBlock p (learnedEarlyFor k r d η hη p) i) -
          (k + r))
        (classifiedLateWork
          (baseClassifiedJobs p (learnedEarlyFor k r d η hη p)))
        (classifiedLatePairMin
          (baseClassifiedJobs p (learnedEarlyFor k r d η hη p))) +
        17 * (k + r : ℝ) * k / 2 := by
  let eSample := earlyMassCount (splitSampleEarly k r d η hη p)
  let eRest := earlyMassCount (splitRestEarly k r d η hη p)
  let workSample := ∑ i, discoveryBlock
    (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) i
  let workRest := ∑ i, discoveryBlock
    (splitRestProcessing k r p) (splitRestEarly k r d η hη p) i
  have hsampleUniform := sampleFirstScalarCost_le_uniform_add
    (eSample := eSample) (eRest := eRest)
    (workSample := workSample) (workRest := workRest)
    (selfSample := earlySelfWork
      (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p))
    (selfRest := earlySelfWork
      (splitRestProcessing k r p) (splitRestEarly k r d η hη p))
    (lateCost := classifiedLateCost
      (baseClassifiedJobs
          (splitSampleProcessing k r p) (splitSampleEarly k r d η hη p) ++
        baseClassifiedJobs
          (splitRestProcessing k r p) (splitRestEarly k r d η hη p)))
    (earlyMassCount_nonneg _) (discoveryWork_nonneg _ _
      (fun i => hp (Fin.natAdd k i)))
  have hcross := sampleFirst_cross_overhead_B32
    (eRest := eRest) (workSample := workSample)
    (n := (k + r : ℝ)) (k := (k : ℝ))
    (earlyMassCount_nonneg _)
    (earlyMassCount_le_card (splitRestEarly k r d η hη p) |>.trans
      (by exact_mod_cast Nat.le_add_left r k))
    (discoveryWork_nonneg _ _ (fun i => hp (Fin.castAdd r i)))
    (learnedSample_discoveryWork_le k r d η hη p hp)
    (by positivity)
  dsimp [learnedSampleFirstScalarCost, eSample, eRest,
    workSample, workRest] at hsampleUniform hcross ⊢
  rw [uniformStationaryScalarCost_learnedSplit_eq] at hsampleUniform
  linarith

/-! ## The transcript histogram is the concentration histogram -/

def firstBlockPositions (k r : ℕ) : Finset (Fin (k + r)) :=
  Finset.univ.map (Fin.castAddEmb r)

@[simp] theorem firstBlockPositions_card (k r : ℕ) :
    (firstBlockPositions k r).card = k := by
  simp [firstBlockPositions]

theorem firstBlockPositions_nonempty
    {k r : ℕ} (hk : 0 < k) : (firstBlockPositions k r).Nonempty := by
  apply Finset.card_pos.mp
  simp [hk]

theorem firstBlockPositions_val_lt
    (k r : ℕ) (i : ↥(firstBlockPositions k r)) : i.val.val < k := by
  obtain ⟨j, _hj, heq⟩ := Finset.mem_map.mp i.property
  simpa [← heq] using j.isLt

def firstBlockEquiv (k r : ℕ) :
    Fin k ≃ ↥(firstBlockPositions k r) where
  toFun i := ⟨Fin.castAdd r i, by
    unfold firstBlockPositions
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  invFun i := ⟨i.val.val, firstBlockPositions_val_lt k r i⟩
  left_inv i := by rfl
  right_inv i := by
    apply Subtype.ext
    rfl

theorem permutationSampleSum_firstBlock_refl
    (k r : ℕ) (y : Fin (k + r) → ℝ) :
    permutationSampleSum (firstBlockPositions k r) y (Equiv.refl _) =
      ∑ i : Fin k, y (Fin.castAdd r i) := by
  unfold permutationSampleSum
  have h := Equiv.sum_comp (firstBlockEquiv k r)
    (fun i : ↥(firstBlockPositions k r) => y i.val)
  simpa using h.symm

theorem length_filter_ofFn
    {α : Type*} {n : ℕ} (f : Fin n → α) (pred : α → Bool) :
    ((List.ofFn f).filter pred).length =
      ∑ i : Fin n, if pred (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.filter_cons, Fin.sum_univ_succ]
      split <;> simp [ih] <;> omega

theorem resultCategoryFraction_fixedTake_eq_sampleCategoryFraction
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) (b : QuantizedCategory d) :
    Online.resultCategoryFraction d η hη
        ((Online.fixedTestResults p).take k) b =
      sampleCategoryFraction (firstBlockPositions k r)
        (categoryClass (fun i => quantizedCategory d η (p i) hη) b)
        (Equiv.refl _) := by
  have hvalues := map_snd_fixedTestResults_take_add k r p
  unfold Online.resultCategoryFraction sampleCategoryFraction
  have hfilterNat :
      (List.filter (fun result =>
          quantizedCategory d η result.2 hη = b)
          ((Online.fixedTestResults p).take k)).length =
        (List.filter (fun value =>
          quantizedCategory d η value hη = b)
          (((Online.fixedTestResults p).take k).map Prod.snd)).length := by
    induction (Online.fixedTestResults p).take k with
    | nil => rfl
    | cons x xs ih => simp only [List.filter_cons, List.map_cons]; split <;> simp_all
  have hfilter :
      ((List.filter (fun result =>
          quantizedCategory d η result.2 hη = b)
          ((Online.fixedTestResults p).take k)).length : ℝ) =
        ((List.filter (fun value =>
          quantizedCategory d η value hη = b)
          (((Online.fixedTestResults p).take k).map Prod.snd)).length : ℝ) := by
    exact_mod_cast hfilterNat
  have hlength : ((Online.fixedTestResults p).take k).length = k := by
    simp [Online.fixedTestResults_length]
  rw [hfilter, hvalues, hlength]
  rw [length_filter_ofFn]
  rw [permutationSampleSum_firstBlock_refl, firstBlockPositions_card]
  unfold categoryIndicator categoryClass
  have hcount :
      (∑ i : Fin k,
        if decide (quantizedCategory d η (p (Fin.castAdd r i)) hη = b)
          then (1 : ℕ) else 0) =
      ∑ i : Fin k,
        if Fin.castAdd r i ∈
          (Finset.univ.filter fun a =>
            quantizedCategory d η (p a) hη = b)
          then (1 : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hcountR :
      ((∑ i : Fin k,
        if decide (quantizedCategory d η (p (Fin.castAdd r i)) hη = b)
          then (1 : ℕ) else 0 : ℕ) : ℝ) =
      ∑ i : Fin k,
        if Fin.castAdd r i ∈
          (Finset.univ.filter fun a =>
            quantizedCategory d η (p a) hη = b)
          then (1 : ℝ) else 0 := by
    exact_mod_cast hcount
  rw [hcountR]

theorem resultCategoryFraction_fixedTake_eq_sampleHistogram
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) :
    Online.resultCategoryFraction d η hη
        ((Online.fixedTestResults p).take k) =
      fun b => sampleCategoryFraction (firstBlockPositions k r)
        (categoryClass (fun i => quantizedCategory d η (p i) hη) b)
        (Equiv.refl _) := by
  funext b
  exact resultCategoryFraction_fixedTake_eq_sampleCategoryFraction
    k r d η hη p b

theorem learnedEarlyFor_eq_learnedEarly
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) {θHat : ℝ}
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = some θHat) :
    learnedEarlyFor k r d η hη p = learnedEarly d η hη p θHat := by
  funext i
  unfold learnedEarlyFor Online.learnedClassifiesEarly learnedEarly
  rw [hlearn]

/-- Complete deterministic good-learned bound for the conditional scalar
cost extracted from the operational run. -/
theorem learned_good_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θHat : ℝ}
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = some θHat)
    (hgood : histogramL1Error (firstBlockPositions k r)
      (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) ≤
        1 / (32 * 33)) :
    learnedSampleFirstScalarCost k r d η hη p ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (1024 * histogramL1Error (firstBlockPositions k r)
            (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) +
            22 * η) +
        17 * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let sample := firstBlockPositions k r
  let c := fun i : Fin (k + r) => quantizedCategory d η (p i) hη
  let Δ := histogramL1Error sample c (Equiv.refl _)
  let earlyθ := learnedEarly d η hη p θHat
  let early := learnedEarlyFor k r d η hη p
  have hearly : early = earlyθ :=
    learnedEarlyFor_eq_learnedEarly k r d η hη p hlearn
  have hclosure := Online.learnedThresholdFromResults_closure_certificate
    d η hη ((Online.fixedTestResults p).take k) hlearn
  dsimp only at hclosure
  have hhist := resultCategoryFraction_fixedTake_eq_sampleHistogram
    k r d η hη p
  rw [hhist] at hclosure
  have hfluidθ := goodLearned_fluid_certificate_B32
    hn sample (Equiv.refl _) d hη hcutoff p hp
    hclosure.1 hclosure.2.1 hclosure.2.2.1 hclosure.2.2.2 hgood
  dsimp only at hfluidθ
  have htransfer := learned_histogram_transfer_B32
    sample (Equiv.refl _) d hη hcutoff hclosure.2.1 p hp
  dsimp only at htransfer
  have haLower : 1 / 32 ≤ weightedMass (earlyJobWeight earlyθ) := by
    apply learned_mass_lower_B32 hclosure.2.2.1 hgood
    rw [learnedEarly_mass_eq_populationMass hn d hη p]
    simpa [Fintype.card_fin, sample, c] using htransfer.1
  have haPos : 0 < weightedMass (earlyJobWeight earlyθ) :=
    lt_of_lt_of_le (by norm_num) haLower
  have hscalarEq := stationaryScalarCost_eq_finiteFluid
    hn p earlyθ haPos
  have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
  have hs : 0 ≤ 1536 * Δ + 33 * η := by
    have hΔ0 : 0 ≤ Δ := by
      dsimp [Δ, sample, c]
      unfold histogramL1Error
      positivity
    positivity
  have hstationary :
      stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) ≤
        4 / 3 * finiteObligatoryOPT p +
          (k + r : ℝ) ^ 2 * (1024 * Δ + 22 * η) := by
    have hfinite := finite_goodLearned_cost_bound
      (n := (k + r : ℝ))
      (e := earlyMassCount earlyθ)
      (sumP := ∑ i, p i)
      (P := stationaryFluidCost
        ((1 + weightedMoment (earlyJobWeight earlyθ) p) /
          weightedMass (earlyJobWeight earlyθ))
        (weightedMass (earlyJobWeight earlyθ))
        (weightedMinPair (lateJobWeight earlyθ) p))
      (O := finiteOfflineFluid p)
      (s := 1536 * Δ + 33 * η)
      (ideal := stationaryScalarCost (k + r)
        (earlyMassCount earlyθ)
        ((∑ i, discoveryBlock p earlyθ i) - (k + r))
        (classifiedLateWork (baseClassifiedJobs p earlyθ))
        (classifiedLatePairMin (baseClassifiedJobs p earlyθ)))
      (actual := stationaryScalarCost (k + r)
        (earlyMassCount earlyθ)
        ((∑ i, discoveryBlock p earlyθ i) - (k + r))
        (classifiedLateWork (baseClassifiedJobs p earlyθ))
        (classifiedLatePairMin (baseClassifiedJobs p earlyθ)))
      (overhead := 0)
      (finiteOpt := finiteObligatoryOPT p)
      (by positivity) (earlyMassCount_nonneg _)
      (by simpa only [Nat.cast_add] using earlyMassCount_le_card earlyθ)
      hsum hs hfluidθ
      (by simpa only [Nat.cast_add] using hscalarEq) (by linarith)
      (by unfold finiteObligatoryOPT finiteOfflineCorrection; rw [Nat.cast_add])
    dsimp [Δ, sample, c] at hfinite ⊢
    nlinarith
  have hsample := learnedSampleFirstScalarCost_le_stationary_add
    k r d η hη p hp
  rw [learnedEarlyFor_eq_learnedEarly k r d η hη p hlearn] at hsample
  dsimp [Δ, sample, c] at hstationary ⊢
  linarith

theorem stationaryScalarCost_eq_directFiniteFluid
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (early : Fin n → Bool) :
    stationaryScalarCost n
        (earlyMassCount early)
        ((∑ i, discoveryBlock p early i) - n)
        (classifiedLateWork (baseClassifiedJobs p early))
        (classifiedLatePairMin (baseClassifiedJobs p early)) =
      (n : ℝ) ^ 2 *
          ((1 + weightedMoment (earlyJobWeight early) p) *
              (1 - weightedMass (earlyJobWeight early) / 2) +
            weightedMinPair (lateJobWeight early) p / 2) +
        (earlyMassCount early + ∑ i, p i) / 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [stationaryScalarCost_eq_normalized hnR]
  have ha := earlyMassCount_div_eq_weightedMass hn early
  have hm := discoveryWork_sub_card_div_eq_weightedMoment hn p early
  have hlate := weightedMinPair_lateJobWeight_eq hn p early
  have hsum := classifiedLateWork_base_add_earlyWork p early
  rw [← ha, ← hm, hlate]
  field_simp [hnR]
  nlinarith

/-- If every job is deferred, the stationary comparator is exactly the
test-all-then-SPT schedule: it exceeds clairvoyant SPT only by the ordering
of the unit tests. -/
theorem stationaryScalarCost_allLate_eq_opt_add
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) :
    stationaryScalarCost n
        (earlyMassCount (fun _ : Fin n => false))
        ((∑ i, discoveryBlock p (fun _ : Fin n => false) i) - n)
        (classifiedLateWork (baseClassifiedJobs p (fun _ : Fin n => false)))
        (classifiedLatePairMin (baseClassifiedJobs p (fun _ : Fin n => false))) =
      finiteObligatoryOPT p + ((n : ℝ) ^ 2 - n) / 2 := by
  have hscalar := stationaryScalarCost_eq_directFiniteFluid hn p (fun _ => false)
  rw [hscalar]
  unfold finiteObligatoryOPT finiteOfflineFluid finiteOfflineCorrection
  change
    (n : ℝ) ^ 2 *
          ((1 + weightedMoment (fun _ : Fin n => 0) p) *
              (1 - weightedMass (fun _ : Fin n => 0) / 2) +
            weightedMinPair (uniformJobWeight n) p / 2) +
        (earlyMassCount (fun _ : Fin n => false) + ∑ i, p i) / 2 = _
  simp [weightedMoment, weightedMass, earlyMassCount]
  ring

theorem stationaryScalarCost_allLate_le_opt_add_half
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) :
    stationaryScalarCost n
        (earlyMassCount (fun _ : Fin n => false))
        ((∑ i, discoveryBlock p (fun _ : Fin n => false) i) - n)
        (classifiedLateWork (baseClassifiedJobs p (fun _ : Fin n => false)))
        (classifiedLatePairMin (baseClassifiedJobs p (fun _ : Fin n => false))) ≤
      finiteObligatoryOPT p + (n : ℝ) ^ 2 / 2 := by
  rw [stationaryScalarCost_allLate_eq_opt_add hn p]
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  linarith

theorem finite_boundedEarly_directFluid_le_offline_add_eight
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (early : Fin n → Bool)
    (hEarly : ∀ i, early i = true → p i ≤ 16)
    (hordered : ∀ i j, early i = true → early j = false → p i ≤ p j) :
    (1 + weightedMoment (earlyJobWeight early) p) *
          (1 - weightedMass (earlyJobWeight early) / 2) +
        weightedMinPair (lateJobWeight early) p / 2 ≤
      finiteOfflineFluid p + 8 := by
  let a := weightedMass (earlyJobWeight early)
  let m := weightedMoment (earlyJobWeight early) p
  let h := weightedMass (lateJobWeight early)
  let KE := weightedMinPair (earlyJobWeight early) p
  let KL := weightedMinPair (lateJobWeight early) p
  have ha0 : 0 ≤ a := by
    dsimp [a]
    unfold weightedMass earlyJobWeight
    positivity
  have hmass := weightedMass_late_eq_one_sub_early hn early
  have ha1 : a ≤ 1 := by
    have hh0 : 0 ≤ h := by
      dsimp [h]
      unfold weightedMass lateJobWeight
      positivity
    dsimp [a, h] at hmass ⊢
    linarith
  have hm16 : m ≤ 16 * a := by
    unfold m a weightedMoment weightedMass
    calc
      (∑ i, earlyJobWeight early i * p i) ≤
          ∑ i, earlyJobWeight early i * 16 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : early i = true
        · exact mul_le_mul_of_nonneg_left (hEarly i hi) (by
            simp [earlyJobWeight, hi])
        · have hiFalse : early i = false := Bool.eq_false_of_not_eq_true hi
          simp [earlyJobWeight, hiFalse]
      _ = 16 * ∑ i, earlyJobWeight early i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hKE0 : 0 ≤ KE := by
    dsimp [KE]
    unfold weightedMinPair earlyJobWeight
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (le_min (hp i) (hp j))
  have hsplit := uniformMinPair_split early p hordered
  have hcorner : 1 - a + a * m - KE ≤ 16 := by
    have ham := mul_le_mul_of_nonneg_left hm16 ha0
    have haa : a ^ 2 ≤ a := by nlinarith
    nlinarith
  unfold finiteOfflineFluid
  rw [hsplit]
  dsimp [a, m, h, KE, KL] at hmass hcorner ⊢
  nlinarith

theorem learned_crude_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    {θHat : ℝ}
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = some θHat) :
    learnedSampleFirstScalarCost k r d η hη p ≤
      finiteObligatoryOPT p + 8 * (k + r : ℝ) ^ 2 +
        17 * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  let early := learnedEarlyFor k r d η hη p
  let earlyθ := learnedEarly d η hη p θHat
  have hearly : early = earlyθ :=
    learnedEarlyFor_eq_learnedEarly k r d η hη p hlearn
  have hclosure := Online.learnedThresholdFromResults_closure_certificate
    d η hη ((Online.fixedTestResults p).take k) hlearn
  dsimp only at hclosure
  have hEarly : ∀ i, earlyθ i = true → p i ≤ 16 := by
    intro i hi
    have hpTheta : p i ≤ θHat :=
      quantized_early_actual_le_threshold d hη (hp i) hclosure.2.1
        (by simpa [earlyθ, learnedEarly] using hi)
    exact hpTheta.trans hclosure.2.1
  have hordered : ∀ i j, earlyθ i = true → earlyθ j = false → p i ≤ p j := by
    intro i j hi hj
    have hiSel : thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) := by
      simpa [earlyθ, learnedEarly] using hi
    have hjLate : ¬thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p j) hη) := by
      simpa [earlyθ, learnedEarly] using hj
    exact quantized_threshold_split_ordered_B32 d hη hcutoff
      hclosure.1 hclosure.2.1 (hp i) (hp j) hiSel hjLate
  have hfluid := finite_boundedEarly_directFluid_le_offline_add_eight
    hn p hp earlyθ hEarly hordered
  have hscalarEq := stationaryScalarCost_eq_directFiniteFluid hn p earlyθ
  have hcorr : (earlyMassCount earlyθ + ∑ i, p i) / 2 ≤
      finiteOfflineCorrection p := by
    unfold finiteOfflineCorrection
    have he := earlyMassCount_le_card earlyθ
    nlinarith
  have hstationary :
      stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) ≤
        finiteObligatoryOPT p + 8 * (k + r : ℝ) ^ 2 := by
    unfold finiteObligatoryOPT
    simp only [Nat.cast_add]
    rw [show stationaryScalarCost (k + r)
          (earlyMassCount earlyθ)
          ((∑ i, discoveryBlock p earlyθ i) - (k + r))
          (classifiedLateWork (baseClassifiedJobs p earlyθ))
          (classifiedLatePairMin (baseClassifiedJobs p earlyθ)) =
        (↑k + ↑r) ^ 2 *
            ((1 + weightedMoment (earlyJobWeight earlyθ) p) *
                (1 - weightedMass (earlyJobWeight earlyθ) / 2) +
              weightedMinPair (lateJobWeight earlyθ) p / 2) +
          (earlyMassCount earlyθ + ∑ i, p i) / 2 by
      simpa only [Nat.cast_add] using hscalarEq]
    have hn2 : 0 ≤ (↑k + ↑r : ℝ) ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left hfluid hn2
    nlinarith
  have hsample := learnedSampleFirstScalarCost_le_stationary_add
    k r d η hη p hp
  rw [learnedEarlyFor_eq_learnedEarly k r d η hη p hlearn] at hsample
  linarith

theorem learnedEarlyFor_eq_false_of_none
    (k r d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ)
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = none) :
    learnedEarlyFor k r d η hη p = fun _ => false := by
  funext i
  unfold learnedEarlyFor Online.learnedClassifiesEarly
  rw [hlearn]

/-- The fallback branch is test-all-then-SPT, up to the same harmless
sample-first comparator allowance used for the learned branch. -/
theorem fallback_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = none) :
    learnedSampleFirstScalarCost k r d η hη p ≤
      finiteObligatoryOPT p + (k + r : ℝ) ^ 2 / 2 +
        17 * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  have hsample := learnedSampleFirstScalarCost_le_stationary_add
    k r d η hη p hp
  rw [learnedEarlyFor_eq_false_of_none k r d η hη p hlearn] at hsample
  have hstationary := stationaryScalarCost_allLate_le_opt_add_half hn p
  simp only [Nat.cast_add] at hstationary
  linarith

/-- The category frequencies seen in any nonempty permutation sample sum to
one. -/
theorem sum_sampleCategoryFraction_eq_one
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (hS : S.Nonempty) (c : α → β)
    (σ : Equiv.Perm α) :
    ∑ b, sampleCategoryFraction S (categoryClass c b) σ = 1 := by
  unfold sampleCategoryFraction permutationSampleSum categoryIndicator
  rw [← Finset.sum_div]
  simp only [categoryClass, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  simp [hcard]

theorem subsetMass_sampleCategoryFraction_le_one
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (hS : S.Nonempty) (c : α → β)
    (σ : Equiv.Perm α) (J : Finset β) :
    subsetMass
        (fun b => sampleCategoryFraction S (categoryClass c b) σ) J ≤ 1 := by
  have hnonneg : ∀ b,
      0 ≤ sampleCategoryFraction S (categoryClass c b) σ := by
    intro b
    unfold sampleCategoryFraction permutationSampleSum categoryIndicator
    positivity
  calc
    subsetMass
        (fun b => sampleCategoryFraction S (categoryClass c b) σ) J ≤
        ∑ b, sampleCategoryFraction S (categoryClass c b) σ := by
      unfold subsetMass
      exact Finset.sum_le_univ_sum_of_nonneg hnonneg
    _ = 1 := sum_sampleCategoryFraction_eq_one S hS c σ

/-- Changing a probability mass and its nonnegative first moment by
`Δ` and `BΔ` changes the corresponding completion density by at most
`(1+B)Δ`. -/
theorem subsetDensity_le_of_mass_moment_error
    {a aHat m mHat Δ B : ℝ}
    (ha0 : 0 ≤ a) (haHat0 : 0 ≤ aHat) (haHat1 : aHat ≤ 1)
    (hm0 : 0 ≤ m) (hmHat0 : 0 ≤ mHat)
    (hΔ : 0 ≤ Δ) (hB : 0 ≤ B)
    (hMass : |a - aHat| ≤ Δ)
    (hMoment : |m - mHat| ≤ B * Δ) :
    a / (1 + m) ≤ aHat / (1 + mHat) + (1 + B) * Δ := by
  have hx : 0 < 1 + m := by linarith
  have hy : 0 < 1 + mHat := by linarith
  have haUpper : a ≤ aHat + Δ := by
    have := le_trans (le_abs_self (a - aHat)) hMass
    linarith
  have hmUpper : mHat - m ≤ B * Δ := by
    have := le_trans (le_abs_self (mHat - m)) (by
      simpa [abs_sub_comm] using hMoment)
    exact this
  have hBΔ : 0 ≤ B * Δ := mul_nonneg hB hΔ
  have hmomentTerm : aHat * (mHat - m) ≤ B * Δ := by
    calc
      aHat * (mHat - m) ≤ aHat * (B * Δ) :=
        mul_le_mul_of_nonneg_left hmUpper haHat0
      _ ≤ 1 * (B * Δ) :=
        mul_le_mul_of_nonneg_right haHat1 hBΔ
      _ = B * Δ := by ring
  have hy_le_xy : 1 + mHat ≤ (1 + m) * (1 + mHat) := by
    nlinarith [mul_nonneg hm0 hy.le]
  have hdeltaTerm : Δ * (1 + mHat) ≤
      Δ * ((1 + m) * (1 + mHat)) :=
    mul_le_mul_of_nonneg_left hy_le_xy hΔ
  have hxyOne : 1 ≤ (1 + m) * (1 + mHat) := by
    nlinarith [mul_nonneg hm0 hmHat0]
  have hBterm : B * Δ ≤ B * Δ * ((1 + m) * (1 + mHat)) := by
    nlinarith [mul_nonneg hBΔ (sub_nonneg.mpr hxyOne)]
  have hnum :
      (aHat + Δ) * (1 + mHat) ≤
        (aHat + (1 + B) * Δ * (1 + mHat)) * (1 + m) := by
    nlinarith
  calc
    a / (1 + m) ≤ (aHat + Δ) / (1 + m) :=
      (div_le_div_iff_of_pos_right hx).2 haUpper
    _ ≤ aHat / (1 + mHat) + (1 + B) * Δ := by
      rw [show aHat / (1 + mHat) + (1 + B) * Δ =
          (aHat + (1 + B) * Δ * (1 + mHat)) / (1 + mHat) by
        field_simp [hy.ne']]
      exact (div_le_div_iff₀ hx hy).2 hnum

/-- Entering fallback means that even the best empirical category subset has
completion density strictly below `1/16`. -/
theorem resultMaximumDensity_fallback_lt
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Online.Label n × ℝ))
    (hlearn : Online.learnedThresholdFromResults? d η hη results = none) :
    subsetDensity
        (Online.resultCategoryFraction d η hη results)
        (quantizedRepresentative d η)
        (Online.resultMaximumDensitySet d η hη results) < 1 / 16 := by
  let μ := Online.resultCategoryFraction d η hη results
  let q := quantizedRepresentative d η
  let selected := Online.resultMaximumDensitySet d η hη results
  have hμ : ∀ b, 0 ≤ μ b :=
    Online.resultCategoryFraction_nonneg d η hη results
  have hq : ∀ b, 0 ≤ q b :=
    quantizedRepresentative_nonneg d hη.le
  have ha0 : 0 ≤ subsetMass μ selected := subsetMass_nonneg hμ selected
  have hm0 : 0 ≤ subsetMoment μ q selected :=
    subsetMoment_nonneg hμ hq selected
  unfold Online.learnedThresholdFromResults? at hlearn
  dsimp only at hlearn
  split at hlearn
  next ha =>
    split at hlearn
    next hθ => simp at hlearn
    next hθ =>
      have hθlt : 16 < (1 + subsetMoment μ q selected) /
          subsetMass μ selected := lt_of_not_ge hθ
      unfold subsetDensity
      have hden : 0 < 1 + subsetMoment μ q selected := by linarith
      apply (div_lt_iff₀ hden).2
      have hcross := (lt_div_iff₀ ha).1 hθlt
      norm_num at hcross ⊢
      nlinarith
  next ha =>
    have haZero : subsetMass μ selected = 0 := by
      exact le_antisymm (le_of_not_gt ha) ha0
    unfold subsetDensity
    rw [haZero]
    norm_num

/-- A maximum-density subset has positive mass whenever the ground set is
nonempty and every item has positive mass. -/
theorem maximumDensitySubset_mass_pos
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    {μ q : β → ℝ} {S : Finset β}
    (hμ : ∀ b, 0 < μ b) (hq : ∀ b, 0 ≤ q b)
    (hmax : IsMaximumDensitySubset μ q S) :
    0 < subsetMass μ S := by
  have hμ0 : ∀ b, 0 ≤ μ b := fun b => (hμ b).le
  have ha0 := subsetMass_nonneg hμ0 S
  by_contra hnot
  have ha : subsetMass μ S = 0 := le_antisymm (le_of_not_gt hnot) ha0
  let b : β := Classical.choice inferInstance
  have hsingle : 0 < subsetDensity μ q {b} := by
    simp [subsetDensity, subsetMass, subsetMoment]
    exact div_pos (hμ b) (by
      have := mul_nonneg (hμ b).le (hq b)
      linarith)
  have hzeroDensity : subsetDensity μ q S = 0 := by
    unfold subsetDensity
    rw [ha, zero_div]
  have hle := hmax {b}
  rw [hzeroDensity] at hle
  exact False.elim ((not_lt_of_ge hle) hsingle)

/-- Rounding a true threshold split upward by at most one bin and then
closing whole bins preserves density up to replacing `θ` by `θ+η`. -/
theorem quantized_threshold_gridDensity_lower
    {n : ℕ} (hn : 0 < n)
    (d : ℕ) {η θ : ℝ} (hη : 0 < η)
    (hcutoff : (d : ℝ) * η = 32)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hθ : 0 < θ) (hwithin : θ + η ≤ 32)
    (hdensity :
      1 + selectedMoment (uniformJobWeight n) p (fun i => p i ≤ θ) =
        θ * selectedMass (uniformJobWeight n) (fun i => p i ≤ θ)) :
    1 / (θ + η) ≤
      subsetDensity
        (fun b => ((categoryClass
          (fun i => quantizedCategory d η (p i) hη) b).card : ℝ) / n)
        (quantizedRepresentative d η)
        (Finset.univ.filter fun b =>
          quantizedRepresentative d η b ≤ θ + η) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let c := fun i : Fin n => quantizedCategory d η (p i) hη
  let q := quantizedRepresentative d η
  let μ := fun b : QuantizedCategory d =>
    ((categoryClass c b).card : ℝ) / n
  let selectedGrid := fun b : QuantizedCategory d => q b ≤ θ + η
  let J := Finset.univ.filter selectedGrid
  let trueSelected := fun i : Fin n => p i ≤ θ
  let a := selectedMass (uniformJobWeight n) trueSelected
  let m := selectedMoment (uniformJobWeight n) p trueSelected
  let A := selectedMass μ selectedGrid
  let M := selectedMoment μ q selectedGrid
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hθη : 0 < θ + η := add_pos hθ hη
  have hsub : ∀ i, trueSelected i → selectedGrid (c i) := by
    intro i hi
    dsimp [trueSelected, selectedGrid, c, q] at hi ⊢
    by_cases hzero : p i = 0
    · rw [hzero, quantizedCategory_zero d hη,
        quantizedRepresentative_zero]
      exact hθη.le
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hzero)
      have hcap : p i ≤ (d : ℝ) * η := by
        rw [hcutoff]
        linarith
      have hround := (quantized_rounding_bounds d hη hpos hcap).2
      linarith
  have hpoint : ∀ i,
      q (c i) * (if selectedGrid (c i) then 1 else 0) ≤
        p i * (if trueSelected i then 1 else 0) +
          η * (if trueSelected i then 1 else 0) +
          (θ + η) *
            ((if selectedGrid (c i) then 1 else 0) -
              (if trueSelected i then 1 else 0)) := by
    intro i
    by_cases hi : trueSelected i
    · have hgi := hsub i hi
      have hq : q (c i) < p i + η := by
        dsimp [trueSelected] at hi
        by_cases hzero : p i = 0
        · dsimp [c, q]
          rw [hzero, quantizedCategory_zero d hη,
            quantizedRepresentative_zero]
          simpa using hη
        · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hzero)
          have hcap : p i ≤ (d : ℝ) * η := by
            rw [hcutoff]
            linarith [hi, hwithin]
          exact (quantized_rounding_bounds d hη hpos hcap).2
      simp [hi, hgi]
      linarith
    · by_cases hgi : selectedGrid (c i)
      · have hq : q (c i) ≤ θ + η := hgi
        simp [hi, hgi]
        exact hq
      · simp [hi, hgi]
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
    hpoint i
  have hAeq : A =
      (∑ i, if selectedGrid (c i) then (1 : ℝ) else 0) / n := by
    dsimp [A, μ]
    simpa only [Fintype.card_fin] using
      (selectedMass_population_eq_jobAverage c selectedGrid)
  have hMeq : M =
      (∑ i, q (c i) * (if selectedGrid (c i) then 1 else 0)) / n := by
    dsimp [M, μ]
    simpa only [Fintype.card_fin] using
      (selectedMoment_population_eq_jobAverage c q selectedGrid)
  have haeq : a =
      (∑ i, if trueSelected i then (1 : ℝ) else 0) / n := by
    unfold a selectedMass uniformJobWeight
    rw [show (fun i : Fin n =>
        (1 / (n : ℝ)) * (if trueSelected i then 1 else 0)) =
      fun i => (if trueSelected i then (1 : ℝ) else 0) / n by
        funext i
        ring]
    rw [Finset.sum_div]
  have hmeq : m =
      (∑ i, p i * (if trueSelected i then 1 else 0)) / n := by
    unfold m selectedMoment uniformJobWeight
    rw [show (fun i : Fin n =>
        (1 / (n : ℝ)) * p i * (if trueSelected i then 1 else 0)) =
      fun i => (p i * (if trueSelected i then 1 else 0)) / n by
        funext i
        ring]
    rw [Finset.sum_div]
  have hM : M ≤ m + η * a + (θ + η) * (A - a) := by
    rw [hMeq, hmeq, haeq, hAeq]
    calc
      (∑ i, q (c i) * (if selectedGrid (c i) then 1 else 0)) / n ≤
          (∑ i : Fin n,
            ((p i * (if trueSelected i then 1 else 0) +
                η * (if trueSelected i then 1 else 0)) +
              (θ + η) *
                ((if selectedGrid (c i) then 1 else 0) -
                  (if trueSelected i then 1 else 0)))) / n :=
        div_le_div_of_nonneg_right hsum (by positivity)
      _ =
          (∑ i, p i * (if trueSelected i then 1 else 0)) / n +
            η * ((∑ i, if trueSelected i then 1 else 0) / n) +
            (θ + η) *
              ((∑ i, if selectedGrid (c i) then 1 else 0) / n -
                (∑ i, if trueSelected i then 1 else 0) / n) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
        ring
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact Finset.sum_nonneg fun i _ => by
      exact mul_nonneg (by unfold uniformJobWeight; positivity) (by positivity)
  have haPos : 0 < a := by
    have hm0 : 0 ≤ m := by
      dsimp [m]
      exact Finset.sum_nonneg fun i _ => by
        exact mul_nonneg
          (mul_nonneg (by unfold uniformJobWeight; positivity) (hp i))
          (by positivity)
    have hdensityAM : 1 + m = θ * a := by
      simpa [a, m, trueSelected] using hdensity
    by_contra hnot
    have haZero : a = 0 :=
      le_antisymm (le_of_not_gt hnot) ha0
    nlinarith
  have hApos : 0 < A := by
    have haLeA : a ≤ A := by
      rw [haeq, hAeq]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : trueSelected i
      · simp [hi, hsub i hi]
      · by_cases hgi : selectedGrid (c i) <;> simp [hi, hgi]
    exact lt_of_lt_of_le haPos haLeA
  have hdenGrid : 1 + M ≤ A * (θ + η) := by
    have hdensityAM : 1 + m = θ * a := by
      simpa [a, m, trueSelected] using hdensity
    nlinarith
  have hM0 : 0 ≤ M := by
    unfold M selectedMoment
    exact Finset.sum_nonneg fun b _ =>
      mul_nonneg
        (mul_nonneg (by dsimp [μ]; positivity)
          (quantizedRepresentative_nonneg d hη.le b))
        (by positivity)
  have hdenPos : 0 < 1 + M := by linarith
  have hratio : 1 / (θ + η) ≤ A / (1 + M) := by
    rw [div_le_div_iff₀ hθη hdenPos]
    nlinarith
  unfold subsetDensity
  change 1 / (θ + η) ≤ subsetMass μ J / (1 + subsetMoment μ q J)
  have hmassJ : subsetMass μ J = A := by
    unfold J A subsetMass selectedMass selectedGrid
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : q b ≤ θ + η <;> simp [hb]
  have hmomJ : subsetMoment μ q J = M := by
    unfold J M subsetMoment selectedMoment selectedGrid
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : q b ≤ θ + η <;> simp [hb]
  rw [hmassJ, hmomJ]
  exact hratio

/-- The inverse density of a true maximum-density subset supplies the exact
threshold split used by the fallback lower bound on the offline fluid cost. -/
theorem maximumDensity_offlineFluid_lower_B32
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (S : Finset (Fin n))
    (hmax : IsMaximumDensitySubset (uniformJobWeight n) p S)
    (ha : 0 < subsetMass (uniformJobWeight n) S)
    (hθ : 8 ≤ (1 + subsetMoment (uniformJobWeight n) p S) /
      subsetMass (uniformJobWeight n) S) :
    57 / 16 ≤ finiteOfflineFluid p := by
  let θ := (1 + subsetMoment (uniformJobWeight n) p S) /
    subsetMass (uniformJobWeight n) S
  let early : Fin n → Bool := fun i => decide (p i ≤ θ)
  have hμ0 : ∀ i, 0 ≤ uniformJobWeight n i := by
    intro i
    unfold uniformJobWeight
    positivity
  have hclosure := maximumDensity_thresholdClosure_preserves
    hμ0 hp hmax ha (inverseDensity_identity ha)
  have hmassEarly : weightedMass (earlyJobWeight early) =
      selectedMass (uniformJobWeight n) (fun i => p i ≤ θ) := by
    unfold weightedMass selectedMass earlyJobWeight uniformJobWeight early
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i ≤ θ <;> simp [hi]
  have hmomentEarly : weightedMoment (earlyJobWeight early) p =
      selectedMoment (uniformJobWeight n) p (fun i => p i ≤ θ) := by
    unfold weightedMoment selectedMoment earlyJobWeight uniformJobWeight early
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i ≤ θ <;> simp [hi]
  have hdensity :
      weightedMoment (earlyJobWeight early) p =
        weightedMass (earlyJobWeight early) * θ - 1 := by
    rw [hmassEarly, hmomentEarly]
    have hclosure' :
        1 + selectedMoment (uniformJobWeight n) p (fun i => p i ≤ θ) =
          θ * selectedMass (uniformJobWeight n) (fun i => p i ≤ θ) := by
      simpa [thresholdClosure, θ] using hclosure
    nlinarith
  have hlateMass := weightedMass_late_eq_one_sub_early hn early
  have hEarlyPair :
      weightedMoment (earlyJobWeight early) p ^ 2 ≤
        θ * weightedMinPair (earlyJobWeight early) p := by
    apply weightedMoment_sq_le_threshold_mul_minPair_on_support
      (fun i => by unfold earlyJobWeight; positivity) hp
    intro i hweight
    have hi : early i = true := by
      cases hi : early i
      · simp [earlyJobWeight, hi] at hweight
      · rfl
    simpa [early] using hi
  have hLatePair :
      θ * weightedMass (lateJobWeight early) ^ 2 ≤
        weightedMinPair (lateJobWeight early) p := by
    apply threshold_mul_weightedMass_sq_le_minPair_on_support
      (fun i => by unfold lateJobWeight; positivity)
    intro i hweight
    have hi : early i = false := by
      cases hi : early i
      · rfl
      · simp [lateJobWeight, hi] at hweight
    have hiNot : ¬p i ≤ θ := by simpa [early] using hi
    exact (lt_of_not_ge hiNot).le
  have hlower := fallback_offlineFluid_lower_B32
    (θ := θ)
    (a := weightedMass (earlyJobWeight early))
    (m := weightedMoment (earlyJobWeight early) p)
    (h := weightedMass (lateJobWeight early))
    (Kearly := weightedMinPair (earlyJobWeight early) p)
    (Klate := weightedMinPair (lateJobWeight early) p)
    (by simpa [θ] using hθ) hlateMass hdensity hEarlyPair hLatePair
  have hordered : ∀ i j, early i = true → early j = false → p i ≤ p j := by
    intro i j hi hj
    have hi' : p i ≤ θ := by simpa [early] using hi
    have hj' : ¬p j ≤ θ := by simpa [early] using hj
    exact hi'.trans (le_of_lt (lt_of_not_ge hj'))
  have hsplit := uniformMinPair_split early p hordered
  unfold finiteOfflineFluid offlineFluidCost at hlower
  unfold finiteOfflineFluid
  rw [hsplit]
  simpa [add_assoc] using hlower

/-- On the good histogram event, fallback certifies that the instance itself
has large offline fluid value; hence test-all-then-SPT is already below
`4/3 OPT`. -/
theorem fallback_good_sampleFirstCost_bound
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (η : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hηUpper : η ≤ 32 / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hlearn : Online.learnedThresholdFromResults? d η hη
      ((Online.fixedTestResults p).take k) = none)
    (hgood : histogramL1Error (firstBlockPositions k r)
      (fun i => quantizedCategory d η (p i) hη) (Equiv.refl _) ≤
        1 / (32 * 33)) :
    learnedSampleFirstScalarCost k r d η hη p ≤
      4 / 3 * finiteObligatoryOPT p +
        17 * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let n := k + r
  let sample := firstBlockPositions k r
  let c := fun i : Fin n => quantizedCategory d η (p i) hη
  let q := quantizedRepresentative d η
  let Δ := histogramL1Error sample c (Equiv.refl _)
  let μTrue := uniformJobWeight n
  let trueSet := chosenMaximumDensitySubset μTrue p
  have hmaxTrue : IsMaximumDensitySubset μTrue p trueSet :=
    chosenMaximumDensitySubset_isMaximum μTrue p
  have hμTruePos : ∀ i, 0 < μTrue i := by
    intro i
    dsimp [μTrue, uniformJobWeight, n]
    positivity
  have haTrue : 0 < subsetMass μTrue trueSet :=
    maximumDensitySubset_mass_pos hμTruePos hp hmaxTrue
  let θ := (1 + subsetMoment μTrue p trueSet) /
    subsetMass μTrue trueSet
  have hθPos : 0 < θ := by
    dsimp [θ]
    exact inverseDensity_pos (fun i => (hμTruePos i).le) hp haTrue
  have htrueClosureRaw := maximumDensity_thresholdClosure_preserves
    (fun i => (hμTruePos i).le) hp hmaxTrue haTrue
    (inverseDensity_identity haTrue)
  have htrueClosure :
      1 + selectedMoment μTrue p (fun i => p i ≤ θ) =
        θ * selectedMass μTrue (fun i => p i ≤ θ) := by
    simpa [thresholdClosure, θ] using htrueClosureRaw
  let μPop := fun b : QuantizedCategory d =>
    ((categoryClass c b).card : ℝ) / n
  let μSample := fun b : QuantizedCategory d =>
    sampleCategoryFraction sample (categoryClass c b) (Equiv.refl _)
  let finiteCategory := fun b : QuantizedCategory d => q b ≤ 32
  let μPopFinite := fun b : QuantizedCategory d =>
    if finiteCategory b then μPop b else 0
  let gridSet := chosenMaximumDensitySubset μPopFinite q
  let J := gridSet.filter finiteCategory
  let ρGrid := subsetDensity μPopFinite q gridSet
  have hgridSetMax : IsMaximumDensitySubset μPopFinite q gridSet :=
    chosenMaximumDensitySubset_isMaximum μPopFinite q
  have hgridSetMass : subsetMass μPopFinite gridSet = subsetMass μPop J := by
    unfold subsetMass
    dsimp [μPopFinite, J, finiteCategory]
    simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  have hgridSetMoment : subsetMoment μPopFinite q gridSet =
      subsetMoment μPop q J := by
    unfold subsetMoment
    dsimp [μPopFinite, J, finiteCategory]
    simp only [Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hfinite : q b ≤ 32 <;> simp [hfinite]
  have hρGridEq : ρGrid = subsetDensity μPop q J := by
    unfold ρGrid subsetDensity
    rw [hgridSetMass, hgridSetMoment]
  have hgrid : θ + η ≤ 32 → 1 / (θ + η) ≤ ρGrid := by
    intro hwithin
    let T := Finset.univ.filter fun b : QuantizedCategory d => q b ≤ θ + η
    have hlower : 1 / (θ + η) ≤ subsetDensity μPop q T := by
      exact quantized_threshold_gridDensity_lower hn d hη hcutoff p hp
        hθPos hwithin (by simpa [μTrue, μPop, c, q, n, T] using htrueClosure)
    have hmassT : subsetMass μPopFinite T = subsetMass μPop T := by
      unfold subsetMass
      apply Finset.sum_congr rfl
      intro b hb
      have hbT : q b ≤ θ + η := (Finset.mem_filter.mp hb).2
      have hbFinite : finiteCategory b := hbT.trans hwithin
      simp [μPopFinite, hbFinite]
    have hmomT : subsetMoment μPopFinite q T = subsetMoment μPop q T := by
      unfold subsetMoment
      apply Finset.sum_congr rfl
      intro b hb
      have hbT : q b ≤ θ + η := (Finset.mem_filter.mp hb).2
      have hbFinite : finiteCategory b := hbT.trans hwithin
      simp [μPopFinite, hbFinite]
    have hTle := hgridSetMax T
    unfold ρGrid
    rw [show subsetDensity μPopFinite q T = subsetDensity μPop q T by
      unfold subsetDensity
      rw [hmassT, hmomT]] at hTle
    exact hlower.trans hTle
  have hgridLT : ρGrid < 3 / 32 := by
    have hhist := resultCategoryFraction_fixedTake_eq_sampleHistogram
      k r d η hη p
    have hsampleMax := resultMaximumDensity_fallback_lt
      d η hη ((Online.fixedTestResults p).take k) hlearn
    have hmaxSample := Online.resultMaximumDensitySet_isMaximum
      d η hη ((Online.fixedTestResults p).take k)
    have hsampleJ : subsetDensity μSample q J < 1 / 16 := by
      have hle := hmaxSample J
      have hlt := hle.trans_lt hsampleMax
      simpa [μSample, q, hhist] using hlt
    have hΔ0 : 0 ≤ Δ := by
      dsimp [Δ]
      unfold histogramL1Error
      positivity
    have hMass : |subsetMass μPop J - subsetMass μSample J| ≤ Δ := by
      have h := selectedMass_population_sample_le_histogramL1Error
        sample c (Equiv.refl _) (fun b => b ∈ J)
      simpa [μPop, μSample, Δ, n, subsetMass, selectedMass,
        Fintype.card_fin] using h
    have hMoment : |subsetMoment μPop q J - subsetMoment μSample q J| ≤
        32 * Δ := by
      have h := selectedMoment_population_sample_le_histogramL1Error
        (B := (32 : ℝ)) sample c (Equiv.refl _) q (fun b => b ∈ J)
        (by norm_num) (quantizedRepresentative_nonneg d hη.le)
        (fun b hb => by
          dsimp [J, finiteCategory] at hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          exact hb.2)
      simpa [μPop, μSample, Δ, n, subsetMoment, selectedMoment,
        Fintype.card_fin] using h
    have hPopMass0 : 0 ≤ subsetMass μPop J := by
      apply subsetMass_nonneg
      intro b
      dsimp [μPop]
      positivity
    have hSampleMass0 : 0 ≤ subsetMass μSample J := by
      apply subsetMass_nonneg
      intro b
      dsimp [μSample]
      unfold sampleCategoryFraction permutationSampleSum categoryIndicator
      positivity
    have hSampleMass1 : subsetMass μSample J ≤ 1 := by
      dsimp [μSample]
      exact subsetMass_sampleCategoryFraction_le_one sample
        (firstBlockPositions_nonempty (r := r) hk) c (Equiv.refl _) J
    have hPopMoment0 : 0 ≤ subsetMoment μPop q J :=
      subsetMoment_nonneg
        (fun b => by dsimp [μPop]; positivity)
        (quantizedRepresentative_nonneg d hη.le) J
    have hSampleMoment0 : 0 ≤ subsetMoment μSample q J :=
      subsetMoment_nonneg
        (fun b => by
          dsimp [μSample]
          unfold sampleCategoryFraction permutationSampleSum categoryIndicator
          positivity)
        (quantizedRepresentative_nonneg d hη.le) J
    have hdensityTransfer := subsetDensity_le_of_mass_moment_error
      hPopMass0 hSampleMass0 hSampleMass1 hPopMoment0 hSampleMoment0
      hΔ0 (by norm_num : (0 : ℝ) ≤ 32) hMass hMoment
    have hgood' : Δ ≤ 1 / (32 * 33) := by
      simpa [Δ, sample, c, n] using hgood
    rw [hρGridEq]
    dsimp [μPop, q, J]
    dsimp [μPop, μSample, q, J] at hdensityTransfer hsampleJ
    unfold subsetDensity at hdensityTransfer hsampleJ ⊢
    norm_num at hgood' ⊢
    nlinarith
  have hθEight := fallback_threshold_ge_eight_B32
    hθPos hη.le hηUpper hgridLT hgrid
  have hOffline : 57 / 16 ≤ finiteOfflineFluid p :=
    maximumDensity_offlineFluid_lower_B32 hn p hp trueSet hmaxTrue haTrue
      (by simpa [θ, μTrue, n] using hθEight)
  have hfallback := fallback_sampleFirstCost_bound
    k r d hk hr η hη p hp hlearn
  have hcorrection0 : 0 ≤ finiteOfflineCorrection p := by
    unfold finiteOfflineCorrection
    have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
    positivity
  have hoptFluid : (n : ℝ) ^ 2 * finiteOfflineFluid p ≤
      finiteObligatoryOPT p := by
    unfold finiteObligatoryOPT
    exact le_add_of_nonneg_right hcorrection0
  have hbase :
      learnedSampleFirstScalarCost k r d η hη p -
          17 * (n : ℝ) * k / 2 ≤
        finiteObligatoryOPT p + (n : ℝ) ^ 2 / 2 := by
    simpa [n] using (sub_le_iff_le_add.mpr hfallback)
  have hfour := fallback_le_four_thirds
    (n := (n : ℝ)) (O := finiteOfflineFluid p)
    (opt := finiteObligatoryOPT p)
    (alg := learnedSampleFirstScalarCost k r d η hη p -
      17 * (n : ℝ) * k / 2)
    (by positivity) hOffline hoptFluid hbase
  dsimp [n] at hfour ⊢
  simp only [Nat.cast_add] at hfour ⊢
  linarith

end

end RandomizedObligatory
end SchedulingPaper
