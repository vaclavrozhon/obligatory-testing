import SchedulingPaper.UpperBoundAssembly
import SchedulingPaper.UTERuntimeEndpoint
import SchedulingPaper.UTEFiniteEndpointAccounting
import SchedulingPaper.ListPairPermutation
import Mathlib.Tactic

/-!
# Verified operational bridge for the Zero-prefix branch

This file closes the transcript-to-endpoint interface used by
`UpperBound.ZeroPrefixCostBridge`.

For `s ≥ 1` the zero-prefix policy has threshold one.  Deferred coordinates
are first moved, all together, to whichever of the two endpoints `1` and
`s+1` maximizes their common convex score.  Once the deferred values are
equal, the remaining immediate coordinates admit the ordinary independent
box-vertex reduction.  The resulting endpoint word is evaluated by
`UTEFiniteEndpointAccounting`.

For `0 < s < 1` the factor `1 + 1 / sqrt s` is already large enough to
dominate every self and pair charge of the threshold-`s` execution
pointwise.  This also explains why the operational interface can be stated
on the whole positive range even though the four-class endpoint game is
only needed from `s = 1` onward.
-/

namespace SchedulingPaper

noncomputable section

open Set
open LowerBound

/-! ## The exact status word for a zero forced prefix -/

/-- Immediate/deferred status of `ForcedPrefixUTE(n,s+1,0)`. -/
def zeroPrefixRuntimeOutcome {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) (job : Fin n) :
    BoundaryOutcome :=
  if processing job ≤ min 1 s then .immediate else .deferred

@[simp] theorem zeroPrefixRuntimeOutcome_eq_deferred_iff
    {n : ℕ} {s : ℝ} {processing : Fin n → ℝ} {job : Fin n} :
    zeroPrefixRuntimeOutcome s processing job = .deferred ↔
      ¬ processing job ≤ min 1 s := by
  unfold zeroPrefixRuntimeOutcome
  split <;> simp_all

@[simp] theorem zeroPrefixRuntimeOutcome_ne_deferred_iff
    {n : ℕ} {s : ℝ} {processing : Fin n → ℝ} {job : Fin n} :
    zeroPrefixRuntimeOutcome s processing job ≠ .deferred ↔
      processing job ≤ min 1 s := by
  unfold zeroPrefixRuntimeOutcome
  split <;> simp_all

namespace Online

theorem zeroPrefixRuntime_immediateFor
    {n : ℕ} {s : ℝ}
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n) :
    ∀ job,
      zeroPrefixRuntimeOutcome s processingTime job ≠ .deferred →
        transcript.ImmediateFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n (forcedPrefixCount n 0) (uteThreshold (s + 1)))
          job := by
  intro job himmediate before after p hdecomp
  have hp : p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  have hthreshold :
      uteThreshold (s + 1) = min 1 s := by
    unfold uteThreshold
    congr 2
    ring
  change
    Transcript.forcedPrefixPendingImmediate?
        n (forcedPrefixCount n 0) (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      some job
  rw [hthreshold, forcedPrefixCount_zero,
    forcedPrefixPendingImmediate_append_testResult, hbefore, hp]
  have hcondition :
      processingTime job ≤ min 1 s :=
    zeroPrefixRuntimeOutcome_ne_deferred_iff.mp himmediate
  simp [hcondition]

theorem zeroPrefixRuntime_deferredFor
    {n : ℕ} {s : ℝ}
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n) :
    ∀ job,
      zeroPrefixRuntimeOutcome s processingTime job = .deferred →
        transcript.DeferredFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n (forcedPrefixCount n 0) (uteThreshold (s + 1)))
          job := by
  intro job hdeferred before after p hdecomp
  have hp : p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  have hthreshold :
      uteThreshold (s + 1) = min 1 s := by
    unfold uteThreshold
    congr 2
    ring
  change
    Transcript.forcedPrefixPendingImmediate?
        n (forcedPrefixCount n 0) (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      none
  rw [hthreshold, forcedPrefixCount_zero,
    forcedPrefixPendingImmediate_append_testResult, hbefore, hp]
  have hcondition :
      ¬ processingTime job ≤ min 1 s :=
    zeroPrefixRuntimeOutcome_eq_deferred_iff.mp hdeferred
  simp [hcondition]

theorem zeroPrefixRuntime_deferred_nonzero
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    {processingTime : Label n → ℝ} :
    ∀ job,
      zeroPrefixRuntimeOutcome s processingTime job = .deferred →
        processingTime job ≠ 0 := by
  intro job hdeferred hzero
  have hcondition :=
    zeroPrefixRuntimeOutcome_eq_deferred_iff.mp hdeferred
  apply hcondition
  rw [hzero]
  simp [hs.le]

/-- Exact status-table pair charge for the zero-prefix execution. -/
theorem run_zeroPrefix_pairCharge_eq
    (n : ℕ) {s : ℝ} (hs : 0 < s)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) 0) (2 * n + 1)
    tracePairCharge (.finite (s + 1)) processingTime
        result.config.transcript left right =
      obligatoryALGPairCharge
        ⟨zeroPrefixRuntimeOutcome s processingTime left,
          processingTime left⟩
        ⟨zeroPrefixRuntimeOutcome s processingTime right,
          processingTime right⟩ := by
  dsimp only
  let result :=
    run (.finite (s + 1)) (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n (s + 1) 0) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n (s + 1) 0 (.finite (s + 1)) processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hfollow :
      result.config.transcript.FollowsStrategy
        (testProcessStrategy
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n (forcedPrefixCount n 0)
                (uteThreshold (s + 1)))) := by
    have h :=
      run_followsStrategy (.finite (s + 1))
        (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) 0)
        (2 * n + 1)
    rw [forcedPrefixUTEStrategy_eq_testProcessStrategy] at h
    exact h
  exact
    hrun.2.2.2.2.1.tracePairCharge_eq_obligatoryALGPairCharge
      hrun.2.2.1 hallTests hallProcessed hfollow
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n 0) (uteThreshold (s + 1)))
      (zeroPrefixRuntimeOutcome s processingTime)
      (zeroPrefixRuntime_immediateFor
        hrun.2.2.2.2.1 hrun.2.2.1 hallTests)
      (zeroPrefixRuntime_deferredFor
        hrun.2.2.2.2.1 hrun.2.2.1 hallTests)
      (zeroPrefixRuntime_deferred_nonzero hs)
      (.finite (s + 1)) horder

/-- The whole completion cost is the recursive status-sensitive objective. -/
theorem run_zeroPrefix_completionCost_eq_statusALG
    (n : ℕ) {s : ℝ} (hs : 0 < s)
    (processingTime : Label n → ℝ) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) 0) (2 * n + 1)
    runCompletionCost (.finite (s + 1)) processingTime result =
      obligatoryALGPairObjective
        (obligatoryJobsOfFunctions
          (zeroPrefixRuntimeOutcome s processingTime)
          processingTime) := by
  dsimp only
  rw [run_forcedPrefixUTEStrategy_completionCost_eq_self_add_pairs]
  rw [obligatoryALGPairObjective_jobsOfFunctions_eq_finSums]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro left _hleft
    apply Finset.sum_congr rfl
    intro right hright
    exact run_zeroPrefix_pairCharge_eq
      n hs processingTime (Finset.mem_filter.mp hright).2

end Online

/-! ## A parameterized fixed-word excess -/

def zeroPrefixFixedSelfExcess (s p : ℝ) : ℝ :=
  (1 + p) - zeroPrefixFactor s * uteEffectiveAt s p

def zeroPrefixFixedPairExcess
    (s : ℝ) (symbol : UTEPairSymbol) (p q : ℝ) : ℝ :=
  uteFixedALGPairCharge symbol p q -
    zeroPrefixFactor s * uteFixedOPTPairCharge s p q

def zeroPrefixFixedWordExcess {n : ℕ}
    (s : ℝ) (word : UTEFixedSymbolicWord n)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, zeroPrefixFixedSelfExcess s (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      zeroPrefixFixedPairExcess s
        (word.pairSymbol i j) (processing i) (processing j)

theorem zeroPrefixFactor_pos {s : ℝ} (hs : 0 < s) :
    0 < zeroPrefixFactor s := by
  unfold zeroPrefixFactor
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  positivity

theorem zeroPrefixFixedSelfExcess_convex
    {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ univ (zeroPrefixFixedSelfExcess s) := by
  have h :=
    convexOn_affine_sub_mul_min
      1 (1 - zeroPrefixFactor s) (zeroPrefixFactor s) s
        (zeroPrefixFactor_pos hs).le
  refine h.congr ?_
  intro p _hp
  rw [zeroPrefixFixedSelfExcess, uteEffectiveAt_eq_one_add_min]
  ring

theorem zeroPrefixFixedPairExcess_convex_left
    {s : ℝ} (hs : 0 < s)
    (symbol : UTEPairSymbol) (q : ℝ) :
    ConvexOn ℝ univ
      (fun p => zeroPrefixFixedPairExcess s symbol p q) := by
  have hrho : 0 ≤ zeroPrefixFactor s :=
    (zeroPrefixFactor_pos hs).le
  cases symbol with
  | leftAfterOneTest =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (1 - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s q - 1) hrho
      refine h.congr ?_
      intro p _hp
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring
  | leftAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (2 - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s q - 1) hrho
      refine h.congr ?_
      intro p _hp
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring
  | rightAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (2 + q - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s q - 1) hrho
      refine h.congr ?_
      intro p _hp
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring

theorem zeroPrefixFixedPairExcess_convex_right
    {s : ℝ} (hs : 0 < s)
    (symbol : UTEPairSymbol) (p : ℝ) :
    ConvexOn ℝ univ
      (fun q => zeroPrefixFixedPairExcess s symbol p q) := by
  have hrho : 0 ≤ zeroPrefixFactor s :=
    (zeroPrefixFactor_pos hs).le
  cases symbol with
  | leftAfterOneTest =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s p - 1) hrho
      refine h.congr ?_
      intro q _hq
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring
  | leftAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (2 + p - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s p - 1) hrho
      refine h.congr ?_
      intro q _hq
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring
  | rightAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (2 - zeroPrefixFactor s) (zeroPrefixFactor s)
            (uteEffectiveAt s p - 1) hrho
      refine h.congr ?_
      intro q _hq
      simp only [zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring

private theorem zeroPrefix_convexOn_finset_sum
    {ι : Type*} {domain : Set ℝ} (hdomain : Convex ℝ domain)
    (indices : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ indices, ConvexOn ℝ domain (f i)) :
    ConvexOn ℝ domain (fun x => ∑ i ∈ indices, f i x) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (convexOn_const (𝕜 := ℝ) (β := ℝ) 0 hdomain)
  | @insert i indices hi ih =>
      have hhead := hf i (Finset.mem_insert_self i indices)
      have htail :
          ∀ j ∈ indices, ConvexOn ℝ domain (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum := hhead.add (ih htail)
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hsum

theorem zeroPrefixFixedWordExcess_coordinatewiseConvex
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (word : UTEFixedSymbolicWord n)
    (lower upper : Fin n → ℝ) :
    CoordinatewiseConvexOnBox lower upper
      (zeroPrefixFixedWordExcess s word) := by
  classical
  intro processing _hbox coordinate
  let interval : Set ℝ :=
    Icc (lower coordinate) (upper coordinate)
  have hinterval : Convex ℝ interval :=
    convex_Icc (lower coordinate) (upper coordinate)
  have hself (i : Fin n) :
      ConvexOn ℝ interval
        (fun x =>
          zeroPrefixFixedSelfExcess s
            (Function.update processing coordinate x i)) := by
    by_cases hi : i = coordinate
    · subst i
      simpa [interval] using
        (zeroPrefixFixedSelfExcess_convex hs).subset
          (subset_univ _) hinterval
    · have hconst :
          (fun x =>
            zeroPrefixFixedSelfExcess s
              (Function.update processing coordinate x i)) =
            (fun _ : ℝ =>
              zeroPrefixFixedSelfExcess s (processing i)) := by
          funext x
          simp [Function.update, hi]
      rw [hconst]
      exact convexOn_const _ hinterval
  have hpair (i j : Fin n) (hij : i < j) :
      ConvexOn ℝ interval
        (fun x =>
          zeroPrefixFixedPairExcess s (word.pairSymbol i j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    by_cases hi : i = coordinate
    · subst i
      have hj : j ≠ coordinate := ne_of_gt hij
      have hleft :=
        (zeroPrefixFixedPairExcess_convex_left hs
          (word.pairSymbol coordinate j)
          (processing j)).subset (subset_univ _) hinterval
      simpa [Function.update, hj] using hleft
    · by_cases hj : j = coordinate
      · subst j
        have hright :=
          (zeroPrefixFixedPairExcess_convex_right hs
            (word.pairSymbol i coordinate)
            (processing i)).subset (subset_univ _) hinterval
        simpa [Function.update, hi] using hright
      · have hconst :
            (fun x =>
              zeroPrefixFixedPairExcess s (word.pairSymbol i j)
                (Function.update processing coordinate x i)
                (Function.update processing coordinate x j)) =
              (fun _ : ℝ =>
                zeroPrefixFixedPairExcess s
                  (word.pairSymbol i j)
                  (processing i) (processing j)) := by
            funext x
            simp [Function.update, hi, hj]
        rw [hconst]
        exact convexOn_const _ hinterval
  have hselfSum :
      ConvexOn ℝ interval
        (fun x => ∑ i,
          zeroPrefixFixedSelfExcess s
            (Function.update processing coordinate x i)) := by
    simpa using zeroPrefix_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => zeroPrefixFixedSelfExcess s
        (Function.update processing coordinate x i))
      (fun i _hi => hself i)
  have hpairRow (i : Fin n) :
      ConvexOn ℝ interval
        (fun x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
          zeroPrefixFixedPairExcess s (word.pairSymbol i j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    apply zeroPrefix_convexOn_finset_sum hinterval
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hj).2
  have hpairSum :
      ConvexOn ℝ interval
        (fun x => ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            zeroPrefixFixedPairExcess s (word.pairSymbol i j)
              (Function.update processing coordinate x i)
              (Function.update processing coordinate x j)) := by
    simpa using zeroPrefix_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
        zeroPrefixFixedPairExcess s (word.pairSymbol i j)
          (Function.update processing coordinate x i)
          (Function.update processing coordinate x j))
      (fun i _hi => hpairRow i)
  simpa [zeroPrefixFixedWordExcess, interval, Pi.add_apply] using
    hselfSum.add hpairSum

theorem exists_zeroPrefixFixedWord_endpoint_ge
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (word : UTEFixedSymbolicWord n)
    (lower upper processing : Fin n → ℝ)
    (horder : ∀ i, lower i ≤ upper i)
    (hprocessing : processing ∈ coordinateBox lower upper) :
    ∃ vertex,
      vertex ∈ coordinateBox lower upper ∧
      IsBoxVertex lower upper vertex ∧
      zeroPrefixFixedWordExcess s word processing ≤
        zeroPrefixFixedWordExcess s word vertex :=
  exists_boxVertex_ge horder
    (zeroPrefixFixedWordExcess_coordinatewiseConvex
      hs word lower upper)
    processing hprocessing

/-! ## Uniform reduction of the deferred suffix -/

def zeroPrefixDeferredScore (s p : ℝ) : ℝ :=
  p - zeroPrefixFactor s * min p s

/-- All deferred coordinates use the same maximizing endpoint. -/
def zeroPrefixDeferredEndpoint (s : ℝ) : ℝ :=
  if zeroPrefixDeferredScore s 1 ≤
      zeroPrefixDeferredScore s (s + 1) then
    s + 1
  else
    1

theorem zeroPrefixDeferredEndpoint_eq_one_or_cap (s : ℝ) :
    zeroPrefixDeferredEndpoint s = 1 ∨
      zeroPrefixDeferredEndpoint s = s + 1 := by
  unfold zeroPrefixDeferredEndpoint
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem zeroPrefixDeferredEndpoint_mem
    {s : ℝ} (hs : 1 ≤ s) :
    zeroPrefixDeferredEndpoint s ∈ Icc (1 : ℝ) (s + 1) := by
  rcases zeroPrefixDeferredEndpoint_eq_one_or_cap s with h | h
  · rw [h]
    constructor <;> linarith
  · rw [h]
    constructor <;> linarith

theorem zeroPrefixDeferredScore_convex
    {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ univ (zeroPrefixDeferredScore s) := by
  simpa [zeroPrefixDeferredScore] using
    convexOn_affine_sub_mul_min
      1 0 (zeroPrefixFactor s) s (zeroPrefixFactor_pos hs).le

theorem zeroPrefixDeferredScore_le_endpoint
    {s p : ℝ} (hs : 1 ≤ s)
    (hpLower : 1 ≤ p) (hpUpper : p ≤ s + 1) :
    zeroPrefixDeferredScore s p ≤
      zeroPrefixDeferredScore s (zeroPrefixDeferredEndpoint s) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hconvex :
      ConvexOn ℝ (Icc (1 : ℝ) (s + 1))
        (zeroPrefixDeferredScore s) :=
    (zeroPrefixDeferredScore_convex hspos).subset
      (subset_univ _) (convex_Icc _ _)
  have hmax :=
    convexOn_Icc_le_max_endpoints hconvex
      (show p ∈ Icc (1 : ℝ) (s + 1) from
        ⟨hpLower, hpUpper⟩)
  unfold zeroPrefixDeferredEndpoint
  split_ifs with hends
  · simpa [max_eq_right hends] using hmax
  · have hreverse :
        zeroPrefixDeferredScore s (s + 1) ≤
          zeroPrefixDeferredScore s 1 :=
      le_of_not_ge hends
    simpa [max_eq_left hreverse] using hmax

def zeroPrefixUniformDeferred {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if processing i ≤ 1 then
      processing i
    else
      zeroPrefixDeferredEndpoint s

/-- A fixed pair word which realizes the frozen immediate/deferred table.
The choice for two deferred jobs is immaterial after their values have been
made equal. -/
def zeroPrefixStatusWord {n : ℕ}
    (processing : Fin n → ℝ) : UTEFixedSymbolicWord n where
  pairSymbol := fun left right =>
    if processing left ≤ 1 then
      .leftAfterOneTest
    else if processing right ≤ 1 then
      .rightAfterTwoTests
    else
      .leftAfterTwoTests

def zeroPrefixStatusExcess {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : ℝ :=
  obligatoryALGPairObjective
      (obligatoryJobsOfFunctions
        (zeroPrefixRuntimeOutcome s processing) processing) -
    zeroPrefixFactor s *
      vectorOfflineCost (.finite (s + 1)) processing

theorem run_zeroPrefix_excess_eq_statusExcess
    (n : ℕ) {s : ℝ} (hs : 0 < s)
    (processingTime : Online.Label n → ℝ) :
    let result :=
      Online.run (.finite (s + 1))
        (Online.fixedOracle processingTime)
        (Online.forcedPrefixUTEStrategy n (s + 1) 0)
        (2 * n + 1)
    Online.runCompletionCost (.finite (s + 1))
          processingTime result -
        zeroPrefixFactor s *
          vectorOfflineCost (.finite (s + 1)) processingTime =
      zeroPrefixStatusExcess s processingTime := by
  dsimp only
  rw [Online.run_zeroPrefix_completionCost_eq_statusALG
    n hs processingTime]
  rfl

theorem zeroPrefixStatusExcess_eq_finSums
    {n : ℕ} (s : ℝ) (processing : Fin n → ℝ) :
    zeroPrefixStatusExcess s processing =
      (∑ i, zeroPrefixFixedSelfExcess s (processing i)) +
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (obligatoryALGPairCharge
              ⟨zeroPrefixRuntimeOutcome s processing i, processing i⟩
              ⟨zeroPrefixRuntimeOutcome s processing j, processing j⟩ -
            zeroPrefixFactor s *
              uteFixedOPTPairCharge s
                (processing i) (processing j)) := by
  unfold zeroPrefixStatusExcess
  rw [Online.obligatoryALGPairObjective_jobsOfFunctions_eq_finSums,
    vectorOfflineCost_finite_add_one_eq_uteFixedWordOPT]
  unfold uteFixedWordOPT zeroPrefixFixedSelfExcess
  rw [mul_add]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_sub_distrib]
  ring

theorem uteFixedOPTPairCharge_eq_one_add_min_min
    (s p q : ℝ) :
    uteFixedOPTPairCharge s p q =
      1 + min (min p q) s := by
  unfold uteFixedOPTPairCharge
  rw [uteEffectiveAt_eq_one_add_min,
    uteEffectiveAt_eq_one_add_min]
  rw [show
      min (1 + min p s) (1 + min q s) =
        1 + min (min p s) (min q s) by
      simpa [add_comm] using
        min_add_add_left 1 (min p s) (min q s)]
  simp only [min_def]
  split_ifs <;> linarith

theorem zeroPrefixFixedSelfExcess_le_uniformDeferred
    {s p : ℝ} (hs : 1 ≤ s)
    (hpUpper : p ≤ s + 1) :
    zeroPrefixFixedSelfExcess s p ≤
      zeroPrefixFixedSelfExcess s
        (if p ≤ 1 then p else zeroPrefixDeferredEndpoint s) := by
  by_cases himmediate : p ≤ 1
  · simp [himmediate]
  · have hpLower : 1 ≤ p := le_of_not_ge himmediate
    have hscore :=
      zeroPrefixDeferredScore_le_endpoint hs hpLower hpUpper
    simp only [if_neg himmediate]
    rw [zeroPrefixFixedSelfExcess,
      zeroPrefixFixedSelfExcess,
      uteEffectiveAt_eq_one_add_min,
      uteEffectiveAt_eq_one_add_min]
    unfold zeroPrefixDeferredScore at hscore
    linarith

theorem zeroPrefixStatusPairExcess_le_uniformDeferred
    {s p q : ℝ} (hs : 1 ≤ s)
    (hpUpper : p ≤ s + 1) :
    obligatoryALGPairCharge
          ⟨if p ≤ 1 then .immediate else .deferred, p⟩
          ⟨if q ≤ 1 then .immediate else .deferred, q⟩ -
        zeroPrefixFactor s * uteFixedOPTPairCharge s p q ≤
      zeroPrefixFixedPairExcess s
        (if p ≤ 1 then
          .leftAfterOneTest
        else if q ≤ 1 then
          .rightAfterTwoTests
        else
          .leftAfterTwoTests)
        (if p ≤ 1 then p else zeroPrefixDeferredEndpoint s)
        (if q ≤ 1 then q else zeroPrefixDeferredEndpoint s) := by
  by_cases hp1 : p ≤ 1
  · by_cases hq1 : q ≤ 1
    · simp [hp1, hq1, obligatoryALGPairCharge,
        zeroPrefixFixedPairExcess, uteFixedALGPairCharge]
    · have hqLower : 1 ≤ q := le_of_not_ge hq1
      have heLower : 1 ≤ zeroPrefixDeferredEndpoint s :=
        (zeroPrefixDeferredEndpoint_mem hs).1
      have hpS : p ≤ s := hp1.trans hs
      have hpq : p ≤ q := hp1.trans hqLower
      have hpE : p ≤ zeroPrefixDeferredEndpoint s :=
        hp1.trans heLower
      simp only [if_pos hp1, if_neg hq1]
      unfold zeroPrefixFixedPairExcess
      rw [uteFixedOPTPairCharge_eq_one_add_min_min,
        uteFixedOPTPairCharge_eq_one_add_min_min]
      simp [obligatoryALGPairCharge, uteFixedALGPairCharge,
        min_eq_left hpq, min_eq_left hpS,
        min_eq_left hpE]
  · by_cases hq1 : q ≤ 1
    · have hpLower : 1 ≤ p := le_of_not_ge hp1
      have heLower : 1 ≤ zeroPrefixDeferredEndpoint s :=
        (zeroPrefixDeferredEndpoint_mem hs).1
      have hqS : q ≤ s := hq1.trans hs
      have hqp : q ≤ p := hq1.trans hpLower
      have hqE : q ≤ zeroPrefixDeferredEndpoint s :=
        hq1.trans heLower
      simp only [if_neg hp1, if_pos hq1]
      unfold zeroPrefixFixedPairExcess
      rw [uteFixedOPTPairCharge_eq_one_add_min_min,
        uteFixedOPTPairCharge_eq_one_add_min_min]
      simp [obligatoryALGPairCharge, uteFixedALGPairCharge,
        min_eq_right hqp, min_eq_left hqS,
        min_eq_right hqE]
    · have hpLower : 1 ≤ p := le_of_not_ge hp1
      have hqLower : 1 ≤ q := le_of_not_ge hq1
      let x := min p q
      have hxLower : 1 ≤ x := le_min hpLower hqLower
      have hxUpper : x ≤ s + 1 :=
        (min_le_left p q).trans hpUpper
      have hscore :=
        zeroPrefixDeferredScore_le_endpoint hs hxLower hxUpper
      simp only [if_neg hp1, if_neg hq1]
      unfold zeroPrefixFixedPairExcess
      rw [uteFixedOPTPairCharge_eq_one_add_min_min,
        uteFixedOPTPairCharge_eq_one_add_min_min]
      have hminEE :
          min (zeroPrefixDeferredEndpoint s)
              (zeroPrefixDeferredEndpoint s) =
            zeroPrefixDeferredEndpoint s := min_self _
      simp only [obligatoryALGPairCharge, uteFixedALGPairCharge]
      rw [hminEE]
      dsimp [x] at hscore
      unfold zeroPrefixDeferredScore at hscore
      linarith

theorem zeroPrefixStatusExcess_le_uniformDeferred
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1) :
    zeroPrefixStatusExcess s processing ≤
      zeroPrefixFixedWordExcess s
        (zeroPrefixStatusWord processing)
        (zeroPrefixUniformDeferred s processing) := by
  rw [zeroPrefixStatusExcess_eq_finSums]
  unfold zeroPrefixFixedWordExcess
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _hi
    simpa [zeroPrefixUniformDeferred] using
      zeroPrefixFixedSelfExcess_le_uniformDeferred
        hs (hprocessing i).2
  · apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    have hpair :=
      zeroPrefixStatusPairExcess_le_uniformDeferred
        (q := processing j) hs (hprocessing i).2
    simpa [zeroPrefixRuntimeOutcome, min_eq_left hs,
      zeroPrefixStatusWord, zeroPrefixUniformDeferred] using hpair

def zeroPrefixImmediateLower {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if processing i ≤ 1 then 0 else zeroPrefixDeferredEndpoint s

def zeroPrefixImmediateUpper {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if processing i ≤ 1 then 1 else zeroPrefixDeferredEndpoint s

theorem zeroPrefixImmediateLower_le_upper
    {n : ℕ} (s : ℝ) (processing : Fin n → ℝ) :
    ∀ i,
      zeroPrefixImmediateLower s processing i ≤
        zeroPrefixImmediateUpper s processing i := by
  intro i
  by_cases hi : processing i ≤ 1
  · simp [zeroPrefixImmediateLower, zeroPrefixImmediateUpper, hi]
  · simp [zeroPrefixImmediateLower, zeroPrefixImmediateUpper, hi]

theorem zeroPrefixUniformDeferred_mem_box
    {n : ℕ} {s : ℝ}
    (processing : Fin n → ℝ)
    (hprocessing : ∀ i, 0 ≤ processing i) :
    zeroPrefixUniformDeferred s processing ∈
      coordinateBox
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) := by
  intro i
  by_cases hi : processing i ≤ 1
  · simp [zeroPrefixUniformDeferred, zeroPrefixImmediateLower,
      zeroPrefixImmediateUpper, hi, hprocessing i]
  · simp [zeroPrefixUniformDeferred, zeroPrefixImmediateLower,
      zeroPrefixImmediateUpper, hi]

/-- Endpoint reduction of the immediate coordinates after the deferred
suffix has been made uniform. -/
theorem exists_zeroPrefix_endpoint_vertex_ge
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hprocessing : ∀ i, 0 ≤ processing i) :
    ∃ vertex,
      vertex ∈ coordinateBox
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) ∧
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex ∧
      zeroPrefixFixedWordExcess s
          (zeroPrefixStatusWord processing)
          (zeroPrefixUniformDeferred s processing) ≤
        zeroPrefixFixedWordExcess s
          (zeroPrefixStatusWord processing) vertex := by
  exact exists_zeroPrefixFixedWord_endpoint_ge
    (zero_lt_one.trans_le hs)
    (zeroPrefixStatusWord processing)
    (zeroPrefixImmediateLower s processing)
    (zeroPrefixImmediateUpper s processing)
    (zeroPrefixUniformDeferred s processing)
    (zeroPrefixImmediateLower_le_upper s processing)
    (zeroPrefixUniformDeferred_mem_box processing hprocessing)

/-! ## Reading a box vertex as a four-class UTE endpoint word -/

def zeroPrefixEndpointOf {n : ℕ}
    (s : ℝ) (processing vertex : Fin n → ℝ)
    (i : Fin n) : UTEEndpoint :=
  if processing i ≤ 1 then
    if vertex i = 0 then .suffixZero else .immediateOne
  else if zeroPrefixDeferredEndpoint s = s + 1 then
    .cappedDeferred
  else
    .boundaryDeferred

theorem zeroPrefixEndpointOf_not_forced
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ)
    (i : Fin n) :
    ¬(zeroPrefixEndpointOf s processing vertex i).IsForced := by
  unfold zeroPrefixEndpointOf
  split <;> split <;> simp [UTEEndpoint.IsForced]

theorem zeroPrefixEndpointOf_processing
    {n : ℕ} {s : ℝ} {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex) :
    ∀ i,
      vertex i =
        uteEndpointProcessing s
          (zeroPrefixEndpointOf s processing vertex i) := by
  intro i
  have hi := hvertex i
  by_cases himmediate : processing i ≤ 1
  · simp [zeroPrefixImmediateLower, zeroPrefixImmediateUpper,
      himmediate] at hi
    rcases hi with hzero | hone
    · simp [zeroPrefixEndpointOf, himmediate, hzero,
        uteEndpointProcessing]
    · by_cases hzero : vertex i = 0
      · simp [zeroPrefixEndpointOf, himmediate, hzero,
          uteEndpointProcessing]
      · simp [zeroPrefixEndpointOf, himmediate,
          uteEndpointProcessing, hone]
  · simp [zeroPrefixImmediateLower, zeroPrefixImmediateUpper,
      himmediate] at hi
    have heq : vertex i = zeroPrefixDeferredEndpoint s := hi
    by_cases hcap :
        zeroPrefixDeferredEndpoint s = s + 1
    · simp [zeroPrefixEndpointOf, himmediate, hcap,
        uteEndpointProcessing, heq]
    · have hone : zeroPrefixDeferredEndpoint s = 1 := by
        rcases zeroPrefixDeferredEndpoint_eq_one_or_cap s with
          hone | hcap'
        · exact hone
        · exact (hcap hcap').elim
      simp only [zeroPrefixEndpointOf, if_neg himmediate,
        if_neg hcap, uteEndpointProcessing]
      rw [← hone, ← heq]

theorem zeroPrefixEndpointOf_isImmediate
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ)
    (i : Fin n) :
    (zeroPrefixEndpointOf s processing vertex i).IsImmediate =
      if processing i ≤ 1 then true else false := by
  by_cases hi : processing i ≤ 1
  · by_cases hv : vertex i = 0 <;>
      simp [zeroPrefixEndpointOf, hi, hv,
        UTEEndpoint.IsImmediate]
  · by_cases he : zeroPrefixDeferredEndpoint s = s + 1 <;>
      simp [zeroPrefixEndpointOf, hi, he,
        UTEEndpoint.IsImmediate]

theorem zeroPrefixStatusWord_pair_eq_endpointALG
    {n : ℕ} {s : ℝ} {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex)
    (left right : Fin n) :
    uteFixedALGPairCharge
        ((zeroPrefixStatusWord processing).pairSymbol left right)
        (vertex left) (vertex right) =
      uteALGPairCharge s
        (zeroPrefixEndpointOf s processing vertex left)
        (zeroPrefixEndpointOf s processing vertex right) := by
  have hleft :=
    zeroPrefixEndpointOf_processing hvertex left
  have hright :=
    zeroPrefixEndpointOf_processing hvertex right
  rw [hleft, hright]
  by_cases hl : processing left ≤ 1
  · simp [zeroPrefixStatusWord, hl, uteFixedALGPairCharge,
      uteALGPairCharge, zeroPrefixEndpointOf_isImmediate]
  · by_cases hr : processing right ≤ 1
    · simp [zeroPrefixStatusWord, hl, hr, uteFixedALGPairCharge,
        uteALGPairCharge, zeroPrefixEndpointOf_isImmediate]
    · have hequal :
          zeroPrefixEndpointOf s processing vertex left =
            zeroPrefixEndpointOf s processing vertex right := by
        simp [zeroPrefixEndpointOf, hl, hr]
      rw [hequal]
      simp [zeroPrefixStatusWord, hl, hr, uteFixedALGPairCharge,
        uteALGPairCharge, zeroPrefixEndpointOf_isImmediate]

theorem zeroPrefixVertex_pairOPT_eq_endpointOPT
    {n : ℕ} {s : ℝ} {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex)
    (left right : Fin n) :
    uteFixedOPTPairCharge s (vertex left) (vertex right) =
      uteOPTPairCharge s
        (zeroPrefixEndpointOf s processing vertex left)
        (zeroPrefixEndpointOf s processing vertex right) := by
  rw [zeroPrefixEndpointOf_processing hvertex left,
    zeroPrefixEndpointOf_processing hvertex right]
  rfl

def zeroPrefixEndpointList {n : ℕ}
    (s : ℝ) (processing vertex : Fin n → ℝ) :
    List UTEEndpoint :=
  List.ofFn (zeroPrefixEndpointOf s processing vertex)

theorem zeroPrefixEndpointList_length
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ) :
    (zeroPrefixEndpointList s processing vertex).length = n := by
  simp [zeroPrefixEndpointList]

theorem zeroPrefixEndpointList_no_forcedCap
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ) :
    (zeroPrefixEndpointList s processing vertex).count
        .forcedCap = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  rcases List.mem_ofFn.mp hmem with ⟨i, hi⟩
  have hnot :=
    zeroPrefixEndpointOf_not_forced s processing vertex i
  rw [hi] at hnot
  simp [UTEEndpoint.IsForced] at hnot

theorem zeroPrefixEndpointList_no_forcedZero
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ) :
    (zeroPrefixEndpointList s processing vertex).count
        .forcedZero = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  rcases List.mem_ofFn.mp hmem with ⟨i, hi⟩
  have hnot :=
    zeroPrefixEndpointOf_not_forced s processing vertex i
  rw [hi] at hnot
  simp [UTEEndpoint.IsForced] at hnot

private theorem uteEndpoint_all_counts :
    ∀ values : List UTEEndpoint,
      values.count .forcedCap +
          values.count .forcedZero +
          values.count .cappedDeferred +
          values.count .boundaryDeferred +
          values.count .immediateOne +
          values.count .suffixZero =
        values.length := by
  intro values
  induction values with
  | nil =>
      simp
  | cons endpoint values ih =>
      cases endpoint <;> simp_all <;> omega

theorem zeroPrefixEndpointList_count_total
    {n : ℕ} (s : ℝ) (processing vertex : Fin n → ℝ) :
    (zeroPrefixEndpointList s processing vertex).count
          .cappedDeferred +
        (zeroPrefixEndpointList s processing vertex).count
          .boundaryDeferred +
        (zeroPrefixEndpointList s processing vertex).count
          .immediateOne +
        (zeroPrefixEndpointList s processing vertex).count
          .suffixZero =
      n := by
  have hall :=
    uteEndpoint_all_counts
      (zeroPrefixEndpointList s processing vertex)
  rw [zeroPrefixEndpointList_no_forcedCap,
    zeroPrefixEndpointList_no_forcedZero,
    zeroPrefixEndpointList_length] at hall
  omega

theorem uteEndpointProcessing_nonneg
    {s : ℝ} (hs : 0 ≤ s) (endpoint : UTEEndpoint) :
    0 ≤ uteEndpointProcessing s endpoint := by
  cases endpoint <;> simp [uteEndpointProcessing] <;> linarith

theorem uteEndpointProcessing_le_cap
    {s : ℝ} (hs : 1 ≤ s) (endpoint : UTEEndpoint) :
    uteEndpointProcessing s endpoint ≤ s + 1 := by
  cases endpoint <;> simp [uteEndpointProcessing] <;> linarith

theorem zeroPrefixFixedSelfExcess_endpoint_le
    {s : ℝ} (hs : 1 ≤ s) (endpoint : UTEEndpoint) :
    zeroPrefixFixedSelfExcess s
        (uteEndpointProcessing s endpoint) ≤
      s + 2 := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hp0 :
      0 ≤ uteEndpointProcessing s endpoint :=
    uteEndpointProcessing_nonneg hs0 endpoint
  have hpUpper :
      uteEndpointProcessing s endpoint ≤ s + 1 :=
    uteEndpointProcessing_le_cap hs endpoint
  have heff0 :
      0 ≤ uteEffectiveAt s (uteEndpointProcessing s endpoint) := by
    unfold uteEffectiveAt
    exact
      le_min (by linarith) (by linarith)
  have hrho0 : 0 ≤ zeroPrefixFactor s :=
    (zeroPrefixFactor_pos (zero_lt_one.trans_le hs)).le
  unfold zeroPrefixFixedSelfExcess
  nlinarith [mul_nonneg hrho0 heff0]

theorem zeroPrefixVertex_self_sum_le
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex) :
    (∑ i, zeroPrefixFixedSelfExcess s (vertex i)) ≤
      (s + 2) * n := by
  calc
    (∑ i, zeroPrefixFixedSelfExcess s (vertex i)) ≤
        ∑ _i : Fin n, (s + 2) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [zeroPrefixEndpointOf_processing hvertex i]
      exact zeroPrefixFixedSelfExcess_endpoint_le hs _
    _ = (s + 2) * n := by
      simp
      ring

theorem zeroPrefixVertex_pairSum_eq_listObjectives
    {n : ℕ} {s : ℝ} {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        zeroPrefixFixedPairExcess s
          ((zeroPrefixStatusWord processing).pairSymbol i j)
          (vertex i) (vertex j)) =
      listPairObjective (fun _ => 0) (uteALGPairCharge s)
          (zeroPrefixEndpointList s processing vertex) -
        zeroPrefixFactor s *
          listPairObjective (fun _ => 0) (uteOPTPairCharge s)
            (zeroPrefixEndpointList s processing vertex) := by
  let endpointFn : Fin n → UTEEndpoint :=
    zeroPrefixEndpointOf s processing vertex
  have halg :=
    finSelfPairSum_eq_listPairObjective
      (fun _ : UTEEndpoint => (0 : ℝ))
      (uteALGPairCharge s) endpointFn
  have hopt :=
    finSelfPairSum_eq_listPairObjective
      (fun _ : UTEEndpoint => (0 : ℝ))
      (uteOPTPairCharge s) endpointFn
  have halg' :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          uteALGPairCharge s (endpointFn i) (endpointFn j)) =
        listPairObjective (fun _ => 0) (uteALGPairCharge s)
          (zeroPrefixEndpointList s processing vertex) := by
    simpa [endpointFn, zeroPrefixEndpointList] using halg
  have hopt' :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          uteOPTPairCharge s (endpointFn i) (endpointFn j)) =
        listPairObjective (fun _ => 0) (uteOPTPairCharge s)
          (zeroPrefixEndpointList s processing vertex) := by
    simpa [endpointFn, zeroPrefixEndpointList] using hopt
  calc
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        zeroPrefixFixedPairExcess s
          ((zeroPrefixStatusWord processing).pairSymbol i j)
          (vertex i) (vertex j)) =
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (uteALGPairCharge s (endpointFn i) (endpointFn j) -
            zeroPrefixFactor s *
              uteOPTPairCharge s (endpointFn i) (endpointFn j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      unfold zeroPrefixFixedPairExcess
      rw [zeroPrefixStatusWord_pair_eq_endpointALG
          hvertex i j,
        zeroPrefixVertex_pairOPT_eq_endpointOPT
          hvertex i j]
    _ =
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          uteALGPairCharge s (endpointFn i) (endpointFn j)) -
        zeroPrefixFactor s *
          (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            uteOPTPairCharge s (endpointFn i) (endpointFn j)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ =
      listPairObjective (fun _ => 0) (uteALGPairCharge s)
          (zeroPrefixEndpointList s processing vertex) -
        zeroPrefixFactor s *
          listPairObjective (fun _ => 0) (uteOPTPairCharge s)
            (zeroPrefixEndpointList s processing vertex) := by
      rw [halg', hopt']

theorem zeroPrefixVertex_excess_le_finiteCore
    {n : ℕ} {s : ℝ} (hs : 1 ≤ s)
    {processing vertex : Fin n → ℝ}
    (hvertex :
      IsBoxVertex
        (zeroPrefixImmediateLower s processing)
        (zeroPrefixImmediateUpper s processing) vertex) :
    zeroPrefixFixedWordExcess s
        (zeroPrefixStatusWord processing) vertex ≤
      uteFiniteALGCore s 0 0
          ((zeroPrefixEndpointList s processing vertex).count
            .cappedDeferred)
          ((zeroPrefixEndpointList s processing vertex).count
            .boundaryDeferred)
          ((zeroPrefixEndpointList s processing vertex).count
            .immediateOne)
          ((zeroPrefixEndpointList s processing vertex).count
            .suffixZero) -
        zeroPrefixFactor s *
          uteFiniteOPTCore s 0 0
            ((zeroPrefixEndpointList s processing vertex).count
              .cappedDeferred)
            ((zeroPrefixEndpointList s processing vertex).count
              .boundaryDeferred)
            ((zeroPrefixEndpointList s processing vertex).count
              .immediateOne)
            ((zeroPrefixEndpointList s processing vertex).count
              .suffixZero) +
        (s + 2) * n := by
  let values := zeroPrefixEndpointList s processing vertex
  have hself := zeroPrefixVertex_self_sum_le hs hvertex
  have hpairs :=
    zeroPrefixVertex_pairSum_eq_listObjectives hvertex
  have hcanonical :
      listPairObjective (fun _ => 0) (uteALGPairCharge s) values ≤
        listPairObjective (fun _ => 0)
          (uteCanonicalALGPairCharge s) values := by
    have hsuffix :
        ∀ endpoint ∈ values, ¬endpoint.IsForced := by
      intro endpoint hmem
      rcases List.mem_ofFn.mp (by simpa [values,
          zeroPrefixEndpointList] using hmem) with ⟨i, hi⟩
      rw [← hi]
      exact
        zeroPrefixEndpointOf_not_forced
          s processing vertex i
    have h :=
      ute_listPairObjective_le_canonical
        (zero_le_one.trans hs) ([] : List UTEEndpoint) values
        (by simp)
        hsuffix
    simpa [values] using h
  have hpairBound :
      listPairObjective (fun _ => 0) (uteALGPairCharge s) values -
          zeroPrefixFactor s *
            listPairObjective (fun _ => 0) (uteOPTPairCharge s) values ≤
        listPairObjective (fun _ => 0)
            (uteCanonicalALGPairCharge s) values -
          zeroPrefixFactor s *
            listPairObjective (fun _ => 0)
              (uteOPTPairCharge s) values := by
    linarith
  unfold zeroPrefixFixedWordExcess
  rw [hpairs]
  calc
    (∑ i, zeroPrefixFixedSelfExcess s (vertex i)) +
          (listPairObjective (fun _ => 0) (uteALGPairCharge s) values -
            zeroPrefixFactor s *
              listPairObjective (fun _ => 0)
                (uteOPTPairCharge s) values) ≤
        (s + 2) * n +
          (listPairObjective (fun _ => 0)
              (uteCanonicalALGPairCharge s) values -
            zeroPrefixFactor s *
              listPairObjective (fun _ => 0)
                (uteOPTPairCharge s) values) := by
      linarith
    _ =
      uteFiniteALGCore s 0 0
          (values.count .cappedDeferred)
          (values.count .boundaryDeferred)
          (values.count .immediateOne)
          (values.count .suffixZero) -
        zeroPrefixFactor s *
          uteFiniteOPTCore s 0 0
            (values.count .cappedDeferred)
            (values.count .boundaryDeferred)
            (values.count .immediateOne)
            (values.count .suffixZero) +
        (s + 2) * n := by
      rw [listPairObjective_canonicalALG_eq_finiteCore,
        listPairObjective_opt_eq_finiteCore]
      simp [values, zeroPrefixEndpointList_no_forcedCap,
        zeroPrefixEndpointList_no_forcedZero]
      ring

/-! ## Exact normalization of a zero-prefix finite endpoint word -/

theorem uteLiteralALGWithPrefix_zero_eq_zeroPrefixAlg
    {s d t m : ℝ} (hs : 0 ≤ s) :
    uteLiteralALGWithPrefix s 0 0 d t m =
      zeroPrefixAlg s d t m := by
  rw [uteLiteralALGWithPrefix_eq_polynomial hs]
  unfold zeroPrefixAlg
  ring

theorem uteLiteralOPTWithPrefix_zero_eq_zeroPrefixOpt
    {s d t m : ℝ} (hs : 1 ≤ s) :
    uteLiteralOPTWithPrefix s 0 0 d t m =
      zeroPrefixOpt s d t m := by
  rw [uteLiteralOPTWithPrefix_eq_polynomial hs]
  unfold zeroPrefixOpt
  ring

theorem zeroPrefixFinite_pairExcess_le_normalized
    {n d t m z : ℕ} {s : ℝ}
    (hn : n ≠ 0) (hs : 1 ≤ s)
    (htotal : d + t + m + z = n) :
    uteFiniteALGCore s 0 0 d t m z -
        zeroPrefixFactor s *
          uteFiniteOPTCore s 0 0 d t m z ≤
      (n : ℝ) ^ 2 *
        (zeroPrefixAlg s (d / n) (t / n) (m / n) -
          zeroPrefixFactor s *
            zeroPrefixOpt s (d / n) (t / n) (m / n)) +
        (zeroPrefixFactor s * (s + 1) / 2) * n := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hrho0 : 0 ≤ zeroPrefixFactor s :=
    (zeroPrefixFactor_pos (zero_lt_one.trans_le hs)).le
  have htotalR :
      (d : ℝ) + t + m + z = n := by
    exact_mod_cast htotal
  have hz :
      (n : ℝ) * (1 - 0) - d - t - m = z := by
    norm_num
    linarith
  have hz' :
      (n : ℝ) - d - t - m = z := by
    linarith
  have halgNorm :=
    uteLiteralALGWithPrefix_normalized hn
      s 0 (0 : ℝ) (d : ℝ) (t : ℝ) (m : ℝ)
  norm_num at halgNorm
  rw [uteLiteralALGWithPrefix_zero_eq_zeroPrefixAlg hs0] at halgNorm
  have halgNorm' :
      (n : ℝ) ^ 2 *
          zeroPrefixAlg s (d / n) (t / n) (m / n) =
        uteLiteralALGCore s 0 0 d t m z := by
    rw [hz'] at halgNorm
    exact halgNorm
  have hoptNorm :=
    uteLiteralOPTWithPrefix_normalized hn
      s 0 (0 : ℝ) (d : ℝ) (t : ℝ) (m : ℝ)
  norm_num at hoptNorm
  rw [uteLiteralOPTWithPrefix_zero_eq_zeroPrefixOpt hs] at hoptNorm
  have hoptNorm' :
      (n : ℝ) ^ 2 *
          zeroPrefixOpt s (d / n) (t / n) (m / n) =
        uteLiteralOPTCore s 0 0 d t m z := by
    rw [hz'] at hoptNorm
    exact hoptNorm
  have halg :
      uteFiniteALGCore s 0 0 d t m z ≤
        uteLiteralALGCore s 0 0 d t m z :=
    by simpa using
      (uteFiniteALGCore_le_literal hs0 0 0 d t m z)
  have hdiag :=
    uteFiniteOPT_diagonal_le hs 0 0 d t m z
  have hdiag' :
      uteLiteralOPTCore s 0 0 d t m z -
          uteFiniteOPTCore s 0 0 d t m z ≤
        (s + 1) / 2 * n := by
    norm_num at hdiag
    nlinarith
  have hdiagScaled :
      zeroPrefixFactor s *
          (uteLiteralOPTCore s 0 0 d t m z -
            uteFiniteOPTCore s 0 0 d t m z) ≤
        zeroPrefixFactor s * ((s + 1) / 2 * n) :=
    mul_le_mul_of_nonneg_left hdiag' hrho0
  have hgapNorm :
      (n : ℝ) ^ 2 *
          (zeroPrefixAlg s (d / n) (t / n) (m / n) -
            zeroPrefixFactor s *
              zeroPrefixOpt s (d / n) (t / n) (m / n)) =
        uteLiteralALGCore s 0 0 d t m z -
          zeroPrefixFactor s *
            uteLiteralOPTCore s 0 0 d t m z := by
    calc
      (n : ℝ) ^ 2 *
          (zeroPrefixAlg s (d / n) (t / n) (m / n) -
            zeroPrefixFactor s *
              zeroPrefixOpt s (d / n) (t / n) (m / n)) =
        (n : ℝ) ^ 2 *
            zeroPrefixAlg s (d / n) (t / n) (m / n) -
          zeroPrefixFactor s *
            ((n : ℝ) ^ 2 *
              zeroPrefixOpt s (d / n) (t / n) (m / n)) := by
          ring
      _ =
        uteLiteralALGCore s 0 0 d t m z -
          zeroPrefixFactor s *
            uteLiteralOPTCore s 0 0 d t m z := by
          rw [halgNorm', hoptNorm']
  rw [hgapNorm]
  nlinarith

theorem exists_zeroPrefix_normalized_endpoint_bound
    {n : ℕ} {s : ℝ} (hn : n ≠ 0) (hs : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1) :
    ∃ d t m : ℝ,
      0 ≤ d ∧ 0 ≤ t ∧ 0 ≤ m ∧
      zeroPrefixStatusExcess s processing ≤
        (n : ℝ) ^ 2 *
          (zeroPrefixAlg s d t m -
            zeroPrefixFactor s * zeroPrefixOpt s d t m) +
          ((s + 2) +
            zeroPrefixFactor s * (s + 1) / 2) * n := by
  obtain ⟨vertex, _hvbox, hvvertex, hvge⟩ :=
    exists_zeroPrefix_endpoint_vertex_ge hs processing
      (fun i => (hprocessing i).1)
  let values := zeroPrefixEndpointList s processing vertex
  let dN : ℕ := values.count .cappedDeferred
  let tN : ℕ := values.count .boundaryDeferred
  let mN : ℕ := values.count .immediateOne
  let zN : ℕ := values.count .suffixZero
  let dR : ℝ := dN / n
  let tR : ℝ := tN / n
  let mR : ℝ := mN / n
  have htotal : dN + tN + mN + zN = n := by
    simpa [values, dN, tN, mN, zN] using
      zeroPrefixEndpointList_count_total
        s processing vertex
  have hfinite :=
    zeroPrefixFinite_pairExcess_le_normalized
      hn hs htotal
  have hvertexFinite :=
    zeroPrefixVertex_excess_le_finiteCore hs hvvertex
  have hstatusUniform :=
    zeroPrefixStatusExcess_le_uniformDeferred
      hs processing hprocessing
  have hchain :
      zeroPrefixStatusExcess s processing ≤
        uteFiniteALGCore s 0 0 dN tN mN zN -
            zeroPrefixFactor s *
              uteFiniteOPTCore s 0 0 dN tN mN zN +
          (s + 2) * n :=
    hstatusUniform.trans (hvge.trans (by
      simpa [values, dN, tN, mN, zN] using hvertexFinite))
  refine ⟨dR, tR, mR, ?_, ?_, ?_, ?_⟩
  · dsimp [dR]
    positivity
  · dsimp [tR]
    positivity
  · dsimp [mR]
    positivity
  · dsimp [dR, tR, mR]
    nlinarith

theorem zeroPrefixStatusExcess_zero
    (s : ℝ) (processing : Fin 0 → ℝ) :
    zeroPrefixStatusExcess s processing = 0 := by
  unfold zeroPrefixStatusExcess obligatoryJobsOfFunctions
    obligatoryALGPairObjective vectorOfflineCost
    vectorEffectiveLengths
  simp [shortestFirst]

/-! ## The direct `0 < s < 1` estimate -/

theorem zeroPrefixFactor_ge_two_of_le_one
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    2 ≤ zeroPrefixFactor s := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hr1 : Real.sqrt s ≤ 1 := by
    nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s]
  have honeDiv : 1 ≤ 1 / Real.sqrt s := by
    rw [le_div_iff₀ hr]
    simpa using hr1
  unfold zeroPrefixFactor
  linarith

theorem add_one_le_zeroPrefixFactor_of_le_one
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s + 1 ≤ zeroPrefixFactor s := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hr1 : Real.sqrt s ≤ 1 := by
    nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg s]
  have hsr :
      s * Real.sqrt s ≤ 1 := by
    calc
      s * Real.sqrt s ≤ 1 * Real.sqrt s :=
        mul_le_mul_of_nonneg_right hs1
          (Real.sqrt_nonneg s)
      _ ≤ 1 := by simpa using hr1
  have hsDiv : s ≤ 1 / Real.sqrt s := by
    rw [le_div_iff₀ hr]
    simpa [mul_comm] using hsr
  unfold zeroPrefixFactor
  linarith

theorem add_three_le_factor_mul_add_one
    {s : ℝ} (hs : 0 < s) :
    s + 3 ≤ zeroPrefixFactor s * (s + 1) := by
  let r := Real.sqrt s
  have hr : 0 < r := by
    simpa [r] using Real.sqrt_pos.2 hs
  have hrsq : r ^ 2 = s := by
    simpa [r] using Real.sq_sqrt hs.le
  have htwo :
      2 * r ≤ s + 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hquot :
      2 ≤ (s + 1) / r := by
    rw [le_div_iff₀ hr]
    exact htwo
  have hid :
      zeroPrefixFactor s * (s + 1) =
        s + 1 + (s + 1) / r := by
    unfold zeroPrefixFactor
    dsimp [r]
    ring
  rw [hid]
  linarith

theorem zeroPrefixSmall_self_nonpos
    {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp0 : 0 ≤ p) (hpUpper : p ≤ s + 1) :
    zeroPrefixFixedSelfExcess s p ≤ 0 := by
  have hrho1 : 1 ≤ zeroPrefixFactor s := by
    linarith [zeroPrefixFactor_ge_two_of_le_one hs hs1]
  by_cases hp : p ≤ s
  · have heff : uteEffectiveAt s p = 1 + p := by
      rw [uteEffectiveAt_eq_one_add_min, min_eq_left hp]
    rw [zeroPrefixFixedSelfExcess, heff]
    have hbase : 0 ≤ 1 + p := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hrho1 hbase]
  · have hsp : s ≤ p := le_of_not_ge hp
    have heff : uteEffectiveAt s p = 1 + s := by
      rw [uteEffectiveAt_eq_one_add_min, min_eq_right hsp]
    rw [zeroPrefixFixedSelfExcess, heff]
    have hcap :=
      add_three_le_factor_mul_add_one hs
    linarith

theorem zeroPrefixSmall_pair_nonpos
    {s p q : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hpUpper : p ≤ s + 1) :
    obligatoryALGPairCharge
          ⟨if p ≤ s then .immediate else .deferred, p⟩
          ⟨if q ≤ s then .immediate else .deferred, q⟩ -
        zeroPrefixFactor s * uteFixedOPTPairCharge s p q ≤
      0 := by
  have hrho0 : 0 ≤ zeroPrefixFactor s :=
    (zeroPrefixFactor_pos hs).le
  have hrho1 : 1 ≤ zeroPrefixFactor s := by
    linarith [zeroPrefixFactor_ge_two_of_le_one hs hs1]
  have hrho2 : 2 ≤ zeroPrefixFactor s :=
    zeroPrefixFactor_ge_two_of_le_one hs hs1
  have hcapFactor :=
    add_three_le_factor_mul_add_one hs
  rw [uteFixedOPTPairCharge_eq_one_add_min_min]
  by_cases hp : p ≤ s
  · by_cases hq : q ≤ s
    · have hmin0 : 0 ≤ min p q := le_min hp0 hq0
      have hoptLower :
          zeroPrefixFactor s ≤
            zeroPrefixFactor s * (1 + min p q) := by
        have hone : 1 ≤ 1 + min p q := by linarith
        simpa using
          mul_le_mul_of_nonneg_left hone hrho0
      simp [hp, hq, obligatoryALGPairCharge]
      have hpFactor :
          1 + p ≤ zeroPrefixFactor s := by
        exact (by
          linarith [add_one_le_zeroPrefixFactor_of_le_one
            hs hs1])
      linarith
    · have hsq : s ≤ q := le_of_not_ge hq
      have hpq : p ≤ q := hp.trans hsq
      simp [hp, obligatoryALGPairCharge,
        min_eq_left hpq]
      have hbase : 0 ≤ 1 + p := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hrho1 hbase]
  · have hsp : s ≤ p := le_of_not_ge hp
    by_cases hq : q ≤ s
    · have hqp : q ≤ p := hq.trans hsp
      simp [hp, hq, obligatoryALGPairCharge,
        min_eq_right hqp]
      have hbase : 0 ≤ 1 + q := by linarith
      have hscaled :
          2 * (1 + q) ≤
            zeroPrefixFactor s * (1 + q) :=
        mul_le_mul_of_nonneg_right hrho2 hbase
      linarith
    · have hsq : s ≤ q := le_of_not_ge hq
      have hsmin : s ≤ min p q := le_min hsp hsq
      have hminUpper :
          min p q ≤ s + 1 :=
        (min_le_left p q).trans hpUpper
      simp [hp, hq, obligatoryALGPairCharge,
        min_eq_right hsmin]
      linarith

theorem zeroPrefixStatusExcess_nonpos_of_le_one
    {n : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1) :
    zeroPrefixStatusExcess s processing ≤ 0 := by
  rw [zeroPrefixStatusExcess_eq_finSums]
  have hself :
      (∑ i, zeroPrefixFixedSelfExcess s (processing i)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _hi
    exact zeroPrefixSmall_self_nonpos hs hs1
      (hprocessing i).1 (hprocessing i).2
  have hpairs :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (obligatoryALGPairCharge
            ⟨zeroPrefixRuntimeOutcome s processing i, processing i⟩
            ⟨zeroPrefixRuntimeOutcome s processing j, processing j⟩ -
          zeroPrefixFactor s *
            uteFixedOPTPairCharge s
              (processing i) (processing j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _hi
    apply Finset.sum_nonpos
    intro j _hj
    have hpair :=
      zeroPrefixSmall_pair_nonpos hs hs1
        (hprocessing i).1 (hprocessing j).1
        (hprocessing i).2
    simpa [zeroPrefixRuntimeOutcome, min_eq_right hs1] using hpair
  linarith

theorem zeroPrefix_equality_parameters
    {s : ℝ} (hs : 0 < s) :
    zeroPrefixAlg s (1 / Real.sqrt s) 0 0 -
        zeroPrefixFactor s *
          zeroPrefixOpt s (1 / Real.sqrt s) 0 0 =
      0 := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hrsq : (Real.sqrt s) ^ 2 = s :=
    Real.sq_sqrt hs.le
  unfold zeroPrefixAlg zeroPrefixOpt zeroPrefixFactor
  field_simp [hr.ne']
  nlinarith

/-! ## The exported operational bridge -/

namespace UpperBound

/-- The zero-prefix transcript/endpoint bridge is unconditional on the
whole positive cap-parameter range. -/
theorem zeroPrefixCostBridge_of_pos
    {s : ℝ} (hs : 0 < s) :
    ZeroPrefixCostBridge s := by
  let C : ℝ :=
    (s + 2) + zeroPrefixFactor s * (s + 1) / 2
  have hsOne : 0 < s + 1 := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have hrho0 : 0 ≤ zeroPrefixFactor s :=
      (zeroPrefixFactor_pos hs).le
    positivity
  refine ⟨C, hC, ?_⟩
  intro n input
  have hprocessing :
      ∀ i, 0 ≤ input.processingTime i ∧
        input.processingTime i ≤ s + 1 := by
    intro i
    exact input.admissible i
  have hoperational :
      strategyCost (.finite (s + 1))
            (zeroPrefixStrategy s) n input -
          zeroPrefixFactor s *
            fixedOfflineCost (.finite (s + 1)) n input =
        zeroPrefixStatusExcess s input.processingTime := by
    simpa [strategyCost, fixedOfflineCost,
      FixedInput.onlineCost, FixedInput.runResult,
      analysisFuel, zeroPrefixStrategy] using
        (run_zeroPrefix_excess_eq_statusExcess
          n hs input.processingTime)
  by_cases hn : n = 0
  · subst n
    refine ⟨0, 0, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hoperational,
      zeroPrefixStatusExcess_zero s input.processingTime]
    norm_num
  · by_cases hsOneLower : 1 ≤ s
    · obtain ⟨d, t, m, hd, ht, hm, hbound⟩ :=
        exists_zeroPrefix_normalized_endpoint_bound
          hn hsOneLower input.processingTime hprocessing
      refine ⟨d, t, m, hd, ht, hm, ?_⟩
      rw [hoperational]
      simpa [C] using hbound
    · have hsUpper : s ≤ 1 := (le_of_not_ge hsOneLower)
      have hnonpos :
          zeroPrefixStatusExcess s input.processingTime ≤ 0 :=
        zeroPrefixStatusExcess_nonpos_of_le_one
          hs hsUpper input.processingTime hprocessing
      let d : ℝ := 1 / Real.sqrt s
      have hd : 0 ≤ d := by
        dsimp [d]
        positivity
      have hgap :
          zeroPrefixAlg s d 0 0 -
              zeroPrefixFactor s * zeroPrefixOpt s d 0 0 =
            0 := by
        simpa [d] using zeroPrefix_equality_parameters hs
      refine ⟨d, 0, 0, hd, by norm_num, by norm_num, ?_⟩
      rw [hoperational, hgap]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hlinear : 0 ≤ C * (n : ℝ) :=
        mul_nonneg hC hn0
      nlinarith

/-- Exact range-specialized form consumed by the fourth upper branch. -/
theorem verifiedZeroPrefixCostBridge
    {s : ℝ} (hs : 0 < s)
    (_hsφ : s ≤ goldenRatio + 1) :
    ZeroPrefixCostBridge s :=
  zeroPrefixCostBridge_of_pos hs

end UpperBound

end

end SchedulingPaper
