import SchedulingPaper.MixedQuotaNoCross
import SchedulingPaper.MixedQuotaFreeze
import Mathlib.Tactic

/-!
# Cost of the terminal no-crossing mixed branch

If the quota line is never crossed, a completed mixed history contains no
tests.  Thus every label was completed raw, the canonical mixed default is
zero everywhere, the frozen offline optimum is `triangular n`, and the
online cost is at least `u * triangular n`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

theorem vectorEffectiveLengths_zero_of_one_le
    (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    vectorEffectiveLengths (.finite u)
        (fun _ : Online.Label n => 0) =
      List.replicate n 1 := by
  unfold vectorEffectiveLengths
  rw [List.ofFn_const]
  apply List.replicate_inj.mpr
  refine ⟨rfl, Or.inr ?_⟩
  simp [effectiveLength_finite, min_eq_right hu]

theorem vectorOfflineCost_zero_of_one_le
    (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    vectorOfflineCost (.finite u)
        (fun _ : Online.Label n => 0) =
      triangular n := by
  have heffective :=
    vectorEffectiveLengths_zero_of_one_le n hu
  calc
    vectorOfflineCost (.finite u)
        (fun _ : Online.Label n => 0) =
        pairCost
          (vectorEffectiveLengths (.finite u)
            (fun _ : Online.Label n => 0)) := by
      exact shortestFirst_pair_formula _
    _ = pairCost (List.replicate n 1) := by rw [heffective]
    _ = prefixCost (List.replicate n 1) := by
      symm
      exact prefixCost_eq_pairCost_of_pairwise (by simp)
    _ = triangular n := by
      rw [prefixCost_replicate]
      ring

/-- Exact terminal accounting for the completed pre-crossing phase of the
concrete mixed-quota run. -/
theorem MixedQuotaHistory.pre_completed_cost
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 1 < u)
    {M A B : ℕ} (hM : 0 < M) (hA : 0 < A)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.pre caps)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel).result
    let default :=
      mixedQuotaDefault n u (quotaFraction M A B) A B
        result.config.transcript
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u M A B) strategy default fuel
    vectorOfflineCost (.finite u) frozen = triangular n ∧
      u * triangular n ≤
        Online.runCompletionCost (.finite u) frozen result := by
  dsimp only
  let result :=
    (Online.adaptiveRun (.finite u)
      (oracle n u M A B) strategy fuel).result
  let default :=
    mixedQuotaDefault n u (quotaFraction M A B) A B
      result.config.transcript
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (oracle n u M A B) strategy default fuel
  have hreach :
      Online.AdaptiveReachable (.finite u)
        (oracle n u M A B) result.config
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned := by
    simpa [result] using
      Online.adaptiveRun_reachable (.finite u)
        (oracle n u M A B) strategy fuel
  have hprocess := hreach.processHistoryInvariant
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hβone : quotaFraction M A B < 1 :=
    quotaFraction_lt_one hA
  have htests :
      result.config.transcript.testResults.length = 0 := by
    exact history.pre_testResults_length_eq_zero_of_completed
      hn hβ hβone hprocess hcompleted
  have hrawCount :
      HiddenStoppingOracle.rawCount
          result.config.transcript = n := by
    exact history.pre_rawCount_eq_of_completed
      hn hβ hβone hprocess hcompleted
  have htail :
      (scan n u (quotaFraction M A B)
        result.config.transcript).tail = [] :=
    scan_tail_eq_nil_of_not_crossed hn hβ
      (history.pre_not_crossed hn hβ)
  have hdefaultZero : ∀ job, default job = 0 := by
    intro job
    dsimp [default]
    unfold mixedQuotaDefault
    rw [dif_neg]
    intro hexists
    obtain ⟨p, hp⟩ := hexists
    have hlabel :
        job ∈
          (virtualTail n u (quotaFraction M A B)
            (tailPositiveCount A B
              (scan n u (quotaFraction M A B)
                result.config.transcript).tailSize)
            (tailZeroCount A B
              (scan n u (quotaFraction M A B)
                result.config.transcript).tailSize)
            result.config.transcript).testResults.map Prod.fst :=
      List.mem_map.mpr ⟨(job, p), hp, rfl⟩
    rw [virtualTail_testLabels, htail] at hlabel
    simp at hlabel
  have hfrozenZero : ∀ job, frozen job = 0 := by
    intro job
    dsimp [frozen]
    rw [Online.frozenProcessingTimes_eq_default_of_not_tested]
    · exact hdefaultZero job
    · intro hexists
      obtain ⟨p, hp⟩ := hexists
      have hpos :
          0 < result.config.transcript.testResults.length :=
        List.length_pos_of_mem hp
      omega
  have hfrozenFun :
      frozen = (fun _ : Online.Label n => 0) :=
    funext hfrozenZero
  constructor
  · change vectorOfflineCost (.finite u) frozen = triangular n
    rw [hfrozenFun]
    exact vectorOfflineCost_zero_of_one_le n hu.le
  · change
      u * triangular n ≤
        Online.runCompletionCost (.finite u) frozen result
    have hall :
        result.config.transcript.AllTestsEqual u := by
      simpa [result] using history.pre_allTestsEqual
    have hprocessedLength :
        result.config.transcript.processedLabels.length = 0 := by
      have hle :=
        hprocess.processed_length_le_tests
      omega
    have hprocessedNil :
        result.config.transcript.processedLabels = [] :=
      List.eq_nil_of_length_eq_zero hprocessedLength
    have hpreInvariant :
        result.config.PreCostInvariant u :=
      hreach.preCostInvariant_of_allTestsEqual
        (by linarith) hall
    have hrawPrefix :
        prefixCost (List.replicate n u) ≤
          prefixCost
            (result.config.transcript.preCompletionWeights u) := by
      simpa [hrawCount, hprocessedLength] using
        Online.preCompletionWeights_blocks_le
          (by linarith : 0 ≤ u) result.config.transcript
    have hfrozenProcessed :
        ∀ job ∈ result.config.transcript.processedLabels,
          frozen job = u := by
      intro job hjob
      rw [hprocessedNil] at hjob
      simp at hjob
    have honline :
        u * triangular n ≤
          Online.suffixWeightedDuration (.finite u) frozen
            result.config.transcript := by
      calc
        u * triangular n =
            prefixCost (List.replicate n u) :=
          (prefixCost_replicate n u).symm
        _ ≤ prefixCost
            (result.config.transcript.preCompletionWeights u) :=
          hrawPrefix
        _ ≤ Online.suffixWeightedDuration (.finite u)
            (fun _ => u) result.config.transcript :=
          hpreInvariant
        _ = Online.suffixWeightedDuration (.finite u) frozen
            result.config.transcript := by
          symm
          exact
            Online.suffixWeightedDuration_eq_const_of_processed
              hfrozenProcessed
    rw [Online.runCompletionCost_eq_suffixWeightedDuration]
    exact honline

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
