import SchedulingPaper.MixedQuotaUniformOffsets
import SchedulingPaper.MixedQuotaRunAccounting
import SchedulingPaper.MixedQuotaNoCrossCost
import Mathlib.Tactic

/-!
# Unconditional adaptive mixed-quota lower bound

This file assembles the concrete mixed-quota oracle, its two terminal
branches, the uniform dynamic numerical estimate, and the physical
cap/tail exchange.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Before a crossing the canonical mixed default is identically zero. -/
theorem MixedQuotaHistory.pre_mixedQuotaDefault_eq_zero
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {A B : ℕ} {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config) :
    ∀ job, mixedQuotaDefault n u β A B
      config.transcript job = 0 := by
  have htail :
      (scan n u β config.transcript).tail = [] :=
    scan_tail_eq_nil_of_not_crossed hn hβ
      (history.pre_not_crossed hn hβ)
  intro job
  unfold mixedQuotaDefault
  rw [dif_neg]
  intro hexists
  obtain ⟨p, hp⟩ := hexists
  have hlabel :
      job ∈
        (virtualTail n u β
          (tailPositiveCount A B
            (scan n u β config.transcript).tailSize)
          (tailZeroCount A B
            (scan n u β config.transcript).tailSize)
          config.transcript).testResults.map Prod.fst :=
    List.mem_map.mpr ⟨(job, p), hp, rfl⟩
  rw [virtualTail_testLabels, htail] at hlabel
  simp at hlabel

/-- The canonical default is legal in both reachable phases. -/
theorem MixedQuotaHistory.mixedQuotaDefault_admissible_all
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M) (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        phase config) :
    ∀ job,
      Online.ValueAdmissible (.finite u)
        (mixedQuotaDefault n u (quotaFraction M A B) A B
          config.transcript job) := by
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  cases phase with
  | pre caps =>
      intro job
      rw [history.pre_mixedQuotaDefault_eq_zero hn hβ job]
      have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
      exact ⟨le_rfl, by linarith⟩
  | post H L z caps pending =>
      exact history.mixedQuotaDefault_admissible
        hn hβ hB hraw

/-- Any nonpositive requested ratio is defeated by the constant-zero
adversary at universal analysis fuel. -/
theorem adaptiveSizeLowerBound_of_nonpos_target
    {u target : ℝ} (hu : 1 ≤ u) (htarget : target ≤ 0) :
    ∀ (strategy : ∀ n, Online.Strategy n) (N : ℕ),
      ∃ n, N ≤ n ∧
        ∃ adversary : Online.Oracle n,
          ∃ default : Online.Label n → ℝ, ∃ fuel,
            adversary.Admissible (.finite u) ∧
            (∀ job, Online.ValueAdmissible (.finite u) (default job)) ∧
            adaptiveDefeats (.finite u) adversary
              (strategy n) default fuel target := by
  intro strategy N
  let n : ℕ := max N 1
  let adversary : Online.Oracle n := fun _ _ => 0
  let default : Online.Label n → ℝ := fun _ => 0
  let fuel : ℕ := 2 * n + 1
  refine ⟨n, Nat.le_max_left _ _, adversary, default, fuel, ?_, ?_, ?_⟩
  · intro transcript job
    exact ⟨le_rfl, zero_le_one.trans hu⟩
  · intro job
    exact ⟨le_rfl, zero_le_one.trans hu⟩
  · let frozen :=
      Online.frozenProcessingTimes (.finite u) adversary
        (strategy n) default fuel
    let result :=
      (Online.adaptiveRun (.finite u) adversary
        (strategy n) fuel).result
    change
      resultSettled result ∧
        (¬ resultCompleted result ∨
          target * vectorOfflineCost (.finite u) frozen ≤
            Online.runCompletionCost (.finite u) frozen result)
    have hsettled : resultSettled result := by
      simpa [result, fuel] using
        adaptiveRun_analysisFuel_settled
          (.finite u) adversary (strategy n)
    refine ⟨hsettled, ?_⟩
    by_cases hcompleted : resultCompleted result
    · right
      have hfrozen :
          frozen = (fun _ : Online.Label n => 0) := by
        simpa [frozen, adversary, default] using
          Online.frozenProcessingTimes_constant
            (.finite u) 0 (strategy n) fuel
      have hoffline :
          0 ≤ vectorOfflineCost (.finite u) frozen := by
        rw [hfrozen, vectorOfflineCost_zero_of_one_le n hu]
        unfold triangular
        positivity
      have honline :
          0 ≤ Online.runCompletionCost (.finite u) frozen result := by
        unfold Online.runCompletionCost
        apply Online.completionCost_nonneg
        · simpa [Cap.Valid] using (zero_lt_one.trans_le hu)
        · intro job
          rw [hfrozen]
          exact ⟨le_rfl, zero_le_one.trans hu⟩
      have hleft :
          target * vectorOfflineCost (.finite u) frozen ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg htarget hoffline
      exact hleft.trans honline
    · exact Or.inl hcompleted

/-- Positive-tail actual-run closure in the form needed by the coarse
cap-exchange remainder. -/
theorem adaptiveRun_completedPositiveTail_adaptiveDefeats_of_exchange_gap
    {n : ℕ} (hn : 0 < n) {u ratio remainder : ℝ}
    {M A B : ℕ} (hM : 0 < M) (hB : 0 < B)
    {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {L z : ℕ} {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H L z caps pending)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result)
    (hsettled :
      resultSettled
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let default :=
      mixedQuotaDefault n u (quotaFraction M A B) A B transcript
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u M A B) strategy default fuel
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    0 ≤
        mixedFiniteOnline u C K Z -
          ratio * mixedFiniteOffline u C K Z +
          (u - ratio) * mixedPrefixZeroOffline v (C + K + Z) -
          remainder →
      mixedFiniteOnline u C K Z +
            u * mixedPrefixZeroOffline v (C + K + Z) -
            remainder ≤
          Online.runCompletionCost (.finite u) frozen run.result →
        adaptiveDefeats (.finite u)
          (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  intro hgap honline
  have haccount :=
    adaptiveRun_completedPost_exact_accounting
      hn hM hB hH hraw strategy fuel history hcompleted
  have hcanonical :
      ratio *
          mixedExtendedFiniteOffline u
            (n -
              HiddenStoppingOracle.longCount u
                (Online.adaptiveRun (.finite u)
                  (oracle n u M A B) strategy fuel).result.config.transcript -
              H)
            (HiddenStoppingOracle.longCount u
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).result.config.transcript)
            (tailPositiveCount A B H) (tailZeroCount A B H) ≤
        mixedFiniteOnline u
            (HiddenStoppingOracle.longCount u
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).result.config.transcript)
            (tailPositiveCount A B H) (tailZeroCount A B H) +
          u *
            mixedPrefixZeroOffline
              (n -
                HiddenStoppingOracle.longCount u
                  (Online.adaptiveRun (.finite u)
                    (oracle n u M A B) strategy fuel).result.config.transcript -
                H)
              (HiddenStoppingOracle.longCount u
                  (Online.adaptiveRun (.finite u)
                    (oracle n u M A B) strategy fuel).result.config.transcript +
                tailPositiveCount A B H + tailZeroCount A B H) -
          remainder := by
    rw [mixedExtendedFiniteOffline]
    linarith
  unfold adaptiveDefeats
  dsimp only
  refine ⟨hsettled, Or.inr ?_⟩
  have hcost :
      ratio *
          vectorOfflineCost (.finite u)
            (terminalProcessing n u (quotaFraction M A B) A B
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).result.config.transcript
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).assigned) ≤
        Online.runCompletionCost (.finite u)
          (terminalProcessing n u (quotaFraction M A B) A B
            (Online.adaptiveRun (.finite u)
              (oracle n u M A B) strategy fuel).result.config.transcript
            (Online.adaptiveRun (.finite u)
              (oracle n u M A B) strategy fuel).assigned)
          (Online.adaptiveRun (.finite u)
            (oracle n u M A B) strategy fuel).result := by
    rw [haccount.1]
    exact hcanonical.trans (by
      simpa [Online.frozenProcessingTimes, terminalProcessing] using honline)
  simpa [Online.frozenProcessingTimes, terminalProcessing] using hcost

/-- The two trace-global facts isolated from the final assembly.  Both fields
are proved for the concrete oracle by the crossing-prefix and augmented-tail
exchange developments. -/
structure MixedQuotaCompletionBridge : Prop where
  crossing
      {n : ℕ} (hn : 0 < n) {u : ℝ}
      {M A B : ℕ} (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
      (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
      {H L z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n} {config : Online.Config n}
      (history :
        MixedQuotaHistory n u (quotaFraction M A B) A B
          (.post H L z caps pending) config) :
      let C := HiddenStoppingOracle.longCount u config.transcript
      let v := n - C - H
      n = v + C + H ∧
        (C + H = 0 ∨
          ∃ q, DynamicQuotaWindow M A B q C H)
  physical
      {n : ℕ} (hn : 0 < n) {u : ℝ}
      {M A B : ℕ} (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
      {H : ℕ} (hH : 0 < H)
      (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
      (strategy : Online.Strategy n) (fuel : ℕ)
      {L z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      (history :
        MixedQuotaHistory n u (quotaFraction M A B) A B
          (.post H L z caps pending)
          (Online.adaptiveRun (.finite u)
            (oracle n u M A B) strategy fuel).result.config)
      (hcompleted :
        resultCompleted
          (Online.adaptiveRun (.finite u)
            (oracle n u M A B) strategy fuel).result) :
      let run :=
        Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel
      let transcript := run.result.config.transcript
      let default :=
        mixedQuotaDefault n u (quotaFraction M A B) A B transcript
      let frozen :=
        Online.frozenProcessingTimes (.finite u)
          (oracle n u M A B) strategy default fuel
      let C := HiddenStoppingOracle.longCount u transcript
      let v := n - C - H
      let K := tailPositiveCount A B H
      let Z := tailZeroCount A B H
      mixedFiniteOnline u C K Z +
            u * mixedPrefixZeroOffline v (C + K + Z) -
            dynamicCapExchangeRemainder u A B C H ≤
        Online.runCompletionCost (.finite u) frozen run.result

/-- Once the two concrete trace-global bridge fields are available, all
remaining parameter choice, rounding, small-scale absorption, freezing, and
terminal case analysis is automatic. -/
theorem mixedQuota_adaptive_of_completionBridge
    (bridge : MixedQuotaCompletionBridge)
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ))
    (huUpper : (u : ℝ) < zStar) :
    AdaptiveSizeLowerBound (.finite (u : ℝ)) (mixedFiniteCurve u) := by
  intro strategies ε hε N
  let c : ℝ := mixedFiniteCurve u - ε
  have huOne : 1 ≤ (u : ℝ) := by
    linarith [goldenRatio_pos]
  by_cases hc : 0 ≤ c
  · obtain ⟨M, A, B, hM, hA, hB, htarget, hraw, hdeferral⟩ :=
      exists_integral_mixed_parameters u huLower huUpper hε
    have huc : 0 < (u : ℝ) - c := by
      dsimp [c]
      exact mixedTarget_cap_gap u huLower hε
    obtain ⟨n, hnN, hclosing⟩ :=
      exists_size_closing_dynamicQuota_with_exchangeRemainder
        hM hA hB huOne hc huc hraw htarget hdeferral
        (max N 1)
    have hnN' : N ≤ n :=
      (Nat.le_max_left N 1).trans hnN
    have hn : 0 < n := by
      have : 1 ≤ n := (Nat.le_max_right N 1).trans hnN
      omega
    let fuel : ℕ := 2 * n + 1
    let run :=
      Online.adaptiveRun (.finite (u : ℝ))
        (oracle n (u : ℝ) M A B) (strategies n) fuel
    let result := run.result
    obtain ⟨hsettled, phase, history⟩ :=
      mixedQuota_analysisFuel_history
        hn hM (strategies n)
    let default : Online.Label n → ℝ :=
      mixedQuotaDefault n (u : ℝ) (quotaFraction M A B) A B
        result.config.transcript
    refine
      ⟨n, hnN', oracle n (u : ℝ) M A B, default, fuel,
        oracle_admissible hB hraw, ?_, ?_⟩
    · intro job
      simpa [default, result, run, fuel] using
        history.mixedQuotaDefault_admissible_all
          hn hM hB hraw job
    · by_cases hcompleted : resultCompleted result
      · cases phase with
        | pre caps =>
            have hpre :=
              history.pre_completed_cost
                hn (lt_of_lt_of_le
                  (by linarith [goldenRatio_pos] :
                    1 < goldenRatio + 2) huLower.le)
                hM hA (strategies n) fuel
                (by simpa [result, run] using hcompleted)
            unfold adaptiveDefeats
            dsimp only
            refine ⟨?_, Or.inr ?_⟩
            · simpa [result, run, fuel] using hsettled
            · have htri : 0 ≤ triangular n := by
                unfold triangular
                positivity
              calc
                c *
                      vectorOfflineCost (.finite (u : ℝ))
                        (Online.frozenProcessingTimes
                          (.finite (u : ℝ))
                          (oracle n (u : ℝ) M A B)
                          (strategies n) default fuel) =
                    c * triangular n := by
                      rw [hpre.1]
                _ ≤ (u : ℝ) * triangular n :=
                  mul_le_mul_of_nonneg_right
                    (by linarith : c ≤ (u : ℝ)) htri
                _ ≤
                    Online.runCompletionCost (.finite (u : ℝ))
                      (Online.frozenProcessingTimes
                        (.finite (u : ℝ))
                        (oracle n (u : ℝ) M A B)
                        (strategies n) default fuel)
                      (Online.adaptiveRun (.finite (u : ℝ))
                        (oracle n (u : ℝ) M A B)
                        (strategies n) fuel).result := hpre.2
        | post H L z caps pending =>
            have hcross :=
              bridge.crossing hn hM hA hB hraw history
            let C :=
              HiddenStoppingOracle.longCount (u : ℝ)
                result.config.transcript
            let v := n - C - H
            let K := tailPositiveCount A B H
            let Z := tailZeroCount A B H
            have hcross' :
                n = v + C + H ∧
                  (C + H = 0 ∨
                    ∃ q, DynamicQuotaWindow M A B q C H) := by
              simpa [C, v, result, run, fuel] using hcross
            have hsize : n = v + C + H := hcross'.1
            rcases hcross'.2 with hzero | ⟨q, hwindow⟩
            · have hCH : C = 0 ∧ H = 0 := by omega
              rcases hCH with ⟨hC, hH⟩
              have hCfull :
                  HiddenStoppingOracle.longCount (u : ℝ)
                    (Online.adaptiveRun (.finite (u : ℝ))
                      (oracle n (u : ℝ) M A B)
                      (strategies n) fuel).result.config.transcript = 0 := by
                simpa [C, result, run] using hC
              subst H
              have hdefeat :=
                adaptiveRun_completedPost_adaptiveDefeats_cases
                  hn hM hB hraw (show c ≤ (u : ℝ) by linarith)
                  (strategies n) fuel history
                  (by simpa [result, run] using hcompleted)
                  (by simpa [result, run, fuel] using hsettled)
                  (by
                    intro _
                    simpa [hCfull] using
                      (zeroTail_zeroCap_ratio_le_physical
                        (v := n) (show c ≤ (u : ℝ) by linarith)))
                  (by intro h; omega)
                  (by intro h; omega)
              simpa [c, default, result, run, fuel] using hdefeat
            · have hgap :=
                hclosing v C H q hsize hwindow
              by_cases hH : H = 0
              · subst H
                have hzeroRatio :
                    c * mixedExtendedFiniteOffline
                        (u : ℝ) (n - C) C 0 0 ≤
                      prefixCost
                        (List.replicate (n - C) (u : ℝ) ++
                          List.replicate C (1 + (u : ℝ))) := by
                  have hv : v = n - C := by
                    omega
                  rw [← hv]
                  exact zeroTail_ratio_le_physical_of_exchange_gap
                    (A := A) (B := B)
                    (by
                      simpa [tailPositiveCount, tailZeroCount] using hgap)
                have hdefeat :=
                  adaptiveRun_completedPost_adaptiveDefeats_cases
                    hn hM hB hraw (show c ≤ (u : ℝ) by linarith)
                    (strategies n) fuel history
                    (by simpa [result, run] using hcompleted)
                    (by simpa [result, run, fuel] using hsettled)
                    (by intro _; simpa [C, result, run] using hzeroRatio)
                    (by intro h; omega)
                    (by intro h; omega)
                simpa [c, default, result, run, fuel] using hdefeat
              · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
                have hphysical :=
                  bridge.physical hn hM hA hB hHpos hraw
                    (strategies n) fuel history
                    (by simpa [result, run] using hcompleted)
                have hgap' :
                    0 ≤
                      mixedFiniteOnline (u : ℝ) C K Z -
                        c * mixedFiniteOffline (u : ℝ) C K Z +
                        ((u : ℝ) - c) *
                          mixedPrefixZeroOffline v (C + K + Z) -
                        dynamicCapExchangeRemainder
                          (u : ℝ) A B C H := by
                  have htailEq : C + K + Z = C + H := by
                    have hsplit := tail_split A B H
                    dsimp [K, Z]
                    omega
                  rw [htailEq]
                  exact hgap
                have hdefeat :=
                  adaptiveRun_completedPositiveTail_adaptiveDefeats_of_exchange_gap
                    hn hM hB hHpos hraw (strategies n) fuel
                    history
                    (by simpa [result, run] using hcompleted)
                    (by simpa [result, run, fuel] using hsettled)
                    hgap'
                    (by
                      simpa [C, v, K, Z, default, result, run, fuel]
                        using hphysical)
                simpa [c, default, result, run, fuel] using hdefeat
      · unfold adaptiveDefeats
        dsimp only
        refine ⟨?_, Or.inl ?_⟩
        · simpa [result, run, fuel] using hsettled
        · simpa [result, run] using hcompleted
  · have hc' : c ≤ 0 := le_of_not_ge hc
    simpa [c] using
      adaptiveSizeLowerBound_of_nonpos_target
        huOne hc' strategies N

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
