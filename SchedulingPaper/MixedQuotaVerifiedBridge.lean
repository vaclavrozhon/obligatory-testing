import SchedulingPaper.MixedQuotaAdaptive
import SchedulingPaper.MixedQuotaVerifiedCrossing
import SchedulingPaper.MixedQuotaExchangeRuntimeGlue
import Mathlib.Tactic

/-!
# Verified completion bridge for the mixed-quota oracle

This module discharges the two trace-global premises of
`MixedQuotaCompletionBridge`.  The only extra lifecycle fact needed by the
terminal physical exchange is that every label retained in the cap-pending
list is genuinely live in state `tested u`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

private def CapLive
    (u : ℝ) (caps : MixedCapPending n)
    (jobs : Online.Label n → Online.JobState) : Prop :=
  caps.Nodup ∧
    ∀ job ∈ caps, jobs job = .tested u

/-- Phase-indexed form of the live-cap lifecycle invariant. -/
def MixedPhase.capLiveInvariant
    (u : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre caps => CapLive u caps config.jobs
  | .post _ _ _ caps _ => CapLive u caps config.jobs

private theorem CapLive.update_fresh
    {u : ℝ} {caps : MixedCapPending n}
    {jobs : Online.Label n → Online.JobState}
    (live : CapLive u caps jobs)
    {job : Online.Label n}
    (hjob : jobs job = .untouched)
    (state : Online.JobState) :
    CapLive u caps (Function.update jobs job state) := by
  refine ⟨live.1, ?_⟩
  intro capped hcapped
  have hcappedState := live.2 capped hcapped
  have hne : capped ≠ job := by
    intro heq
    subst capped
    rw [hjob] at hcappedState
    contradiction
  simpa [Function.update, hne] using hcappedState

private theorem CapLive.append_fresh_test
    {u : ℝ} {caps : MixedCapPending n}
    {jobs : Online.Label n → Online.JobState}
    (live : CapLive u caps jobs)
    {job : Online.Label n}
    (hjob : jobs job = .untouched) :
    CapLive u (caps ++ [job])
      (Function.update jobs job (.tested u)) := by
  have hnot : job ∉ caps := by
    intro hmem
    have hstate := live.2 job hmem
    rw [hjob] at hstate
    contradiction
  constructor
  · apply List.nodup_append.mpr
    refine ⟨live.1, by simp, ?_⟩
    intro capped hcapped added hadded
    have haddEq : added = job := by simpa using hadded
    subst added
    intro heq
    subst capped
    exact hnot hcapped
  · intro capped hcapped
    rcases List.mem_append.mp hcapped with hold | hnew
    · have hstate := live.2 capped hold
      have hne : capped ≠ job := by
        intro heq
        subst capped
        exact hnot hold
      simpa [Function.update, hne] using hstate
    · have heq : capped = job := by simpa using hnew
      subst capped
      simp [Function.update]

private theorem CapLive.update_tested_ne
    {u p : ℝ} {caps : MixedCapPending n}
    {jobs : Online.Label n → Online.JobState}
    (live : CapLive u caps jobs)
    {job : Online.Label n}
    (hjob : jobs job = .tested p)
    (hp : p ≠ u) :
    CapLive u caps (Function.update jobs job .done) := by
  refine ⟨live.1, ?_⟩
  intro capped hcapped
  have hstate := live.2 capped hcapped
  have hne : capped ≠ job := by
    intro heq
    subst capped
    rw [hjob] at hstate
    injection hstate with hpu
    exact hp hpu
  simpa [Function.update, hne] using hstate

private theorem CapLive.remove
    {u : ℝ} {before after : MixedCapPending n}
    {jobs : Online.Label n → Online.JobState}
    {job : Online.Label n}
    (live : CapLive u (before ++ job :: after) jobs) :
    CapLive u (before ++ after)
      (Function.update jobs job .done) := by
  have holdNodup := List.nodup_append.mp live.1
  have htailNodup := List.nodup_cons.mp holdNodup.2.1
  constructor
  · apply List.nodup_append.mpr
    refine ⟨holdNodup.1, htailNodup.2, ?_⟩
    intro left hleft right hright
    exact holdNodup.2.2 left hleft right (by simp [hright])
  · intro capped hcapped
    have holdMem :
        capped ∈ before ++ job :: after := by
      rcases List.mem_append.mp hcapped with hbefore | hafter
      · exact List.mem_append.mpr (Or.inl hbefore)
      · exact List.mem_append.mpr (Or.inr (by simp [hafter]))
    have hstate := live.2 capped holdMem
    have hne : capped ≠ job := by
      rcases List.mem_append.mp hcapped with hbefore | hafter
      · exact holdNodup.2.2 capped hbefore job (by simp)
      · intro heq
        subst capped
        exact htailNodup.1 hafter
    simpa [Function.update, hne] using hstate

/-- Every cap retained by a reachable mixed history is distinct and is
currently live in state `tested u`. -/
theorem MixedQuotaHistory.capLive_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ} (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.capLiveInvariant u config := by
  have hu : 0 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  induction history with
  | initial =>
      simp [MixedPhase.capLiveInvariant, CapLive]
  | preTestBelow history job hjob hbelow ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.append_fresh_test hjob
  | preTestCross history job hjob hcross H hH ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.append_fresh_test hjob
  | preProcessCap history hjob ih =>
      simpa [MixedPhase.capLiveInvariant] using ih.remove
  | preRawBelow history job hjob hbelow ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob .done
  | preRawCross history job hjob hcross H hH ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob .done
  | postTestPositive history hL job hjob ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob
          (.tested
            (harmonicLevel
              (tailZeroCount A B _ : ℝ) 0 (_ - 1)))
  | postTestZero history hz job hjob ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob (.tested 0)
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      have hpVirtual :
          (job, p) ∈
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults :=
        (history.post_virtual_history hn hβ)
          |>.pending_mem_testResult (job, p) (by simp)
      have hpDefault :=
        history.mixedQuotaDefault_eq_of_virtual_testResult
          hn hβ hpVirtual
      have hpSafe :=
        (history.mixedQuotaDefault_rawSafe
          hn hβ hB hraw job).2
      rw [hpDefault] at hpSafe
      have hpNe : p ≠ u := by linarith
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_tested_ne hjob hpNe
  | postProcessZero history job hjob hvirtual ih =>
      have hzeroNe : (0 : ℝ) ≠ u := by linarith
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_tested_ne hjob hzeroNe
  | postProcessCap history hjob hvirtual ih =>
      simpa [MixedPhase.capLiveInvariant] using ih.remove
  | postRawPositive history hL job hjob ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob .done
  | postRawZero history hz job hjob ih =>
      simpa [MixedPhase.capLiveInvariant] using
        ih.update_fresh hjob .done

/-- A completed post-crossing configuration has no live cap pending. -/
theorem MixedQuotaHistory.post_caps_eq_nil_of_completed
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ} (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (hcompleted : ∀ job, config.jobs job = .done) :
    caps = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro job hmem
  have hlive :=
    (history.capLive_invariant hn hβ hB hraw).2 job hmem
  rw [hcompleted job] at hlive
  contradiction

/-- Actual-run wrapper around the terminal physical exchange. -/
theorem adaptiveRun_completedPost_full_exchange_lower
    {n : ℕ} (hn : 0 < n) {u : ℝ}
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
      Online.runCompletionCost (.finite u) frozen run.result := by
  dsimp only
  let run :=
    Online.adaptiveRun (.finite u)
      (oracle n u M A B) strategy fuel
  let transcript := run.result.config.transcript
  let assignment := run.assigned
  let processing :=
    terminalProcessing n u (quotaFraction M A B) A B
      transcript assignment
  let C := HiddenStoppingOracle.longCount u transcript
  let v := n - C - H
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hreachable :
      Online.AdaptiveReachable (.finite u)
        (oracle n u M A B) run.result.config assignment := by
    simpa [run, assignment] using
      Online.adaptiveRun_reachable (.finite u)
        (oracle n u M A B) strategy fuel
  have hterminal :=
    history.post_terminal_indices hn hβ hB
      hreachable.processHistoryInvariant hcompleted
  rcases hterminal with ⟨hL, hz, hpending⟩
  have hcaps :
      caps = [] :=
    history.post_caps_eq_nil_of_completed
      hn hβ hB hraw hcompleted
  subst L
  subst z
  subst caps
  subst pending
  have hsupported :
      Online.SupportedByTranscript assignment transcript := by
    simpa [transcript] using hreachable.supportedByTranscript
  have hmatches :
      Online.MatchesTranscript assignment transcript := by
    simpa [run, assignment, transcript, Online.adaptiveRun] using
      (Online.runAdaptiveFuel_matchesTranscript
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (by
          simp [Online.MatchesTranscript,
            Online.Config.initial, Online.emptyAssignment]))
  have hassignment :
      Online.AssignmentAdmissible (.finite u) assignment := by
    simpa [run, assignment, Online.adaptiveRun] using
      (Online.runAdaptiveFuel_assignment_admissible
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (oracle_admissible hB hraw)
        (Online.emptyAssignment_admissible (.finite u)))
  have hphysical :=
    history.terminalProcessing_full_exchange_lower
      hn hβ hB hH hraw assignment
      hsupported hmatches hassignment
  have htail : C + K + Z = C + H := by
    have hsplit := tail_split A B H
    dsimp [K, Z]
    omega
  rw [htail]
  simpa [run, transcript, assignment, processing, C, v, K, Z,
    Online.frozenProcessingTimes, terminalProcessing,
    Online.runCompletionCost] using hphysical

/-- Both concrete trace-global obligations of the adaptive mixed-quota
assembly. -/
noncomputable def verifiedMixedQuotaCompletionBridge :
    MixedQuotaCompletionBridge where
  crossing := by
    intro n hn u M A B hM hA hB hraw
      H L z caps pending config history
    exact
      history.fullCount_dynamicQuotaWindow_or_zero
        hn hM hA hB hraw
  physical := by
    intro n hn u M A B hM hA hB
      H hH hraw strategy fuel L z caps pending
      history hcompleted
    exact
      adaptiveRun_completedPost_full_exchange_lower
        hn hM hB hH hraw strategy fuel history hcompleted

end MixedQuotaOracle

/-- Unconditional adaptive lower bound on the strict mixed-quota interval. -/
theorem mixedQuota_adaptive
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ))
    (huUpper : (u : ℝ) < zStar) :
    AdaptiveSizeLowerBound (.finite (u : ℝ)) (mixedFiniteCurve u) :=
  MixedQuotaOracle.mixedQuota_adaptive_of_completionBridge
    MixedQuotaOracle.verifiedMixedQuotaCompletionBridge
    u huLower huUpper

end LowerBound

end

end SchedulingPaper
