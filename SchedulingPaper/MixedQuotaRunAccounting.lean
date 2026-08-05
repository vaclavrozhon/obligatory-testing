import SchedulingPaper.MixedQuotaFrozenMultiset
import SchedulingPaper.MixedQuotaRunFacts
import SchedulingPaper.MixedQuotaDynamicNumerics
import Mathlib.Tactic

/-!
# Actual-run accounting for the mixed-quota construction

This module removes the last bookkeeping premises from the completed
post-crossing branch.  The only remaining conditional input in the strongest
mixed-core theorem is the physical online exchange inequality; the frozen
multiset and exact offline identity are now automatic.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Static zero-tail endpoint of the extended accounting theorem. -/
theorem vectorOfflineCost_eq_mixedExtendedFiniteOffline_zeroTail_of_perm
    {n v C : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (processing : Online.Label n → ℝ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C 0 0).Perm
        (vectorEffectiveLengths (.finite u) processing)) :
    vectorOfflineCost (.finite u) processing =
      mixedExtendedFiniteOffline u v C 0 0 := by
  have hcandidate :
      mixedExtendedEffectiveCandidate u v C 0 0 =
        List.replicate v 1 ++ List.replicate C u := by
    simp [mixedExtendedEffectiveCandidate,
      mixedEffectiveCandidate,
      mixedHarmonicEffectiveCandidate,
      harmonicFutureLevels]
  have hpairwise :
      (mixedExtendedEffectiveCandidate u v C 0 0).Pairwise
        (· ≤ ·) := by
    rw [hcandidate, List.pairwise_append]
    refine ⟨by simp, by simp, ?_⟩
    intro a ha b hb
    have haEq : a = 1 := (List.mem_replicate.mp ha).2
    have hbEq : b = u := (List.mem_replicate.mp hb).2
    simpa [haEq, hbEq] using hu
  unfold vectorOfflineCost
  rw [shortestFirst_pair_formula]
  rw [← pairCost_perm hperm]
  rw [← prefixCost_eq_pairCost_of_pairwise hpairwise]
  rw [hcandidate, prefixCost_append,
    prefixCost_replicate, prefixCost_replicate]
  simp [mixedExtendedFiniteOffline, mixedPrefixZeroOffline,
    mixedFiniteOffline, harmonicFiniteOffline,
    harmonicFutureLevels, triangular]
  ring

/-- Exact ALG/OPT accounting for an actual adaptive run whose mixed tail is
already in its terminal state. -/
theorem adaptiveRun_terminalProcessing_exact_accounting
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H 0 0 caps [])
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let processing :=
      terminalProcessing n u (quotaFraction M A B) A B
        transcript run.assigned
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    vectorOfflineCost (.finite u) processing =
        mixedExtendedFiniteOffline u v C K Z ∧
      harmonicFiniteOnline K Z 0 ≤
        Online.runCompletionCost (.finite u)
          processing run.result ∧
      n = v + C + K + Z := by
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
  have hsupported :
      Online.SupportedByTranscript assignment transcript := by
    simpa [transcript] using hreachable.supportedByTranscript
  have hassignment :
      Online.AssignmentAdmissible (.finite u) assignment := by
    simpa [run, assignment, Online.adaptiveRun] using
      (Online.runAdaptiveFuel_assignment_admissible
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (oracle_admissible hB hraw)
        (Online.emptyAssignment_admissible (.finite u)))
  have hmultiset :=
    adaptiveRun_terminalProcessing_frozenMultiset
      hn hM hB hH hraw strategy fuel history
  have hperm :
      (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u) processing) := by
    simpa [run, transcript, assignment, processing, C, v, K, Z] using
      hmultiset.1
  have hsize : n = v + C + K + Z := by
    simpa [run, transcript, C, v, K, Z] using hmultiset.2
  have haccount :=
    history.terminalProcessing_exact_accounting
      hn hβ hB hH hraw assignment hsupported hassignment
      v C (by simpa [processing, K, Z] using hperm)
  refine ⟨?_, ?_, hsize⟩
  · simpa [processing, v, C, K, Z] using haccount.1
  · simpa [processing, K, Z, Online.runCompletionCost,
      run, transcript] using haccount.2

/-- A completed actual post-crossing run automatically has terminal tail
indices, so no terminal-shape hypothesis is needed by callers. -/
theorem adaptiveRun_completedPost_exact_accounting
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
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
    let processing :=
      terminalProcessing n u (quotaFraction M A B) A B
        transcript run.assigned
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    vectorOfflineCost (.finite u) processing =
        mixedExtendedFiniteOffline u v C K Z ∧
      harmonicFiniteOnline K Z 0 ≤
        Online.runCompletionCost (.finite u)
          processing run.result ∧
      n = v + C + K + Z := by
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hreachable :=
    Online.adaptiveRun_reachable (.finite u)
      (oracle n u M A B) strategy fuel
  have hterminal :=
    history.post_terminal_indices hn hβ hB
      hreachable.processHistoryInvariant hcompleted
  rcases hterminal with ⟨hL, hz, hpending⟩
  subst L
  subst z
  subst pending
  exact adaptiveRun_terminalProcessing_exact_accounting
    hn hM hB hH hraw strategy fuel history

/-- Exact zero-tail accounting.  Here the online lower benchmark is the
literal completed raw/cap block; no positive harmonic scale is available or
needed. -/
theorem adaptiveRun_completedZeroTail_exact_accounting
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post 0 0 0 caps [])
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
    let processing :=
      terminalProcessing n u (quotaFraction M A B) A B
        transcript run.assigned
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C
    vectorOfflineCost (.finite u) processing =
        mixedExtendedFiniteOffline u v C 0 0 ∧
      prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) ≤
        Online.runCompletionCost (.finite u)
          processing run.result ∧
      n = v + C := by
  dsimp only
  let run :=
    Online.adaptiveRun (.finite u)
      (oracle n u M A B) strategy fuel
  let config := run.result.config
  let transcript := config.transcript
  let assignment := run.assigned
  let processing :=
    terminalProcessing n u (quotaFraction M A B) A B
      transcript assignment
  let C := HiddenStoppingOracle.longCount u transcript
  let v := n - C
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hu : 1 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  have hreachable :
      Online.AdaptiveReachable (.finite u)
        (oracle n u M A B) config assignment := by
    simpa [run, config, assignment] using
      Online.adaptiveRun_reachable (.finite u)
        (oracle n u M A B) strategy fuel
  have hprocess := hreachable.processHistoryInvariant
  have hstarted := hreachable.startedHistoryInvariant
  have hvirtualNil :
      (virtualTail n u (quotaFraction M A B)
        (tailPositiveCount A B 0)
        (tailZeroCount A B 0)
        transcript).testResults = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlength :=
      history.terminalVirtualLabels_length hn hβ
    simpa [terminalVirtualLabels, transcript, config] using hlength
  have hall : transcript.AllTestsEqual u := by
    intro job p hp
    rcases history.testValue_classification hn hβ job p
        (by simpa [transcript, config] using hp) with hcap | hvirtual
    · exact hcap
    · rw [hvirtualNil] at hvirtual
      simp at hvirtual
  have hlong :
      HiddenStoppingOracle.longCount u transcript =
        transcript.testResults.length :=
    HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
      hall
  have hstartedLength : transcript.startedLabels.length = n := by
    simpa [transcript, config] using
      Online.Config.startedLabels_length_eq_card_of_completed
        hstarted hprocess hcompleted
  have hrawCount :
      HiddenStoppingOracle.rawCount transcript = v := by
    have hstartedCount :=
      transcript.startedLabels_length_eq_raw_add_tests
    dsimp [v, C]
    omega
  have htestLabelsNodup :
      (transcript.testResults.map Prod.fst).Nodup := by
    exact List.Nodup.sublist
      (transcript.testLabels_sublist_startedLabels)
      hstarted.nodup
  have hprocessedLength :
      transcript.processedLabels.length =
        transcript.testResults.length := by
    have hle :
        transcript.processedLabels.length ≤
          transcript.testResults.length := by
      simpa [transcript, config] using
        hprocess.processed_length_le_tests
    have hreverse :
        transcript.testResults.length ≤
          transcript.processedLabels.length := by
      let tested := transcript.testResults.map Prod.fst
      let processed := transcript.processedLabels
      have hsubset : tested.toFinset ⊆ processed.toFinset := by
        intro job hjob
        have hmem : job ∈ tested := by
          simpa [tested] using hjob
        rcases List.mem_map.mp hmem with
          ⟨⟨testedJob, p⟩, hp, heq⟩
        change testedJob = job at heq
        subst testedJob
        by_contra hnot
        have hstate :=
          hprocess.recordedUnprocessedTested job p hp
            (by simpa [processed] using hnot)
        have hdone : config.jobs job = .done := by
          exact hcompleted job
        rw [hdone] at hstate
        contradiction
      calc
        transcript.testResults.length = tested.length := by
          simp [tested]
        _ = tested.toFinset.card := by
          rw [List.toFinset_card_of_nodup]
          simpa [tested] using htestLabelsNodup
        _ ≤ processed.toFinset.card :=
          Finset.card_le_card hsubset
        _ = processed.length := by
          rw [List.toFinset_card_of_nodup]
          simpa [processed] using hprocess.processedNodup
    exact Nat.le_antisymm hle hreverse
  have hprocessedC :
      transcript.processedLabels.length = C := by
    dsimp [C]
    omega
  have hfrozenProcessed :
      ∀ job ∈ transcript.processedLabels,
        processing job = u := by
    intro job hjob
    have hrecorded :=
      hprocess.processedRecorded job hjob
    rcases List.mem_map.mp hrecorded with
      ⟨⟨testedJob, p⟩, hp, heq⟩
    change testedJob = job at heq
    subst testedJob
    have hpEq : p = u := hall job p hp
    subst p
    have hassigned :
        assignment job = some u := by
      simpa [run, assignment, transcript, config] using
        Online.adaptiveRun_assigned_of_testResult
          (.finite u) (oracle n u M A B)
          strategy fuel hp
    simp [processing, terminalProcessing, hassigned]
  have hpreInvariant : config.PreCostInvariant u :=
    hreachable.preCostInvariant_of_allTestsEqual
      (by linarith) (by simpa [transcript, config] using hall)
  have honline :
      prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) ≤
        Online.runCompletionCost (.finite u)
          processing run.result := by
    rw [Online.runCompletionCost_eq_suffixWeightedDuration]
    calc
      prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) ≤
          prefixCost (transcript.preCompletionWeights u) := by
        simpa [hrawCount, hprocessedC] using
          Online.preCompletionWeights_blocks_le
            (by linarith : 0 ≤ u) transcript
      _ ≤ Online.suffixWeightedDuration (.finite u)
          (fun _ => u) transcript := by
        simpa [Online.Config.PreCostInvariant,
          transcript, config] using hpreInvariant
      _ = Online.suffixWeightedDuration (.finite u)
          processing transcript := by
        symm
        exact
          Online.suffixWeightedDuration_eq_const_of_processed
            hfrozenProcessed
  have hmultiset :=
    adaptiveRun_terminalProcessing_frozenMultiset_all
      hn hM hB hraw strategy fuel history
  have hperm :
      (mixedExtendedEffectiveCandidate u v C 0 0).Perm
        (vectorEffectiveLengths (.finite u) processing) := by
    simpa [run, config, transcript, assignment, processing,
      v, C, tailPositiveCount, tailZeroCount] using hmultiset.1
  have hoffline :
      vectorOfflineCost (.finite u) processing =
        mixedExtendedFiniteOffline u v C 0 0 :=
    vectorOfflineCost_eq_mixedExtendedFiniteOffline_zeroTail_of_perm
      hu.le processing hperm
  have hsize : n = v + C := by
    simpa [run, config, transcript, v, C,
      tailPositiveCount, tailZeroCount] using hmultiset.2
  exact ⟨hoffline, honline, hsize⟩

/-- The completed `H = 0` branch closes against its exact raw/cap physical
benchmark.  This statement makes the genuinely necessary zero-tail
numerical inequality explicit. -/
theorem adaptiveRun_completedZeroTail_adaptiveDefeats
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post 0 0 0 caps [])
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
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C
    ratio * mixedExtendedFiniteOffline u v C 0 0 ≤
        prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) →
      adaptiveDefeats (.finite u)
        (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  intro hratio
  have haccount :=
    adaptiveRun_completedZeroTail_exact_accounting
      hn hM hB hraw strategy fuel history hcompleted
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
    exact hratio.trans haccount.2.1
  simpa [Online.frozenProcessingTimes, terminalProcessing] using hcost

/-- The currently available unconditional online bound closes any ratio
already dominated by the harmonic benchmark of the recovered instance. -/
theorem adaptiveRun_terminal_ratio_of_harmonic_bound
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H 0 0 caps [])
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let processing :=
      terminalProcessing n u (quotaFraction M A B) A B
        transcript run.assigned
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    ratio * mixedExtendedFiniteOffline u v C K Z ≤
        harmonicFiniteOnline K Z 0 →
      ratio * vectorOfflineCost (.finite u) processing ≤
        Online.runCompletionCost (.finite u)
          processing run.result := by
  dsimp only
  intro hratio
  have haccount :=
    adaptiveRun_terminalProcessing_exact_accounting
      hn hM hB hH hraw strategy fuel history
  rw [haccount.1]
  exact hratio.trans haccount.2.1

/-- Conditional global-exchange closure.  Once the physical transcript is
known to dominate the full canonical mixed online expression, the numerical
mixed-core inequality and `ratio ≤ u` imply the desired actual-run ratio.

This is the strongest bridge available before the augmented global exchange
is exported as a terminal physical-cost theorem. -/
theorem adaptiveRun_terminal_ratio_of_full_online_lower
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hratioCap : ratio ≤ u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H 0 0 caps [])
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let processing :=
      terminalProcessing n u (quotaFraction M A B) A B
        transcript run.assigned
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    ratio * mixedFiniteOffline u C K Z ≤
        mixedFiniteOnline u C K Z →
      mixedFiniteOnline u C K Z +
            u * mixedPrefixZeroOffline v (C + K + Z) ≤
          Online.runCompletionCost (.finite u)
            processing run.result →
        ratio * vectorOfflineCost (.finite u) processing ≤
          Online.runCompletionCost (.finite u)
            processing run.result := by
  dsimp only
  intro hcore honline
  have haccount :=
    adaptiveRun_terminalProcessing_exact_accounting
      hn hM hB hH hraw strategy fuel history
  rw [haccount.1]
  rw [mixedExtendedFiniteOffline]
  have hprefix :
      0 ≤ mixedPrefixZeroOffline
        (n -
            HiddenStoppingOracle.longCount u
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).result.config.transcript -
            H)
        (HiddenStoppingOracle.longCount u
            (Online.adaptiveRun (.finite u)
              (oracle n u M A B) strategy fuel).result.config.transcript +
          tailPositiveCount A B H + tailZeroCount A B H) :=
    mixedPrefixZeroOffline_nonneg _ _
  calc
    ratio *
          (mixedPrefixZeroOffline
              (n -
                  HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript -
                  H)
              (HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript +
                tailPositiveCount A B H + tailZeroCount A B H) +
            mixedFiniteOffline u
              (HiddenStoppingOracle.longCount u
                (Online.adaptiveRun (.finite u)
                  (oracle n u M A B) strategy fuel).result.config.transcript)
              (tailPositiveCount A B H) (tailZeroCount A B H)) =
        ratio *
            mixedPrefixZeroOffline
              (n -
                  HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript -
                  H)
              (HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript +
                tailPositiveCount A B H + tailZeroCount A B H) +
          ratio *
            mixedFiniteOffline u
              (HiddenStoppingOracle.longCount u
                (Online.adaptiveRun (.finite u)
                  (oracle n u M A B) strategy fuel).result.config.transcript)
              (tailPositiveCount A B H) (tailZeroCount A B H) := by
          ring
    _ ≤ u *
            mixedPrefixZeroOffline
              (n -
                  HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript -
                  H)
              (HiddenStoppingOracle.longCount u
                    (Online.adaptiveRun (.finite u)
                      (oracle n u M A B) strategy fuel).result.config.transcript +
                tailPositiveCount A B H + tailZeroCount A B H) +
          mixedFiniteOnline u
            (HiddenStoppingOracle.longCount u
              (Online.adaptiveRun (.finite u)
                (oracle n u M A B) strategy fuel).result.config.transcript)
            (tailPositiveCount A B H) (tailZeroCount A B H) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hratioCap hprefix) hcore
    _ ≤ _ := by
      simpa [add_comm] using honline

/-- Completed-post actual-run defeat, conditional only on the remaining
physical global-exchange lower bound and the numerical mixed-core
inequality.  In particular there is no permutation or offline-accounting
premise. -/
theorem adaptiveRun_completedPost_adaptiveDefeats_of_full_online_lower
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hratioCap : ratio ≤ u)
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
    ratio * mixedFiniteOffline u C K Z ≤
        mixedFiniteOnline u C K Z →
      mixedFiniteOnline u C K Z +
            u * mixedPrefixZeroOffline v (C + K + Z) ≤
          Online.runCompletionCost (.finite u) frozen run.result →
        adaptiveDefeats (.finite u)
          (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  intro hcore honline
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hreachable :=
    Online.adaptiveRun_reachable (.finite u)
      (oracle n u M A B) strategy fuel
  have hterminal :=
    history.post_terminal_indices hn hβ hB
      hreachable.processHistoryInvariant hcompleted
  rcases hterminal with ⟨hL, hz, hpending⟩
  subst L
  subst z
  subst pending
  have hratio :=
    adaptiveRun_terminal_ratio_of_full_online_lower
      hn hM hB hH hraw hratioCap strategy fuel history
      hcore (by
        simpa [Online.frozenProcessingTimes, terminalProcessing] using
          honline)
  unfold adaptiveDefeats
  dsimp only
  refine ⟨hsettled, Or.inr ?_⟩
  simpa [Online.frozenProcessingTimes, terminalProcessing] using
    hratio

/-- Exhaustive completed-post bridge.  The zero-tail and positive-tail
numerical obligations are separated explicitly, so no proof can silently
discard the possible `H = 0` first crossing. -/
theorem adaptiveRun_completedPost_adaptiveDefeats_cases
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ}
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hratioCap : ratio ≤ u)
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
    (H = 0 →
      ratio * mixedExtendedFiniteOffline u (n - C) C 0 0 ≤
        prefixCost
          (List.replicate (n - C) u ++
            List.replicate C (1 + u))) →
      (0 < H →
        ratio * mixedFiniteOffline u C K Z ≤
          mixedFiniteOnline u C K Z) →
      (0 < H →
        mixedFiniteOnline u C K Z +
              u * mixedPrefixZeroOffline v (C + K + Z) ≤
            Online.runCompletionCost (.finite u)
              frozen run.result) →
      adaptiveDefeats (.finite u)
        (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  intro hzero hcore honline
  by_cases hH : H = 0
  · subst H
    have hβ : 0 < quotaFraction M A B :=
      quotaFraction_pos hM
    have hreachable :=
      Online.adaptiveRun_reachable (.finite u)
        (oracle n u M A B) strategy fuel
    have hterminal :=
      history.post_terminal_indices hn hβ hB
        hreachable.processHistoryInvariant hcompleted
    rcases hterminal with ⟨hL, hz, hpending⟩
    subst L
    subst z
    subst pending
    exact adaptiveRun_completedZeroTail_adaptiveDefeats
      hn hM hB hraw strategy fuel history hcompleted hsettled
      (hzero rfl)
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    exact
      adaptiveRun_completedPost_adaptiveDefeats_of_full_online_lower
        hn hM hB hHpos hraw hratioCap strategy fuel
        history hcompleted hsettled
        (hcore hHpos) (honline hHpos)

/-- At universal analysis fuel the settledness premise in the preceding
completed-post bridge is automatic. -/
theorem adaptiveRun_analysisFuel_completedPost_adaptiveDefeats
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hratioCap : ratio ≤ u)
    (strategy : Online.Strategy n)
    {L z : ℕ} {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H L z caps pending)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy (2 * n + 1)).result.config)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy (2 * n + 1)).result) :
    let fuel := 2 * n + 1
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
    ratio * mixedFiniteOffline u C K Z ≤
        mixedFiniteOnline u C K Z →
      mixedFiniteOnline u C K Z +
            u * mixedPrefixZeroOffline v (C + K + Z) ≤
          Online.runCompletionCost (.finite u) frozen run.result →
        adaptiveDefeats (.finite u)
          (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  exact
    adaptiveRun_completedPost_adaptiveDefeats_of_full_online_lower
      hn hM hB hH hraw hratioCap strategy (2 * n + 1)
      history hcompleted
      (adaptiveRun_analysisFuel_settled
        (.finite u) (oracle n u M A B) strategy)

/-- Universal-fuel version of the exhaustive completed-post bridge.  This is
the operational all-`H` entry point: settledness is automatic, while the
distinct numerical obligations for `H = 0` and `H > 0` remain visible. -/
theorem adaptiveRun_analysisFuel_completedPost_adaptiveDefeats_cases
    {n : ℕ} (hn : 0 < n) {u ratio : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ}
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hratioCap : ratio ≤ u)
    (strategy : Online.Strategy n)
    {L z : ℕ} {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H L z caps pending)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy (2 * n + 1)).result.config)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy (2 * n + 1)).result) :
    let fuel := 2 * n + 1
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
    (H = 0 →
      ratio * mixedExtendedFiniteOffline u (n - C) C 0 0 ≤
        prefixCost
          (List.replicate (n - C) u ++
            List.replicate C (1 + u))) →
      (0 < H →
        ratio * mixedFiniteOffline u C K Z ≤
          mixedFiniteOnline u C K Z) →
      (0 < H →
        mixedFiniteOnline u C K Z +
              u * mixedPrefixZeroOffline v (C + K + Z) ≤
            Online.runCompletionCost (.finite u)
              frozen run.result) →
      adaptiveDefeats (.finite u)
        (oracle n u M A B) strategy default fuel ratio := by
  dsimp only
  exact
    adaptiveRun_completedPost_adaptiveDefeats_cases
      hn hM hB hraw hratioCap strategy (2 * n + 1)
      history hcompleted
      (adaptiveRun_analysisFuel_settled
        (.finite u) (oracle n u M A B) strategy)

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
