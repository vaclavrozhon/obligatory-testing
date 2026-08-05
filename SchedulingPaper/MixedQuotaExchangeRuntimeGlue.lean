import SchedulingPaper.MixedQuotaGlobalExchange
import SchedulingPaper.MixedQuotaExchangeAlgebra
import Mathlib.Tactic

/-!
# Runtime glue for the dynamic mixed cap exchange

This module separates the generic append accounting from the trace-specific
invariants.  A caller only has to provide the canonical prefix lower bound,
its elapsed time, the number of suffix completions, and the augmented-tail
lower bound.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

theorem completionCost_append_dynamic_exchange_lower
    {n : ℕ} (processing : Online.Label n → ℝ)
    (crossingPrefix physical : Online.Transcript n)
    (u : ℝ) (A B v C H e R : ℕ)
    (hu : 0 ≤ u)
    (hcount : C = e + R)
    (hprefix :
      prefixCost
          (List.replicate v u ++
            List.replicate e (1 + u)) ≤
        Online.completionCost (.finite u) processing
          crossingPrefix)
    (helapsed :
      (v : ℝ) * u + (C : ℝ) + (e : ℝ) * u ≤
        Online.transcriptElapsed (.finite u) processing
          crossingPrefix)
    (hcompletions :
      H + R ≤ Online.completionCount processing physical)
    (hsuffix :
      harmonicFiniteOnline
            (tailPositiveCount A B H)
            (tailZeroCount A B H) 0 +
          (R : ℝ) *
            (((H : ℕ) : ℝ) +
              (harmonicFutureLevels
                (tailZeroCount A B H : ℝ) 0
                (tailPositiveCount A B H)).sum) +
          u * triangular R ≤
        Online.completionCost (.finite u) processing physical) :
    mixedFiniteOnline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) +
        u * mixedPrefixZeroOffline v (C + H) -
        dynamicCapExchangeRemainder u A B C H ≤
      Online.completionCost (.finite u) processing
        (crossingPrefix ++ physical) := by
  have hscalar :=
    dynamicCapExchange_full_scalar_lower
      u A B v C H e R hcount
  have hcountReal :
      ((H + R : ℕ) : ℝ) ≤
        (Online.completionCount processing physical : ℝ) := by
    exact_mod_cast hcompletions
  have hbaseNonneg :
      0 ≤ (v : ℝ) * u + (C : ℝ) + (e : ℝ) * u := by
    positivity
  have hdelay :
      ((H + R : ℕ) : ℝ) *
          ((v : ℝ) * u + (C : ℝ) + (e : ℝ) * u) ≤
        Online.completionCount processing physical *
          Online.transcriptElapsed (.finite u) processing
            crossingPrefix := by
    exact mul_le_mul hcountReal helapsed hbaseNonneg (by positivity)
  rw [Online.completionCost_eq_suffixWeightedDuration] at hprefix hsuffix ⊢
  rw [Online.suffixWeightedDuration_append]
  exact hscalar.trans
    (add_le_add
      (add_le_add hprefix hdelay)
      hsuffix)

/-- The completed concrete mixed history satisfies the full physical online
lower bound, including the raw-prefix contribution and the dynamic cap
exchange remainder. -/
theorem MixedQuotaHistory.terminalProcessing_full_exchange_lower
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 [] []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    let processing :=
      terminalProcessing n u β A B
        config.transcript assignment
    let C := HiddenStoppingOracle.longCount u config.transcript
    let v := n - C - H
    mixedFiniteOnline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) +
        u * mixedPrefixZeroOffline v (C + H) -
        dynamicCapExchangeRemainder u A B C H ≤
      Online.completionCost (.finite u) processing
        config.transcript := by
  dsimp only
  let processing :=
    terminalProcessing n u β A B
      config.transcript assignment
  let C := HiddenStoppingOracle.longCount u config.transcript
  let v := n - C - H
  have hu : 0 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  obtain
    ⟨crossingPrefix, physical, initialCaps,
      hdecomp, hdata, hcapCount, hphysicalLong,
      hcompletion, htail⟩ :=
        history.terminalProcessing_augmentedTail_lower
          hn hβ hB hH hraw assignment
          hsupported hmatches hassignment
  let e := crossingPrefix.processedLabels.length
  let R := initialCaps.length
  have hprefixProcessed :
      ∀ job ∈ crossingPrefix.processedLabels,
        processing job = u := by
    intro job hjob
    have hrecorded := hdata.processedRecorded job hjob
    rcases List.mem_map.mp hrecorded with
      ⟨⟨testedJob, p⟩, hp, heq⟩
    change testedJob = job at heq
    subst testedJob
    have hpEq : p = u := hdata.allTestsEqual job p hp
    subst p
    have hfull :
        (job, u) ∈ config.transcript.testResults := by
      rw [hdecomp, Online.Transcript.testResults_append]
      exact List.mem_append.mpr (Or.inl hp)
    have hassigned : assignment job = some u :=
      hmatches job u hfull
    simpa [processing, terminalProcessing] using
      Online.completeAssignment_eq_assigned
        (mixedQuotaDefault n u β A B config.transcript)
        assignment job u hassigned
  have hprefix :
      prefixCost
          (List.replicate
              (HiddenStoppingOracle.rawCount crossingPrefix) u ++
            List.replicate e (1 + u)) ≤
        Online.completionCost (.finite u) processing
          crossingPrefix := by
    rw [Online.completionCost_eq_suffixWeightedDuration]
    calc
      prefixCost
          (List.replicate
              (HiddenStoppingOracle.rawCount crossingPrefix) u ++
            List.replicate e (1 + u)) ≤
          prefixCost
            (crossingPrefix.preCompletionWeights u) := by
        simpa [e] using
          Online.preCompletionWeights_blocks_le hu.le crossingPrefix
      _ ≤ Online.suffixWeightedDuration (.finite u)
          (fun _ => u) crossingPrefix :=
        hdata.preCost
      _ = Online.suffixWeightedDuration (.finite u)
          processing crossingPrefix := by
        symm
        exact
          Online.suffixWeightedDuration_eq_const_of_processed
            hprefixProcessed
  have hprefixLong :
      HiddenStoppingOracle.longCount u crossingPrefix =
        crossingPrefix.testResults.length :=
    HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
      hdata.allTestsEqual
  have hC :
      C = crossingPrefix.testResults.length := by
    dsimp [C]
    rw [hdecomp, HiddenStoppingOracle.longCount_append,
      hphysicalLong, Nat.add_zero]
    exact hprefixLong
  have hcount : C = e + R := by
    dsimp [e, R]
    omega
  have hstartedBound :
      crossingPrefix.startedLabels.length ≤ n := by
    calc
      crossingPrefix.startedLabels.length =
          crossingPrefix.startedLabels.toFinset.card := by
        rw [List.toFinset_card_of_nodup hdata.startedNodup]
      _ ≤ Fintype.card (Online.Label n) :=
        Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hstarted :=
    crossingPrefix.startedLabels_length_eq_raw_add_tests
  have hremaining := hdata.remaining
  have hraw :
      HiddenStoppingOracle.rawCount crossingPrefix = v := by
    dsimp [v]
    omega
  have helapsed :
      (v : ℝ) * u + (C : ℝ) + (e : ℝ) * u ≤
        Online.transcriptElapsed (.finite u) processing
          crossingPrefix := by
    have heq :
        Online.transcriptElapsed (.finite u) processing
            crossingPrefix =
          (v : ℝ) * u + (C : ℝ) + (e : ℝ) * u := by
      calc
        Online.transcriptElapsed (.finite u) processing
            crossingPrefix =
            Online.transcriptElapsed (.finite u) (fun _ => u)
              crossingPrefix :=
          Online.transcriptElapsed_eq_const_of_processed
            hprefixProcessed
        _ =
            crossingPrefix.testResults.length +
              u * crossingPrefix.processedLabels.length +
              u * HiddenStoppingOracle.rawCount crossingPrefix :=
          crossingPrefix.elapsed_const_long_exact u
        _ = (v : ℝ) * u + (C : ℝ) + (e : ℝ) * u := by
          rw [hraw]
          dsimp [e]
          have hCReal :
              (crossingPrefix.testResults.length : ℝ) = (C : ℝ) := by
            exact_mod_cast hC.symm
          rw [hCReal]
          ring
    exact heq.ge
  have hprefix' :
      prefixCost
          (List.replicate v u ++
            List.replicate e (1 + u)) ≤
        Online.completionCost (.finite u) processing
          crossingPrefix := by
    simpa [hraw] using hprefix
  have hcompletion' :
      H + R ≤ Online.completionCount processing physical := by
    simpa [processing, R] using hcompletion
  have htail' :
      harmonicFiniteOnline
            (tailPositiveCount A B H)
            (tailZeroCount A B H) 0 +
          (R : ℝ) *
            (((H : ℕ) : ℝ) +
              (harmonicFutureLevels
                (tailZeroCount A B H : ℝ) 0
                (tailPositiveCount A B H)).sum) +
          u * triangular R ≤
        Online.completionCost (.finite u) processing physical := by
    simpa [processing, R] using htail
  have hfull :=
    completionCost_append_dynamic_exchange_lower
      processing crossingPrefix physical u A B v C H e R
      hu.le hcount hprefix' helapsed hcompletion' htail'
  simpa [processing, C, v, hdecomp] using hfull

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
