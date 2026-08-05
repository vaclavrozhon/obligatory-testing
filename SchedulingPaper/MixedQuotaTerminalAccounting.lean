import SchedulingPaper.MixedQuotaPhysicalVirtual
import SchedulingPaper.MixedQuotaFreeze
import SchedulingPaper.MixedQuotaTerminal
import SchedulingPaper.MixedQuotaExtendedStatic
import Mathlib.Tactic

/-!
# Terminal accounting for the mixed quota construction

This module packages the operational virtual-tail lower bound with the
canonical completion of the adaptive assignment.  Its final statements
also expose the exact additive cap term which remains between the harmonic
tail benchmark and `mixedFiniteOnline`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Complete the terminal partial assignment by the canonical mixed default.
This is the processing vector which is frozen for replay. -/
noncomputable def terminalProcessing
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (transcript : Online.Transcript n)
    (assignment : Online.PartialAssignment n) :
    Online.Label n → ℝ :=
  Online.completeAssignment
    (mixedQuotaDefault n u β A B transcript) assignment

/-- The part of `mixedFiniteOnline` contributed by the capped block and
its pairs with the harmonic tail. -/
def mixedFiniteCapContribution
    (u : ℝ) (C K Z : ℕ) : ℝ :=
  C * ((K + Z : ℕ) +
      (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
    u * triangular C +
    C * (C + K + Z : ℕ)

theorem mixedFiniteOnline_eq_harmonic_add_capContribution
    (u : ℝ) (C K Z : ℕ) :
    mixedFiniteOnline u C K Z =
      harmonicFiniteOnline K Z 0 +
        mixedFiniteCapContribution u C K Z := by
  simp only [mixedFiniteOnline, mixedFiniteCapContribution]
  ring

/-- The dynamically rounded `A:B` tail satisfies the static raw-safety
premise expected by the canonical mixed effective-length candidate. -/
theorem dynamicTail_static_rawSafe
    {u : ℝ} {A B H : ℕ}
    (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    ∀ L ≤ tailPositiveCount A B H,
      1 +
          harmonicLevel
            (tailZeroCount A B H : ℝ) 0 L ≤
        u := by
  intro L hL
  have hZ : 0 < tailZeroCount A B H :=
    tailZeroCount_pos hB hH
  have hlevel :=
    harmonicLevel_le_one_add_ratio hZ hL
  have hratio :=
    tail_ratio_le (A := A) hB hH
  linarith

/-- At a completed post-crossing harmonic state, the canonical frozen
processing vector has physical finite-cap cost at least the exact harmonic
online benchmark.  All matching, admissibility, and raw-safety premises are
discharged from the reachable history and the supported assignment. -/
theorem MixedQuotaHistory.terminalProcessing_harmonicOnline_le_physical
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    harmonicFiniteOnline
        (tailPositiveCount A B H)
        (tailZeroCount A B H) 0 ≤
      Online.completionCost (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment)
        config.transcript := by
  let processingTime :=
    terminalProcessing n u β A B config.transcript assignment
  have hu : 0 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  have hZ : 0 < tailZeroCount A B H :=
    tailZeroCount_pos hB hH
  have hdefault :
      ∀ job,
        Online.ValueAdmissible (.finite u)
          (mixedQuotaDefault n u β A B config.transcript job) :=
    history.mixedQuotaDefault_admissible
      hn hβ hB hraw
  have hadmissible :
      ∀ job,
        Online.ValueAdmissible (.finite u)
          (processingTime job) := by
    exact Online.completeAssignment_admissible
      (.finite u)
      (mixedQuotaDefault n u β A B config.transcript)
      assignment hdefault hassignment
  have hmatch :
      MixedTailMatches processingTime
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript) := by
    simpa [processingTime, terminalProcessing] using
      history.completeAssignment_matches_virtual
        hn hβ hB hraw assignment hsupported hassignment
  have hsafe :
      ∀ job p,
        (job, p) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults →
        1 + p ≤ u := by
    intro job p hp
    have heq :=
      history.mixedQuotaDefault_eq_of_virtual_testResult
        hn hβ hp
    have hs :=
      (history.mixedQuotaDefault_rawSafe
        hn hβ hB hraw job).2
    rw [heq] at hs
    exact hs
  simpa [processingTime] using
    history.terminal_harmonicOnline_le_physical
      hn hu hβ hZ processingTime hadmissible hmatch hsafe

/-- Exact terminal ALG/OPT accounting once the frozen effective lengths
have been classified as the raw-zero prefix followed by the canonical
mixed candidate. -/
theorem MixedQuotaHistory.terminalProcessing_exact_accounting
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment)
    (v C : ℕ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C
        (tailPositiveCount A B H)
        (tailZeroCount A B H)).Perm
      (vectorEffectiveLengths (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment))) :
    vectorOfflineCost (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment) =
      mixedExtendedFiniteOffline u v C
        (tailPositiveCount A B H)
        (tailZeroCount A B H) ∧
    harmonicFiniteOnline
        (tailPositiveCount A B H)
        (tailZeroCount A B H) 0 ≤
      Online.completionCost (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment)
        config.transcript := by
  have hZ : 0 < tailZeroCount A B H :=
    tailZeroCount_pos hB hH
  have hsafe :=
    dynamicTail_static_rawSafe hB hH hraw
  constructor
  · exact
      vectorOfflineCost_eq_mixedExtendedFiniteOffline_of_perm
        hZ hsafe
        (terminalProcessing n u β A B
          config.transcript assignment)
        hperm
  · exact history.terminalProcessing_harmonicOnline_le_physical
      hn hβ hB hH hraw assignment hsupported hassignment

/-- Unconditional competitive-gap form of the exact terminal accounting.
It retains the full offline objective, including the raw-zero prefix. -/
theorem MixedQuotaHistory.terminalProcessing_harmonic_gap
    {n : ℕ} (hn : 0 < n) {u β c : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment)
    (v C : ℕ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C
        (tailPositiveCount A B H)
        (tailZeroCount A B H)).Perm
      (vectorEffectiveLengths (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment))) :
    harmonicFiniteOnline
          (tailPositiveCount A B H)
          (tailZeroCount A B H) 0 -
        c * mixedExtendedFiniteOffline u v C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) ≤
      Online.completionCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)
          config.transcript -
        c * vectorOfflineCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment) := by
  rcases history.terminalProcessing_exact_accounting
      hn hβ hB hH hraw assignment hsupported hassignment
      v C hperm with ⟨hoffline, honline⟩
  rw [hoffline]
  linarith

/-- Explicit additive form in terms of `mixedFiniteOnline`.  It states
precisely that the only online term not supplied by the virtual harmonic
simulation is `mixedFiniteCapContribution`. -/
theorem MixedQuotaHistory.terminalProcessing_mixed_gap_with_cap_remainder
    {n : ℕ} (hn : 0 < n) {u β c : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment)
    (v C : ℕ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C
        (tailPositiveCount A B H)
        (tailZeroCount A B H)).Perm
      (vectorEffectiveLengths (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment))) :
    mixedFiniteOnline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) -
        c * mixedExtendedFiniteOffline u v C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) ≤
      Online.completionCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)
          config.transcript -
        c * vectorOfflineCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment) +
        mixedFiniteCapContribution u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) := by
  have hgap :=
    history.terminalProcessing_harmonic_gap
      hn hβ hB hH hraw assignment hsupported hassignment
      v C hperm (c := c)
  rw [mixedFiniteOnline_eq_harmonic_add_capContribution]
  linarith

/-- Final raw-prefix decomposition.  If the remaining physical prefix/cap
accounting supplies the displayed online lower bound, the competitive gap
contains the canonical mixed gap plus the nonnegative raw-prefix correction
`(u-c) * mixedPrefixZeroOffline`. -/
theorem MixedQuotaHistory.terminalProcessing_full_mixed_gap_of_online_lower
    {n : ℕ} (hn : 0 < n) {u β c : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment)
    (v C : ℕ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C
        (tailPositiveCount A B H)
        (tailZeroCount A B H)).Perm
      (vectorEffectiveLengths (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment)))
    (honline :
      mixedFiniteOnline u C
            (tailPositiveCount A B H)
            (tailZeroCount A B H) +
          u * mixedPrefixZeroOffline v
            (C + tailPositiveCount A B H +
              tailZeroCount A B H) ≤
        Online.completionCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)
          config.transcript) :
    mixedFiniteOnline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) -
        c * mixedFiniteOffline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) +
        (u - c) * mixedPrefixZeroOffline v
          (C + tailPositiveCount A B H +
            tailZeroCount A B H) ≤
      Online.completionCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)
          config.transcript -
        c * vectorOfflineCost (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment) := by
  have haccount :=
    history.terminalProcessing_exact_accounting
      hn hβ hB hH hraw assignment hsupported hassignment
      v C hperm
  have hoffline := haccount.1
  rw [hoffline, mixedExtendedFiniteOffline]
  linarith

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
