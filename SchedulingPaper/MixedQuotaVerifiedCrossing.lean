import SchedulingPaper.MixedQuotaCrossingWindow
import SchedulingPaper.MixedQuotaFreeze
import Mathlib.Tactic

/-!
# Full-count form of the mixed first-crossing window

The scan stores the literal first-crossing prefix, whereas the terminal
accounting names the number of cap jobs using the whole public transcript.
Raw safety implies that every post-crossing harmonic test is strictly below
the cap, so these two cap counts coincide.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

private theorem longCount_eq_zero_of_test_ne
    {n : ℕ} {u : ℝ} {transcript : Online.Transcript n}
    (hne :
      ∀ job p, (job, p) ∈ transcript.testResults → p ≠ u) :
    HiddenStoppingOracle.longCount u transcript = 0 := by
  induction transcript with
  | nil =>
      rfl
  | cons observation rest ih =>
      have htail :
          ∀ job p,
            (job, p) ∈ Online.Transcript.testResults rest → p ≠ u := by
        intro job p hp
        exact hne job p (by
          cases observation <;> simp_all)
      cases observation with
      | testResult job p =>
          have hp : p ≠ u :=
            hne job p (by simp)
          simp [HiddenStoppingOracle.longCount, hp, ih htail]
      | processed job =>
          simpa [HiddenStoppingOracle.longCount] using ih htail
      | rawCompleted job =>
          simpa [HiddenStoppingOracle.longCount] using ih htail

/-- No test in the physical suffix stored by the crossing scan contributes
to the whole-transcript cap count. -/
theorem MixedQuotaHistory.scanTail_longCount_eq_zero
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B H L z : ℕ} (hM : 0 < M) (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H L z caps pending) config) :
    HiddenStoppingOracle.longCount u
        (scan n u (quotaFraction M A B)
          config.transcript).tail = 0 := by
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  apply longCount_eq_zero_of_test_ne
  intro job p hp
  have hpVirtual :
      (job, p) ∈
        (virtualTail n u (quotaFraction M A B)
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript).testResults :=
    virtualTail_actual_test_mem
      n u (quotaFraction M A B)
      (tailPositiveCount A B H)
      (tailZeroCount A B H)
      config.transcript hp
  have hpDefault :=
    history.mixedQuotaDefault_eq_of_virtual_testResult
      hn hβ hpVirtual
  have hpSafe :=
    (history.mixedQuotaDefault_rawSafe
      hn hβ hB hraw job).2
  rw [hpDefault] at hpSafe
  linarith

/-- Full-transcript form of the integral crossing dichotomy used by the
final adaptive assembly. -/
theorem MixedQuotaHistory.fullCount_dynamicQuotaWindow_or_zero
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
        ∃ q, DynamicQuotaWindow M A B q C H) := by
  dsimp only
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  obtain
    ⟨dataPrefix, hdataDecomp, _hfirst, hdataTests,
      _hdataNodup, _hdataH⟩ :=
      history.crossingPrefixData hn hβ
  obtain
    ⟨quotaPrefix, hquotaDecomp, hsize, hquotaCases⟩ :=
      (history.crossingPrefixData hn hβ)
        |>.exists_dynamicQuotaWindow_or_zero hM hA hB
  have hprefixEq : quotaPrefix = dataPrefix := by
    exact List.append_cancel_right
      (hquotaDecomp.symm.trans hdataDecomp)
  subst quotaPrefix
  have htailZero :=
    history.scanTail_longCount_eq_zero hn hM hB hraw
  have hprefixLong :
      HiddenStoppingOracle.longCount u dataPrefix =
        crossingCapCount dataPrefix := by
    simpa [crossingCapCount] using
      HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
        hdataTests
  have hfullLong :
      HiddenStoppingOracle.longCount u config.transcript =
        crossingCapCount dataPrefix := by
    rw [hdataDecomp, HiddenStoppingOracle.longCount_append,
      htailZero, add_zero]
    exact hprefixLong
  have hsplit :
      tailPositiveCount A B H + tailZeroCount A B H = H :=
    tail_split A B H
  have hsize' :
      n =
        crossingRawCount dataPrefix +
          crossingCapCount dataPrefix + H := by
    omega
  constructor
  · rw [hfullLong]
    omega
  · rw [hfullLong]
    exact hquotaCases

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
