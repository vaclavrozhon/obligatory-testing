import SchedulingPaper.MixedQuotaGlobalExchange
import SchedulingPaper.MixedQuotaUniformOffsets
import Mathlib.Tactic

/-!
# Integral scale attached to a mixed first crossing

The operational crossing estimate is stated with the normalized denominator
`n - v`, whereas the uniform numerical theorem uses an integral quota scale.
This file performs that bookkeeping once: a retained first-crossing prefix
determines a natural scale `q` and satisfies `DynamicQuotaWindow`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- The normalized quota window at a first crossing, including the degenerate
all-raw case.  If no cap and no tail job remains, the denominator is zero;
otherwise it is positive and the usual one-job overshoot estimate applies. -/
theorem CrossingPrefixData.quota_window_or_zero
    {n : ℕ} {u β : ℝ} {H : ℕ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {transcript : Online.Transcript n}
    (data : CrossingPrefixData n u β H transcript) :
    ∃ crossingPrefix : Online.Transcript n,
      transcript =
          crossingPrefix ++ (scan n u β transcript).tail ∧
      (crossingCapCount crossingPrefix + H = 0 ∨
        0 < crossingCapCount crossingPrefix + H ∧
          β ≤
              (crossingCapCount crossingPrefix : ℝ) /
                ((n : ℝ) - crossingRawCount crossingPrefix) ∧
          (crossingCapCount crossingPrefix : ℝ) /
                ((n : ℝ) - crossingRawCount crossingPrefix) - β <
            1 / ((n : ℝ) - crossingRawCount crossingPrefix)) := by
  obtain
    ⟨crossingPrefix, hdecomp, hfirst, hall, hnodup, hHdef⟩ :=
      data
  refine ⟨crossingPrefix, hdecomp, ?_⟩
  by_cases hzero : crossingCapCount crossingPrefix + H = 0
  · exact Or.inl hzero
  right
  have hpositive : 0 < crossingCapCount crossingPrefix + H :=
    Nat.pos_of_ne_zero hzero
  refine ⟨hpositive, ?_⟩
  have hlong :
      HiddenStoppingOracle.longCount u crossingPrefix =
        crossingCapCount crossingPrefix := by
    simpa [crossingCapCount] using
      HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
        hall
  have hbound :
      crossingPrefix.startedLabels.length ≤ n := by
    calc
      crossingPrefix.startedLabels.length =
          crossingPrefix.startedLabels.toFinset.card := by
        rw [List.toFinset_card_of_nodup hnodup]
      _ ≤ Fintype.card (Online.Label n) :=
        Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hlength :
      crossingPrefix.startedLabels.length + H = n := by
    omega
  rcases hfirst with
      ⟨before, job, rfl, hcross⟩ |
      ⟨before, job, rfl, hcross⟩
  · have hv :
        crossingRawCount
            (before ++ [.testResult job u]) =
          HiddenStoppingOracle.rawCount before := by
        simp [crossingRawCount, HiddenStoppingOracle.rawCount]
    have hk :
        crossingCapCount
            (before ++ [.testResult job u]) =
          HiddenStoppingOracle.longCount u before + 1 := by
        rw [← hlong]
        simp [HiddenStoppingOracle.longCount]
    have hremainingNat :
        HiddenStoppingOracle.rawCount before < n := by
      have hstarted :=
        (before ++
          [Online.Observation.testResult job u]).startedLabels_length_eq_raw_add_tests
      have hprefixLen :
          (before ++
            [Online.Observation.testResult job u]).startedLabels.length =
            before.startedLabels.length + 1 := by simp
      have hbeforeStarted :=
        before.startedLabels_length_eq_raw_add_tests
      omega
    have hremaining :
        0 < (n : ℝ) -
          HiddenStoppingOracle.rawCount before := by
      exact sub_pos.mpr (by exact_mod_cast hremainingNat)
    have hover :=
      HiddenStoppingOracle.firstCrossing_long_overshoot
        hcross hremaining
    dsimp only at hover
    rw [hv, hk]
    push_cast
    constructor
    · linarith [hover.1]
    · exact hover.2
  · have hv :
        crossingRawCount
            (before ++ [.rawCompleted job]) =
          HiddenStoppingOracle.rawCount before + 1 := by
        simp [crossingRawCount, HiddenStoppingOracle.rawCount]
    have hk :
        crossingCapCount
            (before ++ [.rawCompleted job]) =
          HiddenStoppingOracle.longCount u before := by
        rw [← hlong]
        simp [HiddenStoppingOracle.longCount]
    have hremainingNat :
        HiddenStoppingOracle.rawCount before + 1 < n := by
      have hstarted :=
        (before ++
          [Online.Observation.rawCompleted job]).startedLabels_length_eq_raw_add_tests
      have hprefixLen :
          (before ++
            [Online.Observation.rawCompleted job]).startedLabels.length =
            before.startedLabels.length + 1 := by simp
      have hbeforeStarted :=
        before.startedLabels_length_eq_raw_add_tests
      have htests :
          (before ++
            [Online.Observation.rawCompleted job]).testResults.length =
            before.testResults.length := by simp
      have hcapTailPositive :
          0 <
            (before ++
              [Online.Observation.rawCompleted job]).testResults.length +
              H := by
        simpa [crossingCapCount] using hpositive
      omega
    have hremaining :
        0 < (n : ℝ) -
          ((HiddenStoppingOracle.rawCount before : ℝ) + 1) := by
      have hcast :
          ((HiddenStoppingOracle.rawCount before + 1 : ℕ) : ℝ) <
            (n : ℝ) := by
        exact_mod_cast hremainingNat
      push_cast at hcast
      linarith
    have hover :=
      HiddenStoppingOracle.firstCrossing_raw_overshoot
        hβ0 hβ1 hcross hremaining
    dsimp only at hover
    rw [hv, hk]
    norm_num
    constructor
    · linarith [hover.1]
    · simpa using hover.2

/-- A genuine first crossing has an integral scale and the exact
raw/cap/tail size decomposition needed by the dynamic numerical theorem. -/
theorem CrossingPrefixData.exists_dynamicQuotaWindow
    {n : ℕ} {u : ℝ} {M A B H : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hH : 0 < H)
    {transcript : Online.Transcript n}
    (data :
      CrossingPrefixData n u (quotaFraction M A B) H transcript) :
    ∃ crossingPrefix : Online.Transcript n, ∃ q : ℕ,
      transcript =
          crossingPrefix ++
            (scan n u (quotaFraction M A B) transcript).tail ∧
      n =
        crossingRawCount crossingPrefix +
          crossingCapCount crossingPrefix +
          tailPositiveCount A B H +
          tailZeroCount A B H ∧
      DynamicQuotaWindow M A B q
        (crossingCapCount crossingPrefix) H := by
  have hβ0 : 0 ≤ quotaFraction M A B :=
    (quotaFraction_pos hM).le
  have hβ1 : quotaFraction M A B < 1 :=
    quotaFraction_lt_one hA
  obtain ⟨quotaPrefix, hquotaDecomp, hquotaLower, hquotaUpper⟩ :=
    data.quota_window hβ0 hβ1 hH
  obtain ⟨sizePrefix, hsizeDecomp, _hfirst, _hall, _hnodup,
      hsize⟩ :=
    data.size_identity (A := A) (B := B)
  have hprefixEq : quotaPrefix = sizePrefix := by
    exact List.append_cancel_right
      (hquotaDecomp.symm.trans hsizeDecomp)
  subst sizePrefix
  let C : ℕ := crossingCapCount quotaPrefix
  let v : ℕ := crossingRawCount quotaPrefix
  let D : ℕ := M + A + B
  let S : ℕ := C + H
  let q : ℕ := S / D
  have hD : 0 < D := by
    dsimp [D]
    omega
  have hsplit :
      tailPositiveCount A B H + tailZeroCount A B H = H :=
    tail_split A B H
  have hnSize : n = v + S := by
    dsimp [v, S, C]
    omega
  have hremNat : n - v = S := by omega
  have hremReal :
      (n : ℝ) - (v : ℝ) = (S : ℝ) := by
    have hvn : v ≤ n := by omega
    rw [← Nat.cast_sub hvn]
    exact_mod_cast hremNat
  have hS : 0 < S := by
    dsimp [S]
    omega
  have hquotaLower' :
      quotaFraction M A B ≤ (C : ℝ) / (S : ℝ) := by
    simpa [C, v, hremReal] using hquotaLower
  have hquotaUpper' :
      (C : ℝ) / (S : ℝ) - quotaFraction M A B <
        1 / (S : ℝ) := by
    simpa [C, v, hremReal] using hquotaUpper
  have hcleared :=
    quota_window_clear_denominator hS
      hquotaLower' hquotaUpper'
  have hscaleLower : D * q ≤ S := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self S D
  have hscaleUpper : S < D * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ S hD
  refine ⟨quotaPrefix, q, hquotaDecomp, ?_, ?_⟩
  · simpa [v, C] using hsize
  · refine
      { scaleLower := ?_
        scaleUpper := ?_
        capLower := ?_
        capUpper := ?_ }
    · simpa [D, S, C] using hscaleLower
    · simpa [D, S, C] using hscaleUpper
    · simpa [quotaFraction, D, S, C] using hcleared.1
    · simpa [quotaFraction, D, S, C] using hcleared.2

/-- Integral first-crossing bookkeeping without assuming a nonempty tail.
The only excluded quota window is the genuine zero-denominator case:
the crossing prefix and the harmonic tail contain no capped jobs at all. -/
theorem CrossingPrefixData.exists_dynamicQuotaWindow_or_zero
    {n : ℕ} {u : ℝ} {M A B H : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {transcript : Online.Transcript n}
    (data :
      CrossingPrefixData n u (quotaFraction M A B) H transcript) :
    ∃ crossingPrefix : Online.Transcript n,
      transcript =
          crossingPrefix ++
            (scan n u (quotaFraction M A B) transcript).tail ∧
      n =
        crossingRawCount crossingPrefix +
          crossingCapCount crossingPrefix +
          tailPositiveCount A B H +
          tailZeroCount A B H ∧
      (crossingCapCount crossingPrefix + H = 0 ∨
        ∃ q : ℕ,
          DynamicQuotaWindow M A B q
            (crossingCapCount crossingPrefix) H) := by
  have hβ0 : 0 ≤ quotaFraction M A B :=
    (quotaFraction_pos hM).le
  have hβ1 : quotaFraction M A B < 1 :=
    quotaFraction_lt_one hA
  obtain
    ⟨quotaPrefix, hquotaDecomp, hquotaCases⟩ :=
      data.quota_window_or_zero hβ0 hβ1
  obtain ⟨sizePrefix, hsizeDecomp, _hfirst, _hall, _hnodup,
      hsize⟩ :=
    data.size_identity (A := A) (B := B)
  have hprefixEq : quotaPrefix = sizePrefix := by
    exact List.append_cancel_right
      (hquotaDecomp.symm.trans hsizeDecomp)
  subst sizePrefix
  refine ⟨quotaPrefix, hquotaDecomp, ?_, ?_⟩
  · exact hsize
  rcases hquotaCases with hzero | hquota
  · exact Or.inl hzero
  obtain ⟨hS, hquotaLower, hquotaUpper⟩ := hquota
  let C : ℕ := crossingCapCount quotaPrefix
  let v : ℕ := crossingRawCount quotaPrefix
  let D : ℕ := M + A + B
  let S : ℕ := C + H
  let q : ℕ := S / D
  have hD : 0 < D := by
    dsimp [D]
    omega
  have hsplit :
      tailPositiveCount A B H + tailZeroCount A B H = H :=
    tail_split A B H
  have hnSize : n = v + S := by
    dsimp [v, S, C]
    omega
  have hremNat : n - v = S := by omega
  have hremReal :
      (n : ℝ) - (v : ℝ) = (S : ℝ) := by
    have hvn : v ≤ n := by omega
    rw [← Nat.cast_sub hvn]
    exact_mod_cast hremNat
  have hS' : 0 < S := by
    simpa [S, C] using hS
  have hquotaLower' :
      quotaFraction M A B ≤ (C : ℝ) / (S : ℝ) := by
    simpa [C, v, hremReal] using hquotaLower
  have hquotaUpper' :
      (C : ℝ) / (S : ℝ) - quotaFraction M A B <
        1 / (S : ℝ) := by
    simpa [C, v, hremReal] using hquotaUpper
  have hcleared :=
    quota_window_clear_denominator hS'
      hquotaLower' hquotaUpper'
  have hscaleLower : D * q ≤ S := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self S D
  have hscaleUpper : S < D * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ S hD
  refine Or.inr ⟨q, ?_⟩
  refine
    { scaleLower := ?_
      scaleUpper := ?_
      capLower := ?_
      capUpper := ?_ }
  · simpa [D, S, C] using hscaleLower
  · simpa [D, S, C] using hscaleUpper
  · simpa [quotaFraction, D, S, C] using hcleared.1
  · simpa [quotaFraction, D, S, C] using hcleared.2

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
