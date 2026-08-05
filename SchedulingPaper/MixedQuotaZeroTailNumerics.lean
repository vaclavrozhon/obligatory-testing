import SchedulingPaper.MixedQuotaUniformOffsets
import Mathlib.Tactic

/-!
# Numerical closure of the zero-tail mixed crossing

When the first crossing occurs at the last first touch, the harmonic tail is
empty.  The generic exchange remainder is then exactly `C²`.  Cancelling it
from the mixed online expression leaves a bound which is dominated by the
literal raw/cap prefix schedule used by the operational zero-tail theorem.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

theorem dynamicCapExchangeRemainder_zero_tail
    (u : ℝ) (A B C : ℕ) :
    dynamicCapExchangeRemainder u A B C 0 = (C : ℝ) ^ 2 := by
  simp [dynamicCapExchangeRemainder, dynamicDeferralMargin,
    tailPositiveCount, tailZeroCount, harmonicFutureLevels,
    max_eq_right]
  ring

theorem mixedFiniteOnline_zero_tail
    (u : ℝ) (C : ℕ) :
    mixedFiniteOnline u C 0 0 =
      u * triangular C + (C : ℝ) ^ 2 := by
  simp [mixedFiniteOnline, harmonicFiniteOnline,
    harmonicDynamicPotential, harmonicFutureLevels]
  ring

/-- The remainder-aware dynamic mixed gap implies exactly the numerical
premise required by `adaptiveRun_completedZeroTail_adaptiveDefeats`. -/
theorem zeroTail_physical_prefix_closes_of_exchange_gap
    {u c : ℝ} {A B v C : ℕ}
    (hgap :
      0 ≤
        mixedFiniteOnline u C 0 0 -
          c * mixedFiniteOffline u C 0 0 +
          (u - c) * mixedPrefixZeroOffline v C -
          dynamicCapExchangeRemainder u A B C 0) :
    c * mixedExtendedFiniteOffline u v C 0 0 ≤
      prefixCost
        (List.replicate v u ++
          List.replicate C (1 + u)) := by
  have htri : 0 ≤ triangular C := by
    unfold triangular
    positivity
  have hcanonical :
      c *
          (mixedPrefixZeroOffline v C +
            u * triangular C) ≤
        u * mixedPrefixZeroOffline v C +
          u * triangular C := by
    rw [mixedFiniteOnline_zero_tail,
      mixedFiniteOffline_zero_tail,
      dynamicCapExchangeRemainder_zero_tail] at hgap
    linarith
  have hphysical :
      prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) =
        u * mixedPrefixZeroOffline v C +
          (1 + u) * triangular C := by
    rw [prefixCost_append, prefixCost_replicate,
      prefixCost_replicate]
    simp [mixedPrefixZeroOffline, List.sum_replicate]
    push_cast
    ring
  rw [mixedExtendedFiniteOffline,
    mixedFiniteOffline_zero_tail]
  calc
    c * (mixedPrefixZeroOffline v (C + 0 + 0) +
          u * triangular C) =
        c * (mixedPrefixZeroOffline v C +
          u * triangular C) := by simp
    _ ≤ u * mixedPrefixZeroOffline v C +
          u * triangular C :=
      hcanonical
    _ ≤ u * mixedPrefixZeroOffline v C +
          (1 + u) * triangular C := by
      nlinarith
    _ = prefixCost
          (List.replicate v u ++
            List.replicate C (1 + u)) :=
      hphysical.symm

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
