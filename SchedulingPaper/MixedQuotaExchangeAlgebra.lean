import SchedulingPaper.MixedQuotaUniformOffsets
import Mathlib.Tactic

/-!
# Scalar closure of the dynamic cap exchange

The operational proof splits the cap jobs present at the first crossing
into `e` jobs which were already processed and `R` jobs which are still
pending.  This file records the last purely algebraic step: the loss caused
by the early jobs is bounded by `dynamicCapExchangeRemainder`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Exact scalar form of the cap/tail exchange, with the strategy-independent
dynamic remainder subtracted on the right. -/
theorem dynamicCapExchange_scalar_lower
    (u : ℝ) (A B C H e R : ℕ)
    (hcount : C = e + R) :
    (1 + u) * triangular e +
          ((H + R : ℕ) : ℝ) *
            ((C : ℝ) + (e : ℝ) * u) +
          (R : ℝ) *
            (((H : ℕ) : ℝ) +
              (harmonicFutureLevels
                (tailZeroCount A B H : ℝ) 0
                (tailPositiveCount A B H)).sum) +
          u * triangular R ≥
        (C : ℝ) *
              (((H : ℕ) : ℝ) +
                (harmonicFutureLevels
                  (tailZeroCount A B H : ℝ) 0
                  (tailPositiveCount A B H)).sum) +
            u * triangular C +
            (C : ℝ) * ((C + H : ℕ) : ℝ) -
            dynamicCapExchangeRemainder u A B C H := by
  let margin := dynamicDeferralMargin u A B C H
  let loss := max 0 (-margin)
  have hlossNonneg : 0 ≤ loss := by
    exact le_max_left _ _
  have hmargin : -loss ≤ margin := by
    dsimp [loss]
    linarith [le_max_right 0 (-margin)]
  have heC : e ≤ C := by omega
  have heCReal : (e : ℝ) ≤ C := by exact_mod_cast heC
  have heNonneg : 0 ≤ (e : ℝ) := by positivity
  have hCNonneg : 0 ≤ (C : ℝ) := by positivity
  have hscaledMargin :
      -(C : ℝ) * loss ≤ (e : ℝ) * margin := by
    have hfirst :
        -(e : ℝ) * loss ≤ (e : ℝ) * margin := by
      nlinarith
    have hsecond :
        -(C : ℝ) * loss ≤ -(e : ℝ) * loss := by
      nlinarith
    exact hsecond.trans hfirst
  have htri : 0 ≤ triangular e := by
    unfold triangular
    positivity
  have hidentity :
      (1 + u) * triangular e +
            ((H + R : ℕ) : ℝ) *
              ((C : ℝ) + (e : ℝ) * u) +
            (R : ℝ) *
              (((H : ℕ) : ℝ) +
                (harmonicFutureLevels
                  (tailZeroCount A B H : ℝ) 0
                  (tailPositiveCount A B H)).sum) +
            u * triangular R -
          ((C : ℝ) *
                (((H : ℕ) : ℝ) +
                  (harmonicFutureLevels
                    (tailZeroCount A B H : ℝ) 0
                    (tailPositiveCount A B H)).sum) +
              u * triangular C +
              (C : ℝ) * ((C + H : ℕ) : ℝ)) =
        (e : ℝ) * margin + triangular e := by
    subst C
    dsimp [margin, dynamicDeferralMargin]
    rw [tail_split A B H]
    unfold triangular
    push_cast
    ring
  unfold dynamicCapExchangeRemainder
  change _ ≥ _ - (C : ℝ) * loss
  linarith [hidentity, hscaledMargin, htri]

/-- Form directly consumed by the operational prefix/suffix decomposition.
The first two terms on the right are respectively the canonical completed
prefix and the delay which that prefix imposes on all suffix completions. -/
theorem dynamicCapExchange_full_scalar_lower
    (u : ℝ) (A B v C H e R : ℕ)
    (hcount : C = e + R) :
    mixedFiniteOnline u C
          (tailPositiveCount A B H)
          (tailZeroCount A B H) +
        u * mixedPrefixZeroOffline v (C + H) -
        dynamicCapExchangeRemainder u A B C H ≤
      prefixCost
          (List.replicate v u ++
            List.replicate e (1 + u)) +
        ((H + R : ℕ) : ℝ) *
          ((v : ℝ) * u + (C : ℝ) + (e : ℝ) * u) +
        (harmonicFiniteOnline
            (tailPositiveCount A B H)
            (tailZeroCount A B H) 0 +
          (R : ℝ) *
            (((H : ℕ) : ℝ) +
              (harmonicFutureLevels
                (tailZeroCount A B H : ℝ) 0
                (tailPositiveCount A B H)).sum) +
          u * triangular R) := by
  have hscalar :=
    dynamicCapExchange_scalar_lower u A B C H e R hcount
  have hprefix :
      prefixCost
          (List.replicate v u ++
            List.replicate e (1 + u)) =
        u * triangular v +
          (1 + u) * triangular e +
          (e : ℝ) * ((v : ℝ) * u) := by
    rw [prefixCost_append, prefixCost_replicate,
      prefixCost_replicate]
    simp only [List.length_replicate, List.sum_replicate,
      nsmul_eq_mul]
    push_cast
    ring
  have hsplit :
      tailPositiveCount A B H + tailZeroCount A B H = H :=
    tail_split A B H
  have hcountReal :
      (C : ℝ) = (e : ℝ) + (R : ℝ) := by
    exact_mod_cast hcount
  have hsplitReal :
      (tailPositiveCount A B H : ℝ) +
          (tailZeroCount A B H : ℝ) =
        (H : ℝ) := by
    exact_mod_cast hsplit
  have htotal :
      C + tailPositiveCount A B H + tailZeroCount A B H =
        C + H := by
    omega
  have hrawIdentity :
      u * triangular v +
            (e : ℝ) * ((v : ℝ) * u) +
            ((H : ℝ) + (R : ℝ)) * ((v : ℝ) * u) =
        u *
          (triangular v +
            (v : ℝ) * ((C : ℝ) + (H : ℝ))) := by
    rw [hcountReal]
    ring
  rw [hprefix]
  unfold mixedFiniteOnline mixedPrefixZeroOffline
  rw [hsplit, htotal]
  push_cast at hscalar ⊢
  linarith [hrawIdentity]

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
