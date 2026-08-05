import SchedulingPaper.ZeroPrefixGame
import SchedulingPaper.EndpointReduction
import Mathlib.Tactic

/-!
# Literal pair accounting for the Zero-prefix endpoint word

This module supplies the algebraic layer immediately before
`zeroPrefixAlg` and `zeroPrefixOpt`.  The canonical endpoint order is

`capped-deferred, boundary-deferred, immediate-one, zero`.

For each pair of endpoint classes we use the literal online pair charge of
ForcedPrefixUTE and the literal finite-cap shortest-first charge.  Summing
the ten diagonal/cross class contributions and imposing total normalized
mass one gives exactly the two scalar objectives in `ZeroPrefixGame`.
-/

namespace SchedulingPaper

noncomputable section

/-- The four endpoint classes in the normalized Zero-prefix word. -/
inductive ZeroPrefixEndpoint where
  | cappedDeferred
  | boundaryDeferred
  | immediateOne
  | zero
  deriving DecidableEq

/-- Limiting processing value of a Zero-prefix endpoint. -/
def zeroPrefixEndpointProcessing
    (s : ℝ) : ZeroPrefixEndpoint → ℝ
  | .cappedDeferred => s + 1
  | .boundaryDeferred => 1
  | .immediateOne => 1
  | .zero => 0

/-- Whether the endpoint is processed immediately during the test phase. -/
def ZeroPrefixEndpoint.IsImmediate : ZeroPrefixEndpoint → Bool
  | .cappedDeferred | .boundaryDeferred => false
  | .immediateOne | .zero => true

/-- Literal online contribution of a pair in canonical test order. -/
def zeroPrefixALGPairCharge
    (s : ℝ) (left right : ZeroPrefixEndpoint) : ℝ :=
  let p := zeroPrefixEndpointProcessing s left
  let q := zeroPrefixEndpointProcessing s right
  if left.IsImmediate then
    1 + p
  else if right.IsImmediate then
    2 + q
  else
    2 + min p q

/-- Effective finite-cap length represented by an endpoint. -/
def zeroPrefixEndpointEffective
    (s : ℝ) (endpoint : ZeroPrefixEndpoint) : ℝ :=
  min (1 + zeroPrefixEndpointProcessing s endpoint) (s + 1)

/-- Literal shortest-first offline contribution of an unordered pair. -/
def zeroPrefixOPTPairCharge
    (s : ℝ) (left right : ZeroPrefixEndpoint) : ℝ :=
  min (zeroPrefixEndpointEffective s left)
    (zeroPrefixEndpointEffective s right)

/-- Fluid pair objective obtained by summing all within-class and
cross-class online pair charges in the canonical endpoint order. -/
def zeroPrefixLiteralALG
    (s d t m zeros : ℝ) : ℝ :=
  d ^ 2 / 2 *
      zeroPrefixALGPairCharge s .cappedDeferred .cappedDeferred +
    t ^ 2 / 2 *
      zeroPrefixALGPairCharge s .boundaryDeferred .boundaryDeferred +
    m ^ 2 / 2 *
      zeroPrefixALGPairCharge s .immediateOne .immediateOne +
    zeros ^ 2 / 2 *
      zeroPrefixALGPairCharge s .zero .zero +
    d * t *
      zeroPrefixALGPairCharge s .cappedDeferred .boundaryDeferred +
    d * m *
      zeroPrefixALGPairCharge s .cappedDeferred .immediateOne +
    d * zeros *
      zeroPrefixALGPairCharge s .cappedDeferred .zero +
    t * m *
      zeroPrefixALGPairCharge s .boundaryDeferred .immediateOne +
    t * zeros *
      zeroPrefixALGPairCharge s .boundaryDeferred .zero +
    m * zeros *
      zeroPrefixALGPairCharge s .immediateOne .zero

/-- Fluid pair objective obtained from the literal finite-cap offline
shortest-first pair charges. -/
def zeroPrefixLiteralOPT
    (s d t m zeros : ℝ) : ℝ :=
  d ^ 2 / 2 *
      zeroPrefixOPTPairCharge s .cappedDeferred .cappedDeferred +
    t ^ 2 / 2 *
      zeroPrefixOPTPairCharge s .boundaryDeferred .boundaryDeferred +
    m ^ 2 / 2 *
      zeroPrefixOPTPairCharge s .immediateOne .immediateOne +
    zeros ^ 2 / 2 *
      zeroPrefixOPTPairCharge s .zero .zero +
    d * t *
      zeroPrefixOPTPairCharge s .cappedDeferred .boundaryDeferred +
    d * m *
      zeroPrefixOPTPairCharge s .cappedDeferred .immediateOne +
    d * zeros *
      zeroPrefixOPTPairCharge s .cappedDeferred .zero +
    t * m *
      zeroPrefixOPTPairCharge s .boundaryDeferred .immediateOne +
    t * zeros *
      zeroPrefixOPTPairCharge s .boundaryDeferred .zero +
    m * zeros *
      zeroPrefixOPTPairCharge s .immediateOne .zero

/-- The literal online pair table, expanded as a polynomial in the four
endpoint masses. -/
theorem zeroPrefixLiteralALG_eq_pairPolynomial
    {s d t m zeros : ℝ} (hs : 0 ≤ s) :
    zeroPrefixLiteralALG s d t m zeros =
      (s + 3) * d ^ 2 / 2 +
        3 * t ^ 2 / 2 + m ^ 2 + zeros ^ 2 / 2 +
        3 * d * t + 3 * d * m + 2 * d * zeros +
        3 * t * m + 2 * t * zeros + 2 * m * zeros := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  simp [zeroPrefixLiteralALG, zeroPrefixALGPairCharge,
    zeroPrefixEndpointProcessing, ZeroPrefixEndpoint.IsImmediate,
    min_eq_right hone]
  ring

/-- The literal offline pair table, expanded as a polynomial. -/
theorem zeroPrefixLiteralOPT_eq_pairPolynomial
    {s d t m zeros : ℝ} (hs : 1 ≤ s) :
    zeroPrefixLiteralOPT s d t m zeros =
      (s + 1) * d ^ 2 / 2 +
        t ^ 2 + m ^ 2 + zeros ^ 2 / 2 +
        2 * d * t + 2 * d * m + d * zeros +
        2 * t * m + t * zeros + m * zeros := by
  have htwo : (2 : ℝ) ≤ s + 1 := by linarith
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  simp [zeroPrefixLiteralOPT, zeroPrefixOPTPairCharge,
    zeroPrefixEndpointEffective, zeroPrefixEndpointProcessing,
    min_eq_left hone, min_eq_right hone]
  norm_num only
  rw [min_eq_left htwo]
  norm_num
  ring

/-- Exact identification of the literal online pair objective with the
normalized scalar `zeroPrefixAlg`. -/
theorem zeroPrefixLiteralALG_eq_zeroPrefixAlg
    {s d t m zeros : ℝ}
    (hs : 0 ≤ s) (hmass : d + t + m + zeros = 1) :
    zeroPrefixLiteralALG s d t m zeros =
      zeroPrefixAlg s d t m := by
  rw [zeroPrefixLiteralALG_eq_pairPolynomial hs]
  unfold zeroPrefixAlg
  have hzeros : zeros = 1 - (d + t + m) := by linarith
  rw [hzeros]
  ring

/-- Exact identification of the literal offline pair objective with the
normalized scalar `zeroPrefixOpt`. -/
theorem zeroPrefixLiteralOPT_eq_zeroPrefixOpt
    {s d t m zeros : ℝ}
    (hs : 1 ≤ s) (hmass : d + t + m + zeros = 1) :
    zeroPrefixLiteralOPT s d t m zeros =
      zeroPrefixOpt s d t m := by
  rw [zeroPrefixLiteralOPT_eq_pairPolynomial hs]
  unfold zeroPrefixOpt
  have hzeros : zeros = 1 - (d + t + m) := by linarith
  rw [hzeros]
  ring

/-- Consequently the literal pair excess is exactly the scalar excess used
by the proved Zero-prefix game. -/
theorem zeroPrefixLiteralPairExcess_eq
    {s d t m zeros : ℝ}
    (hs : 1 ≤ s) (hmass : d + t + m + zeros = 1) :
    zeroPrefixLiteralALG s d t m zeros -
        zeroPrefixFactor s * zeroPrefixLiteralOPT s d t m zeros =
      zeroPrefixAlg s d t m -
        zeroPrefixFactor s * zeroPrefixOpt s d t m := by
  rw [zeroPrefixLiteralALG_eq_zeroPrefixAlg
      (zero_le_one.trans hs) hmass,
    zeroPrefixLiteralOPT_eq_zeroPrefixOpt hs hmass]

/-- Literal-pair version of the complete normalized Zero-prefix certificate. -/
theorem zeroPrefixLiteralALG_le_factor_mul_OPT
    {s d t m zeros : ℝ}
    (hs : 1 ≤ s) (hsφ : s ≤ goldenRatio + 1)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hmass : d + t + m + zeros = 1) :
    zeroPrefixLiteralALG s d t m zeros ≤
      zeroPrefixFactor s * zeroPrefixLiteralOPT s d t m zeros := by
  rw [zeroPrefixLiteralALG_eq_zeroPrefixAlg
      (zero_le_one.trans hs) hmass,
    zeroPrefixLiteralOPT_eq_zeroPrefixOpt hs hmass]
  exact zeroPrefixAlg_le_factor_mul_opt
    (zero_lt_one.trans_le hs) hsφ hd ht hm

end

end SchedulingPaper
