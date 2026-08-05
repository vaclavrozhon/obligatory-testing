import SchedulingPaper.VerifiedZeroPrefixBridge
import SchedulingPaper.UTERuntimeEndpoint
import SchedulingPaper.UTEFiniteEndpointAccounting
import Mathlib.Tactic

/-!
# Verified operational bridge for ForcedPrefixUTE below two

This file formalizes the Bernoulli reduction used when
`u = s + 1 < 2`.  Its last theorem discharges
`UpperBound.UTEBelowTwoCostBridge` without an extra interface premise.
-/

namespace SchedulingPaper

noncomputable section

open Set
open LowerBound

/-! ## The binary scalar game -/

/-- The binary pair objective before subtracting the offline objective.
For `x ≤ b` all long jobs fit into the forced prefix; otherwise the
remaining long jobs form the deferred suffix block. -/
def uteBinaryALG (s b x : ℝ) : ℝ :=
  if x ≤ b then
    1 / 2 + (s + 1) * (x - x ^ 2 / 2)
  else
    1 / 2 +
      (s + 1) * (b - b ^ 2 / 2) +
      (1 - b) * (x - b) +
      s * (x - b) ^ 2 / 2

def uteBinaryOPT (s x : ℝ) : ℝ :=
  1 / 2 + s * x ^ 2 / 2

def uteBinaryGap (s b x : ℝ) : ℝ :=
  uteBinaryALG s b x - uteRho s * uteBinaryOPT s x

theorem uteB_pos_below_two
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < uteB s := by
  have hrho : uteRho s < 2 := uteRho_lt_two hs
  have hs2 : s ^ 2 < 1 := by nlinarith [sq_nonneg s]
  have hprod :
      s ^ 2 * uteRho s < 2 * s ^ 2 := by
    simpa [mul_comm] using
      mul_lt_mul_of_pos_left hrho (sq_pos_of_pos hs)
  have hnum : 0 < uteK s - s ^ 2 * uteRho s := by
    unfold uteK
    nlinarith
  exact div_pos hnum (uteD_pos hs)

theorem uteB_lt_one_of_pos
    {s : ℝ} (hs : 0 < s) :
    uteB s < 1 := by
  have hD : 0 < uteD s := uteD_pos hs
  have hrho : 0 < uteRho s := uteRho_pos hs
  unfold uteB
  rw [div_lt_one hD]
  unfold uteD
  nlinarith [mul_pos hs hrho]

def uteBinaryLargeSlopeAtB (s : ℝ) : ℝ :=
  1 - uteB s - s * uteRho s * uteB s

theorem uteBinaryLargeSlopeAtB_eq
    {s : ℝ} (hs : 0 < s) :
    uteBinaryLargeSlopeAtB s =
      s * (uteRho s - 1) * (uteAlpha s - uteB s) := by
  have hD := (uteD_pos hs).ne'
  have hroot := uteRho_root hs
  unfold uteBinaryLargeSlopeAtB uteB uteAlpha
  field_simp [hD]
  unfold rhoPolynomial at hroot
  unfold uteD uteK
  nlinarith

theorem uteBinaryLargeSlopeAtB_pos
    {s : ℝ} (hs : 0 < s) :
    0 < uteBinaryLargeSlopeAtB s := by
  rw [uteBinaryLargeSlopeAtB_eq hs]
  have hrho : 0 < uteRho s - 1 :=
    sub_pos.mpr (uteRho_gt_one hs)
  have hab : 0 < uteAlpha s - uteB s := by
    rw [uteB_eq_succ_mul_alpha_sub_s hs]
    have ha := uteAlpha_lt_one hs
    nlinarith
  positivity

def uteBinarySmallSlopeAtB (s : ℝ) : ℝ :=
  (s + 1) - (s + 1 + uteRho s * s) * uteB s

theorem uteBinarySmallSlopeAtB_eq (s : ℝ) :
    uteBinarySmallSlopeAtB s =
      uteBinaryLargeSlopeAtB s + s * (1 - uteB s) := by
  unfold uteBinarySmallSlopeAtB uteBinaryLargeSlopeAtB
  ring

theorem uteBinarySmallSlopeAtB_pos
    {s : ℝ} (hs : 0 < s) :
    0 < uteBinarySmallSlopeAtB s := by
  rw [uteBinarySmallSlopeAtB_eq]
  have hlarge := uteBinaryLargeSlopeAtB_pos hs
  have hb1 := uteB_lt_one_of_pos hs
  nlinarith [mul_pos hs (sub_pos.mpr hb1)]

def uteBinarySmallGap (s x : ℝ) : ℝ :=
  (1 - uteRho s) / 2 +
    (s + 1) * (x - x ^ 2 / 2) -
    uteRho s * s * x ^ 2 / 2

theorem uteBinaryGap_eq_small
    {s b x : ℝ} (hxb : x ≤ b) :
    uteBinaryGap s b x = uteBinarySmallGap s x := by
  simp [uteBinaryGap, uteBinaryALG, uteBinaryOPT,
    uteBinarySmallGap, hxb]
  ring

theorem uteBinaryGap_eq_large
    {s b x : ℝ} (hbx : b ≤ x) :
    uteBinaryGap s b x =
      1 / 2 +
        (s + 1) * (b - b ^ 2 / 2) +
        (1 - b) * (x - b) +
        s * (x - b) ^ 2 / 2 -
        uteRho s * (1 / 2 + s * x ^ 2 / 2) := by
  rcases eq_or_lt_of_le hbx with rfl | hlt
  · simp [uteBinaryGap, uteBinaryALG, uteBinaryOPT]
  · simp [uteBinaryGap, uteBinaryALG, uteBinaryOPT,
      not_le.mpr hlt]

theorem uteBinaryGap_at_uteB_eq_large
    {s x : ℝ} (hbx : uteB s ≤ x) :
    uteBinaryGap s (uteB s) x = uteLargeGap s x := by
  rw [uteBinaryGap_eq_large hbx]
  rfl

theorem uteBinarySmallGap_at_b_eq_large (s : ℝ) :
    uteBinarySmallGap s (uteB s) =
      uteLargeGap s (uteB s) := by
  unfold uteBinarySmallGap uteLargeGap
  ring

theorem uteBinarySmallGap_sub_identity (s x : ℝ) :
    uteBinarySmallGap s (uteB s) -
        uteBinarySmallGap s x =
      (uteB s - x) *
        ((s + 1) -
          (s + 1 + uteRho s * s) *
            (uteB s + x) / 2) := by
  unfold uteBinarySmallGap
  ring

theorem uteBinarySmallGap_le_at_b
    {s x : ℝ} (hs : 0 < s) (hxb : x ≤ uteB s) :
    uteBinarySmallGap s x ≤
      uteBinarySmallGap s (uteB s) := by
  have hcoef :
      0 ≤ s + 1 + uteRho s * s := by
    have hrho := (uteRho_pos hs).le
    nlinarith [mul_nonneg hrho hs.le]
  have havg :
      uteBinarySmallSlopeAtB s ≤
        (s + 1) -
          (s + 1 + uteRho s * s) *
            (uteB s + x) / 2 := by
    unfold uteBinarySmallSlopeAtB
    have hmul :=
      mul_le_mul_of_nonneg_left hxb hcoef
    nlinarith
  have hfactor :
      0 ≤
        (s + 1) -
          (s + 1 + uteRho s * s) *
            (uteB s + x) / 2 :=
    (uteBinarySmallSlopeAtB_pos hs).le.trans havg
  rw [← sub_nonneg, uteBinarySmallGap_sub_identity]
  exact mul_nonneg (sub_nonneg.mpr hxb) hfactor

theorem uteBinaryGap_nonpos
    {s x : ℝ} (hs : 0 < s) :
    uteBinaryGap s (uteB s) x ≤ 0 := by
  by_cases hxb : x ≤ uteB s
  · rw [uteBinaryGap_eq_small hxb]
    calc
      uteBinarySmallGap s x ≤
          uteBinarySmallGap s (uteB s) :=
        uteBinarySmallGap_le_at_b hs hxb
      _ = uteLargeGap s (uteB s) :=
        uteBinarySmallGap_at_b_eq_large s
      _ ≤ 0 := uteLargeGap_nonpos hs
  · rw [uteBinaryGap_at_uteB_eq_large (le_of_not_ge hxb)]
    exact uteLargeGap_nonpos hs

/-! The rounded prefix size is `b' = floor(bn)/n`.  The following
one-sided Lipschitz estimate is the only fact needed to absorb rounding. -/

theorem uteBinaryALG_large_sub
    (s b₁ b₂ x : ℝ) :
    (1 / 2 +
        (s + 1) * (b₁ - b₁ ^ 2 / 2) +
        (1 - b₁) * (x - b₁) +
        s * (x - b₁) ^ 2 / 2) -
      (1 / 2 +
        (s + 1) * (b₂ - b₂ ^ 2 / 2) +
        (1 - b₂) * (x - b₂) +
        s * (x - b₂) ^ 2 / 2) =
      (b₁ - b₂) *
        ((b₁ + b₂) / 2 + s - (s + 1) * x) := by
  ring

theorem uteBinaryALG_rounding_le
    {s b' b x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hb'0 : 0 ≤ b') (hbb : b' ≤ b) (hb1 : b ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    uteBinaryALG s b' x ≤ uteBinaryALG s b x + (b - b') := by
  by_cases hxb' : x ≤ b'
  · have hxb : x ≤ b := hxb'.trans hbb
    simp [uteBinaryALG, hxb', hxb]
    exact hbb
  · have hb'x : b' ≤ x := le_of_not_ge hxb'
    by_cases hxb : x ≤ b
    · have hbx' : b' < x := lt_of_not_ge hxb'
      have hlarge :
          uteBinaryALG s b' x =
            1 / 2 +
              (s + 1) * (b' - b' ^ 2 / 2) +
              (1 - b') * (x - b') +
              s * (x - b') ^ 2 / 2 := by
        simp [uteBinaryALG, not_le.mpr hbx']
      have hsmall :
          uteBinaryALG s b x =
            1 / 2 + (s + 1) * (x - x ^ 2 / 2) := by
        simp [uteBinaryALG, hxb]
      rw [hlarge, hsmall]
      have hid := uteBinaryALG_large_sub s b' x x
      have hfactor :
          -1 ≤ (b' + x) / 2 + s - (s + 1) * x := by
        nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hx1)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hb'x))
        (by linarith : 0 ≤
          ((b' + x) / 2 + s - (s + 1) * x) + 1)]
    · have hbx : b ≤ x := le_of_not_ge hxb
      have hlarge' :
          uteBinaryALG s b' x =
            1 / 2 +
              (s + 1) * (b' - b' ^ 2 / 2) +
              (1 - b') * (x - b') +
              s * (x - b') ^ 2 / 2 := by
        simp [uteBinaryALG, not_le.mpr (lt_of_not_ge hxb')]
      have hlarge :
          uteBinaryALG s b x =
            1 / 2 +
              (s + 1) * (b - b ^ 2 / 2) +
              (1 - b) * (x - b) +
              s * (x - b) ^ 2 / 2 := by
        rcases eq_or_lt_of_le hbx with rfl | hlt
        · simp [uteBinaryALG]
        · simp [uteBinaryALG, not_le.mpr hlt]
      rw [hlarge', hlarge]
      have hid := uteBinaryALG_large_sub s b' b x
      have hfactor :
          -1 ≤ (b' + b) / 2 + s - (s + 1) * x := by
        nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hx1)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hbb)
        (by linarith : 0 ≤
          ((b' + b) / 2 + s - (s + 1) * x) + 1)]

theorem uteBinaryGap_rounding_le
    {s b' b x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hb'0 : 0 ≤ b') (hbb : b' ≤ b) (hb1 : b ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    uteBinaryGap s b' x ≤ uteBinaryGap s b x + (b - b') := by
  unfold uteBinaryGap
  linarith [uteBinaryALG_rounding_le
    hs0 hs1 hb'0 hbb hb1 hx0 hx1]

/-! ## Exact finite binary accounting -/

theorem uteLiteralOPTWithPrefix_binary
    {s b a d : ℝ} (hs : 0 ≤ s) :
    uteLiteralOPTWithPrefix s b a d 0 0 =
      uteBinaryOPT s (a + d) := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  have hcap : s + 1 ≤ s + 2 := by linarith
  simp [uteLiteralOPTWithPrefix, uteLiteralOPTCore,
    uteOPTPairCharge, uteEndpointEffective,
    uteEndpointProcessing, uteBinaryOPT,
    min_eq_left hone, min_eq_right hone,
    min_eq_left hcap, min_eq_right hcap]
  ring

theorem uteLiteralALGWithPrefix_binary_le
    {s b a d : ℝ}
    (hs0 : 0 ≤ s) (hb0 : 0 ≤ b)
    (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hd0 : 0 ≤ d) (hx1 : a + d ≤ 1) :
    uteLiteralALGWithPrefix s b a d 0 0 ≤
      uteBinaryALG s b (a + d) := by
  rw [uteLiteralALGWithPrefix_eq_polynomial hs0]
  by_cases hxb : a + d ≤ b
  · rw [uteBinaryALG, if_pos hxb]
    have hax : a ≤ a + d := by linarith
    have hfactor :
        0 ≤
          s * (1 - (a + d)) + b - (a + (a + d)) / 2 := by
      have hsTerm :
          0 ≤ s * (1 - (a + d)) :=
        mul_nonneg hs0 (sub_nonneg.mpr hx1)
      nlinarith
    have hid :
        (1 / 2 + (s + 1) *
            ((a + d) - (a + d) ^ 2 / 2)) -
          (1 / 2 + (s + 1) * (a - a ^ 2 / 2) +
            (1 - b) * d + s * d ^ 2 / 2) =
          ((a + d) - a) *
            (s * (1 - (a + d)) + b -
              (a + (a + d)) / 2) := by ring
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hax) hfactor
    nlinarith [hid]
  · have hbx : b ≤ a + d := le_of_not_ge hxb
    rw [uteBinaryALG, if_neg hxb]
    have hfactor :
        0 ≤
          s * (1 - (a + d)) + b - (a + b) / 2 := by
      have hsTerm :
          0 ≤ s * (1 - (a + d)) :=
        mul_nonneg hs0 (sub_nonneg.mpr hx1)
      nlinarith
    have hid :
        (1 / 2 +
            (s + 1) * (b - b ^ 2 / 2) +
            (1 - b) * ((a + d) - b) +
            s * ((a + d) - b) ^ 2 / 2) -
          (1 / 2 + (s + 1) * (a - a ^ 2 / 2) +
            (1 - b) * d + s * d ^ 2 / 2) =
          (b - a) *
            (s * (1 - (a + d)) + b -
              (a + b) / 2) := by ring
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hab) hfactor
    nlinarith [hid]

theorem uteFiniteOPT_binary_diagonal_le
    {s : ℝ} (hs : 0 ≤ s)
    (af zf d zs : ℕ) :
    uteLiteralOPTCore s af zf d 0 0 zs -
        uteFiniteOPTCore s af zf d 0 0 zs ≤
      (s + 1) / 2 * (af + zf + d + zs) := by
  rw [uteFiniteOPTCore_eq_literal_sub_diagonal]
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  have hcap : s + 1 ≤ s + 2 := by linarith
  simp [uteOPTPairCharge, uteEndpointEffective,
    uteEndpointProcessing, min_eq_left hone,
    min_eq_right hone, min_eq_left hcap,
    min_eq_right hcap]
  push_cast
  have haf : (0 : ℝ) ≤ af := by positivity
  have hzf : (0 : ℝ) ≤ zf := by positivity
  have hd : (0 : ℝ) ≤ d := by positivity
  have hzs : (0 : ℝ) ≤ zs := by positivity
  nlinarith [mul_nonneg hs haf, mul_nonneg hs hzf,
    mul_nonneg hs hd, mul_nonneg hs hzs]

set_option maxHeartbeats 800000 in
theorem uteFinite_binary_pairExcess_le
    {n k af zf d zs : ℕ} {s b : ℝ}
    (hn : n ≠ 0)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb : b = uteB s)
    (hkLower : (k : ℝ) ≤ b * n)
    (hkUpper : b * n < k + 1)
    (hforced : af + zf = k)
    (htotal : af + zf + d + zs = n) :
    uteFiniteALGCore s af zf d 0 0 zs -
        uteRho s * uteFiniteOPTCore s af zf d 0 0 zs ≤
      (1 + uteRho s * (s + 1) / 2) * n := by
  have hs0 : 0 ≤ s := hs.le
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let b' : ℝ := k / n
  let a : ℝ := af / n
  let deferred : ℝ := d / n
  let x : ℝ := a + deferred
  have hb'0 : 0 ≤ b' := by
    dsimp [b']
    positivity
  have hb'b : b' ≤ b := by
    dsimp [b']
    rw [div_le_iff₀ hnR]
    simpa [mul_comm] using hkLower
  have hround : b - b' < 1 / n := by
    dsimp [b']
    rw [sub_lt_iff_lt_add]
    rw [← add_div]
    rw [lt_div_iff₀ hnR]
    push_cast at hkUpper
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hd0 : 0 ≤ deferred := by
    dsimp [deferred]
    positivity
  have hab' : a ≤ b' := by
    dsimp [a, b']
    rw [div_le_div_iff_of_pos_right hnR]
    exact_mod_cast (by omega : af ≤ k)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    linarith
  have hx1 : x ≤ 1 := by
    dsimp [x, a, deferred]
    rw [show (af : ℝ) / n + d / n =
        ((af : ℝ) + d) / n by ring]
    rw [div_le_one hnR]
    exact_mod_cast (by omega : af + d ≤ n)
  have hzfR :
      (n : ℝ) * b' - af = zf := by
    dsimp [b']
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hforcedR :
        (af : ℝ) + zf = k := by
      exact_mod_cast hforced
    field_simp [hn0]
    nlinarith
  have hzsR :
      (n : ℝ) * (1 - b') - d = zs := by
    dsimp [b']
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnat : k + d + zs = n := by omega
    have hnatR :
        (k : ℝ) + d + zs = n := by
      exact_mod_cast hnat
    field_simp [hn0]
    nlinarith
  have halgNorm :=
    uteLiteralALGWithPrefix_normalized hn
      s b' (af : ℝ) (d : ℝ) 0 0
  have hoptNorm :=
    uteLiteralOPTWithPrefix_normalized hn
      s b' (af : ℝ) (d : ℝ) 0 0
  rw [hzfR, hzsR] at halgNorm hoptNorm
  norm_num at halgNorm hoptNorm
  have halgFinite :
      uteFiniteALGCore s af zf d 0 0 zs ≤
        (n : ℝ) ^ 2 *
          uteLiteralALGWithPrefix s b' a deferred 0 0 := by
    rw [halgNorm]
    simpa only [Nat.cast_zero] using
      (uteFiniteALGCore_le_literal hs0 af zf d 0 0 zs)
  have hoptDiag :=
    uteFiniteOPT_binary_diagonal_le hs0 af zf d zs
  have hoptLiteral :
      (n : ℝ) ^ 2 *
          uteLiteralOPTWithPrefix s b' a deferred 0 0 -
        uteFiniteOPTCore s af zf d 0 0 zs ≤
      (s + 1) / 2 * n := by
    rw [hoptNorm]
    have htotalR :
        (af : ℝ) + zf + d + zs = n := by
      exact_mod_cast htotal
    calc
      uteLiteralOPTCore s (af : ℝ) (zf : ℝ) (d : ℝ) 0 0 (zs : ℝ) -
          uteFiniteOPTCore s af zf d 0 0 zs ≤
        (s + 1) / 2 * ((af : ℝ) + zf + d + zs) := by
          simpa only [Nat.cast_zero] using hoptDiag
      _ = (s + 1) / 2 * n := by rw [htotalR]
  have hrho0 : 0 ≤ uteRho s := by
    exact (uteRho_pos hs).le
  have hsaturated :
      uteLiteralALGWithPrefix s b' a deferred 0 0 ≤
        uteBinaryALG s b' x :=
    uteLiteralALGWithPrefix_binary_le
      hs0 hb'0 ha0 hab' hd0 hx1
  have hoptBinary :
      uteLiteralOPTWithPrefix s b' a deferred 0 0 =
        uteBinaryOPT s x := by
    simpa [x] using
      (uteLiteralOPTWithPrefix_binary
        (s := s) (b := b') (a := a) (d := deferred) hs0)
  have hgapRound :
      uteBinaryGap s b' x ≤
        uteBinaryGap s b x + (b - b') :=
    uteBinaryGap_rounding_le
      hs0 hs1 hb'0 hb'b hb1 hx0 hx1
  have hgap :
      uteBinaryGap s b x ≤ 0 := by
    simpa [hb] using (uteBinaryGap_nonpos (s := s) (x := x) hs)
  have hroundScaled :
      (n : ℝ) ^ 2 * (b - b') ≤ n := by
    have hnnonneg : (0 : ℝ) ≤ n := hnR.le
    have hmul :=
      mul_le_mul_of_nonneg_left hround.le
        (sq_nonneg (n : ℝ))
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    calc
      (n : ℝ) ^ 2 * (b - b') ≤
          (n : ℝ) ^ 2 * (1 / n) := hmul
      _ = n := by field_simp [hn0]
  have hleading :
      (n : ℝ) ^ 2 *
          (uteLiteralALGWithPrefix s b' a deferred 0 0 -
            uteRho s *
              uteLiteralOPTWithPrefix s b' a deferred 0 0) ≤
        n := by
    rw [hoptBinary]
    have hpair :
        uteLiteralALGWithPrefix s b' a deferred 0 0 -
            uteRho s * uteBinaryOPT s x ≤
          uteBinaryGap s b' x := by
      unfold uteBinaryGap
      linarith
    have hgap' : uteBinaryGap s b' x ≤ b - b' := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left
      (hpair.trans hgap') (sq_nonneg (n : ℝ))]
  have hcombine :
      uteFiniteALGCore s af zf d 0 0 zs -
          uteRho s * uteFiniteOPTCore s af zf d 0 0 zs ≤
        (n : ℝ) ^ 2 *
            (uteLiteralALGWithPrefix s b' a deferred 0 0 -
              uteRho s *
                uteLiteralOPTWithPrefix s b' a deferred 0 0) +
          uteRho s * ((s + 1) / 2 * n) := by
    have hscaledDiag :=
      mul_le_mul_of_nonneg_left hoptLiteral hrho0
    nlinarith
  calc
    uteFiniteALGCore s af zf d 0 0 zs -
          uteRho s * uteFiniteOPTCore s af zf d 0 0 zs ≤
        (n : ℝ) ^ 2 *
            (uteLiteralALGWithPrefix s b' a deferred 0 0 -
              uteRho s *
                uteLiteralOPTWithPrefix s b' a deferred 0 0) +
          uteRho s * ((s + 1) / 2 * n) := hcombine
    _ ≤ (1 + uteRho s * (s + 1) / 2) * n := by
      nlinarith

/-! ## Exact runtime status word below two -/

def uteBelowRuntimeOutcome {n : ℕ}
    (k : ℕ) (s : ℝ) (processing : Fin n → ℝ)
    (job : Fin n) : BoundaryOutcome :=
  if job.val < k ∨ processing job ≤ s then
    .immediate
  else
    .deferred

@[simp] theorem uteBelowRuntimeOutcome_eq_deferred_iff
    {n k : ℕ} {s : ℝ} {processing : Fin n → ℝ}
    {job : Fin n} :
    uteBelowRuntimeOutcome k s processing job = .deferred ↔
      ¬(job.val < k ∨ processing job ≤ s) := by
  unfold uteBelowRuntimeOutcome
  split <;> simp_all

@[simp] theorem uteBelowRuntimeOutcome_ne_deferred_iff
    {n k : ℕ} {s : ℝ} {processing : Fin n → ℝ}
    {job : Fin n} :
    uteBelowRuntimeOutcome k s processing job ≠ .deferred ↔
      job.val < k ∨ processing job ≤ s := by
  unfold uteBelowRuntimeOutcome
  split <;> simp_all

@[simp] theorem uteBelowRuntimeOutcome_eq_immediate_iff
    {n k : ℕ} {s : ℝ} {processing : Fin n → ℝ}
    {job : Fin n} :
    uteBelowRuntimeOutcome k s processing job = .immediate ↔
      job.val < k ∨ processing job ≤ s := by
  unfold uteBelowRuntimeOutcome
  split <;> simp_all

theorem uteThreshold_add_one_eq_self
    {s : ℝ} (hs1 : s ≤ 1) :
    Online.uteThreshold (s + 1) = s := by
  unfold Online.uteThreshold
  rw [min_eq_right]
  · ring
  · linarith

namespace Online

theorem uteBelowRuntime_immediateFor
    {n k : ℕ} {s : ℝ} (hs1 : s ≤ 1)
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n) :
    ∀ job,
      uteBelowRuntimeOutcome k s processingTime job ≠ .deferred →
        transcript.ImmediateFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n k (uteThreshold (s + 1)))
          job := by
  intro job himmediate before after p hdecomp
  have hp : p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  change
    Transcript.forcedPrefixPendingImmediate?
        n k (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      some job
  rw [uteThreshold_add_one_eq_self hs1,
    forcedPrefixPendingImmediate_append_testResult, hbefore, hp]
  have hcondition :
      job.val < k ∨ processingTime job ≤ s :=
    uteBelowRuntimeOutcome_ne_deferred_iff.mp himmediate
  simp [hcondition]

theorem uteBelowRuntime_deferredFor
    {n k : ℕ} {s : ℝ} (hs1 : s ≤ 1)
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n) :
    ∀ job,
      uteBelowRuntimeOutcome k s processingTime job = .deferred →
        transcript.DeferredFor
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n k (uteThreshold (s + 1)))
          job := by
  intro job hdeferred before after p hdecomp
  have hp : p = processingTime job := by
    apply hmatch job p
    rw [hdecomp]
    simp
  have hbefore :
      (Transcript.testResults before).length = job.val :=
    testsBefore_testResult_eq_label
      htrace hallTests job p hdecomp
  change
    Transcript.forcedPrefixPendingImmediate?
        n k (uteThreshold (s + 1))
        (before ++ [Observation.testResult job p]) =
      none
  rw [uteThreshold_add_one_eq_self hs1,
    forcedPrefixPendingImmediate_append_testResult, hbefore, hp]
  have hcondition :
      ¬(job.val < k ∨ processingTime job ≤ s) :=
    uteBelowRuntimeOutcome_eq_deferred_iff.mp hdeferred
  simp [hcondition]

theorem uteBelowRuntime_deferred_nonzero
    {n k : ℕ} {s : ℝ} (hs : 0 < s)
    {processingTime : Label n → ℝ} :
    ∀ job,
      uteBelowRuntimeOutcome k s processingTime job = .deferred →
        processingTime job ≠ 0 := by
  intro job hdeferred hzero
  have hcondition :=
    uteBelowRuntimeOutcome_eq_deferred_iff.mp hdeferred
  apply hcondition
  right
  rw [hzero]
  exact hs.le

theorem run_forcedPrefixUTE_below_pairCharge_eq
    (n : ℕ) {s b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processingTime : Label n → ℝ)
    {left right : Label n} (horder : left < right) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
    tracePairCharge (.finite (s + 1)) processingTime
        result.config.transcript left right =
      obligatoryALGPairCharge
        ⟨uteBelowRuntimeOutcome (forcedPrefixCount n b) s
            processingTime left,
          processingTime left⟩
        ⟨uteBelowRuntimeOutcome (forcedPrefixCount n b) s
            processingTime right,
          processingTime right⟩ := by
  dsimp only
  let result :=
    run (.finite (s + 1)) (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n (s + 1) b (.finite (s + 1)) processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hfollow :
      result.config.transcript.FollowsStrategy
        (testProcessStrategy
          (fun current =>
            current.forcedPrefixPendingImmediate?
              n (forcedPrefixCount n b)
                (uteThreshold (s + 1)))) := by
    have h :=
      run_followsStrategy (.finite (s + 1))
        (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b)
        (2 * n + 1)
    rw [forcedPrefixUTEStrategy_eq_testProcessStrategy] at h
    exact h
  exact
    hrun.2.2.2.2.1.tracePairCharge_eq_obligatoryALGPairCharge
      hrun.2.2.1 hallTests hallProcessed hfollow
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n b) (uteThreshold (s + 1)))
      (uteBelowRuntimeOutcome (forcedPrefixCount n b) s processingTime)
      (uteBelowRuntime_immediateFor hs1
        hrun.2.2.2.2.1 hrun.2.2.1 hallTests)
      (uteBelowRuntime_deferredFor hs1
        hrun.2.2.2.2.1 hrun.2.2.1 hallTests)
      (uteBelowRuntime_deferred_nonzero hs)
      (.finite (s + 1)) horder

theorem run_forcedPrefixUTE_below_completionCost_eq_statusALG
    (n : ℕ) {s b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processingTime : Label n → ℝ) :
    let result :=
      run (.finite (s + 1)) (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n (s + 1) b) (2 * n + 1)
    runCompletionCost (.finite (s + 1)) processingTime result =
      obligatoryALGPairObjective
        (obligatoryJobsOfFunctions
          (uteBelowRuntimeOutcome (forcedPrefixCount n b) s
            processingTime)
          processingTime) := by
  dsimp only
  rw [run_forcedPrefixUTEStrategy_completionCost_eq_self_add_pairs]
  rw [obligatoryALGPairObjective_jobsOfFunctions_eq_finSums]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro left _hleft
    apply Finset.sum_congr rfl
    intro right hright
    exact run_forcedPrefixUTE_below_pairCharge_eq
      n hs hs1 processingTime (Finset.mem_filter.mp hright).2

end Online

def uteBelowStatusExcess {n : ℕ}
    (s : ℝ) (k : ℕ) (processing : Fin n → ℝ) : ℝ :=
  uteStatusWordExcess s
    (uteBelowRuntimeOutcome k s processing) processing

theorem run_forcedPrefixUTE_below_excess_eq_statusExcess
    (n : ℕ) {s b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processingTime : Online.Label n → ℝ) :
    let result :=
      Online.run (.finite (s + 1))
        (Online.fixedOracle processingTime)
        (Online.forcedPrefixUTEStrategy n (s + 1) b)
        (2 * n + 1)
    Online.runCompletionCost (.finite (s + 1))
          processingTime result -
        uteRho s *
          vectorOfflineCost (.finite (s + 1)) processingTime =
      uteBelowStatusExcess s
        (Online.forcedPrefixCount n b) processingTime := by
  dsimp only
  rw [Online.run_forcedPrefixUTE_below_completionCost_eq_statusALG
    n hs hs1 processingTime]
  unfold uteBelowStatusExcess uteStatusWordExcess
    uteStatusPairExcess
  rw [Online.obligatoryALGPairObjective_jobsOfFunctions_eq_finSums,
    vectorOfflineCost_finite_add_one_eq_uteFixedWordOPT]
  unfold uteFixedSelfExcessAt uteFixedWordOPT
  simp only [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  ring

/-! ## Deterministic Bernoulli extremalization -/

def uteBelowRoundWeight {n : ℕ}
    (k : ℕ) (s : ℝ) (processing : Fin n → ℝ)
    (coordinate : Fin n) : ℝ :=
  if uteBelowRuntimeOutcome k s processing coordinate = .deferred then
    1
  else if coordinate.val < k then
    processing coordinate / (s + 1)
  else
    processing coordinate

theorem uteEffectiveAt_zero
    {s : ℝ} (hs : 0 ≤ s) :
    uteEffectiveAt s 0 = 1 := by
  simp [uteEffectiveAt, min_eq_left (by linarith : (1 : ℝ) ≤ s + 1)]

theorem uteEffectiveAt_cap
    (s : ℝ) :
    uteEffectiveAt s (s + 1) = s + 1 := by
  unfold uteEffectiveAt
  rw [min_eq_right]
  linarith

theorem uteEffectiveAt_mem
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) :
    uteEffectiveAt s p ∈ Icc 1 (s + 1) := by
  unfold uteEffectiveAt
  constructor
  · exact le_min (by linarith) (by linarith)
  · exact min_le_right _ _

theorem uteBelowRoundWeight_mem
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n) :
    uteBelowRoundWeight k s processing coordinate ∈ Icc 0 1 := by
  by_cases hdeferred :
      uteBelowRuntimeOutcome k s processing coordinate = .deferred
  · simp [uteBelowRoundWeight, hdeferred]
  · have himmediate :
        coordinate.val < k ∨ processing coordinate ≤ s :=
      uteBelowRuntimeOutcome_ne_deferred_iff.mp hdeferred
    by_cases hprefix : coordinate.val < k
    · simp [uteBelowRoundWeight, hdeferred, hprefix]
      constructor
      · exact div_nonneg (hprocessing coordinate).1
          (by linarith : 0 ≤ s + 1)
      · rw [div_le_one (by linarith : 0 < s + 1)]
        exact (hprocessing coordinate).2
    · have hpUpper : processing coordinate ≤ 1 := by
        rcases himmediate with h | h
        · exact False.elim (hprefix h)
        · exact h.trans hs1
      simp [uteBelowRoundWeight, hdeferred, hprefix,
        (hprocessing coordinate).1, hpUpper]

theorem uteBelow_expectedEffective_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n) :
    1 + uteBelowRoundWeight k s processing coordinate * s ≤
      uteEffectiveAt s (processing coordinate) := by
  let p := processing coordinate
  by_cases hdeferred :
      uteBelowRuntimeOutcome k s processing coordinate = .deferred
  · have hp : s ≤ p := by
      have hcondition :=
        uteBelowRuntimeOutcome_eq_deferred_iff.mp hdeferred
      dsimp [p]
      exact le_of_not_ge (fun h => hcondition (Or.inr h))
    have heff : uteEffectiveAt s p = s + 1 := by
      rw [uteEffectiveAt_eq_one_add_min, min_eq_right hp]
      ring
    rw [show processing coordinate = p by rfl, heff]
    simp [uteBelowRoundWeight, hdeferred]
    linarith
  · have himmediate :
        coordinate.val < k ∨ p ≤ s := by
      simpa [p] using
        uteBelowRuntimeOutcome_ne_deferred_iff.mp hdeferred
    by_cases hprefix : coordinate.val < k
    · have hu : 0 < s + 1 := by linarith
      have hp0 : 0 ≤ p := (hprocessing coordinate).1
      have hpU : p ≤ s + 1 := (hprocessing coordinate).2
      by_cases hps : p ≤ s
      · rw [uteEffectiveAt_eq_one_add_min, min_eq_left hps]
        simp [uteBelowRoundWeight, hdeferred, hprefix, p]
        have hsdiv : s / (s + 1) ≤ 1 := by
          rw [div_le_one hu]
          linarith
        have hscaled :=
          mul_le_mul_of_nonneg_right hsdiv hp0
        have hid :
            p / (s + 1) * s =
              (s / (s + 1)) * p := by ring
        rw [hid]
        nlinarith
      · have hsp : s ≤ p := le_of_not_ge hps
        rw [uteEffectiveAt_eq_one_add_min, min_eq_right hsp]
        simp [uteBelowRoundWeight, hdeferred, hprefix, p]
        have hr :
            p / (s + 1) ≤ 1 := by
          rw [div_le_one hu]
          exact hpU
        nlinarith [mul_le_mul_of_nonneg_right hr hs.le]
    · have hpS : p ≤ s := by
        rcases himmediate with h | h
        · exact False.elim (hprefix h)
        · exact h
      rw [uteEffectiveAt_eq_one_add_min, min_eq_left hpS]
      simp [uteBelowRoundWeight, hdeferred, hprefix, p]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1)
        (hprocessing coordinate).1]

theorem uteBelow_expectedOPT_left_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate other : Fin n) :
    let r := uteBelowRoundWeight k s processing coordinate
    (1 - r) *
          uteFixedOPTPairCharge s 0 (processing other) +
        r *
          uteFixedOPTPairCharge s (s + 1) (processing other) ≤
      uteFixedOPTPairCharge s
        (processing coordinate) (processing other) := by
  dsimp only
  let r := uteBelowRoundWeight k s processing coordinate
  let ep := uteEffectiveAt s (processing coordinate)
  let eq := uteEffectiveAt s (processing other)
  have hr := uteBelowRoundWeight_mem (k := k) hs hs1
    processing hprocessing coordinate
  have heq := uteEffectiveAt_mem hs.le
    (hprocessing other).1
  have havg :
      1 + r * (eq - 1) ≤ ep := by
    have hqCap : eq - 1 ≤ s := by
      dsimp [eq]
      linarith [heq.2]
    have hscaled :=
      mul_le_mul_of_nonneg_left hqCap hr.1
    have heff :=
      uteBelow_expectedEffective_le (k := k) hs hs1
        processing hprocessing coordinate
    nlinarith
  have havgQ :
      1 + r * (eq - 1) ≤ eq := by
    have hscaled :=
      mul_le_mul_of_nonneg_right hr.2
        (sub_nonneg.mpr heq.1)
    nlinarith
  have hmin :
      1 + r * (eq - 1) ≤ min ep eq :=
    le_min havg havgQ
  have hzero := uteEffectiveAt_zero hs.le
  have hcap := uteEffectiveAt_cap s
  unfold uteFixedOPTPairCharge
  dsimp [ep, eq] at hmin ⊢
  rw [hzero, hcap, min_eq_left heq.1,
    min_eq_right heq.2]
  nlinarith

theorem uteBelow_expectedOPT_right_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (other coordinate : Fin n) :
    let r := uteBelowRoundWeight k s processing coordinate
    (1 - r) *
          uteFixedOPTPairCharge s (processing other) 0 +
        r *
          uteFixedOPTPairCharge s (processing other) (s + 1) ≤
      uteFixedOPTPairCharge s
        (processing other) (processing coordinate) := by
  simpa [uteFixedOPTPairCharge, min_comm] using
    uteBelow_expectedOPT_left_le hs hs1
      processing hprocessing coordinate other

@[simp] theorem uteBelowRuntimeOutcome_update_zero
    {n k : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (processing : Fin n → ℝ) (coordinate : Fin n) :
    uteBelowRuntimeOutcome k s
        (Function.update processing coordinate 0) coordinate =
      .immediate := by
  simp [uteBelowRuntimeOutcome, Function.update, hs]

theorem uteBelowRuntimeOutcome_update_cap
    {n k : ℕ} {s : ℝ} (hs : 0 < s)
    (processing : Fin n → ℝ) (coordinate : Fin n) :
    uteBelowRuntimeOutcome k s
        (Function.update processing coordinate (s + 1)) coordinate =
      if coordinate.val < k then .immediate else .deferred := by
  unfold uteBelowRuntimeOutcome
  simp [Function.update]
  by_cases hprefix : coordinate.val < k
  · simp [hprefix]
  · have hnot : ¬s + 1 ≤ s := by linarith
    simp [hprefix, hnot]

theorem uteBelowRuntimeOutcome_update_ne
    {n k : ℕ} {s value : ℝ}
    (processing : Fin n → ℝ) {coordinate other : Fin n}
    (hne : other ≠ coordinate) :
    uteBelowRuntimeOutcome k s
        (Function.update processing coordinate value) other =
      uteBelowRuntimeOutcome k s processing other := by
  simp [uteBelowRuntimeOutcome, Function.update, hne, Ne.symm hne]

theorem uteBelow_expectedSelfALG_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n) :
    let r := uteBelowRoundWeight k s processing coordinate
    1 + processing coordinate ≤
      (1 - r) * (1 + 0) + r * (1 + (s + 1)) := by
  dsimp only
  let p := processing coordinate
  by_cases hdeferred :
      uteBelowRuntimeOutcome k s processing coordinate = .deferred
  · simp [uteBelowRoundWeight, hdeferred, p]
    exact (hprocessing coordinate).2
  · by_cases hprefix : coordinate.val < k
    · have hu : 0 < s + 1 := by linarith
      simp [uteBelowRoundWeight, hdeferred, hprefix, p]
      field_simp [hu.ne']
      nlinarith
    · have hp0 : 0 ≤ p := (hprocessing coordinate).1
      simp [uteBelowRoundWeight, hdeferred, hprefix, p]
      nlinarith [mul_nonneg hs.le hp0]

theorem uteBelow_expectedSelfExcess_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n) :
    let r := uteBelowRoundWeight k s processing coordinate
    uteFixedSelfExcessAt s (processing coordinate) ≤
      (1 - r) * uteFixedSelfExcessAt s 0 +
        r * uteFixedSelfExcessAt s (s + 1) := by
  dsimp only
  let r := uteBelowRoundWeight k s processing coordinate
  have halg :=
    uteBelow_expectedSelfALG_le (k := k) hs hs1
      processing hprocessing coordinate
  have heff :=
    uteBelow_expectedEffective_le (k := k) hs hs1
      processing hprocessing coordinate
  have hrho := (uteRho_pos hs).le
  have heff0 := uteEffectiveAt_zero hs.le
  have heffU := uteEffectiveAt_cap s
  unfold uteFixedSelfExcessAt
  rw [heff0, heffU]
  have hscaled :=
    mul_le_mul_of_nonneg_left heff hrho
  nlinarith

theorem uteBelow_expectedALGPair_left_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    {coordinate other : Fin n} (horder : coordinate < other) :
    let r := uteBelowRoundWeight k s processing coordinate
    let atZero := Function.update processing coordinate 0
    let atCap :=
      Function.update processing coordinate (s + 1)
    obligatoryALGPairCharge
        ⟨uteBelowRuntimeOutcome k s processing coordinate,
          processing coordinate⟩
        ⟨uteBelowRuntimeOutcome k s processing other,
          processing other⟩ ≤
      (1 - r) *
          obligatoryALGPairCharge
            ⟨uteBelowRuntimeOutcome k s atZero coordinate,
              atZero coordinate⟩
            ⟨uteBelowRuntimeOutcome k s atZero other,
              atZero other⟩ +
        r *
          obligatoryALGPairCharge
            ⟨uteBelowRuntimeOutcome k s atCap coordinate,
              atCap coordinate⟩
            ⟨uteBelowRuntimeOutcome k s atCap other,
              atCap other⟩ := by
  dsimp only
  have hne : other ≠ coordinate := ne_of_gt horder
  have hout0 :=
    uteBelowRuntimeOutcome_update_zero (k := k) hs.le
      processing coordinate
  have houtU :=
    uteBelowRuntimeOutcome_update_cap (k := k) hs
      processing coordinate
  have hother0 :=
    uteBelowRuntimeOutcome_update_ne (k := k) (s := s)
      processing (value := (0 : ℝ)) hne
  have hotherU :=
    uteBelowRuntimeOutcome_update_ne (k := k) (s := s)
      processing (value := s + 1) hne
  rw [hout0, houtU, hother0, hotherU]
  simp only [Function.update_self]
  simp [Function.update, hne, Ne.symm hne]
  let p := processing coordinate
  let q := processing other
  by_cases hdeferred :
      uteBelowRuntimeOutcome k s processing coordinate = .deferred
  · have hprefix : ¬coordinate.val < k := by
      intro h
      exact
        (uteBelowRuntimeOutcome_eq_deferred_iff.mp hdeferred)
          (Or.inl h)
    have hpU : p ≤ s + 1 := (hprocessing coordinate).2
    rw [hdeferred]
    simp only [uteBelowRoundWeight, hdeferred, if_pos,
      hprefix, if_neg, sub_self, zero_mul, one_mul, zero_add]
    by_cases hother :
        uteBelowRuntimeOutcome k s processing other = .deferred
    · rw [hother]
      simpa only [obligatoryALGPairCharge, ite_false,
        p, q, add_comm] using
          add_le_add_left (min_le_min_right q hpU) 2
    · have hotherI :
          uteBelowRuntimeOutcome k s processing other =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr
          (uteBelowRuntimeOutcome_ne_deferred_iff.mp hother)
      rw [hotherI]
      simp only [obligatoryALGPairCharge, ite_false]
      exact le_rfl
  · have himmediate :
        coordinate.val < k ∨ p ≤ s := by
      simpa [p] using
        uteBelowRuntimeOutcome_ne_deferred_iff.mp hdeferred
    by_cases hprefix : coordinate.val < k
    · have hu : 0 < s + 1 := by linarith
      have hpEq : processing coordinate = p := rfl
      have himmEq :
          uteBelowRuntimeOutcome k s processing coordinate =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr himmediate
      rw [himmEq]
      simp [uteBelowRoundWeight, hdeferred, hprefix,
        obligatoryALGPairCharge]
      field_simp [hu.ne']
      nlinarith
    · have hpS : p ≤ s := by
        rcases himmediate with h | h
        · exact False.elim (hprefix h)
        · exact h
      have hp0 : 0 ≤ p := (hprocessing coordinate).1
      have hq0 : 0 ≤ q := (hprocessing other).1
      have hqU : q ≤ s + 1 := (hprocessing other).2
      have himmEq :
          uteBelowRuntimeOutcome k s processing coordinate =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr himmediate
      rw [himmEq]
      simp only [uteBelowRoundWeight, hdeferred, if_neg,
        hprefix]
      by_cases hother :
          uteBelowRuntimeOutcome k s processing other = .deferred
      · rw [hother]
        simp only [obligatoryALGPairCharge, ite_false]
        rw [min_eq_right hqU]
        nlinarith [mul_nonneg hp0 hq0]
      · have hotherI :
            uteBelowRuntimeOutcome k s processing other =
              .immediate :=
          uteBelowRuntimeOutcome_eq_immediate_iff.mpr
            (uteBelowRuntimeOutcome_ne_deferred_iff.mp hother)
        rw [hotherI]
        simp only [obligatoryALGPairCharge, ite_false]
        nlinarith [mul_nonneg hp0 hq0]

theorem uteBelow_expectedALGPair_right_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    {other coordinate : Fin n} (horder : other < coordinate)
    (hprior :
      ∀ i, i < coordinate →
        processing i = 0 ∨ processing i = s + 1) :
    let r := uteBelowRoundWeight k s processing coordinate
    let atZero := Function.update processing coordinate 0
    let atCap :=
      Function.update processing coordinate (s + 1)
    obligatoryALGPairCharge
        ⟨uteBelowRuntimeOutcome k s processing other,
          processing other⟩
        ⟨uteBelowRuntimeOutcome k s processing coordinate,
          processing coordinate⟩ ≤
      (1 - r) *
          obligatoryALGPairCharge
            ⟨uteBelowRuntimeOutcome k s atZero other,
              atZero other⟩
            ⟨uteBelowRuntimeOutcome k s atZero coordinate,
              atZero coordinate⟩ +
        r *
          obligatoryALGPairCharge
            ⟨uteBelowRuntimeOutcome k s atCap other,
              atCap other⟩
            ⟨uteBelowRuntimeOutcome k s atCap coordinate,
              atCap coordinate⟩ := by
  dsimp only
  have hne : other ≠ coordinate := ne_of_lt horder
  have hout0 :=
    uteBelowRuntimeOutcome_update_zero (k := k) hs.le
      processing coordinate
  have houtU :=
    uteBelowRuntimeOutcome_update_cap (k := k) hs
      processing coordinate
  have hother0 :=
    uteBelowRuntimeOutcome_update_ne (k := k) (s := s)
      processing (value := (0 : ℝ)) hne
  have hotherU :=
    uteBelowRuntimeOutcome_update_ne (k := k) (s := s)
      processing (value := s + 1) hne
  rw [hout0, houtU, hother0, hotherU]
  simp only [Function.update_self]
  simp [Function.update, hne, Ne.symm hne]
  let p := processing coordinate
  let q := processing other
  have hqBinary : q = 0 ∨ q = s + 1 := by
    simpa [q] using hprior other horder
  by_cases hdeferred :
      uteBelowRuntimeOutcome k s processing coordinate = .deferred
  · have hprefix : ¬coordinate.val < k := by
      intro h
      exact
        (uteBelowRuntimeOutcome_eq_deferred_iff.mp hdeferred)
          (Or.inl h)
    have hpU : p ≤ s + 1 := (hprocessing coordinate).2
    rw [hdeferred]
    simp only [uteBelowRoundWeight, hdeferred, if_pos,
      hprefix, if_neg, sub_self, zero_mul, one_mul, zero_add]
    by_cases hleft :
        uteBelowRuntimeOutcome k s processing other = .deferred
    · have hqU : q = s + 1 := by
        rcases hqBinary with hq0 | hqU
        · have hcondition :=
            uteBelowRuntimeOutcome_eq_deferred_iff.mp hleft
          exfalso
          apply hcondition
          right
          change processing other = 0 at hq0
          rw [hq0]
          exact hs.le
        · exact hqU
      change processing other = s + 1 at hqU
      rw [hleft, hqU]
      simp only [obligatoryALGPairCharge, ite_false]
      rw [min_eq_right hpU]
      rw [min_self]
      linarith
    · have hleftI :
          uteBelowRuntimeOutcome k s processing other =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr
          (uteBelowRuntimeOutcome_ne_deferred_iff.mp hleft)
      rw [hleftI]
      simp only [obligatoryALGPairCharge, ite_false]
      exact le_rfl
  · have himmediate :
        coordinate.val < k ∨ p ≤ s := by
      simpa [p] using
        uteBelowRuntimeOutcome_ne_deferred_iff.mp hdeferred
    by_cases hprefix : coordinate.val < k
    · have hleftPrefix : other.val < k :=
        lt_trans horder hprefix
      have hleftImmediate :
          uteBelowRuntimeOutcome k s processing other =
            .immediate := by
        unfold uteBelowRuntimeOutcome
        simp [hleftPrefix]
      have himmEq :
          uteBelowRuntimeOutcome k s processing coordinate =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr himmediate
      rw [himmEq, hleftImmediate]
      simp [uteBelowRoundWeight, hdeferred, hprefix,
        obligatoryALGPairCharge]
      ring_nf
      exact le_refl (1 + processing other)
    · have hpS : p ≤ s := by
        rcases himmediate with h | h
        · exact False.elim (hprefix h)
        · exact h
      have hp0 : 0 ≤ p := (hprocessing coordinate).1
      have himmEq :
          uteBelowRuntimeOutcome k s processing coordinate =
            .immediate :=
        uteBelowRuntimeOutcome_eq_immediate_iff.mpr himmediate
      rw [himmEq]
      simp only [uteBelowRoundWeight, hdeferred, if_neg,
        hprefix]
      by_cases hleft :
          uteBelowRuntimeOutcome k s processing other = .deferred
      · have hqU : q = s + 1 := by
          rcases hqBinary with hq0 | hqU
          · have hcondition :=
              uteBelowRuntimeOutcome_eq_deferred_iff.mp hleft
            exfalso
            apply hcondition
            right
            change processing other = 0 at hq0
            rw [hq0]
            exact hs.le
          · exact hqU
        change processing other = s + 1 at hqU
        rw [hleft, hqU]
        simp only [obligatoryALGPairCharge, ite_false]
        rw [min_self]
        nlinarith [mul_nonneg hs.le hp0]
      · have hleftI :
            uteBelowRuntimeOutcome k s processing other =
              .immediate :=
          uteBelowRuntimeOutcome_eq_immediate_iff.mpr
            (uteBelowRuntimeOutcome_ne_deferred_iff.mp hleft)
        rw [hleftI]
        simp only [obligatoryALGPairCharge, ite_false]
        ring_nf
        exact le_refl (1 + processing other)

end

end SchedulingPaper
