import SchedulingPaper.LowRegime

/-!
# The normalized Zero-prefix game

After the exchange reductions in the Zero-prefix extension lemma, a schedule
is described by four nonnegative normalized parameters:

* `s` is the cap parameter,
* `d` is the mass tested and then processed,
* `t` is the mass tested and killed, and
* `m` is the untested mass.

Writing `y = d + t + m`, the two normalized costs in the manuscript are

`A = 1/2 + y - m²/2 + s d²/2`

and

`O = 1/2 + y²/2 + (s - 1)d²/2`.

This file proves the full algebraic interpolation between the two scalar
faces checked in `LowRegime.lean`.  In particular, it removes the informal
"the quotient is fractional-linear in `d²`, hence its maximum is at an
endpoint" step.
-/

namespace SchedulingPaper

noncomputable section

/-- Normalized online cost in the reduced Zero-prefix game. -/
def zeroPrefixAlg (s d t m : ℝ) : ℝ :=
  1 / 2 + (d + t + m) - m ^ 2 / 2 + s * d ^ 2 / 2

/-- Normalized clairvoyant cost in the reduced Zero-prefix game. -/
def zeroPrefixOpt (s d t m : ℝ) : ℝ :=
  1 / 2 + (d + t + m) ^ 2 / 2 + (s - 1) * d ^ 2 / 2

/-- Competitive factor used on the fourth finite-cap branch. -/
def zeroPrefixFactor (s : ℝ) : ℝ :=
  1 + 1 / Real.sqrt s

/-- On the range `s ≤ φ + 1`, the uncapped scalar face is also bounded by
the fourth-branch factor. -/
theorem goldenRatio_le_zeroPrefixFactor {s : ℝ}
    (hs : 0 < s) (hsφ : s ≤ goldenRatio + 1) :
    goldenRatio ≤ zeroPrefixFactor s := by
  have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsqrt_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hsqrt_le : Real.sqrt s ≤ goldenRatio := by
    have hφnonneg : 0 ≤ goldenRatio := goldenRatio_pos.le
    have hsqrtnonneg : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    nlinarith [goldenRatio_sq]
  have hinv_le :
      1 / goldenRatio ≤ 1 / Real.sqrt s :=
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le
  have hφinv : 1 / goldenRatio = goldenRatio - 1 := by
    rw [div_eq_iff (ne_of_gt goldenRatio_pos)]
    nlinarith [goldenRatio_mul_sub_one]
  unfold zeroPrefixFactor
  rw [hφinv] at hinv_le
  linarith

/-- The reduced offline expression is strictly positive on the feasible
region.  This lets us state the result both as a multiplicative inequality
and as a ratio bound. -/
theorem zeroPrefixOpt_pos {s d t m : ℝ}
    (hs : 0 < s) (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    0 < zeroPrefixOpt s d t m := by
  let y := d + t + m
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdy : d ≤ y := by
    dsimp [y]
    linarith
  have hsqdiff : 0 ≤ y ^ 2 - d ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdy) (add_nonneg hy hd)]
  have hsd : 0 ≤ s * d ^ 2 := mul_nonneg hs.le (sq_nonneg d)
  unfold zeroPrefixOpt
  dsimp [y] at hy hdy hsqdiff ⊢
  nlinarith

/-- Complete normalized Zero-prefix certificate.  The proof uses that the
gap is affine in `z = d²`: according to the sign of its coefficient, it is
bounded by either the `z = 0` face or the `z = y²` face. -/
theorem zeroPrefixAlg_le_factor_mul_opt {s d t m : ℝ}
    (hs : 0 < s) (hsφ : s ≤ goldenRatio + 1)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    zeroPrefixAlg s d t m ≤
      zeroPrefixFactor s * zeroPrefixOpt s d t m := by
  let y := d + t + m
  let r := zeroPrefixFactor s
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdy : d ≤ y := by
    dsimp [y]
    linarith
  have hdz : 0 ≤ d ^ 2 := sq_nonneg d
  have hdz_le : d ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdy) (add_nonneg hy hd)]

  have hφr : goldenRatio ≤ r := by
    simpa [r] using goldenRatio_le_zeroPrefixFactor hs hsφ

  have hden0 : 0 < 1 + y ^ 2 := by positivity
  have hface0φ :
      1 + 2 * y ≤ goldenRatio * (1 + y ^ 2) := by
    exact (div_le_iff₀ hden0).mp (zeroPrefix_uncapped_face y)
  have hface0 :
      1 + 2 * y ≤ r * (1 + y ^ 2) := by
    calc
      1 + 2 * y ≤ goldenRatio * (1 + y ^ 2) := hface0φ
      _ ≤ r * (1 + y ^ 2) :=
        mul_le_mul_of_nonneg_right hφr hden0.le

  have hden1 : 0 < 1 + s * y ^ 2 := by positivity
  have hface1ratio :
      (1 + 2 * y + s * y ^ 2) / (1 + s * y ^ 2) ≤ r := by
    calc
      (1 + 2 * y + s * y ^ 2) / (1 + s * y ^ 2) =
          1 + 2 * y / (1 + s * y ^ 2) := by
            field_simp
            ring
      _ ≤ 1 + 1 / Real.sqrt s := zeroPrefix_capped_face hs y
      _ = r := rfl
  have hface1 :
      1 + 2 * y + s * y ^ 2 ≤ r * (1 + s * y ^ 2) :=
    (div_le_iff₀ hden1).mp hface1ratio

  let c := s - r * (s - 1)
  have hcore :
      1 + 2 * y + s * d ^ 2 ≤
        r * (1 + y ^ 2 + (s - 1) * d ^ 2) := by
    by_cases hc : 0 ≤ c
    · have hmono : c * d ^ 2 ≤ c * y ^ 2 :=
        mul_le_mul_of_nonneg_left hdz_le hc
      dsimp [c] at hmono
      nlinarith [hface1]
    · have hc' : c ≤ 0 := le_of_not_ge hc
      have hmono : c * d ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc' hdz
      dsimp [c] at hmono
      nlinarith [hface0]

  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  unfold zeroPrefixAlg zeroPrefixOpt
  dsimp [y] at hcore ⊢
  nlinarith

/-- Ratio form of the preceding theorem. -/
theorem zeroPrefix_ratio_le {s d t m : ℝ}
    (hs : 0 < s) (hsφ : s ≤ goldenRatio + 1)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    zeroPrefixAlg s d t m / zeroPrefixOpt s d t m ≤
      zeroPrefixFactor s := by
  rw [div_le_iff₀ (zeroPrefixOpt_pos hs hd ht hm)]
  exact zeroPrefixAlg_le_factor_mul_opt hs hsφ hd ht hm

end

end SchedulingPaper
