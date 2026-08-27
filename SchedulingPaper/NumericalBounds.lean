import SchedulingPaper.ExactCurve
import SchedulingPaper.RevealingOptimizationAlgebra

/-!
# Certified decimal brackets used in the paper

The main development uses exact symbolic constants.  These short lemmas
certify the decimal summaries printed in the introduction and figures.
-/

namespace SchedulingPaper

noncomputable section

theorem sqrt_five_decimal_bounds :
    (2236 : ℝ) / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
  have hs0 := Real.sqrt_nonneg 5
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor <;> nlinarith

theorem uDiamond_decimal_bounds :
    (1866 : ℝ) / 1000 < uDiamond ∧ uDiamond < 1867 / 1000 := by
  have hφ : (1618 : ℝ) / 1000 < goldenRatio ∧
      goldenRatio < 3237 / 2000 := by
    unfold goldenRatio
    rcases sqrt_five_decimal_bounds with ⟨h5l, h5u⟩
    constructor <;> linarith
  have hprod := uDiamond_mul_sub_one
  have hu1 := uDiamond_gt_one
  constructor
  · by_contra hnot
    have hu : uDiamond ≤ (1866 : ℝ) / 1000 := le_of_not_gt hnot
    have hmul : uDiamond * (uDiamond - 1) ≤
        ((1866 : ℝ) / 1000) * (1866 / 1000 - 1) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ uDiamond - 1)
        (by norm_num : (0 : ℝ) ≤ 1866 / 1000 - 1)]
    rw [hprod] at hmul
    norm_num at hmul
    linarith [hφ.1]
  · by_contra hnot
    have hu : (1867 : ℝ) / 1000 ≤ uDiamond := le_of_not_gt hnot
    have hmul : ((1867 : ℝ) / 1000) * (1867 / 1000 - 1) ≤
        uDiamond * (uDiamond - 1) := by
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1867 / 1000 - 1)
        (by linarith : 0 ≤ uDiamond - 1)]
    rw [hprod] at hmul
    norm_num at hmul
    linarith [hφ.2]

theorem uZero_decimal_bounds :
    (3147 : ℝ) / 1000 < uZero ∧ uZero < 3148 / 1000 := by
  have hroot : sZeroPolynomial sZero = 0 := by
    exact sub_eq_zero.mpr sZero_spec.2.2
  have hleft : sZeroPolynomial ((2147 : ℝ) / 1000) < 0 := by
    norm_num [sZeroPolynomial]
  have hright : 0 < sZeroPolynomial ((2148 : ℝ) / 1000) := by
    norm_num [sZeroPolynomial]
  have hs2 := sZero_spec.1
  constructor
  · unfold uZero
    by_contra hnot
    have hs : sZero ≤ (2147 : ℝ) / 1000 := by linarith
    have hmono := sZeroPolynomial_strictMono_above_two hs2
      (show sZero < (2147 : ℝ) / 1000 by
        rcases eq_or_lt_of_le hs with heq | hlt
        · rw [heq] at hroot
          linarith
        · exact hlt)
    rw [hroot] at hmono
    linarith
  · unfold uZero
    by_contra hnot
    have hs : (2148 : ℝ) / 1000 ≤ sZero := by linarith
    rcases eq_or_lt_of_le hs with heq | hlt
    · have hroot' := hroot
      rw [← heq] at hroot'
      linarith
    · have hmono := sZeroPolynomial_strictMono_above_two
          (by norm_num : (2 : ℝ) < 2148 / 1000) hlt
      rw [hroot] at hmono
      linarith

namespace RevealingOptimization

theorem transition_decimal_bounds :
    (5048917 : ℝ) / 1000000 < transition ∧
      transition < 5048918 / 1000000 := by
  have hleft : transitionPolynomial ((5048917 : ℝ) / 1000000) < 0 := by
    norm_num [transitionPolynomial]
  have hright : 0 < transitionPolynomial ((5048918 : ℝ) / 1000000) := by
    norm_num [transitionPolynomial]
  have hroot := transition_spec.2
  constructor
  · have hle := (transitionPolynomial_nonpos_iff
        (by norm_num : (1 : ℝ) < 5048917 / 1000000)).1 hleft.le
    exact lt_of_le_of_ne hle (by
      intro heq
      rw [heq, hroot] at hleft
      linarith)
  · by_contra hnot
    have hle : (5048918 : ℝ) / 1000000 ≤ transition := le_of_not_gt hnot
    have hnonpos := (transitionPolynomial_nonpos_iff
      (by norm_num : (1 : ℝ) < 5048918 / 1000000)).2 hle
    linarith

theorem sqrt_three_decimal_bounds :
    (1732 : ℝ) / 1000 < Real.sqrt 3 ∧ Real.sqrt 3 < 1733 / 1000 := by
  have hs0 := Real.sqrt_nonneg 3
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  constructor <;> nlinarith

theorem globalMaximum_decimal_bounds :
    (1625 : ℝ) / 1000 < globalMaximum ∧
      globalMaximum < 1626 / 1000 := by
  unfold globalMaximum
  rcases sqrt_three_decimal_bounds with ⟨h3l, h3u⟩
  constructor <;> nlinarith

end RevealingOptimization

/-! The logarithmic endpoint.  We evaluate `log q` with the rapidly
convergent identity
`log q = 2 * ∑ x^(2i+1)/(2i+1) + remainder`,
where `x=(q-1)/(q+1)`. -/

theorem zRootFunction_at_45051_neg :
    zRootFunction ((45051 : ℝ) / 10000) < 0 := by
  let x : ℝ := (((45051 : ℝ) / 10000) - 1) /
    (((45051 : ℝ) / 10000) + 1)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hlog := Real.sum_range_le_log_div hx0 hx1 13
  norm_num [x] at hlog
  unfold zRootFunction
  linarith

theorem zRootFunction_at_45056_pos :
    0 < zRootFunction ((45056 : ℝ) / 10000) := by
  let x : ℝ := (((45056 : ℝ) / 10000) - 1) /
    (((45056 : ℝ) / 10000) + 1)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hlog := Real.log_div_le_sum_range_add hx0 hx1 13
  norm_num [x] at hlog
  unfold zRootFunction
  linarith

theorem zStar_decimal_bounds :
    (45051 : ℝ) / 10000 < zStar ∧ zStar < 45056 / 10000 := by
  have hroot : zRootFunction zStar = 0 := by
    unfold zRootFunction
    linarith [zStar_equation]
  constructor
  · by_contra hnot
    have hle : zStar ≤ (45051 : ℝ) / 10000 := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hneg := zRootFunction_at_45051_neg
      rw [← heq, hroot] at hneg
      linarith
    · have hmono := zRootFunction_strictMonoOn
          zStar_gt_one (by norm_num) hlt
      rw [hroot] at hmono
      linarith [zRootFunction_at_45051_neg]
  · by_contra hnot
    have hle : (45056 : ℝ) / 10000 ≤ zStar := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hpos := zRootFunction_at_45056_pos
      rw [heq, hroot] at hpos
      linarith
    · have hmono := zRootFunction_strictMonoOn
          (by norm_num) zStar_gt_one hlt
      rw [hroot] at hmono
      linarith [zRootFunction_at_45056_pos]

theorem RStar_decimal_bounds :
    (15705 : ℝ) / 10000 < RStar ∧ RStar < 15706 / 10000 := by
  rcases zStar_decimal_bounds with ⟨hzl, hzu⟩
  have hden : 0 < zStar - 1 := by linarith [zStar_gt_one]
  unfold RStar rhoStar
  constructor
  · have hfrac : (5705 : ℝ) / 10000 < 2 / (zStar - 1) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    linarith
  · have hfrac : 2 / (zStar - 1) < (5706 : ℝ) / 10000 := by
      apply (div_lt_iff₀ hden).2
      nlinarith
    linarith

end
end SchedulingPaper
