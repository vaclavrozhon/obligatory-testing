import SchedulingPaper.BlindOptimizationAlgebra
import Mathlib.Tactic

/-!
# Finite hidden-stopping arithmetic for blind optimization

The operational adversary leaves four real counts: completed raw jobs `v`,
optimized-long jobs `ell`, and the untouched suffix.  This file proves the
exact decomposition and the uniform linear remainder used by the two lower
branches of the deterministic curve.
-/

namespace SchedulingPaper
namespace BlindOptimization

noncomputable section

def stoppingAlgorithmCost (u n v ell : ℝ) : ℝ :=
  let x := n - v - ell
  u * (v * n - v * (v - 1) / 2) +
    (u + 1) * (ell * (n - v) - ell * (ell - 1) / 2) +
    x * (x + 1) / 2

def stoppingOfflineCost (u n ell : ℝ) : ℝ :=
  n * (n + 1) / 2 + (u - 1) * ell * (ell + 1) / 2

theorem stoppingCost_exact_decomposition
    {u R n v ell : ℝ} (hn : 0 < n) (hremaining : 0 < n - v) :
    let sigma := (n - v) / n
    let y := ell / (n - v)
    2 * (stoppingAlgorithmCost u n v ell -
        R * stoppingOfflineCost u n ell) =
      n ^ 2 * ((u - R) * (1 - sigma ^ 2) +
        sigma ^ 2 * deterministicStoppingPolynomial u R y) +
      ((1 - R) * n + (u - 1) * v +
        (u - R * (u - 1)) * ell) := by
  dsimp
  unfold stoppingAlgorithmCost stoppingOfflineCost deterministicStoppingPolynomial
  field_simp [hn.ne', hremaining.ne']
  ring

theorem stoppingPolynomial_overshoot_lower
    {u R alpha y S : ℝ}
    (hu : 1 < u) (hR0 : 0 ≤ R) (hRu : R ≤ u)
    (hS : 0 < S)
    (ha0 : 0 ≤ alpha) (hy0 : alpha ≤ y)
    (hy1 : y ≤ 1) (ha1 : alpha ≤ 1)
    (hover : y - alpha ≤ 1 / S)
    (hcertificate : 0 ≤ deterministicStoppingPolynomial u R alpha) :
    -(2 * u ^ 2) / S ≤ deterministicStoppingPolynomial u R y := by
  let A := u + R * (u - 1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (by linarith) (mul_nonneg hR0 (by linarith))
  have hAu : A ≤ u ^ 2 := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hRu) (by linarith : 0 ≤ u - 1)]
  have hd0 : 0 ≤ y - alpha := sub_nonneg.mpr hy0
  have hsum : 0 ≤ y + alpha := by linarith
  have hsum2 : y + alpha ≤ 2 := by linarith
  have hAd : A * (y - alpha) ≤ u ^ 2 / S := by
    have hmul := mul_le_mul_of_nonneg_left hover hA0
    have hAS : A / S ≤ u ^ 2 / S := by
      exact div_le_div_of_nonneg_right hAu hS.le
    calc
      A * (y - alpha) ≤ A * (1 / S) := hmul
      _ = A / S := by ring
      _ ≤ u ^ 2 / S := hAS
  have hAds : A * (y - alpha) * (y + alpha) ≤ 2 * u ^ 2 / S := by
    calc
      A * (y - alpha) * (y + alpha) ≤
          (u ^ 2 / S) * (y + alpha) :=
        mul_le_mul_of_nonneg_right hAd hsum
      _ ≤ (u ^ 2 / S) * 2 :=
        mul_le_mul_of_nonneg_left hsum2 (div_nonneg (sq_nonneg u) hS.le)
      _ = 2 * u ^ 2 / S := by ring
  have hdiff :
      deterministicStoppingPolynomial u R y =
        deterministicStoppingPolynomial u R alpha +
          2 * u * (y - alpha) - A * (y - alpha) * (y + alpha) := by
    unfold deterministicStoppingPolynomial
    dsimp [A]
    ring
  have hlinear : 0 ≤ 2 * u * (y - alpha) := by positivity
  calc
    -(2 * u ^ 2) / S ≤ -A * (y - alpha) * (y + alpha) := by
      have hneg := neg_le_neg hAds
      convert hneg using 1 <;> ring
    _ ≤ deterministicStoppingPolynomial u R y := by
      rw [hdiff]
      linarith

/-- Quantitative hidden-stopping lemma.  It is stated directly for the
crossing counts supplied by the operational replay: the exact algorithm and
offline formulas lose only `O_u(n)` from a nonnegative scalar certificate. -/
theorem stoppingCost_competitive_of_crossing
    {u R n v ell alpha : ℝ}
    (hu : 1 < u) (hR0 : 0 ≤ R) (hRu : R ≤ u)
    (hn : 0 < n) (hv0 : 0 ≤ v) (hell0 : 0 ≤ ell)
    (hvell : v + ell ≤ n) (hremaining : 0 < n - v)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hyAlpha : alpha ≤ ell / (n - v))
    (hyOne : ell / (n - v) ≤ 1)
    (hyOvershoot : ell / (n - v) - alpha ≤ 1 / (n - v))
    (hcertificate : 0 ≤ deterministicStoppingPolynomial u R alpha) :
    stoppingAlgorithmCost u n v ell ≥
      R * stoppingOfflineCost u n ell - (2 * u ^ 2 + u) * n := by
  let S := n - v
  let sigma := S / n
  let y := ell / S
  have hS : 0 < S := hremaining
  have hpoly : -(2 * u ^ 2) / S ≤
      deterministicStoppingPolynomial u R y := by
    exact stoppingPolynomial_overshoot_lower hu hR0 hRu hS ha0
      hyAlpha hyOne ha1 hyOvershoot hcertificate
  have hSle : S ≤ n := by dsimp [S]; linarith
  have hsigma0 : 0 ≤ sigma := div_nonneg hS.le hn.le
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma]
    exact (div_le_one hn).2 hSle
  have hscale :
      n ^ 2 * sigma ^ 2 * (-(2 * u ^ 2) / S) =
        -(2 * u ^ 2) * S := by
    dsimp [sigma]
    field_simp [hn.ne', hS.ne']
  have hpolyScaled :
      -(2 * u ^ 2) * n ≤
        n ^ 2 * sigma ^ 2 * deterministicStoppingPolynomial u R y := by
    have hmul := mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg (sq_nonneg n) (sq_nonneg sigma))
    rw [hscale] at hmul
    have hcoef : 0 ≤ 2 * u ^ 2 := by positivity
    have hSn := mul_le_mul_of_nonneg_left hSle hcoef
    nlinarith
  have hraw : 0 ≤ (u - R) * (1 - sigma ^ 2) := by
    exact mul_nonneg (sub_nonneg.mpr hRu)
      (by nlinarith [sq_nonneg sigma, hsigma1])
  have hleading :
      -(2 * u ^ 2) * n ≤
        n ^ 2 * ((u - R) * (1 - sigma ^ 2) +
          sigma ^ 2 * deterministicStoppingPolynomial u R y) := by
    have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
    nlinarith [mul_nonneg hn2 hraw]
  have hdiag :
      -(u ^ 2 + u) * n ≤
        (1 - R) * n + (u - 1) * v +
          (u - R * (u - 1)) * ell := by
    have helln : ell ≤ n := by linarith
    have hfirst : (1 - u) * n ≤ (1 - R) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hn.le
    have hmiddle : 0 ≤ (u - 1) * v := mul_nonneg (by linarith) hv0
    have hcoef : -(u ^ 2) ≤ u - R * (u - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hRu) (by linarith : 0 ≤ u - 1)]
    have hlast : -(u ^ 2) * n ≤
        (u - R * (u - 1)) * ell := by
      have hcoefEll := mul_le_mul_of_nonneg_right hcoef hell0
      have hsquare := mul_le_mul_of_nonneg_left helln (sq_nonneg u)
      nlinarith
    nlinarith
  have hexact := stoppingCost_exact_decomposition
    (u := u) (R := R) (n := n) (v := v) (ell := ell) hn hremaining
  dsimp [S, sigma, y] at hleading
  dsimp only at hexact
  nlinarith

/-- Raw-branch certificate used for `1<u≤2`. -/
theorem raw_branch_crossing_lower
    {u n v ell : ℝ} (hu1 : 1 < u) (hu2 : u ≤ 2)
    (hn : 0 < n) (hv0 : 0 ≤ v) (hell0 : 0 ≤ ell)
    (hvell : v + ell ≤ n) (hremaining : 0 < n - v)
    (hyAlpha : 1 / u ≤ ell / (n - v))
    (hyOne : ell / (n - v) ≤ 1)
    (hyOvershoot : ell / (n - v) - 1 / u ≤ 1 / (n - v)) :
    stoppingAlgorithmCost u n v ell ≥
      u * stoppingOfflineCost u n ell - (2 * u ^ 2 + u) * n := by
  apply stoppingCost_competitive_of_crossing (alpha := 1 / u)
    hu1 (by linarith) le_rfl hn
    hv0 hell0 hvell hremaining
  · positivity
  · rw [div_le_one (by linarith : 0 < u)]; linarith
  · exact hyAlpha
  · exact hyOne
  · exact hyOvershoot
  · rw [deterministicStoppingPolynomial_raw hu1]
    linarith

/-- OptimizeAll-branch certificate used for `u≥2`. -/
theorem optimizeAll_branch_crossing_lower
    {u n v ell : ℝ} (hu : 2 ≤ u)
    (hn : 0 < n) (hv0 : 0 ≤ v) (hell0 : 0 ≤ ell)
    (hvell : v + ell ≤ n) (hremaining : 0 < n - v)
    (hyAlpha :
      let R := deterministicOptimizeAllRatio u
      u / (u + R * (u - 1)) ≤ ell / (n - v))
    (hyOne : ell / (n - v) ≤ 1)
    (hyOvershoot :
      let R := deterministicOptimizeAllRatio u
      ell / (n - v) - u / (u + R * (u - 1)) ≤ 1 / (n - v)) :
    let R := deterministicOptimizeAllRatio u
    stoppingAlgorithmCost u n v ell ≥
      R * stoppingOfflineCost u n ell - (2 * u ^ 2 + u) * n := by
  dsimp only
  let R := deterministicOptimizeAllRatio u
  let alpha := u / (u + R * (u - 1))
  have hR0 : 0 ≤ R := (deterministicOptimizeAllRatio_pos hu).le
  have hRu : R ≤ u := deterministicOptimizeAllRatio_le_u hu
  have hden : 0 < u + R * (u - 1) := by
    exact add_pos_of_pos_of_nonneg (by linarith)
      (mul_nonneg hR0 (by linarith))
  have ha0 : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (by linarith) hden.le
  have ha1 : alpha ≤ 1 := by
    dsimp [alpha]
    rw [div_le_one hden]
    exact le_add_of_nonneg_right (mul_nonneg hR0 (by linarith))
  apply stoppingCost_competitive_of_crossing (alpha := alpha)
    (by linarith) hR0 hRu hn
    hv0 hell0 hvell hremaining
  · exact ha0
  · exact ha1
  · simpa [alpha, R] using hyAlpha
  · exact hyOne
  · simpa [alpha, R] using hyOvershoot
  · have hzero := deterministicStoppingPolynomial_optimizeAll hu
    simpa [R, alpha] using le_of_eq hzero.symm

end

end BlindOptimization
end SchedulingPaper
