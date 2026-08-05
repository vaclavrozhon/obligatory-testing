import SchedulingPaper.AlgebraicBranch
import SchedulingPaper.MixedCurve

/-!
# The exact six-branch finite-cap curve

This file assembles the scalar branches proved in `AlgebraicBranch` and
`MixedCurve` into the exact curve from the theorem statement.  The
definition is total on `ℝ`; on the theorem's natural domain `u > 0` it has
the six advertised branches.
-/

namespace SchedulingPaper

noncomputable section

open Set

/-- The fourth branch of the exact curve. -/
def reciprocalBranch (u : ℝ) : ℝ :=
  1 + 1 / Real.sqrt (u - 1)

theorem goldenRatio_gt_three_halves :
    (3 : ℝ) / 2 < goldenRatio := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  unfold goldenRatio
  nlinarith

theorem goldenRatio_gt_eight_fifths :
    (8 : ℝ) / 5 < goldenRatio := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  unfold goldenRatio
  nlinarith

theorem uDiamond_lt_two : uDiamond < 2 := by
  by_contra h
  have hu : 2 ≤ uDiamond := le_of_not_gt h
  have hprod :
      2 ≤ uDiamond * (uDiamond - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu)
      (sub_nonneg.mpr (by linarith : 1 ≤ uDiamond))]
  rw [uDiamond_mul_sub_one] at hprod
  linarith [goldenRatio_lt_two]

theorem uDiamond_lt_uZero : uDiamond < uZero := by
  linarith [uDiamond_lt_two, uZero_bounds.1]

theorem sZero_lt_five_halves :
    sZero < (5 : ℝ) / 2 := by
  have hvalue : 0 < sZeroPolynomial ((5 : ℝ) / 2) := by
    norm_num [sZeroPolynomial]
  by_contra h
  have hle : (5 : ℝ) / 2 ≤ sZero := le_of_not_gt h
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, show sZeroPolynomial sZero = 0 by
      exact sub_eq_zero.mpr sZero_spec.2.2] at hvalue
    linarith
  · have hmono :=
      sZeroPolynomial_strictMono_above_two
        (by norm_num : (2 : ℝ) < 5 / 2) hlt
    rw [show sZeroPolynomial sZero = 0 by
      exact sub_eq_zero.mpr sZero_spec.2.2] at hmono
    linarith

theorem uZero_lt_goldenRatio_add_two :
    uZero < goldenRatio + 2 := by
  unfold uZero
  linarith [sZero_lt_five_halves, goldenRatio_gt_three_halves]

theorem reciprocalBranch_uZero :
    reciprocalBranch uZero = 1 + 1 / Real.sqrt sZero := by
  simp [reciprocalBranch, uZero]

theorem sqrt_goldenRatio_sq :
    Real.sqrt (goldenRatio ^ 2) = goldenRatio := by
  rw [Real.sqrt_sq_eq_abs, abs_of_pos goldenRatio_pos]

theorem reciprocalBranch_goldenRatio_add_two :
    reciprocalBranch (goldenRatio + 2) = goldenRatio := by
  have harg :
      goldenRatio + 2 - 1 = goldenRatio ^ 2 := by
    nlinarith [goldenRatio_sq]
  unfold reciprocalBranch
  rw [harg, sqrt_goldenRatio_sq, mixedRatio_join_binary]

/-- The exact six-branch curve.  At a shared endpoint the earlier branch is
chosen; the join theorems below show that this convention is immaterial. -/
def exactCurve (u : ℝ) : ℝ :=
  if _h₁ : u ≤ 1 then
    1
  else if _h₂ : u ≤ uDiamond then
    u
  else if _h₃ : u ≤ uZero then
    rhoI u
  else if h₄ : u ≤ goldenRatio + 2 then
    reciprocalBranch u
  else if h₅ : u ≤ zStar then
    mixedFiniteCurve
      ⟨u, ⟨(lt_of_not_ge h₄).le, h₅⟩⟩
  else
    RStar

theorem exactCurve_eq_one {u : ℝ} (hu : u ≤ 1) :
    exactCurve u = 1 := by
  simp [exactCurve, hu]

theorem exactCurve_eq_self {u : ℝ}
    (hu₁ : 1 < u) (hu₂ : u ≤ uDiamond) :
    exactCurve u = u := by
  simp [exactCurve, not_le.mpr hu₁, hu₂]

theorem exactCurve_eq_rhoI {u : ℝ}
    (hu₁ : uDiamond < u) (hu₂ : u ≤ uZero) :
    exactCurve u = rhoI u := by
  have h1 : ¬u ≤ 1 := not_le.mpr (uDiamond_gt_one.trans hu₁)
  have hd : ¬u ≤ uDiamond := not_le.mpr hu₁
  simp [exactCurve, h1, hd, hu₂]

theorem exactCurve_eq_reciprocal {u : ℝ}
    (hu₁ : uZero < u) (hu₂ : u ≤ goldenRatio + 2) :
    exactCurve u = reciprocalBranch u := by
  have h1 : ¬u ≤ 1 := not_le.mpr
    (lt_trans uDiamond_gt_one (uDiamond_lt_uZero.trans hu₁))
  have hd : ¬u ≤ uDiamond := not_le.mpr
    (uDiamond_lt_uZero.trans hu₁)
  have hz : ¬u ≤ uZero := not_le.mpr hu₁
  simp [exactCurve, h1, hd, hz, hu₂]

theorem exactCurve_eq_mixed {u : ℝ}
    (hu₁ : goldenRatio + 2 < u) (hu₂ : u ≤ zStar) :
    exactCurve u =
      mixedFiniteCurve ⟨u, ⟨hu₁.le, hu₂⟩⟩ := by
  have h1 : ¬u ≤ 1 := not_le.mpr
    (uDiamond_gt_one.trans
      (uDiamond_lt_uZero.trans
        (uZero_lt_goldenRatio_add_two.trans hu₁)))
  have hd : ¬u ≤ uDiamond := not_le.mpr
    (uDiamond_lt_uZero.trans
      (uZero_lt_goldenRatio_add_two.trans hu₁))
  have hz : ¬u ≤ uZero := not_le.mpr
    (uZero_lt_goldenRatio_add_two.trans hu₁)
  have hp : ¬u ≤ goldenRatio + 2 := not_le.mpr hu₁
  rw [exactCurve, dif_neg h1, dif_neg hd, dif_neg hz,
    dif_neg hp, dif_pos hu₂]

theorem exactCurve_eq_plateau {u : ℝ} (hu : zStar < u) :
    exactCurve u = RStar := by
  have hp : goldenRatio + 2 < u :=
    goldenRatio_add_two_lt_zStar.trans hu
  have h1 : ¬u ≤ 1 := not_le.mpr
    (uDiamond_gt_one.trans
      (uDiamond_lt_uZero.trans
        (uZero_lt_goldenRatio_add_two.trans hp)))
  have hd : ¬u ≤ uDiamond := not_le.mpr
    (uDiamond_lt_uZero.trans
      (uZero_lt_goldenRatio_add_two.trans hp))
  have hz : ¬u ≤ uZero := not_le.mpr
    (uZero_lt_goldenRatio_add_two.trans hp)
  have hphi : ¬u ≤ goldenRatio + 2 := not_le.mpr hp
  have hstar : ¬u ≤ zStar := not_le.mpr hu
  simp [exactCurve, h1, hd, hz, hphi, hstar]

/-! ## Exact endpoint values and joins -/

theorem exactCurve_one :
    exactCurve 1 = 1 :=
  exactCurve_eq_one le_rfl

theorem exactCurve_uDiamond :
    exactCurve uDiamond = uDiamond :=
  exactCurve_eq_self uDiamond_gt_one le_rfl

theorem exactCurve_uZero :
    exactCurve uZero = 1 + 1 / Real.sqrt sZero := by
  rw [exactCurve_eq_rhoI uDiamond_lt_uZero le_rfl,
    rhoI_at_uZero]

theorem exactCurve_goldenRatio_add_two :
    exactCurve (goldenRatio + 2) = goldenRatio := by
  rw [exactCurve_eq_reciprocal uZero_lt_goldenRatio_add_two le_rfl,
    reciprocalBranch_goldenRatio_add_two]

theorem exactCurve_zStar :
    exactCurve zStar = RStar := by
  calc
    exactCurve zStar =
        mixedFiniteCurve
          ⟨zStar, ⟨goldenRatio_add_two_lt_zStar.le, le_rfl⟩⟩ :=
      exactCurve_eq_mixed goldenRatio_add_two_lt_zStar le_rfl
    _ = mixedFiniteCurve mixedUpperUpperEndpoint := by
      congr 1
    _ = RStar := mixedFiniteCurve_upperEndpoint

/-- The two formulas meeting at `u=1` have the same value. -/
theorem exactCurve_join_one :
    (1 : ℝ) = (1 : ℝ) := rfl

/-- The identity and algebraic branches meet at `uDiamond`. -/
theorem exactCurve_join_uDiamond :
    uDiamond = rhoI uDiamond :=
  rhoI_at_uDiamond.symm

/-- The algebraic and reciprocal branches meet at `uZero`. -/
theorem exactCurve_join_uZero :
    rhoI uZero = reciprocalBranch uZero := by
  rw [rhoI_at_uZero, reciprocalBranch_uZero]

/-- The reciprocal and mixed branches meet at `goldenRatio+2`. -/
theorem exactCurve_join_goldenRatio_add_two :
    reciprocalBranch (goldenRatio + 2) =
      mixedFiniteCurve mixedUpperLowerEndpoint := by
  rw [reciprocalBranch_goldenRatio_add_two,
    mixedFiniteCurve_lowerEndpoint]

/-- The mixed branch meets the plateau at `zStar`. -/
theorem exactCurve_join_zStar :
    mixedFiniteCurve mixedUpperUpperEndpoint = RStar :=
  mixedFiniteCurve_upperEndpoint

/-- First closed branch, in the convention of the theorem statement. -/
theorem exactCurve_eq_one_of_mem {u : ℝ}
    (hu : u ∈ Ioc 0 1) :
    exactCurve u = 1 :=
  exactCurve_eq_one hu.2

/-- Second closed branch, including both joins. -/
theorem exactCurve_eq_self_of_mem {u : ℝ}
    (hu : u ∈ Icc 1 uDiamond) :
    exactCurve u = u := by
  rcases hu with ⟨hu1, huD⟩
  rcases eq_or_lt_of_le hu1 with rfl | hlt
  · exact exactCurve_one
  · exact exactCurve_eq_self hlt huD

/-- Third closed branch, including both joins. -/
theorem exactCurve_eq_rhoI_of_mem {u : ℝ}
    (hu : u ∈ Icc uDiamond uZero) :
    exactCurve u = rhoI u := by
  rcases hu with ⟨huD, hu0⟩
  rcases eq_or_lt_of_le huD with rfl | hlt
  · rw [exactCurve_uDiamond, rhoI_at_uDiamond]
  · exact exactCurve_eq_rhoI hlt hu0

/-- Fourth closed branch, including both joins. -/
theorem exactCurve_eq_reciprocal_of_mem {u : ℝ}
    (hu : u ∈ Icc uZero (goldenRatio + 2)) :
    exactCurve u = reciprocalBranch u := by
  rcases hu with ⟨hu0, huφ⟩
  rcases eq_or_lt_of_le hu0 with rfl | hlt
  · rw [exactCurve_uZero, reciprocalBranch_uZero]
  · exact exactCurve_eq_reciprocal hlt huφ

/-- Fifth closed branch, including both joins. -/
theorem exactCurve_eq_mixed_of_mem {u : ℝ}
    (hu : u ∈ Icc (goldenRatio + 2) zStar) :
    exactCurve u = mixedFiniteCurve ⟨u, hu⟩ := by
  rcases hu with ⟨huφ, huS⟩
  rcases eq_or_lt_of_le huφ with rfl | hlt
  · calc
      exactCurve (goldenRatio + 2) = goldenRatio :=
        exactCurve_goldenRatio_add_two
      _ = mixedFiniteCurve mixedUpperLowerEndpoint :=
        mixedFiniteCurve_lowerEndpoint.symm
      _ = mixedFiniteCurve
          ⟨goldenRatio + 2, ⟨le_rfl,
            goldenRatio_add_two_lt_zStar.le⟩⟩ := by
        congr 1
  · exact exactCurve_eq_mixed hlt huS

/-- The sixth branch is a genuine plateau, including its left endpoint. -/
theorem exactCurve_plateau {u : ℝ} (hu : zStar ≤ u) :
    exactCurve u = RStar := by
  rcases eq_or_lt_of_le hu with rfl | hlt
  · exact exactCurve_zStar
  · exact exactCurve_eq_plateau hlt

/-! ## The global maximum -/

theorem five_sixths_lt_uDiamond_sub_one :
    (5 : ℝ) / 6 < uDiamond - 1 := by
  let d : ℝ := uDiamond - 1
  have hdpos : 0 < d := by
    dsimp [d]
    linarith [uDiamond_gt_one]
  by_contra h
  have hdle : d ≤ (5 : ℝ) / 6 := le_of_not_gt h
  have hfactor :
      0 ≤ ((5 : ℝ) / 6 - d) * (d + 11 / 6) :=
    mul_nonneg (sub_nonneg.mpr hdle) (by positivity)
  have hprod : (d + 1) * d = goldenRatio := by
    dsimp [d]
    convert uDiamond_mul_sub_one using 1
    all_goals ring
  nlinarith [goldenRatio_gt_eight_fifths]

theorem seven_fourths_lt_uDiamond :
    (7 : ℝ) / 4 < uDiamond := by
  linarith [five_sixths_lt_uDiamond_sub_one]

theorem goldenRatio_lt_seven_fourths :
    goldenRatio < (7 : ℝ) / 4 := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  unfold goldenRatio
  nlinarith

theorem goldenRatio_lt_uDiamond :
    goldenRatio < uDiamond :=
  goldenRatio_lt_seven_fourths.trans seven_fourths_lt_uDiamond

/-- A polynomial comparison at the left endpoint bounds the entire
algebraic branch by its join value.  This avoids assuming a separate
monotonicity theorem for `rhoI`. -/
theorem rhoI_le_uDiamond_of_le {u : ℝ} (hu : uDiamond ≤ u) :
    rhoI u ≤ uDiamond := by
  rcases eq_or_lt_of_le hu with rfl | huD
  · exact rhoI_at_uDiamond.le
  let d : ℝ := uDiamond - 1
  let s : ℝ := u - 1
  have hdpos : 0 < d := by
    dsimp [d]
    linarith [uDiamond_gt_one]
  have hspos : 0 < s := by
    dsimp [s]
    linarith [uDiamond_gt_one]
  have hds : d < s := by
    dsimp [d, s]
    linarith
  have hdSq : (2 : ℝ) / 3 < d ^ 2 := by
    have hd56 := five_sixths_lt_uDiamond_sub_one
    have hmul :
        0 < (d - 5 / 6) * (d + 5 / 6) := by
      apply mul_pos
      · simpa [d] using sub_pos.mpr hd56
      · positivity
    nlinarith
  have hTd : rhoPolynomial d uDiamond = 0 := by
    have hroot := (rhoI_spec uDiamond_gt_one).2
    rw [rhoI_at_uDiamond] at hroot
    simpa [d] using hroot
  let B : ℝ :=
    d ^ 3 + d ^ 2 * s + 2 * d ^ 2 + d * s ^ 2 +
      d * s - 2 * s - 2
  have hdsMul : d ^ 2 ≤ d * s := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hds.le hdpos.le
  have hinner :
      0 < 2 * d ^ 2 + d * s + d - 2 := by
    nlinarith
  have hbase :
      0 < (d + 1) * (3 * d ^ 2 - 2) := by
    exact mul_pos (by positivity) (by nlinarith)
  have hBidentity :
      B = (d + 1) * (3 * d ^ 2 - 2) +
        (s - d) * (2 * d ^ 2 + d * s + d - 2) := by
    dsimp [B]
    ring
  have hBpos : 0 < B := by
    rw [hBidentity]
    exact add_pos_of_pos_of_nonneg hbase
      (mul_nonneg (sub_nonneg.mpr hds.le) hinner.le)
  have hfactor :
      rhoPolynomial s uDiamond - rhoPolynomial d uDiamond =
        (s - d) * B := by
    dsimp [B, s, d]
    unfold rhoPolynomial
    ring
  have hTnonneg : 0 ≤ rhoPolynomial s uDiamond := by
    have hprod : 0 ≤ (s - d) * B :=
      mul_nonneg (sub_nonneg.mpr hds.le) hBpos.le
    linarith
  have hus : 1 < u := uDiamond_gt_one.trans huD
  have hroot := rhoI_spec hus
  by_contra hle
  have hlt : uDiamond < rhoI u := lt_of_not_ge hle
  have hmono :=
    rhoPolynomial_strictMono_nonneg hspos
      (by linarith [uDiamond_gt_one] : 0 ≤ uDiamond) hlt
  change rhoPolynomial s uDiamond < rhoPolynomial s (rhoI u) at hmono
  rw [hroot.2] at hmono
  linarith

theorem reciprocalBranch_lt_uDiamond {u : ℝ} (hu : uZero < u) :
    reciprocalBranch u < uDiamond := by
  have hs : 2 < u - 1 := by
    linarith [uZero_bounds.1]
  have hsqrt : 0 < Real.sqrt (u - 1) :=
    Real.sqrt_pos.2 (by linarith)
  have hsqrtSq :
      (Real.sqrt (u - 1)) ^ 2 = u - 1 :=
    Real.sq_sqrt (by linarith)
  have hsqrtLower : (4 : ℝ) / 3 < Real.sqrt (u - 1) := by
    nlinarith
  have hinv :
      1 / Real.sqrt (u - 1) < (3 : ℝ) / 4 := by
    rw [div_lt_iff₀ hsqrt]
    nlinarith
  unfold reciprocalBranch
  linarith [seven_fourths_lt_uDiamond]

theorem mixedFiniteCurve_lt_uDiamond {u : ℝ}
    (hu : u ∈ Ioc (goldenRatio + 2) zStar) :
    mixedFiniteCurve ⟨u, ⟨hu.1.le, hu.2⟩⟩ < uDiamond := by
  let us : MixedUpperDomain := ⟨u, ⟨hu.1.le, hu.2⟩⟩
  have hparam : mixedUpperLowerEndpoint < us := by
    exact hu.1
  have hcurve := mixedFiniteCurve_strictAnti hparam
  rw [mixedFiniteCurve_lowerEndpoint] at hcurve
  exact hcurve.trans goldenRatio_lt_uDiamond

theorem RStar_lt_goldenRatio : RStar < goldenRatio := by
  have hparam :
      mixedUpperLowerEndpoint < mixedUpperUpperEndpoint :=
    goldenRatio_add_two_lt_zStar
  have hcurve := mixedFiniteCurve_strictAnti hparam
  rw [mixedFiniteCurve_lowerEndpoint,
    mixedFiniteCurve_upperEndpoint] at hcurve
  exact hcurve

/-- `uDiamond` bounds all six branches. -/
theorem exactCurve_le_uDiamond (u : ℝ) :
    exactCurve u ≤ uDiamond := by
  by_cases h1 : u ≤ 1
  · rw [exactCurve_eq_one h1]
    exact uDiamond_gt_one.le
  by_cases hD : u ≤ uDiamond
  · rw [exactCurve_eq_self (lt_of_not_ge h1) hD]
    exact hD
  by_cases h0 : u ≤ uZero
  · rw [exactCurve_eq_rhoI (lt_of_not_ge hD) h0]
    exact rhoI_le_uDiamond_of_le (le_of_lt (lt_of_not_ge hD))
  by_cases hφ : u ≤ goldenRatio + 2
  · rw [exactCurve_eq_reciprocal (lt_of_not_ge h0) hφ]
    exact (reciprocalBranch_lt_uDiamond (lt_of_not_ge h0)).le
  by_cases hS : u ≤ zStar
  · rw [exactCurve_eq_mixed (lt_of_not_ge hφ) hS]
    exact (mixedFiniteCurve_lt_uDiamond
      ⟨lt_of_not_ge hφ, hS⟩).le
  · rw [exactCurve_eq_plateau (lt_of_not_ge hS)]
    exact (RStar_lt_goldenRatio.trans goldenRatio_lt_uDiamond).le

/-- The exact curve has global maximum `uDiamond` on its natural domain. -/
theorem exactCurve_globalMaximum :
    IsGreatest (exactCurve '' Ioi 0) uDiamond := by
  constructor
  · exact ⟨uDiamond, by
      exact ⟨uDiamond_gt_one.trans' zero_lt_one,
        exactCurve_uDiamond⟩⟩
  · rintro _ ⟨u, _hu, rfl⟩
    exact exactCurve_le_uDiamond u

/-- Paper notation for the exact finite common-upper curve. -/
abbrev V (u : ℝ) : ℝ := exactCurve u

theorem V_one : V 1 = 1 := exactCurve_one

theorem V_uDiamond : V uDiamond = uDiamond :=
  exactCurve_uDiamond

theorem V_uZero :
    V uZero = 1 + 1 / Real.sqrt sZero :=
  exactCurve_uZero

theorem V_goldenRatio_add_two :
    V (goldenRatio + 2) = goldenRatio :=
  exactCurve_goldenRatio_add_two

theorem V_zStar : V zStar = RStar :=
  exactCurve_zStar

theorem V_plateau {u : ℝ} (hu : zStar ≤ u) :
    V u = RStar :=
  exactCurve_plateau hu

theorem V_globalMaximum :
    IsGreatest (V '' Ioi 0) uDiamond :=
  exactCurve_globalMaximum

/-! ## Continuity of the two implicit branches -/

/-- The positive quadratic-formula expression for the algebraic root. -/
def rhoExplicit (u : ℝ) : ℝ :=
  let s := u - 1
  let B := s ^ 3 + s ^ 2 + 1
  let C := (s ^ 2 + s + 1) * (s + 2)
  (Real.sqrt (B ^ 2 + 4 * s * C) - B) / (2 * s)

theorem rhoExplicit_spec {u : ℝ} (hu : 1 < u) :
    0 < rhoExplicit u ∧
      rhoPolynomial (u - 1) (rhoExplicit u) = 0 := by
  let s : ℝ := u - 1
  let B : ℝ := s ^ 3 + s ^ 2 + 1
  let C : ℝ := (s ^ 2 + s + 1) * (s + 2)
  let D : ℝ := B ^ 2 + 4 * s * C
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    have hquad : 0 < s ^ 2 + s + 1 := by
      nlinarith [sq_nonneg (s + 1 / 2)]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hsqrtSq : (Real.sqrt D) ^ 2 = D :=
    Real.sq_sqrt hD
  have hsqrtNonneg : 0 ≤ Real.sqrt D :=
    Real.sqrt_nonneg _
  have hsqrtGt : B < Real.sqrt D := by
    dsimp [D] at hsqrtSq
    nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hs) hC]
  have hform :
      rhoExplicit u = (Real.sqrt D - B) / (2 * s) := by
    simp only [rhoExplicit]
    dsimp [s, B, C, D]
  constructor
  · rw [hform]
    exact div_pos (sub_pos.mpr hsqrtGt) (mul_pos (by norm_num) hs)
  · rw [hform]
    change
      s * ((Real.sqrt D - B) / (2 * s)) ^ 2 +
        B * ((Real.sqrt D - B) / (2 * s)) - C = 0
    field_simp [hs.ne']
    dsimp [D] at hsqrtSq
    nlinarith

theorem rhoI_eq_rhoExplicit {u : ℝ} (hu : 1 < u) :
    rhoI u = rhoExplicit u :=
  rhoI_eq_of_root hu (rhoExplicit_spec hu).1
    (rhoExplicit_spec hu).2

theorem rhoExplicit_continuousOn :
    ContinuousOn rhoExplicit (Ioi 1) := by
  intro u hu
  have hden : 2 * (u - 1) ≠ 0 := by
    have : 0 < u - 1 := sub_pos.mpr hu
    positivity
  unfold rhoExplicit
  fun_prop

theorem rhoI_continuousOn :
    ContinuousOn rhoI (Ioi 1) := by
  exact rhoExplicit_continuousOn.congr fun u hu =>
    rhoI_eq_rhoExplicit hu

theorem rhoI_continuousOn_algebraicInterval :
    ContinuousOn rhoI (Icc uDiamond uZero) :=
  rhoI_continuousOn.mono fun _ hu =>
    uDiamond_gt_one.trans_le hu.1

theorem mixedUpperCurve_mem (c : MixedRatioDomain) :
    mixedUpperCurve c ∈ Icc (goldenRatio + 2) zStar := by
  constructor
  · rw [← mixedUpperCurve_upper]
    exact mixedUpperCurve_strictAnti.antitone c.property.2
  · rw [← mixedUpperCurve_lower]
    exact mixedUpperCurve_strictAnti.antitone c.property.1

theorem mixedRatioAtUpper_surjective :
    Function.Surjective mixedRatioAtUpper := by
  intro c
  let u : MixedUpperDomain :=
    ⟨mixedUpperCurve c, mixedUpperCurve_mem c⟩
  refine ⟨u, ?_⟩
  apply mixedUpperCurve_strictAnti.injective
  exact mixedRatioAtUpper_equation u

def mixedRatioAtUpperDual
    (u : MixedUpperDomain) : MixedRatioDomainᵒᵈ :=
  OrderDual.toDual (mixedRatioAtUpper u)

theorem mixedRatioAtUpperDual_strictMono :
    StrictMono mixedRatioAtUpperDual :=
  mixedRatioAtUpper_strictAnti.dual_right

theorem mixedRatioAtUpperDual_surjective :
    Function.Surjective mixedRatioAtUpperDual := by
  intro c
  obtain ⟨u, hu⟩ :=
    mixedRatioAtUpper_surjective c.ofDual
  exact ⟨u, congrArg OrderDual.toDual hu⟩

noncomputable def mixedRatioAtUpperOrderIso :
    MixedUpperDomain ≃o MixedRatioDomainᵒᵈ :=
  mixedRatioAtUpperDual_strictMono.orderIsoOfSurjective
    mixedRatioAtUpperDual mixedRatioAtUpperDual_surjective

@[simp]
theorem mixedRatioAtUpperOrderIso_apply (u : MixedUpperDomain) :
    mixedRatioAtUpperOrderIso u =
      OrderDual.toDual (mixedRatioAtUpper u) := rfl

theorem mixedRatioAtUpperDual_continuous :
    Continuous mixedRatioAtUpperDual := by
  change Continuous (mixedRatioAtUpperOrderIso :
    MixedUpperDomain → MixedRatioDomainᵒᵈ)
  exact mixedRatioAtUpperOrderIso.continuous

theorem mixedRatioAtUpper_continuous :
    Continuous mixedRatioAtUpper := by
  simpa [mixedRatioAtUpperDual] using
    continuous_ofDual.comp mixedRatioAtUpperDual_continuous

theorem mixedFiniteCurve_continuous :
    Continuous mixedFiniteCurve := by
  unfold mixedFiniteCurve
  exact continuous_const.add
    (continuous_subtype_val.comp mixedRatioAtUpper_continuous)

theorem reciprocalBranch_continuousOn :
    ContinuousOn reciprocalBranch (Ioi 1) := by
  intro u hu
  have hsqrt : Real.sqrt (u - 1) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr hu)).ne'
  unfold reciprocalBranch
  fun_prop

theorem exactCurve_continuousOn_first :
    ContinuousOn exactCurve (Iic 1) := by
  exact continuousOn_const.congr fun u hu =>
    exactCurve_eq_one hu

theorem exactCurve_continuousOn_second :
    ContinuousOn exactCurve (Icc 1 uDiamond) := by
  exact continuousOn_id.congr fun u hu =>
    exactCurve_eq_self_of_mem hu

theorem exactCurve_continuousOn_third :
    ContinuousOn exactCurve (Icc uDiamond uZero) := by
  exact rhoI_continuousOn_algebraicInterval.congr fun u hu =>
    exactCurve_eq_rhoI_of_mem hu

theorem exactCurve_continuousOn_fourth :
    ContinuousOn exactCurve
      (Icc uZero (goldenRatio + 2)) := by
  have hrec :
      ContinuousOn reciprocalBranch
        (Icc uZero (goldenRatio + 2)) :=
    reciprocalBranch_continuousOn.mono fun _ hu =>
      (by linarith [uZero_bounds.1] : 1 < uZero).trans_le hu.1
  exact hrec.congr fun u hu =>
    exactCurve_eq_reciprocal_of_mem hu

theorem exactCurve_continuousOn_fifth :
    ContinuousOn exactCurve
      (Icc (goldenRatio + 2) zStar) := by
  rw [continuousOn_iff_continuous_restrict]
  exact mixedFiniteCurve_continuous.congr fun u =>
    (exactCurve_eq_mixed_of_mem u.property).symm

theorem exactCurve_continuousOn_sixth :
    ContinuousOn exactCurve (Ici zStar) := by
  exact continuousOn_const.congr fun u hu =>
    exactCurve_plateau hu

/-- The six continuous pieces glue at their verified join values.  Since the
totalization is constant to the left of the natural domain, the result is
actually continuous on all of `ℝ`. -/
theorem exactCurve_continuous :
    Continuous exactCurve := by
  have h₂ : ContinuousOn exactCurve (Iic uDiamond) := by
    rw [← Iic_union_Icc_eq_Iic uDiamond_gt_one.le]
    exact exactCurve_continuousOn_first.union_of_isClosed
      exactCurve_continuousOn_second isClosed_Iic isClosed_Icc
  have h₃ : ContinuousOn exactCurve (Iic uZero) := by
    rw [← Iic_union_Icc_eq_Iic uDiamond_lt_uZero.le]
    exact h₂.union_of_isClosed exactCurve_continuousOn_third
      isClosed_Iic isClosed_Icc
  have h₄ :
      ContinuousOn exactCurve (Iic (goldenRatio + 2)) := by
    rw [← Iic_union_Icc_eq_Iic
      uZero_lt_goldenRatio_add_two.le]
    exact h₃.union_of_isClosed exactCurve_continuousOn_fourth
      isClosed_Iic isClosed_Icc
  have h₅ : ContinuousOn exactCurve (Iic zStar) := by
    rw [← Iic_union_Icc_eq_Iic
      goldenRatio_add_two_lt_zStar.le]
    exact h₄.union_of_isClosed exactCurve_continuousOn_fifth
      isClosed_Iic isClosed_Icc
  rw [← continuousOn_univ, ← Iic_union_Ici]
  exact h₅.union_of_isClosed exactCurve_continuousOn_sixth
    isClosed_Iic isClosed_Ici

theorem exactCurve_continuousOn_pos :
    ContinuousOn exactCurve (Ioi 0) :=
  exactCurve_continuous.continuousOn

theorem V_continuous : Continuous V :=
  exactCurve_continuous

theorem V_continuousOn_pos : ContinuousOn V (Ioi 0) :=
  exactCurve_continuousOn_pos

end

end SchedulingPaper
