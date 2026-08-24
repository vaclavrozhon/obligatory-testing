import Mathlib.Tactic

/-!
# Scalar certificates for randomized revealing optimization

The survival-function reduction in the paper leaves two binary families,
`A` and `B`.  This file checks their complete maximization, the unique cubic
transition, the `25/4` plateau transition, and the global maximum.  The key
comparisons are polynomial or completed-square identities; no numerical root
approximation is used.
-/

namespace SchedulingPaper
namespace RevealingOptimization

noncomputable section

def familyA (τ : ℝ) : ℝ := τ ^ 2 / (τ ^ 2 - τ + 1)

def familyB (u τ : ℝ) : ℝ :=
  (τ ^ 2 * u + 2 * τ ^ 2 - 2 * τ * u - τ + u) /
    (τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1)

def boundaryRatio (u : ℝ) : ℝ :=
  u ^ 3 / (u ^ 2 + (u - 1) ^ 3)

def interiorRatio (u : ℝ) : ℝ := 1 + 1 / (2 * (Real.sqrt u - 1))

def transitionPolynomial (u : ℝ) : ℝ :=
  u ^ 3 - 6 * u ^ 2 + 5 * u - 1

theorem familyA_den_pos (τ : ℝ) : 0 < τ ^ 2 - τ + 1 := by
  nlinarith [sq_nonneg (τ - 1 / 2)]

theorem familyB_den_pos {u τ : ℝ} (hu : 0 < u) (hτ : 1 ≤ τ) :
    0 < τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1 := by
  have hsquare : 0 ≤ u * (τ - 1) ^ 2 :=
    mul_nonneg hu.le (sq_nonneg _)
  nlinarith

theorem boundary_den_pos {u : ℝ} (hu : 1 < u) :
    0 < u ^ 2 + (u - 1) ^ 3 := by positivity

theorem familyB_at_u {u : ℝ} (_hu : 1 < u) :
    familyB u u = boundaryRatio u := by
  unfold familyB boundaryRatio
  have hnum :
      u ^ 2 * u + 2 * u ^ 2 - 2 * u * u - u + u = u ^ 3 := by ring
  have hden :
      u ^ 2 * u - 2 * u * u + 2 * u + u - 1 =
        u ^ 2 + (u - 1) ^ 3 := by ring
  rw [hnum, hden]

/-- The first binary family never exceeds the obligatory `4/3` plateau. -/
theorem familyA_le_four_thirds (τ : ℝ) : familyA τ ≤ 4 / 3 := by
  have hden := familyA_den_pos τ
  rw [familyA, div_le_iff₀ hden]
  nlinarith [sq_nonneg (τ - 2)]

theorem familyA_mono_to_two {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    familyA x ≤ familyA y := by
  have hdx := familyA_den_pos x
  have hdy := familyA_den_pos y
  unfold familyA
  rw [div_le_div_iff₀ hdx hdy]
  have hfactor :
      y ^ 2 * (x ^ 2 - x + 1) - x ^ 2 * (y ^ 2 - y + 1) =
        (y - x) * (x + y - x * y) := by ring
  have hfirst : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hsecond : 0 ≤ x + y - x * y := by
    have hx0 : 0 ≤ x := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
    nlinarith
  nlinarith [mul_nonneg hfirst hsecond]

/-! ## The cubic transition -/

theorem transitionPolynomial_neg_of_gt_one_le_four {u : ℝ}
    (hu1 : 1 < u) (hu4 : u ≤ 4) : transitionPolynomial u < 0 := by
  let v := u - 1
  have hv0 : 0 < v := by dsimp [v]; linarith
  have hv3 : v ≤ 3 := by dsimp [v]; linarith
  have hcube : v ^ 3 ≤ 3 * v ^ 2 := by
    have := mul_le_mul_of_nonneg_right hv3 (sq_nonneg v)
    nlinarith
  have hid : transitionPolynomial u = v ^ 3 - 3 * v ^ 2 - 4 * v - 1 := by
    dsimp [v]
    unfold transitionPolynomial
    ring
  rw [hid]
  nlinarith

theorem transitionPolynomial_strictMonoOn :
    StrictMonoOn transitionPolynomial (Set.Ici (4 : ℝ)) := by
  intro x hx y hy hxy
  change 4 ≤ x at hx
  change 4 ≤ y at hy
  have hfactor :
      transitionPolynomial y - transitionPolynomial x =
        (y - x) *
          (x ^ 2 + x * y + y ^ 2 - 6 * x - 6 * y + 5) := by
    unfold transitionPolynomial
    ring
  have hxx : 0 ≤ (x - 4) * (x + 4) :=
    mul_nonneg (by linarith) (by linarith)
  have hyy : 0 ≤ (y - 4) * (y + 4) :=
    mul_nonneg (by linarith) (by linarith)
  have hxy4 : 16 ≤ x * y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x - 4)
      (by linarith : 0 ≤ y - 4)]
  have hbracket :
      0 < x ^ 2 + x * y + y ^ 2 - 6 * x - 6 * y + 5 := by
    nlinarith
  have hdiff : 0 < transitionPolynomial y - transitionPolynomial x := by
    rw [hfactor]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  linarith

theorem existsUnique_transition :
    ∃! u : ℝ, 1 < u ∧ transitionPolynomial u = 0 := by
  have hcont : Continuous transitionPolynomial := by
    unfold transitionPolynomial
    fun_prop
  have hmem :
      (0 : ℝ) ∈ Set.Icc (transitionPolynomial 5) (transitionPolynomial 6) := by
    norm_num [transitionPolynomial]
  rcases intermediate_value_Icc (by norm_num : (5 : ℝ) ≤ 6)
      hcont.continuousOn hmem with ⟨u, huIcc, hroot⟩
  have hu4 : 4 < u := by linarith [huIcc.1]
  refine ⟨u, ⟨by linarith [huIcc.1], hroot⟩, ?_⟩
  intro y hy
  have hy4 : 4 < y := by
    by_contra hnot
    have hneg := transitionPolynomial_neg_of_gt_one_le_four
      hy.1 (le_of_not_gt hnot)
    rw [hy.2] at hneg
    linarith
  exact transitionPolynomial_strictMonoOn.injOn hy4.le hu4.le
    (hy.2.trans hroot.symm)

def transition : ℝ := Classical.choose existsUnique_transition

theorem transition_spec :
    1 < transition ∧ transitionPolynomial transition = 0 :=
  (Classical.choose_spec existsUnique_transition).1

theorem transition_gt_five : 5 < transition := by
  by_contra hnot
  have hle : transition ≤ 5 := le_of_not_gt hnot
  by_cases h4 : transition ≤ 4
  · have hneg := transitionPolynomial_neg_of_gt_one_le_four
      transition_spec.1 h4
    rw [transition_spec.2] at hneg
    linarith
  · have hmono := transitionPolynomial_strictMonoOn.monotoneOn
      (by linarith : (4 : ℝ) ≤ transition) (by norm_num : (4 : ℝ) ≤ 5) hle
    rw [transition_spec.2] at hmono
    norm_num [transitionPolynomial] at hmono

theorem transition_lt_six : transition < 6 := by
  by_contra hnot
  have hmono := transitionPolynomial_strictMonoOn.monotoneOn
    (by norm_num : (4 : ℝ) ≤ 6)
    (by linarith [transition_gt_five] : (4 : ℝ) ≤ transition)
    (le_of_not_gt hnot)
  rw [transition_spec.2] at hmono
  norm_num [transitionPolynomial] at hmono

theorem transitionPolynomial_nonpos_iff {u : ℝ} (hu : 1 < u) :
    transitionPolynomial u ≤ 0 ↔ u ≤ transition := by
  constructor
  · intro hpoly
    by_contra hnot
    have hmono := transitionPolynomial_strictMonoOn
      (by linarith [transition_gt_five] : (4 : ℝ) ≤ transition)
      (by linarith [transition_gt_five] : (4 : ℝ) ≤ u)
      (lt_of_not_ge hnot)
    rw [transition_spec.2] at hmono
    linarith
  · intro hle
    by_cases hu4 : u ≤ 4
    · exact (transitionPolynomial_neg_of_gt_one_le_four hu hu4).le
    · have hmono := transitionPolynomial_strictMonoOn.monotoneOn
        (by linarith : (4 : ℝ) ≤ u)
        (by linarith [transition_gt_five] : (4 : ℝ) ≤ transition) hle
      rwa [transition_spec.2] at hmono

/-! ## Maximization of the `B` family -/

theorem familyB_le_boundary_of_poly_nonpos {u τ : ℝ}
    (hu : 1 < u) (hτ1 : 1 ≤ τ) (hτu : τ ≤ u)
    (hpoly : transitionPolynomial u ≤ 0) :
    familyB u τ ≤ boundaryRatio u := by
  have hdu := boundary_den_pos hu
  have hdτ := familyB_den_pos (u := u) (τ := τ) (by linarith) hτ1
  unfold familyB boundaryRatio
  rw [div_le_div_iff₀ hdτ hdu]
  let c := u ^ 2 - 5 * u + 2
  let q := τ * c - u ^ 2 + 3 * u - 1
  have hq : q ≤ 0 := by
    by_cases hc : c ≤ 0
    · have hmul := mul_le_mul_of_nonpos_right hτ1 hc
      dsimp [q]
      dsimp [c] at hc hmul
      nlinarith
    · have hc0 : 0 ≤ c := le_of_not_ge hc
      have hmul := mul_le_mul_of_nonneg_right hτu hc0
      dsimp [q]
      dsimp [c] at hc0 hmul
      unfold transitionPolynomial at hpoly
      nlinarith
  have hfactor :
      u ^ 3 *
          (τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1) -
        (τ ^ 2 * u + 2 * τ ^ 2 - 2 * τ * u - τ + u) *
          (u ^ 2 + (u - 1) ^ 3) =
        (τ - u) * q := by
    dsimp [q, c]
    ring
  have hprod : 0 ≤ (τ - u) * q :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hτu) hq
  nlinarith [hfactor]

theorem familyB_le_interior_of_four_lt {u τ : ℝ}
    (hu : 4 < u) (hτ : 1 ≤ τ) : familyB u τ ≤ interiorRatio u := by
  let r := Real.sqrt u
  have hu0 : 0 < u := by linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg u
  have hrSq : r ^ 2 = u := Real.sq_sqrt hu0.le
  have hr2 : 2 < r := by nlinarith
  have hr1 : 0 < r - 1 := by linarith
  have hden : 0 <
      r ^ 2 * τ ^ 2 - 2 * r ^ 2 * τ + r ^ 2 + 2 * τ - 1 := by
    have := familyB_den_pos (u := r ^ 2) (τ := τ) (by positivity) hτ
    nlinarith
  have hdenU : 0 <
      τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1 := by
    rw [← hrSq]
    nlinarith [hden]
  unfold familyB
  rw [div_le_iff₀ hdenU]
  have hid :
      interiorRatio u *
          (τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1) -
        (τ ^ 2 * u + 2 * τ ^ 2 - 2 * τ * u - τ + u) =
      (r * τ - r - 2 * τ + 1) ^ 2 / (2 * (r - 1)) := by
    unfold interiorRatio
    rw [show Real.sqrt u = r by rfl, ← hrSq]
    field_simp [hr1.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

theorem interiorRatio_at_square_root_stationary {u : ℝ} (hu : 4 < u) :
    let τ := (Real.sqrt u - 1) / (Real.sqrt u - 2)
    familyB u τ = interiorRatio u := by
  let r := Real.sqrt u
  let τ := (r - 1) / (r - 2)
  have hu0 : 0 < u := by linarith
  have hrSq : r ^ 2 = u := Real.sq_sqrt hu0.le
  have hr2 : 2 < r := by
    have hr0 := Real.sqrt_nonneg u
    nlinarith
  have hne2 : r - 2 ≠ 0 := by linarith
  have hne1 : r - 1 ≠ 0 := by linarith
  have hτ1 : 1 ≤ τ := by
    dsimp [τ]
    rw [le_div_iff₀ (by linarith : 0 < r - 2)]
    linarith
  have hden : 0 <
      τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1 :=
    familyB_den_pos hu0 hτ1
  have hid :
      interiorRatio u *
          (τ ^ 2 * u - 2 * τ * u + 2 * τ + u - 1) -
        (τ ^ 2 * u + 2 * τ ^ 2 - 2 * τ * u - τ + u) =
      (r * τ - r - 2 * τ + 1) ^ 2 / (2 * (r - 1)) := by
    unfold interiorRatio
    rw [show Real.sqrt u = r by rfl, ← hrSq]
    field_simp [hne1]
    ring
  have hzero : r * τ - r - 2 * τ + 1 = 0 := by
    dsimp [τ]
    field_simp [hne2]
    ring
  dsimp only
  unfold familyB
  rw [div_eq_iff hden.ne']
  rw [hzero] at hid
  norm_num at hid
  linarith

theorem interiorRatio_at_transition :
    interiorRatio transition = boundaryRatio transition := by
  let r := Real.sqrt transition
  have hu0 : 0 < transition := by linarith [transition_gt_five]
  have hr0 := Real.sqrt_nonneg transition
  have hrSq : r ^ 2 = transition := Real.sq_sqrt hu0.le
  have hr2 : 2 < r := by nlinarith [transition_gt_five]
  have hpoly := transition_spec.2
  have hsquares :
      (r * (transition - 1)) ^ 2 = (2 * transition - 1) ^ 2 := by
    dsimp [r] at hrSq ⊢
    unfold transitionPolynomial at hpoly
    nlinarith
  have hleft : 0 ≤ r * (transition - 1) :=
    mul_nonneg hr0 (by linarith [transition_gt_five])
  have hright : 0 ≤ 2 * transition - 1 := by
    linarith [transition_gt_five]
  have hlinear : r * (transition - 1) = 2 * transition - 1 := by
    nlinarith [sq_nonneg
      (r * (transition - 1) + (2 * transition - 1))]
  have hτ : (r - 1) / (r - 2) = transition := by
    rw [div_eq_iff (by linarith : r - 2 ≠ 0)]
    nlinarith
  calc
    interiorRatio transition = familyB transition ((r - 1) / (r - 2)) := by
      symm
      simpa [r] using
        interiorRatio_at_square_root_stationary
          (u := transition) (by linarith [transition_gt_five])
    _ = familyB transition transition := by rw [hτ]
    _ = boundaryRatio transition := familyB_at_u transition_spec.1

/-! ## Assembly of the two binary families -/

theorem familyA_le_boundary_before_transition {u τ : ℝ}
    (hu : 1 < u) (hτ1 : 1 ≤ τ) (hτu : τ ≤ u - 1)
    (hpoly : transitionPolynomial u ≤ 0) :
    familyA τ ≤ boundaryRatio u := by
  by_cases hu3 : u ≤ 3
  · have hu2 : 2 ≤ u := by linarith [hτ1, hτu]
    have hA := familyA_mono_to_two hτ1 hτu (by linarith)
    have hdenA := familyA_den_pos (u - 1)
    have hdenB := boundary_den_pos hu
    have hpositive :
        0 < u ^ 4 - 5 * u ^ 3 + 9 * u ^ 2 - 5 * u + 1 := by
      let v := u - 2
      have hv0 : 0 ≤ v := by dsimp [v]; linarith
      have hid :
          u ^ 4 - 5 * u ^ 3 + 9 * u ^ 2 - 5 * u + 1 =
            v ^ 4 + 3 * v ^ 3 + 3 * v ^ 2 + 3 * v + 3 := by
        dsimp [v]
        ring
      rw [hid]
      positivity
    have hcompare : familyA (u - 1) < boundaryRatio u := by
      rw [familyA, boundaryRatio, div_lt_div_iff₀ hdenA hdenB]
      nlinarith
    exact hA.trans hcompare.le
  · have hA := familyA_le_four_thirds τ
    have hden := boundary_den_pos hu
    have hboundary : 4 / 3 ≤ boundaryRatio u := by
      rw [boundaryRatio, le_div_iff₀ hden]
      have hnonneg : 0 ≤ (2 * u - 1) * (u - 3) := by
        apply mul_nonneg <;> linarith
      unfold transitionPolynomial at hpoly
      nlinarith
    exact hA.trans hboundary

theorem interiorRatio_ge_four_thirds {u : ℝ}
    (hu : 4 < u) (huPlateau : u ≤ 25 / 4) :
    4 / 3 ≤ interiorRatio u := by
  have hu0 : 0 ≤ u := by linarith
  have hsqrt0 := Real.sqrt_nonneg u
  have hsqrtSq := Real.sq_sqrt hu0
  have hsqrt1 : 1 < Real.sqrt u := by nlinarith
  have hsqrtUpper : Real.sqrt u ≤ 5 / 2 := by nlinarith
  unfold interiorRatio
  have hden : 0 < 2 * (Real.sqrt u - 1) := by linarith
  have honeThird : (1 : ℝ) / 3 ≤ 1 / (2 * (Real.sqrt u - 1)) := by
    rw [le_div_iff₀ hden]
    nlinarith
  nlinarith

theorem interiorRatio_le_four_thirds {u : ℝ}
    (hu : 25 / 4 ≤ u) : interiorRatio u ≤ 4 / 3 := by
  have hu0 : 0 ≤ u := by linarith
  have hsqrt0 := Real.sqrt_nonneg u
  have hsqrtSq := Real.sq_sqrt hu0
  have hsqrtLower : 5 / 2 ≤ Real.sqrt u := by nlinarith
  unfold interiorRatio
  have hden : 0 < 2 * (Real.sqrt u - 1) := by linarith
  have honeThird : 1 / (2 * (Real.sqrt u - 1)) ≤ (1 : ℝ) / 3 := by
    rw [div_le_iff₀ hden]
    nlinarith
  nlinarith

def randomizedCurve (u : ℝ) : ℝ :=
  if u ≤ 1 then 1
  else if u ≤ transition then boundaryRatio u
  else if u ≤ 25 / 4 then interiorRatio u
  else 4 / 3

/-- Exact scalar upper bound after the survival-function reduction: both
binary families lie below the advertised four-piece curve. -/
theorem binaryFamilies_le_curve {u : ℝ} (hu : 1 < u) :
    (∀ τ, 1 ≤ τ → τ ≤ u →
      familyB u τ ≤ randomizedCurve u) ∧
    (∀ τ, 1 ≤ τ → τ ≤ u - 1 →
      familyA τ ≤ randomizedCurve u) := by
  unfold randomizedCurve
  rw [if_neg (not_le.mpr hu)]
  by_cases htrans : u ≤ transition
  · rw [if_pos htrans]
    have hpoly := (transitionPolynomial_nonpos_iff hu).2 htrans
    constructor
    · intro τ hτ1 hτu
      exact familyB_le_boundary_of_poly_nonpos hu hτ1 hτu hpoly
    · intro τ hτ1 hτu
      exact familyA_le_boundary_before_transition hu hτ1 hτu hpoly
  · rw [if_neg htrans]
    have hu4 : 4 < u := by linarith [transition_gt_five]
    by_cases hplateau : u ≤ 25 / 4
    · rw [if_pos hplateau]
      constructor
      · intro τ hτ1 _hτu
        exact familyB_le_interior_of_four_lt hu4 hτ1
      · intro τ _hτ1 _hτu
        exact (familyA_le_four_thirds τ).trans
          (interiorRatio_ge_four_thirds hu4 hplateau)
    · rw [if_neg hplateau]
      have hlarge : 25 / 4 ≤ u := le_of_lt (lt_of_not_ge hplateau)
      constructor
      · intro τ hτ1 _hτu
        exact (familyB_le_interior_of_four_lt hu4 hτ1).trans
          (interiorRatio_le_four_thirds hlarge)
      · intro τ _hτ1 _hτu
        exact familyA_le_four_thirds τ

/-- Each nontrivial branch is attained by one of the two binary families. -/
theorem binaryFamilies_attain_curve {u : ℝ} (hu : 1 < u) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u, familyB u τ = randomizedCurve u) ∨
      (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1),
        familyA τ = randomizedCurve u) := by
  unfold randomizedCurve
  rw [if_neg (not_le.mpr hu)]
  by_cases htrans : u ≤ transition
  · rw [if_pos htrans]
    exact Or.inl ⟨u, ⟨by linarith, le_rfl⟩, familyB_at_u hu⟩
  · rw [if_neg htrans]
    have hu4 : 4 < u := by linarith [transition_gt_five]
    by_cases hplateau : u ≤ 25 / 4
    · rw [if_pos hplateau]
      let τ := (Real.sqrt u - 1) / (Real.sqrt u - 2)
      have hsqrt0 := Real.sqrt_nonneg u
      have hsqrtSq := Real.sq_sqrt (by linarith : 0 ≤ u)
      have hsqrt2 : 2 < Real.sqrt u := by nlinarith
      have hτ1 : 1 ≤ τ := by
        dsimp [τ]
        rw [le_div_iff₀ (by linarith)]
        linarith
      have hτu : τ ≤ u := by
        have hpoly : 0 ≤ transitionPolynomial u := by
          have hmono := transitionPolynomial_strictMonoOn.monotoneOn
            (by linarith [transition_gt_five] : (4 : ℝ) ≤ transition)
            (by linarith [transition_gt_five] : (4 : ℝ) ≤ u)
            (le_of_lt (lt_of_not_ge htrans))
          rwa [transition_spec.2] at hmono
        dsimp [τ]
        rw [div_le_iff₀ (by linarith : 0 < Real.sqrt u - 2)]
        have hleft : 0 ≤ Real.sqrt u * (u - 1) := by positivity
        have hright : 0 ≤ 2 * u - 1 := by linarith
        have hsquares :
            (2 * u - 1) ^ 2 ≤ (Real.sqrt u * (u - 1)) ^ 2 := by
          unfold transitionPolynomial at hpoly
          nlinarith [mul_nonneg (by linarith : 0 ≤ u) hpoly]
        have hlinear : 2 * u - 1 ≤ Real.sqrt u * (u - 1) := by
          nlinarith [sq_nonneg
            (Real.sqrt u * (u - 1) + (2 * u - 1))]
        nlinarith
      exact Or.inl ⟨τ, ⟨hτ1, hτu⟩,
        interiorRatio_at_square_root_stationary hu4⟩
    · rw [if_neg hplateau]
      have hu3 : 3 ≤ u := by linarith
      exact Or.inr ⟨2, ⟨by norm_num, by linarith⟩, by
        unfold familyA
        norm_num⟩

/-! ## Global maximum -/

def globalMaximum : ℝ := (27 + 6 * Real.sqrt 3) / 23

theorem boundaryRatio_le_globalMaximum {u : ℝ} (hu : 1 < u) :
    boundaryRatio u ≤ globalMaximum := by
  have hden := boundary_den_pos hu
  have hsqrt0 := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hlinear : 0 < u - 2 * Real.sqrt 3 + 3 := by
    have hsqrtUpper : Real.sqrt 3 < 2 := by nlinarith
    linarith
  have hsquare :
      0 ≤ (u - (3 + Real.sqrt 3) / 2) ^ 2 := sq_nonneg _
  have hcoef : 0 ≤ 4 + 6 * Real.sqrt 3 := by positivity
  have hidentity :
      (27 + 6 * Real.sqrt 3) * (u ^ 2 + (u - 1) ^ 3) - 23 * u ^ 3 =
        (4 + 6 * Real.sqrt 3) *
          (u - (3 + Real.sqrt 3) / 2) ^ 2 *
            (u - 2 * Real.sqrt 3 + 3) := by
    ring_nf
    nlinarith
  unfold boundaryRatio globalMaximum
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 23)]
  nlinarith [mul_nonneg (mul_nonneg hcoef hsquare) hlinear.le]

theorem boundaryRatio_attains_globalMaximum :
    boundaryRatio ((3 + Real.sqrt 3) / 2) = globalMaximum := by
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hu : 1 < (3 + Real.sqrt 3) / 2 := by
    have hsqrt0 := Real.sqrt_nonneg 3
    linarith
  have hden := boundary_den_pos hu
  unfold boundaryRatio globalMaximum
  rw [div_eq_div_iff hden.ne' (by norm_num : (23 : ℝ) ≠ 0)]
  ring_nf
  nlinarith

/-- The four-piece randomized revealing-optimization curve attains its
global maximum at the boundary-family point `(3+√3)/2`. -/
theorem randomizedCurve_attains_globalMaximum :
    randomizedCurve ((3 + Real.sqrt 3) / 2) = globalMaximum := by
  have hsqrt0 := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hu1 : 1 < (3 + Real.sqrt 3) / 2 := by linarith
  have hu5 : (3 + Real.sqrt 3) / 2 < 5 := by nlinarith
  have htransition : (3 + Real.sqrt 3) / 2 ≤ transition := by
    linarith [transition_gt_five]
  unfold randomizedCurve
  rw [if_neg (not_le.mpr hu1), if_pos htransition]
  exact boundaryRatio_attains_globalMaximum

theorem randomizedCurve_le_globalMaximum {u : ℝ} (_hu : 0 < u) :
    randomizedCurve u ≤ globalMaximum := by
  unfold randomizedCurve
  by_cases hu1 : u ≤ 1
  · rw [if_pos hu1]
    have hsqrt0 := Real.sqrt_nonneg 3
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    unfold globalMaximum
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 23)]
    nlinarith
  · rw [if_neg hu1]
    have hu1' : 1 < u := lt_of_not_ge hu1
    by_cases htrans : u ≤ transition
    · rw [if_pos htrans]
      exact boundaryRatio_le_globalMaximum hu1'
    · rw [if_neg htrans]
      by_cases hplateau : u ≤ 25 / 4
      · rw [if_pos hplateau]
        have htu : transition ≤ u := le_of_lt (lt_of_not_ge htrans)
        have hsqrtTu : Real.sqrt transition ≤ Real.sqrt u :=
          Real.sqrt_le_sqrt htu
        have hsqrtT2 : 2 < Real.sqrt transition := by
          have hsqrtT0 := Real.sqrt_nonneg transition
          have hsqrtTSq := Real.sq_sqrt
            (by linarith [transition_gt_five] : 0 ≤ transition)
          nlinarith [transition_gt_five]
        have hsqrtU1 : 1 < Real.sqrt u := by linarith
        have hmono : interiorRatio u ≤ interiorRatio transition := by
          unfold interiorRatio
          have hdenT : 0 < 2 * (Real.sqrt transition - 1) := by linarith
          have hdenU : 0 < 2 * (Real.sqrt u - 1) := by linarith
          have hrecip := one_div_le_one_div_of_le hdenT
            (by nlinarith : 2 * (Real.sqrt transition - 1) ≤
              2 * (Real.sqrt u - 1))
          simpa [add_comm] using add_le_add_left hrecip 1
        rw [interiorRatio_at_transition] at hmono
        exact hmono.trans (boundaryRatio_le_globalMaximum transition_spec.1)
      · rw [if_neg hplateau]
        have hsqrt0 := Real.sqrt_nonneg 3
        have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        unfold globalMaximum
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 23)).2
        nlinarith

end

end RevealingOptimization
end SchedulingPaper
