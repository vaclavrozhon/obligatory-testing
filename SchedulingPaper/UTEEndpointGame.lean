import SchedulingPaper.ExactCurve

/-!
# Scalar UTE endpoint game

This file formalizes the quadratic endpoint game in the proof of the UTE
upper bound for `2 ≤ u ≤ uZero`.  We write `s = u - 1`, so the parameter
range is `1 ≤ s ≤ sZero`, and use the positive root
`rho = rhoI (s + 1)`.

The four normalized masses from the paper are prefix-long `a`, capped
suffix-deferred `d`, boundary-deferred `t`, and suffix-immediate-one `m`.
After setting `m = 0`, the optimized reduction is

`a = min b x`, `d = max 0 (x-b)`, `t = max 0 (chi-x)`.

The main theorem `uteEndpointGap_nonpos` checks the resulting gap on the
three intervals `x ≤ b`, `b ≤ x ≤ chi`, and `chi ≤ x`.
-/

namespace SchedulingPaper

noncomputable section

/-! ## Parameters -/

def uteK (s : ℝ) : ℝ := s ^ 2 + s + 1

def uteRho (s : ℝ) : ℝ := rhoI (s + 1)

def uteD (s : ℝ) : ℝ := uteK s + s * uteRho s

def uteB (s : ℝ) : ℝ :=
  (uteK s - s ^ 2 * uteRho s) / uteD s

def uteChi (s : ℝ) : ℝ :=
  s * (s + 1) / uteD s

def uteAlpha (s : ℝ) : ℝ :=
  uteK s / uteD s

def uteGamma (s : ℝ) : ℝ :=
  s - uteRho s * (s - 1)

def uteC0 (s : ℝ) : ℝ :=
  -(uteRho s - 1) / 2 +
    (1 - uteB s) ^ 2 / (2 * uteRho s)

theorem uteRho_pos {s : ℝ} (hs : 0 < s) :
    0 < uteRho s := by
  exact (rhoI_spec (by linarith : 1 < s + 1)).1

theorem uteRho_root {s : ℝ} (hs : 0 < s) :
    rhoPolynomial s (uteRho s) = 0 := by
  simpa [uteRho] using
    (rhoI_spec (by linarith : 1 < s + 1)).2

theorem uteK_pos (s : ℝ) : 0 < uteK s := by
  unfold uteK
  nlinarith [sq_nonneg (s + 1 / 2)]

theorem uteD_pos {s : ℝ} (hs : 0 < s) :
    0 < uteD s := by
  unfold uteD
  exact add_pos_of_pos_of_nonneg (uteK_pos s)
    (mul_nonneg hs.le (uteRho_pos hs).le)

/-! ## Root estimates on `1 ≤ s ≤ sZero` -/

theorem sZeroPolynomial_nonpos_on_ute
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    sZeroPolynomial s ≤ 0 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hroot : sZeroPolynomial sZero = 0 := by
    unfold sZeroPolynomial
    linarith [sZero_spec.2.2]
  by_cases hs2 : s ≤ 2
  · have hcubic : s ^ 3 ≤ 2 * s ^ 2 := by
      have hnonneg : 0 ≤ (2 - s) * s ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg s)
      nlinarith
    have hgap : 2 * s ^ 2 < (s + 1) ^ 2 := by
      have hnonneg : 0 ≤ s * (2 - s) :=
        mul_nonneg hs.le (sub_nonneg.mpr hs2)
      nlinarith
    unfold sZeroPolynomial
    linarith
  · have htwo : 2 < s := lt_of_not_ge hs2
    rcases eq_or_lt_of_le hs0 with heq | hlt
    · rw [heq, hroot]
    · have hmono :=
        sZeroPolynomial_strictMono_above_two htwo hlt
      rw [hroot] at hmono
      exact hmono.le

theorem rhoPolynomial_ute_candidate_nonneg
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 ≤ rhoPolynomial s (uteK s / s ^ 2) := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hpoly := sZeroPolynomial_nonpos_on_ute hs1 hs0
  have hs3 : 0 < s ^ 3 := by positivity
  have hidentity :
      rhoPolynomial s (uteK s / s ^ 2) =
        (uteK s / s ^ 3) * (-sZeroPolynomial s) := by
    unfold rhoPolynomial sZeroPolynomial uteK
    field_simp [hs.ne']
    ring
  rw [hidentity]
  exact mul_nonneg
    (div_nonneg (uteK_pos s).le hs3.le)
    (neg_nonneg.mpr hpoly)

theorem uteRho_le_candidate
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    uteRho s ≤ uteK s / s ^ 2 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hcandidate : 0 < uteK s / s ^ 2 :=
    div_pos (uteK_pos s) (sq_pos_of_pos hs)
  have hvalue := rhoPolynomial_ute_candidate_nonneg hs1 hs0
  by_contra hle
  have hlt : uteK s / s ^ 2 < uteRho s := lt_of_not_ge hle
  have hmono :=
    rhoPolynomial_strictMono_nonneg hs hcandidate.le hlt
  rw [uteRho_root hs] at hmono
  linarith

theorem uteRho_gt_one {s : ℝ} (hs : 0 < s) :
    1 < uteRho s := by
  have hone : rhoPolynomial s 1 < 0 := by
    unfold rhoPolynomial
    nlinarith [sq_nonneg s]
  have hrho := uteRho_pos hs
  by_contra hle
  have hroot := uteRho_root hs
  rcases eq_or_lt_of_le (le_of_not_gt hle) with heq | hlt
  · rw [← heq, hroot] at hone
    linarith
  · have hmono :=
      rhoPolynomial_strictMono_nonneg hs hrho.le hlt
    rw [hroot] at hmono
    linarith

theorem uteRho_lt_two {s : ℝ} (hs : 0 < s) :
    uteRho s < 2 := by
  have htwo : 0 < rhoPolynomial s 2 := by
    unfold rhoPolynomial
    have hfactor : 0 < s * (s ^ 2 - s + 1) := by
      apply mul_pos hs
      nlinarith [sq_nonneg (s - 1 / 2)]
    nlinarith
  have hrho := uteRho_pos hs
  have hroot := uteRho_root hs
  by_contra hle
  have hge : 2 ≤ uteRho s := le_of_not_gt hle
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [heq, hroot] at htwo
    linarith
  · have hmono :=
      rhoPolynomial_strictMono_nonneg hs (by norm_num) hlt
    rw [hroot] at hmono
    linarith

theorem sZero_lt_thirteen_sixths :
    sZero < (13 : ℝ) / 6 := by
  have hvalue :
      0 < sZeroPolynomial ((13 : ℝ) / 6) := by
    norm_num [sZeroPolynomial]
  by_contra hle
  have hge : (13 : ℝ) / 6 ≤ sZero := le_of_not_gt hle
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [heq, show sZeroPolynomial sZero = 0 by
      unfold sZeroPolynomial
      linarith [sZero_spec.2.2]] at hvalue
    linarith
  · have hmono :=
      sZeroPolynomial_strictMono_above_two
        (by norm_num : (2 : ℝ) < 13 / 6) hlt
    rw [show sZeroPolynomial sZero = 0 by
      unfold sZeroPolynomial
      linarith [sZero_spec.2.2]] at hmono
    linarith

theorem seven_fourths_polynomial_pos
    {s : ℝ} (hs2 : 2 ≤ s) :
    0 < rhoPolynomial s ((7 : ℝ) / 4) := by
  have hfactor :
      12 * s ^ 3 - 20 * s ^ 2 + s - 4 =
        14 + (s - 2) * (12 * s ^ 2 + 4 * s + 9) := by ring
  have hsecond : 0 < 12 * s ^ 2 + 4 * s + 9 := by
    nlinarith [sq_nonneg s]
  have hpos :
      0 < 12 * s ^ 3 - 20 * s ^ 2 + s - 4 := by
    rw [hfactor]
    positivity
  unfold rhoPolynomial
  nlinarith

theorem uteRho_lt_seven_fourths
    {s : ℝ} (hs2 : 2 ≤ s) :
    uteRho s < (7 : ℝ) / 4 := by
  have hs : 0 < s := by linarith
  have hvalue := seven_fourths_polynomial_pos hs2
  have hroot := uteRho_root hs
  by_contra hle
  have hge : (7 : ℝ) / 4 ≤ uteRho s := le_of_not_gt hle
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [heq, hroot] at hvalue
    linarith
  · have hmono :=
      rhoPolynomial_strictMono_nonneg hs (by norm_num) hlt
    rw [hroot] at hmono
    linarith

/-! ## Parameter order -/

theorem uteB_nonneg
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 ≤ uteB s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hcompare := uteRho_le_candidate hs1 hs0
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hnum : 0 ≤ uteK s - s ^ 2 * uteRho s := by
    have := (le_div_iff₀ hs2).mp hcompare
    nlinarith
  exact div_nonneg hnum (uteD_pos hs).le

theorem uteAlpha_pos {s : ℝ} (hs : 0 < s) :
    0 < uteAlpha s :=
  div_pos (uteK_pos s) (uteD_pos hs)

theorem uteAlpha_lt_one {s : ℝ} (hs : 0 < s) :
    uteAlpha s < 1 := by
  unfold uteAlpha
  rw [div_lt_one (uteD_pos hs)]
  unfold uteD
  have := mul_pos hs (uteRho_pos hs)
  linarith

theorem uteChi_pos {s : ℝ} (hs : 0 < s) :
    0 < uteChi s := by
  unfold uteChi
  exact div_pos (mul_pos hs (by linarith)) (uteD_pos hs)

theorem uteChi_lt_alpha {s : ℝ} (hs : 0 < s) :
    uteChi s < uteAlpha s := by
  have hD := uteD_pos hs
  unfold uteChi uteAlpha uteK
  rw [div_lt_div_iff_of_pos_right hD]
  ring_nf
  norm_num

theorem uteB_lt_chi
    {s : ℝ} (hs1 : 1 ≤ s) :
    uteB s < uteChi s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hrho : 1 < uteRho s := uteRho_gt_one hs
  have hsSq : 1 ≤ s ^ 2 := by nlinarith
  have hnum : 1 < s ^ 2 * uteRho s := by
    nlinarith [mul_le_mul_of_nonneg_right hsSq (uteRho_pos hs).le]
  have hD := uteD_pos hs
  unfold uteB uteChi uteK
  rw [div_lt_div_iff_of_pos_right hD]
  nlinarith

theorem ute_parameter_order
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 ≤ uteB s ∧
      uteB s < uteChi s ∧
      uteChi s < uteAlpha s ∧
      uteAlpha s < 1 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  exact ⟨uteB_nonneg hs1 hs0, uteB_lt_chi hs1,
    uteChi_lt_alpha hs, uteAlpha_lt_one hs⟩

theorem uteChi_eq_one_sub_b_div_rho
    {s : ℝ} (hs : 0 < s) :
    uteChi s = (1 - uteB s) / uteRho s := by
  have hD := (uteD_pos hs).ne'
  have hrho := (uteRho_pos hs).ne'
  unfold uteChi uteB
  field_simp [hD, hrho]
  unfold uteD uteK
  ring

theorem uteB_eq_succ_mul_alpha_sub_s
    {s : ℝ} (hs : 0 < s) :
    uteB s = (s + 1) * uteAlpha s - s := by
  have hD := (uteD_pos hs).ne'
  unfold uteB uteAlpha
  field_simp [hD]
  unfold uteD uteK
  ring

/-! ## Positivity of the middle-interval curvature -/

theorem uteGamma_pos
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 < uteGamma s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  by_cases hs2 : s ≤ 2
  · rcases eq_or_lt_of_le hs1 with heq | hs1strict
    · subst s
      simp [uteGamma]
    · have hmul :=
        mul_lt_mul_of_pos_right (uteRho_lt_two hs)
          (sub_pos.mpr hs1strict)
      unfold uteGamma
      nlinarith
  · have hs2' : 2 ≤ s := (lt_of_not_ge hs2).le
    have hrho := uteRho_lt_seven_fourths hs2'
    have hmul :=
      mul_lt_mul_of_pos_right hrho (by linarith : 0 < s - 1)
    have hs13 : s < (13 : ℝ) / 6 :=
      hs0.trans_lt sZero_lt_thirteen_sixths
    unfold uteGamma
    nlinarith

/-! ## The small-interval sign certificate -/

def uteSmallCertificate (s : ℝ) : ℝ :=
  -s + (1 + s - s ^ 3) * uteRho s +
    s ^ 2 * (s - 1) * uteRho s ^ 2

theorem five_thirds_polynomial_neg
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    rhoPolynomial s ((5 : ℝ) / 3) < 0 := by
  have hs13 : s < (13 : ℝ) / 6 :=
    hs0.trans_lt sZero_lt_thirteen_sixths
  let f : ℝ → ℝ :=
    fun x => 6 * x ^ 3 - 12 * x ^ 2 - 2 * x - 3
  have hfactor :
      f ((13 : ℝ) / 6) - f s =
        ((13 : ℝ) / 6 - s) *
          (36 * s ^ 2 + 6 * s + 1) / 6 := by
    dsimp [f]
    ring
  have hsecond : 0 < 36 * s ^ 2 + 6 * s + 1 := by
    nlinarith [sq_nonneg s]
  have hdiff : 0 < f ((13 : ℝ) / 6) - f s := by
    rw [hfactor]
    positivity
  have hend : f ((13 : ℝ) / 6) = -(95 : ℝ) / 36 := by
    norm_num [f]
  have hf : f s < 0 := by linarith
  unfold rhoPolynomial
  dsimp [f] at hf
  nlinarith

theorem uteRho_gt_five_thirds
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    (5 : ℝ) / 3 < uteRho s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hvalue := five_thirds_polynomial_neg hs1 hs0
  have hroot := uteRho_root hs
  by_contra hle
  have hge : uteRho s ≤ (5 : ℝ) / 3 := le_of_not_gt hle
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [← heq, hroot] at hvalue
    linarith
  · have hmono :=
      rhoPolynomial_strictMono_nonneg hs (uteRho_pos hs).le hlt
    rw [hroot] at hmono
    linarith

theorem ute_small_at_five_thirds_pos
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 <
      -s + (1 + s - s ^ 3) * ((5 : ℝ) / 3) +
        s ^ 2 * (s - 1) * ((5 : ℝ) / 3) ^ 2 := by
  have hs13 : s < (13 : ℝ) / 6 :=
    hs0.trans_lt sZero_lt_thirteen_sixths
  let z : ℝ := s - 3 / 2
  have hzLower : -(1 : ℝ) / 2 ≤ z := by
    dsimp [z]
    linarith
  have hzUpper : z < (2 : ℝ) / 3 := by
    dsimp [z]
    linarith
  have hQidentity :
      10 * s ^ 3 - 25 * s ^ 2 + 6 * s + 15 =
        (3 : ℝ) / 2 - 3 * z / 2 + 20 * z ^ 2 + 10 * z ^ 3 := by
    dsimp [z]
    ring
  have hQ :
      0 < 10 * s ^ 3 - 25 * s ^ 2 + 6 * s + 15 := by
    rw [hQidentity]
    by_cases hz : z ≤ 0
    · have hcube :
          0 ≤ z ^ 2 * (z + 1 / 2) :=
        mul_nonneg (sq_nonneg z) (by linarith)
      nlinarith [sq_nonneg z]
    · have hz0 : 0 ≤ z := (lt_of_not_ge hz).le
      have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
      have hz3 : 0 ≤ z ^ 3 := by positivity
      nlinarith
  nlinarith

theorem uteSmallCertificate_pos
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 < uteSmallCertificate s := by
  have hrho := uteRho_gt_five_thirds hs1 hs0
  have hs0' : 0 ≤ s := zero_le_one.trans hs1
  have hcoef : 0 ≤ s ^ 2 * (s - 1) :=
    mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)
  have hderivativeAt :
      0 <
        (1 + s - s ^ 3) +
          2 * s ^ 2 * (s - 1) * ((5 : ℝ) / 3) := by
    have hpoly :
        0 < 7 * s ^ 3 - 10 * s ^ 2 + 3 * s + 3 := by
      have hfactor :
          7 * s ^ 3 - 10 * s ^ 2 + 3 * s + 3 =
            3 + s * (s - 1) * (7 * s - 3) := by ring
      rw [hfactor]
      have hnonneg :
          0 ≤ s * (s - 1) * (7 * s - 3) :=
        mul_nonneg
          (mul_nonneg hs0' (sub_nonneg.mpr hs1))
          (by linarith)
      linarith
    nlinarith
  have hbracket :
      0 <
        (1 + s - s ^ 3) +
          s ^ 2 * (s - 1) *
            (uteRho s + (5 : ℝ) / 3) := by
    have hsum :
        2 * ((5 : ℝ) / 3) <
          uteRho s + (5 : ℝ) / 3 := by linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hsum.le hcoef
    nlinarith
  have hdiff :
      0 <
        uteSmallCertificate s -
          (-s + (1 + s - s ^ 3) * ((5 : ℝ) / 3) +
            s ^ 2 * (s - 1) * ((5 : ℝ) / 3) ^ 2) := by
    have hidentity :
        uteSmallCertificate s -
            (-s + (1 + s - s ^ 3) * ((5 : ℝ) / 3) +
              s ^ 2 * (s - 1) * ((5 : ℝ) / 3) ^ 2) =
          (uteRho s - (5 : ℝ) / 3) *
            ((1 + s - s ^ 3) +
              s ^ 2 * (s - 1) *
                (uteRho s + (5 : ℝ) / 3)) := by
      unfold uteSmallCertificate
      ring
    rw [hidentity]
    exact mul_pos (sub_pos.mpr hrho) hbracket
  linarith [ute_small_at_five_thirds_pos hs1 hs0]

theorem ute_small_certificate_identity
    {s : ℝ} (hs : 0 < s) :
    uteD s *
        (uteGamma s * (uteB s + uteChi s) -
          2 * s * uteB s) =
      uteSmallCertificate s := by
  have hD := (uteD_pos hs).ne'
  unfold uteGamma uteB uteChi uteSmallCertificate
  field_simp [hD]
  unfold uteK
  ring

theorem ute_small_bracket_pos
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    0 <
      uteGamma s * (uteB s + uteChi s) -
        2 * s * uteB s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hidentity := ute_small_certificate_identity hs
  have hD := uteD_pos hs
  have hq := uteSmallCertificate_pos hs1 hs0
  by_contra hle
  have hnonpos :
      uteGamma s * (uteB s + uteChi s) -
          2 * s * uteB s ≤ 0 :=
    le_of_not_gt hle
  have hmul :
      uteD s *
          (uteGamma s * (uteB s + uteChi s) -
            2 * s * uteB s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD.le hnonpos
  rw [hidentity] at hmul
  linarith

/-! ## Endpoint costs and the one-variable reduction -/

/-- Leading online coefficient from equation `ute-A`. -/
def uteA (s a d t m : ℝ) : ℝ :=
  1 / 2 + (s + 1) * (a - a ^ 2 / 2) +
    (1 - uteB s) * (d + t + m) - m ^ 2 / 2 +
    s * d ^ 2 / 2

/-- Leading offline coefficient from equation `ute-O`. -/
def uteO (s a d t m : ℝ) : ℝ :=
  1 / 2 + (a + d + t + m) ^ 2 / 2 +
    (s - 1) * (a + d) ^ 2 / 2

def uteGap (s a d t m : ℝ) : ℝ :=
  uteA s a d t m - uteRho s * uteO s a d t m

/-- Moving immediate-one mass `m` to boundary-deferred mass `t` preserves
the offline coefficient. -/
theorem uteO_move_m_to_t (s a d t m : ℝ) :
    uteO s a d (t + m) 0 = uteO s a d t m := by
  unfold uteO
  ring

/-- The same move increases the online coefficient by exactly `m²/2`. -/
theorem uteA_move_m_to_t (s a d t m : ℝ) :
    uteA s a d (t + m) 0 = uteA s a d t m + m ^ 2 / 2 := by
  unfold uteA
  ring

theorem uteGap_le_move_m_to_t (s a d t m : ℝ) :
    uteGap s a d t m ≤ uteGap s a d (t + m) 0 := by
  rw [uteGap, uteGap, uteO_move_m_to_t, uteA_move_m_to_t]
  nlinarith [sq_nonneg m]

/-- Optimized masses from equation `ute-reduction`. -/
def uteReducedA (s x : ℝ) : ℝ :=
  uteA s
    (min (uteB s) x)
    (max 0 (x - uteB s))
    (max 0 (uteChi s - x))
    0

def uteReducedO (s x : ℝ) : ℝ :=
  uteO s
    (min (uteB s) x)
    (max 0 (x - uteB s))
    (max 0 (uteChi s - x))
    0

def uteEndpointGap (s x : ℝ) : ℝ :=
  uteReducedA s x - uteRho s * uteReducedO s x

/-- Formula `ute-small-x`. -/
def uteSmallGap (s x : ℝ) : ℝ :=
  uteC0 s + (s + uteB s) * x -
    (s + 1 + uteRho s * (s - 1)) * x ^ 2 / 2

/-- Formula `ute-positive-t` with `a=b`. -/
def uteMiddleGap (s x : ℝ) : ℝ :=
  uteC0 s +
    uteB s * (s + uteB s - s * x) -
    uteB s ^ 2 / 2 +
    uteGamma s * x ^ 2 / 2

/-- The binary branch after `t=0`, `a=b`, `d=x-b`. -/
def uteLargeGap (s x : ℝ) : ℝ :=
  1 / 2 +
    (s + 1) * (uteB s - uteB s ^ 2 / 2) +
    (1 - uteB s) * (x - uteB s) +
    s * (x - uteB s) ^ 2 / 2 -
    uteRho s * (1 / 2 + s * x ^ 2 / 2)

theorem uteEndpointGap_eq_small
    {s x : ℝ} (hs1 : 1 ≤ s)
    (_hx0 : 0 ≤ x) (hxb : x ≤ uteB s) :
    uteEndpointGap s x = uteSmallGap s x := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hbc : uteB s ≤ uteChi s := by
    exact (uteB_lt_chi hs1).le
  have hdx : x - uteB s ≤ 0 := sub_nonpos.mpr hxb
  have htx : 0 ≤ uteChi s - x := sub_nonneg.mpr (hxb.trans hbc)
  have hrho := (uteRho_pos hs).ne'
  rw [uteEndpointGap, uteReducedA, uteReducedO,
    min_eq_right hxb, max_eq_left hdx, max_eq_right htx]
  unfold uteA uteO uteSmallGap uteC0
  rw [uteChi_eq_one_sub_b_div_rho hs]
  field_simp [hrho]
  ring

theorem uteEndpointGap_eq_middle
    {s x : ℝ} (hs : 0 < s)
    (hbx : uteB s ≤ x) (hxc : x ≤ uteChi s) :
    uteEndpointGap s x = uteMiddleGap s x := by
  have hdx : 0 ≤ x - uteB s := sub_nonneg.mpr hbx
  have htx : 0 ≤ uteChi s - x := sub_nonneg.mpr hxc
  have hrho := (uteRho_pos hs).ne'
  rw [uteEndpointGap, uteReducedA, uteReducedO,
    min_eq_left hbx, max_eq_right hdx, max_eq_right htx]
  unfold uteA uteO uteMiddleGap uteC0 uteGamma
  rw [uteChi_eq_one_sub_b_div_rho hs]
  field_simp [hrho]
  ring

theorem uteEndpointGap_eq_large
    {s x : ℝ} (hs1 : 1 ≤ s)
    (hcx : uteChi s ≤ x) :
    uteEndpointGap s x = uteLargeGap s x := by
  have hbx : uteB s ≤ x :=
    (uteB_lt_chi hs1).le.trans hcx
  have hdx : 0 ≤ x - uteB s := sub_nonneg.mpr hbx
  have htx : uteChi s - x ≤ 0 := sub_nonpos.mpr hcx
  rw [uteEndpointGap, uteReducedA, uteReducedO,
    min_eq_left hbx, max_eq_right hdx, max_eq_left htx]
  unfold uteA uteO uteLargeGap
  ring

/-! ## The large branch: binary tangency -/

theorem uteLargeGap_tangent_identity
    {s x : ℝ} (hs : 0 < s) :
    uteLargeGap s x +
        s * (uteRho s - 1) * (x - uteAlpha s) ^ 2 / 2 =
      -rhoPolynomial s (uteRho s) / (2 * uteD s) := by
  have hD := (uteD_pos hs).ne'
  unfold uteLargeGap uteB uteAlpha
  field_simp [hD]
  unfold uteD uteK rhoPolynomial
  ring

theorem uteLargeGap_completeSquare
    {s x : ℝ} (hs : 0 < s) :
    uteLargeGap s x =
      -s * (uteRho s - 1) * (x - uteAlpha s) ^ 2 / 2 := by
  have hidentity := uteLargeGap_tangent_identity (s := s) (x := x) hs
  rw [uteRho_root hs] at hidentity
  norm_num at hidentity ⊢
  linarith

theorem uteLargeGap_nonpos
    {s x : ℝ} (hs : 0 < s) :
    uteLargeGap s x ≤ 0 := by
  rw [uteLargeGap_completeSquare hs]
  have hrho : 0 < uteRho s - 1 :=
    sub_pos.mpr (uteRho_gt_one hs)
  have hprod :
      0 ≤ s * (uteRho s - 1) * (x - uteAlpha s) ^ 2 :=
    mul_nonneg (mul_nonneg hs.le hrho.le) (sq_nonneg _)
  nlinarith

/-! ## Endpoint identities for the small and middle branches -/

def uteSmallSlopeAtB (s : ℝ) : ℝ :=
  (s + uteB s) -
    (s + 1 + uteRho s * (s - 1)) * uteB s

theorem ute_small_slope_identity
    {s : ℝ} (hs : 0 < s) :
    uteD s * uteSmallSlopeAtB s =
      uteRho s *
        (1 + s ^ 2 + uteRho s * s ^ 2 * (s - 1)) := by
  have hD := (uteD_pos hs).ne'
  unfold uteSmallSlopeAtB uteB
  field_simp [hD]
  unfold uteD uteK
  ring

theorem uteSmallSlopeAtB_pos
    {s : ℝ} (hs1 : 1 ≤ s) :
    0 < uteSmallSlopeAtB s := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hidentity := ute_small_slope_identity hs
  have hD := uteD_pos hs
  have hrho := uteRho_pos hs
  have hbracket :
      0 <
        1 + s ^ 2 + uteRho s * s ^ 2 * (s - 1) := by
    have hlast :
        0 ≤ uteRho s * s ^ 2 * (s - 1) :=
      mul_nonneg
        (mul_nonneg hrho.le (sq_nonneg s))
        (sub_nonneg.mpr hs1)
    nlinarith [sq_nonneg s]
  have hrhs :
      0 <
        uteRho s *
          (1 + s ^ 2 + uteRho s * s ^ 2 * (s - 1)) :=
    mul_pos hrho hbracket
  by_contra hle
  have hnonpos : uteSmallSlopeAtB s ≤ 0 := le_of_not_gt hle
  have hmul : uteD s * uteSmallSlopeAtB s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD.le hnonpos
  rw [hidentity] at hmul
  linarith

theorem uteSmallGap_sub_identity (s x : ℝ) :
    uteSmallGap s (uteB s) - uteSmallGap s x =
      (uteB s - x) *
        ((s + uteB s) -
          (s + 1 + uteRho s * (s - 1)) *
            (uteB s + x) / 2) := by
  unfold uteSmallGap
  ring

theorem uteSmallGap_le_at_b
    {s x : ℝ} (hs1 : 1 ≤ s)
    (_hx0 : 0 ≤ x) (hxb : x ≤ uteB s) :
    uteSmallGap s x ≤ uteSmallGap s (uteB s) := by
  have hH :
      0 ≤ s + 1 + uteRho s * (s - 1) := by
    have hs : 0 < s := zero_lt_one.trans_le hs1
    have hprod :
        0 ≤ uteRho s * (s - 1) :=
      mul_nonneg (uteRho_pos hs).le (sub_nonneg.mpr hs1)
    linarith
  have haverage :
      uteSmallSlopeAtB s ≤
        (s + uteB s) -
          (s + 1 + uteRho s * (s - 1)) *
            (uteB s + x) / 2 := by
    unfold uteSmallSlopeAtB
    have hmul :=
      mul_le_mul_of_nonneg_left hxb hH
    nlinarith
  have hfactor :
      0 ≤
        (s + uteB s) -
          (s + 1 + uteRho s * (s - 1)) *
            (uteB s + x) / 2 :=
    (uteSmallSlopeAtB_pos hs1).le.trans haverage
  rw [← sub_nonneg]
  rw [uteSmallGap_sub_identity]
  exact mul_nonneg (sub_nonneg.mpr hxb) hfactor

theorem uteSmallGap_at_b_eq_middle (s : ℝ) :
    uteSmallGap s (uteB s) =
      uteMiddleGap s (uteB s) := by
  unfold uteSmallGap uteMiddleGap uteGamma
  ring

theorem uteMiddleGap_at_chi_eq_large
    {s : ℝ} (hs : 0 < s) :
    uteMiddleGap s (uteChi s) =
      uteLargeGap s (uteChi s) := by
  have hrho := (uteRho_pos hs).ne'
  unfold uteMiddleGap uteLargeGap uteC0 uteGamma
  rw [uteChi_eq_one_sub_b_div_rho hs]
  field_simp [hrho]
  ring

theorem uteMiddleGap_endpoint_difference (s : ℝ) :
    uteMiddleGap s (uteB s) -
        uteMiddleGap s (uteChi s) =
      (uteChi s - uteB s) / 2 *
        (2 * s * uteB s -
          uteGamma s * (uteB s + uteChi s)) := by
  unfold uteMiddleGap
  ring

theorem uteMiddleGap_at_b_le_chi
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    uteMiddleGap s (uteB s) ≤
      uteMiddleGap s (uteChi s) := by
  have hcb : 0 < uteChi s - uteB s :=
    sub_pos.mpr (uteB_lt_chi hs1)
  have hbracket := ute_small_bracket_pos hs1 hs0
  rw [← sub_nonpos]
  rw [uteMiddleGap_endpoint_difference]
  have hright :
      2 * s * uteB s -
          uteGamma s * (uteB s + uteChi s) < 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hcb.le zero_le_two) hright.le

theorem uteMiddleGap_at_chi_nonpos
    {s : ℝ} (hs1 : 1 ≤ s) :
    uteMiddleGap s (uteChi s) ≤ 0 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  rw [uteMiddleGap_at_chi_eq_large hs]
  exact uteLargeGap_nonpos hs

theorem uteMiddleGap_at_b_nonpos
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    uteMiddleGap s (uteB s) ≤ 0 :=
  (uteMiddleGap_at_b_le_chi hs1 hs0).trans
    (uteMiddleGap_at_chi_nonpos hs1)

theorem uteMiddleGap_chord_identity (s x : ℝ) :
    (uteChi s - uteB s) * uteMiddleGap s x =
      (uteChi s - x) * uteMiddleGap s (uteB s) +
        (x - uteB s) * uteMiddleGap s (uteChi s) -
        uteGamma s * (x - uteB s) *
          (uteChi s - uteB s) * (uteChi s - x) / 2 := by
  unfold uteMiddleGap
  ring

theorem uteMiddleGap_nonpos
    {s x : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (hbx : uteB s ≤ x) (hxc : x ≤ uteChi s) :
    uteMiddleGap s x ≤ 0 := by
  have hcb : 0 < uteChi s - uteB s :=
    sub_pos.mpr (uteB_lt_chi hs1)
  have hleft :
      (uteChi s - x) * uteMiddleGap s (uteB s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hxc)
      (uteMiddleGap_at_b_nonpos hs1 hs0)
  have hright :
      (x - uteB s) * uteMiddleGap s (uteChi s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hbx)
      (uteMiddleGap_at_chi_nonpos hs1)
  have hcurve :
      0 ≤
        uteGamma s * (x - uteB s) *
          (uteChi s - uteB s) * (uteChi s - x) / 2 := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (uteGamma_pos hs1 hs0).le
            (sub_nonneg.mpr hbx))
          hcb.le)
        (sub_nonneg.mpr hxc))
      zero_le_two
  have hmul :
      (uteChi s - uteB s) * uteMiddleGap s x ≤ 0 := by
    rw [uteMiddleGap_chord_identity]
    linarith
  by_contra hpos
  have hstrict : 0 < uteMiddleGap s x := lt_of_not_ge hpos
  have := mul_pos hcb hstrict
  linarith

theorem uteSmallGap_nonpos
    {s x : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (hx0 : 0 ≤ x) (hxb : x ≤ uteB s) :
    uteSmallGap s x ≤ 0 := by
  calc
    uteSmallGap s x ≤ uteSmallGap s (uteB s) :=
      uteSmallGap_le_at_b hs1 hx0 hxb
    _ = uteMiddleGap s (uteB s) :=
      uteSmallGap_at_b_eq_middle s
    _ ≤ 0 := uteMiddleGap_at_b_nonpos hs1 hs0

/-! ## Global endpoint certificate -/

theorem uteEndpointGap_nonpos
    {s x : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (hx0 : 0 ≤ x) :
    uteEndpointGap s x ≤ 0 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  by_cases hxb : x ≤ uteB s
  · rw [uteEndpointGap_eq_small hs1 hx0 hxb]
    exact uteSmallGap_nonpos hs1 hs0 hx0 hxb
  · have hbx : uteB s ≤ x := le_of_lt (lt_of_not_ge hxb)
    by_cases hxc : x ≤ uteChi s
    · rw [uteEndpointGap_eq_middle hs hbx hxc]
      exact uteMiddleGap_nonpos hs1 hs0 hbx hxc
    · have hcx : uteChi s ≤ x := le_of_lt (lt_of_not_ge hxc)
      rw [uteEndpointGap_eq_large hs1 hcx]
      exact uteLargeGap_nonpos hs

/-- The paper's natural feasible domain is `0 ≤ x ≤ 1`; the upper bound is
not needed because the large tangent quadratic is globally nonpositive. -/
theorem uteEndpointGap_nonpos_on_unit
    {s x : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    uteEndpointGap s x ≤ 0 :=
  uteEndpointGap_nonpos hs1 hs0 hx.1

end

end SchedulingPaper
