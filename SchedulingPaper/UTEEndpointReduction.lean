import SchedulingPaper.UTEEndpointGame

/-!
# Reduction of the full UTE endpoint game

`UTEEndpointGame` proves that the one-variable optimized gap is nonpositive.
This file verifies the preceding optimization steps for arbitrary feasible
endpoint masses:

1. move immediate-one mass `m` to boundary-deferred mass `t`;
2. maximize the concave `t`-quadratic at `(chi-x)₊`;
3. at fixed `x=a+d`, move as much mass as possible from `d` to the forced
   prefix, giving `a=min b x` and `d=(x-b)₊`.

Thus the scalar UTE certificate now starts from the four masses appearing
directly after coordinatewise endpoint reduction.
-/

namespace SchedulingPaper

noncomputable section

/-- For fixed `a,d`, the gap is maximized over `t ≥ 0` at
`max 0 (chi-(a+d))`. -/
theorem uteGap_le_optimal_t
    {s a d t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    uteGap s a d t 0 ≤
      uteGap s a d (max 0 (uteChi s - (a + d))) 0 := by
  have hrho : 0 < uteRho s := uteRho_pos hs
  have hchi := uteChi_eq_one_sub_b_div_rho hs
  by_cases hxchi : a + d ≤ uteChi s
  · have hstar : 0 ≤ uteChi s - (a + d) :=
      sub_nonneg.mpr hxchi
    rw [max_eq_right hstar]
    have hid :
        uteGap s a d (uteChi s - (a + d)) 0 -
            uteGap s a d t 0 =
          uteRho s / 2 *
            (t - (uteChi s - (a + d))) ^ 2 := by
      unfold uteGap uteA uteO
      rw [hchi]
      field_simp [hrho.ne']
      ring
    rw [← sub_nonneg]
    rw [hid]
    positivity
  · have hstar : uteChi s - (a + d) ≤ 0 :=
      sub_nonpos.mpr (le_of_not_ge hxchi)
    rw [max_eq_left hstar]
    have hid :
        uteGap s a d t 0 - uteGap s a d 0 0 =
          uteRho s * (uteChi s - (a + d)) * t -
            uteRho s * t ^ 2 / 2 := by
      unfold uteGap uteA uteO
      rw [hchi]
      field_simp [hrho.ne']
      ring
    have hlinear :
        uteRho s * (uteChi s - (a + d)) * t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hrho.le hstar) ht
    have hquad : 0 ≤ uteRho s * t ^ 2 / 2 := by positivity
    rw [← sub_nonpos]
    rw [hid]
    linarith

theorem max_zero_sub_eq_sub_min (b x : ℝ) :
    max 0 (x - b) = x - min b x := by
  by_cases hbx : b ≤ x
  · rw [min_eq_left hbx, max_eq_right (sub_nonneg.mpr hbx)]
  · have hxb : x ≤ b := le_of_not_ge hbx
    rw [min_eq_right hxb, max_eq_left (sub_nonpos.mpr hxb)]
    ring

/-- At fixed total capped mass `x=a+d`, moving mass from the suffix cap
endpoint to the forced prefix cannot decrease the gap. -/
theorem uteGap_le_prefix_saturated
    {s a d t : ℝ}
    (hs : 0 < s) (hd : 0 ≤ d)
    (hab : a ≤ uteB s) (hx1 : a + d ≤ 1) :
    uteGap s a d t 0 ≤
      uteGap s
        (min (uteB s) (a + d))
        (max 0 ((a + d) - uteB s)) t 0 := by
  let x := a + d
  let a' := min (uteB s) x
  have hax : a ≤ x := by
    dsimp [x]
    linarith
  have haa' : a ≤ a' := le_min hab hax
  have ha'b : a' ≤ uteB s := min_le_left _ _
  have ha'x : a' ≤ x := min_le_right _ _
  have hs1x : 0 ≤ s * (1 - x) :=
    mul_nonneg hs.le (sub_nonneg.mpr (by simpa [x] using hx1))
  have hfactor :
      0 ≤ s * (1 - x) + uteB s - (a + a') / 2 := by
    nlinarith
  have hdiff :
      uteGap s a' (x - a') t 0 - uteGap s a (x - a) t 0 =
        (a' - a) *
          (s * (1 - x) + uteB s - (a + a') / 2) := by
    unfold uteGap uteA uteO
    ring
  have hnonneg :
      0 ≤ uteGap s a' (x - a') t 0 -
        uteGap s a (x - a) t 0 := by
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr haa') hfactor
  have hdEq : d = x - a := by
    dsimp [x]
    ring
  have hdeferred :
      max 0 (x - uteB s) = x - a' := by
    dsimp [a']
    exact max_zero_sub_eq_sub_min _ _
  change
    uteGap s a d t 0 ≤
      uteGap s a' (max 0 (x - uteB s)) t 0
  rw [hdEq, hdeferred]
  exact sub_nonneg.mp hnonneg

/-- Complete four-mass reduction to `uteEndpointGap`. -/
theorem uteGap_le_endpointGap
    {s a d t m : ℝ}
    (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (had : a ≤ uteB s)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hmass : d + t + m ≤ 1 - uteB s) :
    uteGap s a d t m ≤ uteEndpointGap s (a + d) := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hb0 : 0 ≤ uteB s := uteB_nonneg hs1 hs0
  have hx1 : a + d ≤ 1 := by
    have hdBound : d ≤ 1 - uteB s := by linarith
    linarith
  let t' := t + m
  let tstar := max 0 (uteChi s - (a + d))
  have ht' : 0 ≤ t' := by
    dsimp [t']
    linarith
  have hmove :
      uteGap s a d t m ≤ uteGap s a d t' 0 := by
    simpa [t'] using uteGap_le_move_m_to_t s a d t m
  have htopt :
      uteGap s a d t' 0 ≤ uteGap s a d tstar 0 := by
    simpa [tstar] using
      uteGap_le_optimal_t (s := s) (a := a) (d := d)
        (t := t') hs ht'
  have hprefix :
      uteGap s a d tstar 0 ≤
        uteGap s
          (min (uteB s) (a + d))
          (max 0 ((a + d) - uteB s)) tstar 0 := by
    exact uteGap_le_prefix_saturated hs hd had hx1
  calc
    uteGap s a d t m ≤ uteGap s a d t' 0 := hmove
    _ ≤ uteGap s a d tstar 0 := htopt
    _ ≤ uteGap s
          (min (uteB s) (a + d))
          (max 0 ((a + d) - uteB s)) tstar 0 := hprefix
    _ = uteEndpointGap s (a + d) := by
      rfl

/-- Full scalar endpoint theorem before the one-variable reduction. -/
theorem uteGap_nonpos_of_feasible
    {s a d t m : ℝ}
    (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (ha : 0 ≤ a) (had : a ≤ uteB s)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hmass : d + t + m ≤ 1 - uteB s) :
    uteGap s a d t m ≤ 0 := by
  exact (uteGap_le_endpointGap hs1 hs0 had hd ht hm hmass).trans
    (uteEndpointGap_nonpos hs1 hs0 (by linarith))

end

end SchedulingPaper
