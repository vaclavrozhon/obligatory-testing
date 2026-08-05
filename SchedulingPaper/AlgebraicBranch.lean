import SchedulingPaper.BinaryCurve

/-!
# The algebraic branch of the finite-cap curve

The third branch is the unique positive root of the quadratic
`rhoPolynomial (u-1)`.  This file proves existence and uniqueness without
using the quadratic formula and verifies both neighboring join values.
-/

namespace SchedulingPaper

noncomputable section

theorem rhoPolynomial_strictMono_nonneg {s x y : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) (hxy : x < y) :
    rhoPolynomial s x < rhoPolynomial s y := by
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hcoef : 0 < s ^ 3 + s ^ 2 + 1 := by positivity
  have hfactor :
      rhoPolynomial s y - rhoPolynomial s x =
        (y - x) * (s * (x + y) + (s ^ 3 + s ^ 2 + 1)) := by
    unfold rhoPolynomial
    ring
  have hbracket :
      0 < s * (x + y) + (s ^ 3 + s ^ 2 + 1) := by
    have : 0 ≤ s * (x + y) :=
      mul_nonneg hs.le (by linarith)
    linarith
  rw [show rhoPolynomial s y =
      rhoPolynomial s x +
        (rhoPolynomial s y - rhoPolynomial s x) by ring, hfactor]
  exact lt_add_of_pos_right _
    (mul_pos (sub_pos.mpr hxy) hbracket)

theorem existsUnique_rhoPolynomial_pos {s : ℝ} (hs : 0 < s) :
    ∃! ρ : ℝ, 0 < ρ ∧ rhoPolynomial s ρ = 0 := by
  let C : ℝ := (s ^ 2 + s + 1) * (s + 2)
  let B : ℝ := s ^ 3 + s ^ 2 + 1
  let M : ℝ := C + 1
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (by nlinarith [sq_nonneg s]) (by linarith)
  have hB : 1 ≤ B := by
    dsimp [B]
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    linarith
  have hM : 0 < M := by
    dsimp [M]
    linarith
  have hzero : rhoPolynomial s 0 < 0 := by
    unfold rhoPolynomial
    dsimp [C] at hC
    linarith
  have hMvalue : 0 < rhoPolynomial s M := by
    have hsquare : 0 ≤ s * M ^ 2 :=
      mul_nonneg hs.le (sq_nonneg M)
    have hlinear : M ≤ B * M :=
      (le_mul_iff_one_le_left hM).2 hB
    unfold rhoPolynomial
    dsimp [C, B, M] at *
    nlinarith
  have hcont : Continuous (rhoPolynomial s) := by
    unfold rhoPolynomial
    fun_prop
  have hmem :
      (0 : ℝ) ∈ Set.Icc (rhoPolynomial s 0) (rhoPolynomial s M) :=
    ⟨hzero.le, hMvalue.le⟩
  obtain ⟨ρ, hρIcc, hρroot⟩ :=
    intermediate_value_Icc hM.le hcont.continuousOn hmem
  have hρpos : 0 < ρ := by
    refine lt_of_le_of_ne hρIcc.1 ?_
    intro hρzero
    rw [← hρzero] at hρroot
    linarith
  refine ⟨ρ, ⟨hρpos, hρroot⟩, ?_⟩
  intro q hq
  rcases hq with ⟨hqpos, hqroot⟩
  by_cases hρq : ρ < q
  · have hlt := rhoPolynomial_strictMono_nonneg hs hρpos.le hρq
    rw [hρroot, hqroot] at hlt
    linarith
  · by_cases hqρ : q < ρ
    · have hlt := rhoPolynomial_strictMono_nonneg hs hqpos.le hqρ
      rw [hρroot, hqroot] at hlt
      linarith
    · exact le_antisymm (le_of_not_gt hρq) (le_of_not_gt hqρ)

/-- The positive algebraic root, totalized by zero outside `u>1`. -/
def rhoI (u : ℝ) : ℝ :=
  if hu : 1 < u then
    (existsUnique_rhoPolynomial_pos (sub_pos.mpr hu)).choose
  else 0

theorem rhoI_spec {u : ℝ} (hu : 1 < u) :
    0 < rhoI u ∧ rhoPolynomial (u - 1) (rhoI u) = 0 := by
  unfold rhoI
  simp only [dif_pos hu]
  exact (existsUnique_rhoPolynomial_pos (sub_pos.mpr hu)).choose_spec.1

theorem rhoI_eq_of_root {u ρ : ℝ}
    (hu : 1 < u) (hρ : 0 < ρ)
    (hroot : rhoPolynomial (u - 1) ρ = 0) :
    rhoI u = ρ := by
  exact (existsUnique_rhoPolynomial_pos (sub_pos.mpr hu)).unique
    (rhoI_spec hu) ⟨hρ, hroot⟩

theorem uDiamond_gt_one : 1 < uDiamond := by
  have hu : 0 < uDiamond := by
    unfold uDiamond
    positivity
  have hprod : 0 < uDiamond * (uDiamond - 1) := by
    rw [uDiamond_mul_sub_one]
    exact goldenRatio_pos
  nlinarith

theorem rhoI_at_uDiamond :
    rhoI uDiamond = uDiamond := by
  apply rhoI_eq_of_root uDiamond_gt_one
  · linarith [uDiamond_gt_one]
  · apply (stoppingTangency_iff_rhoPolynomial uDiamond uDiamond).mp
    rw [stoppingTangency_at_ratio_u,
      uDiamond_transition_polynomial]
    norm_num

theorem sZero_positive : 0 < sZero := by
  linarith [sZero_spec.1]

theorem rhoPolynomial_sZero_zero :
    rhoPolynomial sZero (1 + 1 / Real.sqrt sZero) = 0 := by
  have hs := sZero_positive
  have ht : 0 < Real.sqrt sZero := Real.sqrt_pos.2 hs
  have htSq : (Real.sqrt sZero) ^ 2 = sZero :=
    Real.sq_sqrt hs.le
  have hrelation := sZero_spec.2.2
  have hsq :
      (Real.sqrt sZero * sZero) ^ 2 = (sZero + 1) ^ 2 := by
    calc
      (Real.sqrt sZero * sZero) ^ 2 =
          (Real.sqrt sZero) ^ 2 * sZero ^ 2 := by ring
      _ = sZero ^ 3 := by rw [htSq]; ring
      _ = (sZero + 1) ^ 2 := hrelation
  have hsum :
      0 < Real.sqrt sZero * sZero + (sZero + 1) := by positivity
  have hfactor :
      (Real.sqrt sZero * sZero - (sZero + 1)) *
          (Real.sqrt sZero * sZero + (sZero + 1)) = 0 := by
    nlinarith
  have hrootProduct :
      Real.sqrt sZero * sZero = sZero + 1 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  unfold rhoPolynomial
  field_simp [ht.ne']
  have hmul :
      Real.sqrt sZero * sZero ^ 3 =
        (sZero + 1) * sZero ^ 2 := by
    calc
      Real.sqrt sZero * sZero ^ 3 =
          (Real.sqrt sZero * sZero) * sZero ^ 2 := by ring
      _ = (sZero + 1) * sZero ^ 2 := by rw [hrootProduct]
  nlinarith

theorem rhoI_at_uZero :
    rhoI uZero = 1 + 1 / Real.sqrt sZero := by
  have hu : 1 < uZero := by linarith [uZero_bounds.1]
  apply rhoI_eq_of_root hu
  · have := Real.sqrt_pos.2 sZero_positive
    positivity
  · simpa [uZero] using rhoPolynomial_sZero_zero

end

end SchedulingPaper
