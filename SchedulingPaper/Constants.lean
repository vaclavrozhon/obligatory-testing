import Mathlib

/-!
# The analytic constant at the obligatory-testing endpoint

This file formalizes the one-variable calculation in the harmonic lower
bound.  The constant `zStar` is the unique real number greater than one
satisfying

`zStar - 3 = log zStar`.

The paper's endpoint ratio is then `RStar = 1 + 2 / (zStar - 1)`.  We also
verify directly that this is the global maximum, on `1 < z`, of the
one-variable ratio obtained from the harmonic construction.
-/

namespace SchedulingPaper

noncomputable section

/-- The root function whose unique zero above one defines `zStar`. -/
def zRootFunction (z : ℝ) : ℝ := z - 3 - Real.log z

theorem zRootFunction_hasDerivAt {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt zRootFunction (1 - z⁻¹) z := by
  simpa [zRootFunction] using
    ((hasDerivAt_id z).sub_const 3).sub (Real.hasDerivAt_log hz)

/-- The defining root function is strictly increasing to the right of one. -/
theorem zRootFunction_strictMonoOn :
    StrictMonoOn zRootFunction (Set.Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (1 : ℝ)) ?_ ?_
  · intro z hz
    have hz' : 1 < z := Set.mem_Ioi.mp hz
    have hz0 : z ≠ 0 := by
      exact ne_of_gt (lt_trans zero_lt_one hz')
    exact (zRootFunction_hasDerivAt hz0).continuousAt.continuousWithinAt
  · intro z hz
    simp only [interior_Ioi, Set.mem_Ioi] at hz
    have hz0 : z ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz)
    rw [(zRootFunction_hasDerivAt hz0).deriv]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hz)

theorem exists_zStar :
    ∃ z : ℝ, 1 < z ∧ z - 3 = Real.log z := by
  have hlogTwo : Real.log (2 : ℝ) < 1 := by
    have h :=
      Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hlogEight : Real.log (8 : ℝ) < 3 := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = (3 : ℝ) * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ < 3 := by linarith
  have hAtEight : 0 < zRootFunction 8 := by
    unfold zRootFunction
    linarith
  have hcont : ContinuousOn zRootFunction (Set.Icc (1 : ℝ) 8) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      have : (1 : ℝ) ≤ z := hz.1
      linarith
    exact (zRootFunction_hasDerivAt hz0).continuousAt.continuousWithinAt
  have hzero :
      (0 : ℝ) ∈ Set.Icc (zRootFunction 1) (zRootFunction 8) := by
    constructor
    · norm_num [zRootFunction]
    · exact hAtEight.le
  obtain ⟨z, hzmem, hzroot⟩ :=
    (intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 8) hcont) hzero
  have hzgt : 1 < z := by
    apply lt_of_le_of_ne hzmem.1
    intro h
    rw [← h] at hzroot
    norm_num [zRootFunction] at hzroot
  refine ⟨z, hzgt, ?_⟩
  unfold zRootFunction at hzroot
  linarith

/-- There is exactly one solution of the paper's defining equation above
one. -/
theorem existsUnique_zStar :
    ∃! z : ℝ, 1 < z ∧ z - 3 = Real.log z := by
  obtain ⟨z, hzgt, hzeq⟩ := exists_zStar
  refine ⟨z, ⟨hzgt, hzeq⟩, ?_⟩
  intro y hy
  symm
  apply zRootFunction_strictMonoOn.injOn hzgt hy.1
  simp only [zRootFunction]
  linarith [hzeq, hy.2]

/-- The unique number `z > 1` satisfying `z - 3 = log z`. -/
def zStar : ℝ := existsUnique_zStar.choose

theorem zStar_gt_one : 1 < zStar :=
  by
    simpa [zStar] using existsUnique_zStar.choose_spec.1.1

theorem zStar_equation : zStar - 3 = Real.log zStar :=
  by
    simpa [zStar] using existsUnique_zStar.choose_spec.1.2

theorem zStar_unique {z : ℝ} (hzgt : 1 < z)
    (hzeq : z - 3 = Real.log z) :
    z = zStar := by
  simpa [zStar] using existsUnique_zStar.choose_spec.2 z ⟨hzgt, hzeq⟩

theorem zStar_gt_three : 3 < zStar := by
  have hlog : 0 < Real.log zStar := Real.log_pos zStar_gt_one
  linarith [zStar_equation]

/-- The excess over one in the exact obligatory-testing ratio. -/
def rhoStar : ℝ := 2 / (zStar - 1)

/-- The exact obligatory-testing ratio from the paper. -/
def RStar : ℝ := 1 + rhoStar

theorem rhoStar_pos : 0 < rhoStar := by
  unfold rhoStar
  exact div_pos (by norm_num) (sub_pos.mpr zStar_gt_one)

theorem rhoStar_lt_one : rhoStar < 1 := by
  unfold rhoStar
  rw [div_lt_one₀ (by linarith [zStar_gt_one] : 0 < zStar - 1)]
  linarith [zStar_gt_three]

theorem one_lt_RStar : 1 < RStar := by
  unfold RStar
  linarith [rhoStar_pos]

/-- Denominator of the one-variable harmonic lower-bound ratio. -/
def obligatoryDenominator (z : ℝ) : ℝ :=
  1 + z + z * Real.log z

/-- Equation (4.24) of the manuscript, written as a function of
`z = (1 + α)²`. -/
def obligatoryRatio (z : ℝ) : ℝ :=
  1 + 2 * (z - 1) / obligatoryDenominator z

theorem obligatoryDenominator_pos {z : ℝ} (hz : 1 < z) :
    0 < obligatoryDenominator z := by
  have hlog : 0 < Real.log z := Real.log_pos hz
  unfold obligatoryDenominator
  nlinarith [mul_pos (by linarith : 0 < z) hlog]

theorem obligatoryDenominator_zStar :
    obligatoryDenominator zStar = (zStar - 1) ^ 2 := by
  unfold obligatoryDenominator
  rw [← zStar_equation]
  ring

theorem obligatoryRatio_zStar :
    obligatoryRatio zStar = RStar := by
  have hz1 : zStar - 1 ≠ 0 := by linarith [zStar_gt_one]
  unfold obligatoryRatio RStar rhoStar
  rw [obligatoryDenominator_zStar]
  field_simp

/-- `RStar` is the global maximum of the harmonic lower-bound ratio on its
natural domain `z > 1`. -/
theorem obligatoryRatio_le_RStar {z : ℝ} (hz : 1 < z) :
    obligatoryRatio z ≤ RStar := by
  have hzpos : 0 < z := by linarith
  have hastarpos : 0 < zStar := by linarith [zStar_gt_one]
  have hzsub : 0 < z - 1 := by linarith
  have hastarsub : 0 < zStar - 1 := by linarith [zStar_gt_one]
  have hden : 0 < obligatoryDenominator z :=
    obligatoryDenominator_pos hz
  have hquotpos : 0 < zStar / z := div_pos hastarpos hzpos
  have hlog :=
    Real.log_le_sub_one_of_pos hquotpos
  have hnonneg :
      0 ≤ z * (zStar / z - 1 - Real.log (zStar / z)) := by
    exact mul_nonneg hzpos.le (by linarith)
  have hidentity :
      z * (zStar / z - 1 - Real.log (zStar / z)) =
        obligatoryDenominator z - (z - 1) * (zStar - 1) := by
    rw [Real.log_div (ne_of_gt hastarpos) (ne_of_gt hzpos),
      ← zStar_equation]
    unfold obligatoryDenominator
    field_simp ; ring
  have hcross :
      (z - 1) * (zStar - 1) ≤ obligatoryDenominator z := by
    linarith [hnonneg, hidentity]
  have hfrac :
      (z - 1) / obligatoryDenominator z ≤ 1 / (zStar - 1) := by
    rw [div_le_div_iff₀ hden hastarsub]
    simpa using hcross
  have hscaled :
      2 * ((z - 1) / obligatoryDenominator z) ≤
        2 * (1 / (zStar - 1)) :=
    mul_le_mul_of_nonneg_left hfrac (by norm_num)
  calc
    obligatoryRatio z =
        1 + 2 * ((z - 1) / obligatoryDenominator z) := by
          unfold obligatoryRatio
          ring
    _ ≤ 1 + 2 * (1 / (zStar - 1)) := by linarith
    _ = RStar := by
      unfold RStar rhoStar
      ring

theorem obligatoryRatio_globalMax :
    IsGreatest (obligatoryRatio '' Set.Ioi 1) RStar := by
  constructor
  · exact ⟨zStar, zStar_gt_one, obligatoryRatio_zStar⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact obligatoryRatio_le_RStar hz

end

end SchedulingPaper
