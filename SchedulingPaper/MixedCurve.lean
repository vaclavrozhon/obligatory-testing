import SchedulingPaper.BinaryCurve
import SchedulingPaper.Constants

/-!
# The analytic mixed branch

This file formalizes the scalar system defining the last finite branch of
the competitive-ratio curve.  Its two sides are

`artanh m - m` and `1 - 1 / c + (1 / 2) * log (1 + 2 / c)`,

and the cap parameter is `u = 1 + 2 / c - m`.
-/

namespace SchedulingPaper

noncomputable section

open Set

/-- The mass side `h(m)=artanh(m)-m` of the mixed-branch equation. -/
def mixedMassSide (m : ℝ) : ℝ := Real.artanh m - m

/-- The ratio side `g(c)` of the mixed-branch equation. -/
def mixedRatioSide (c : ℝ) : ℝ :=
  1 - 1 / c + (1 / 2) * Real.log (1 + 2 / c)

/-- The cap represented by a solution `(c,m)` of the mixed equation. -/
def mixedUpperParameter (c m : ℝ) : ℝ := 1 + 2 / c - m

theorem goldenRatio_gt_one : 1 < goldenRatio := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  unfold goldenRatio
  nlinarith

theorem goldenRatio_lt_two : goldenRatio < 2 := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  unfold goldenRatio
  nlinarith

theorem inv_goldenRatio_eq_sub_one :
    1 / goldenRatio = goldenRatio - 1 := by
  apply (mul_left_cancel₀ goldenRatio_pos.ne')
  rw [mul_div_cancel₀ _ goldenRatio_pos.ne']
  exact goldenRatio_mul_sub_one.symm

theorem inv_goldenRatio_pos : 0 < 1 / goldenRatio :=
  one_div_pos.mpr goldenRatio_pos

theorem inv_goldenRatio_lt_one : 1 / goldenRatio < 1 := by
  rw [inv_goldenRatio_eq_sub_one]
  linarith [goldenRatio_lt_two]

theorem mixedMassSide_eq_half_log {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    mixedMassSide m =
      (1 / 2) * Real.log ((1 + m) / (1 - m)) - m := by
  rw [mixedMassSide, Real.artanh_eq_half_log hm]

theorem mixedMassSide_zero : mixedMassSide 0 = 0 := by
  simp [mixedMassSide]

/-- On `(-1,1)`, `h'(m)=m²/(1-m²)`. -/
theorem mixedMassSide_hasDerivAt {m : ℝ} (hm₁ : -1 < m) (hm₂ : m < 1) :
    HasDerivAt mixedMassSide (m ^ 2 / (1 - m ^ 2)) m := by
  have hlog :=
    Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
      (y := m) 1 hm₁ hm₂
  have hlog' :
      HasDerivAt
        (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x)) - x)
        (m ^ 2 / (1 - m ^ 2)) m := by
    simpa using hlog
  apply hlog'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hm₁ hm₂] with x hx
  exact mixedMassSide_eq_half_log ⟨hx.1.le, hx.2.le⟩

/-- The ratio side has derivative `2/(c²(c+2))` for positive `c`. -/
theorem mixedRatioSide_hasDerivAt {c : ℝ} (hc : 0 < c) :
    HasDerivAt mixedRatioSide (2 / (c ^ 2 * (c + 2))) c := by
  have hc0 : c ≠ 0 := hc.ne'
  have harg : 1 + 2 / c ≠ 0 := by positivity
  have hquot :
      HasDerivAt (fun x : ℝ => 2 / x) (-2 / c ^ 2) c := by
    convert (hasDerivAt_const c (2 : ℝ)).div (hasDerivAt_id c) hc0 using 1
    simp only [id_eq]
    field_simp [hc0]
    ring
  have hwhole :=
    ((hasDerivAt_const c (1 : ℝ)).sub
        ((hasDerivAt_const c (1 : ℝ)).div (hasDerivAt_id c) hc0)).add
      (((hasDerivAt_const c (1 / 2 : ℝ))).mul
        (((hasDerivAt_const c (1 : ℝ)).add hquot).log harg))
  convert hwhole using 1
  simp only [id_eq, Pi.add_apply]
  field_simp [hc0, show c + 2 ≠ 0 by positivity]
  ring

theorem mixedMassSide_continuousOn :
    ContinuousOn mixedMassSide (Icc 0 (1 / goldenRatio)) := by
  intro m hm
  have hm₁ : -1 < m := by linarith [hm.1]
  have hm₂ : m < 1 := hm.2.trans_lt inv_goldenRatio_lt_one
  exact (mixedMassSide_hasDerivAt hm₁ hm₂).continuousAt.continuousWithinAt

/-- The mass side is strictly increasing on the complete mixed interval. -/
theorem mixedMassSide_strictMonoOn :
    StrictMonoOn mixedMassSide (Icc 0 (1 / goldenRatio)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) mixedMassSide_continuousOn ?_
  intro m hm
  simp only [interior_Icc, Set.mem_Ioo] at hm
  have hm₁ : -1 < m := by linarith
  have hm₂ : m < 1 := hm.2.trans inv_goldenRatio_lt_one
  rw [(mixedMassSide_hasDerivAt hm₁ hm₂).deriv]
  have hden : 0 < 1 - m ^ 2 := by nlinarith
  exact div_pos (sq_pos_of_pos hm.1) hden

theorem mixedRatioSide_continuousOn :
    ContinuousOn mixedRatioSide (Ioi 0) := by
  intro c hc
  exact (mixedRatioSide_hasDerivAt hc).continuousAt.continuousWithinAt

/-- The ratio side is strictly increasing for positive ratios. -/
theorem mixedRatioSide_strictMonoOn :
    StrictMonoOn mixedRatioSide (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
    mixedRatioSide_continuousOn ?_
  intro c hc
  simp only [interior_Ioi, Set.mem_Ioi] at hc
  rw [(mixedRatioSide_hasDerivAt hc).deriv]
  positivity

theorem two_div_rhoStar :
    2 / rhoStar = zStar - 1 := by
  have hz : zStar - 1 ≠ 0 := by linarith [zStar_gt_one]
  unfold rhoStar
  field_simp [hz]

theorem one_div_rhoStar :
    1 / rhoStar = (zStar - 1) / 2 := by
  have hr : rhoStar ≠ 0 := rhoStar_pos.ne'
  calc
    1 / rhoStar = (2 / rhoStar) / 2 := by field_simp [hr]
    _ = (zStar - 1) / 2 := by rw [two_div_rhoStar]

/-- At the obligatory-testing end, both sides of the mixed equation vanish. -/
theorem mixedRatioSide_rhoStar :
    mixedRatioSide rhoStar = mixedMassSide 0 := by
  rw [mixedMassSide_zero]
  unfold mixedRatioSide
  rw [one_div_rhoStar, two_div_rhoStar]
  have hzlog := zStar_equation
  norm_num only [one_div]
  rw [show 1 + (zStar - 1) = zStar by ring]
  linarith

theorem one_div_inv_goldenRatio :
    1 / (1 / goldenRatio) = goldenRatio := by
  field_simp [goldenRatio_pos.ne']

theorem two_div_inv_goldenRatio :
    2 / (1 / goldenRatio) = 2 * goldenRatio := by
  field_simp [goldenRatio_pos.ne']

theorem golden_log_argument_identity :
    (1 + 1 / goldenRatio) / (1 - 1 / goldenRatio) =
      1 + 2 / (1 / goldenRatio) := by
  rw [two_div_inv_goldenRatio, inv_goldenRatio_eq_sub_one]
  have hden : 2 - goldenRatio ≠ 0 := by
    linarith [goldenRatio_lt_two]
  rw [show 1 + (goldenRatio - 1) = goldenRatio by ring,
    show 1 - (goldenRatio - 1) = 2 - goldenRatio by ring]
  rw [div_eq_iff hden]
  nlinarith [goldenRatio_sq]

/-- At the binary/mixed join the two analytic sides agree exactly. -/
theorem mixedRatioSide_inv_goldenRatio :
    mixedRatioSide (1 / goldenRatio) =
      mixedMassSide (1 / goldenRatio) := by
  have hm : (1 / goldenRatio : ℝ) ∈ Icc (-1) 1 :=
    ⟨by linarith [inv_goldenRatio_pos],
      inv_goldenRatio_lt_one.le⟩
  rw [mixedMassSide_eq_half_log hm]
  unfold mixedRatioSide
  rw [one_div_inv_goldenRatio, golden_log_argument_identity]
  rw [inv_goldenRatio_eq_sub_one]
  ring

theorem mixedMassSide_inv_goldenRatio_pos :
    0 < mixedMassSide (1 / goldenRatio) := by
  rw [← mixedMassSide_zero]
  exact mixedMassSide_strictMonoOn
    ⟨le_rfl, inv_goldenRatio_pos.le⟩
    ⟨inv_goldenRatio_pos.le, le_rfl⟩
    inv_goldenRatio_pos

/-- The interval for the ratio parameter `c` is nonempty. -/
theorem rhoStar_lt_inv_goldenRatio :
    rhoStar < 1 / goldenRatio := by
  apply (mixedRatioSide_strictMonoOn.lt_iff_lt rhoStar_pos
    inv_goldenRatio_pos).mp
  rw [mixedRatioSide_rhoStar, mixedMassSide_zero,
    mixedRatioSide_inv_goldenRatio]
  exact mixedMassSide_inv_goldenRatio_pos

theorem mixedUpperParameter_rhoStar :
    mixedUpperParameter rhoStar 0 = zStar := by
  unfold mixedUpperParameter
  rw [two_div_rhoStar]
  ring

theorem mixedUpperParameter_inv_goldenRatio :
    mixedUpperParameter (1 / goldenRatio) (1 / goldenRatio) =
      goldenRatio + 2 := by
  unfold mixedUpperParameter
  rw [two_div_inv_goldenRatio, inv_goldenRatio_eq_sub_one]
  ring

theorem mixedRatio_join_binary :
    1 + 1 / goldenRatio = goldenRatio := by
  rw [inv_goldenRatio_eq_sub_one]
  ring

theorem mixedRatio_join_obligatory :
    1 + rhoStar = RStar := by
  rfl

/-- Every admissible ratio parameter determines exactly one admissible mass. -/
theorem existsUnique_mixedMass {c : ℝ}
    (hc : c ∈ Icc rhoStar (1 / goldenRatio)) :
    ∃! m : ℝ,
      m ∈ Icc 0 (1 / goldenRatio) ∧
        mixedMassSide m = mixedRatioSide c := by
  have hcpos : 0 < c := rhoStar_pos.trans_le hc.1
  have hlow :
      mixedMassSide 0 ≤ mixedRatioSide c := by
    rw [← mixedRatioSide_rhoStar]
    exact mixedRatioSide_strictMonoOn.monotoneOn rhoStar_pos hcpos hc.1
  have hupp :
      mixedRatioSide c ≤ mixedMassSide (1 / goldenRatio) := by
    rw [← mixedRatioSide_inv_goldenRatio]
    exact mixedRatioSide_strictMonoOn.monotoneOn hcpos
      inv_goldenRatio_pos hc.2
  obtain ⟨m, hm, hmeq⟩ :=
    (intermediate_value_Icc inv_goldenRatio_pos.le
      mixedMassSide_continuousOn) ⟨hlow, hupp⟩
  refine ⟨m, ⟨hm, hmeq⟩, ?_⟩
  intro y hy
  exact mixedMassSide_strictMonoOn.injOn hy.1 hm
    (hy.2.trans hmeq.symm)

/-- Conversely, every admissible mass determines exactly one ratio parameter. -/
theorem existsUnique_mixedRatio {m : ℝ}
    (hm : m ∈ Icc 0 (1 / goldenRatio)) :
    ∃! c : ℝ,
      c ∈ Icc rhoStar (1 / goldenRatio) ∧
        mixedRatioSide c = mixedMassSide m := by
  have hlow :
      mixedRatioSide rhoStar ≤ mixedMassSide m := by
    rw [mixedRatioSide_rhoStar]
    exact mixedMassSide_strictMonoOn.monotoneOn
      ⟨le_rfl, inv_goldenRatio_pos.le⟩ hm hm.1
  have hupp :
      mixedMassSide m ≤ mixedRatioSide (1 / goldenRatio) := by
    rw [mixedRatioSide_inv_goldenRatio]
    exact mixedMassSide_strictMonoOn.monotoneOn hm
      ⟨inv_goldenRatio_pos.le, le_rfl⟩ hm.2
  have hcont :
      ContinuousOn mixedRatioSide
        (Icc rhoStar (1 / goldenRatio)) :=
    mixedRatioSide_continuousOn.mono fun c hc =>
      rhoStar_pos.trans_le hc.1
  obtain ⟨c, hc, hceq⟩ :=
    (intermediate_value_Icc rhoStar_lt_inv_goldenRatio.le hcont)
      ⟨hlow, hupp⟩
  refine ⟨c, ⟨hc, hceq⟩, ?_⟩
  intro d hd
  have hcpos : 0 < c := rhoStar_pos.trans_le hc.1
  have hdpos : 0 < d := rhoStar_pos.trans_le hd.1.1
  exact (mixedRatioSide_strictMonoOn.injOn hcpos hdpos
    (hceq.trans hd.2.symm)).symm

/-- The compact interval of ratio parameters. -/
abbrev MixedRatioDomain :=
  {c : ℝ // c ∈ Icc rhoStar (1 / goldenRatio)}

/-- The compact interval of mixed masses. -/
abbrev MixedMassDomain :=
  {m : ℝ // m ∈ Icc 0 (1 / goldenRatio)}

/-- The unique mass belonging to an admissible ratio parameter. -/
noncomputable def mixedMass (c : MixedRatioDomain) : MixedMassDomain :=
  ⟨(existsUnique_mixedMass c.property).choose,
    (existsUnique_mixedMass c.property).choose_spec.1.1⟩

theorem mixedMass_equation (c : MixedRatioDomain) :
    mixedMassSide (mixedMass c) = mixedRatioSide c :=
  (existsUnique_mixedMass c.property).choose_spec.1.2

/-- The implicit mass is strictly increasing with `c`. -/
theorem mixedMass_strictMono :
    StrictMono mixedMass := by
  intro c d hcd
  apply (mixedMassSide_strictMonoOn.lt_iff_lt
    (mixedMass c).property (mixedMass d).property).mp
  rw [mixedMass_equation, mixedMass_equation]
  exact mixedRatioSide_strictMonoOn
    (rhoStar_pos.trans_le c.property.1)
    (rhoStar_pos.trans_le d.property.1) hcd

/-- The left endpoint of the ratio-parameter interval. -/
def mixedRatioLower : MixedRatioDomain :=
  ⟨rhoStar, le_rfl, rhoStar_lt_inv_goldenRatio.le⟩

/-- The right endpoint of the ratio-parameter interval. -/
def mixedRatioUpper : MixedRatioDomain :=
  ⟨1 / goldenRatio, rhoStar_lt_inv_goldenRatio.le, le_rfl⟩

theorem mixedMass_lower :
    (mixedMass mixedRatioLower : ℝ) = 0 := by
  apply mixedMassSide_strictMonoOn.injOn
    (mixedMass mixedRatioLower).property
    ⟨le_rfl, inv_goldenRatio_pos.le⟩
  rw [mixedMass_equation]
  exact mixedRatioSide_rhoStar

theorem mixedMass_upper :
    (mixedMass mixedRatioUpper : ℝ) = 1 / goldenRatio := by
  apply mixedMassSide_strictMonoOn.injOn
    (mixedMass mixedRatioUpper).property
    ⟨inv_goldenRatio_pos.le, le_rfl⟩
  rw [mixedMass_equation]
  exact mixedRatioSide_inv_goldenRatio

/-- The cap as a function of the ratio parameter. -/
def mixedUpperCurve (c : MixedRatioDomain) : ℝ :=
  mixedUpperParameter c (mixedMass c)

/-- The cap parameter is strictly decreasing along the mixed branch. -/
theorem mixedUpperCurve_strictAnti :
    StrictAnti mixedUpperCurve := by
  intro c d hcd
  have hcpos : 0 < (c : ℝ) := rhoStar_pos.trans_le c.property.1
  have hinv : 1 / (d : ℝ) < 1 / (c : ℝ) :=
    one_div_lt_one_div_of_lt hcpos hcd
  have htwo : 2 / (d : ℝ) < 2 / (c : ℝ) := by
    calc
      2 / (d : ℝ) = 2 * (1 / (d : ℝ)) := by ring
      _ < 2 * (1 / (c : ℝ)) :=
        mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = 2 / (c : ℝ) := by ring
  have hm : (mixedMass c : ℝ) < mixedMass d :=
    mixedMass_strictMono hcd
  unfold mixedUpperCurve mixedUpperParameter
  linarith

theorem mixedUpperCurve_lower :
    mixedUpperCurve mixedRatioLower = zStar := by
  unfold mixedUpperCurve
  rw [mixedMass_lower]
  exact mixedUpperParameter_rhoStar

theorem mixedUpperCurve_upper :
    mixedUpperCurve mixedRatioUpper = goldenRatio + 2 := by
  unfold mixedUpperCurve
  rw [mixedMass_upper]
  exact mixedUpperParameter_inv_goldenRatio

/-- The competitive ratio carried by a mixed-branch parameter. -/
def mixedCompetitiveRatio (c : MixedRatioDomain) : ℝ := 1 + (c : ℝ)

theorem mixedCompetitiveRatio_strictMono :
    StrictMono mixedCompetitiveRatio := by
  intro c d hcd
  unfold mixedCompetitiveRatio
  change 1 + (c : ℝ) < 1 + (d : ℝ)
  have hcd' : (c : ℝ) < (d : ℝ) := hcd
  simpa [add_comm] using add_lt_add_left hcd' (1 : ℝ)

theorem mixedCompetitiveRatio_lower :
    mixedCompetitiveRatio mixedRatioLower = RStar := by
  exact mixedRatio_join_obligatory

theorem mixedCompetitiveRatio_upper :
    mixedCompetitiveRatio mixedRatioUpper = goldenRatio := by
  exact mixedRatio_join_binary

theorem mixedMass_surjective :
    Function.Surjective mixedMass := by
  intro m
  let hex := existsUnique_mixedRatio m.property
  let c : MixedRatioDomain :=
    ⟨hex.choose, hex.choose_spec.1.1⟩
  refine ⟨c, Subtype.ext ?_⟩
  apply mixedMassSide_strictMonoOn.injOn
    (mixedMass c).property m.property
  rw [mixedMass_equation]
  exact hex.choose_spec.1.2

/-- The two compact parameter intervals are order-isomorphic. -/
noncomputable def mixedMassOrderIso :
    MixedRatioDomain ≃o MixedMassDomain :=
  mixedMass_strictMono.orderIsoOfSurjective mixedMass
    mixedMass_surjective

@[simp]
theorem mixedMassOrderIso_apply (c : MixedRatioDomain) :
    mixedMassOrderIso c = mixedMass c := rfl

theorem mixedMass_continuous :
    Continuous mixedMass := by
  change Continuous (mixedMassOrderIso :
    MixedRatioDomain → MixedMassDomain)
  exact mixedMassOrderIso.continuous

/-- The decreasing cap parametrization is continuous. -/
theorem mixedUpperCurve_continuous :
    Continuous mixedUpperCurve := by
  have hc0 : ∀ c : MixedRatioDomain, (c : ℝ) ≠ 0 := fun c =>
    (rhoStar_pos.trans_le c.property.1).ne'
  have hmass :
      Continuous (fun c : MixedRatioDomain => (mixedMass c : ℝ)) :=
    continuous_subtype_val.comp mixedMass_continuous
  have hquot :
      Continuous (fun c : MixedRatioDomain => (2 : ℝ) / (c : ℝ)) :=
    continuous_const.div continuous_subtype_val hc0
  unfold mixedUpperCurve mixedUpperParameter
  exact (continuous_const.add hquot).sub hmass

theorem goldenRatio_add_two_lt_zStar :
    goldenRatio + 2 < zStar := by
  have hdom : mixedRatioLower < mixedRatioUpper :=
    rhoStar_lt_inv_goldenRatio
  have hcap := mixedUpperCurve_strictAnti hdom
  rw [mixedUpperCurve_upper, mixedUpperCurve_lower] at hcap
  exact hcap

/-- Every cap between the two joins has one and only one ratio parameter. -/
theorem existsUnique_mixedUpperParameter {u : ℝ}
    (hu : u ∈ Icc (goldenRatio + 2) zStar) :
    ∃! c : MixedRatioDomain, mixedUpperCurve c = u := by
  letI : PreconnectedSpace MixedRatioDomain :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hu' :
      u ∈ Icc (mixedUpperCurve mixedRatioUpper)
        (mixedUpperCurve mixedRatioLower) := by
    rw [mixedUpperCurve_upper, mixedUpperCurve_lower]
    exact hu
  obtain ⟨c, hc⟩ :=
    intermediate_value_univ mixedRatioUpper mixedRatioLower
      mixedUpperCurve_continuous hu'
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact mixedUpperCurve_strictAnti.injective (hd.trans hc.symm)

/-- The compact interval of cap values covered by the mixed branch. -/
abbrev MixedUpperDomain :=
  {u : ℝ // u ∈ Icc (goldenRatio + 2) zStar}

/-- The unique ratio parameter belonging to a cap in the mixed interval. -/
noncomputable def mixedRatioAtUpper
    (u : MixedUpperDomain) : MixedRatioDomain :=
  (existsUnique_mixedUpperParameter u.property).choose

theorem mixedRatioAtUpper_equation (u : MixedUpperDomain) :
    mixedUpperCurve (mixedRatioAtUpper u) = u :=
  (existsUnique_mixedUpperParameter u.property).choose_spec.1

/-- Increasing the cap strictly decreases the mixed ratio parameter. -/
theorem mixedRatioAtUpper_strictAnti :
    StrictAnti mixedRatioAtUpper := by
  intro u v huv
  apply mixedUpperCurve_strictAnti.lt_iff_gt.mp
  rw [mixedRatioAtUpper_equation, mixedRatioAtUpper_equation]
  exact huv

/-- The mixed branch as a function of the cap `u`. -/
def mixedFiniteCurve (u : MixedUpperDomain) : ℝ :=
  1 + (mixedRatioAtUpper u : ℝ)

theorem mixedFiniteCurve_strictAnti :
    StrictAnti mixedFiniteCurve := by
  intro u v huv
  unfold mixedFiniteCurve
  have h : (mixedRatioAtUpper v : ℝ) <
      (mixedRatioAtUpper u : ℝ) :=
    mixedRatioAtUpper_strictAnti huv
  simpa [add_comm] using add_lt_add_left h (1 : ℝ)

/-- The cap at the binary join, as an element of the mixed cap interval. -/
def mixedUpperLowerEndpoint : MixedUpperDomain :=
  ⟨goldenRatio + 2, le_rfl, goldenRatio_add_two_lt_zStar.le⟩

/-- The cap at the obligatory-testing join. -/
def mixedUpperUpperEndpoint : MixedUpperDomain :=
  ⟨zStar, goldenRatio_add_two_lt_zStar.le, le_rfl⟩

theorem mixedRatioAtUpper_lowerEndpoint :
    mixedRatioAtUpper mixedUpperLowerEndpoint = mixedRatioUpper := by
  apply mixedUpperCurve_strictAnti.injective
  rw [mixedRatioAtUpper_equation, mixedUpperCurve_upper]
  rfl

theorem mixedRatioAtUpper_upperEndpoint :
    mixedRatioAtUpper mixedUpperUpperEndpoint = mixedRatioLower := by
  apply mixedUpperCurve_strictAnti.injective
  rw [mixedRatioAtUpper_equation, mixedUpperCurve_lower]
  rfl

theorem mixedFiniteCurve_lowerEndpoint :
    mixedFiniteCurve mixedUpperLowerEndpoint = goldenRatio := by
  unfold mixedFiniteCurve
  rw [mixedRatioAtUpper_lowerEndpoint]
  exact mixedCompetitiveRatio_upper

theorem mixedFiniteCurve_upperEndpoint :
    mixedFiniteCurve mixedUpperUpperEndpoint = RStar := by
  unfold mixedFiniteCurve
  rw [mixedRatioAtUpper_upperEndpoint]
  exact mixedCompetitiveRatio_lower

/-- The three equations and interval constraints defining a mixed solution. -/
def IsMixedSolution (u c m : ℝ) : Prop :=
  c ∈ Icc rhoStar (1 / goldenRatio) ∧
    m ∈ Icc 0 (1 / goldenRatio) ∧
      mixedMassSide m = mixedRatioSide c ∧
        mixedUpperParameter c m = u

/-- On the whole mixed cap interval, the original two-variable analytic
system has exactly one solution. -/
theorem existsUnique_mixedSolution {u : ℝ}
    (hu : u ∈ Icc (goldenRatio + 2) zStar) :
    ∃! p : ℝ × ℝ, IsMixedSolution u p.1 p.2 := by
  let us : MixedUpperDomain := ⟨u, hu⟩
  let c : MixedRatioDomain := mixedRatioAtUpper us
  let m : MixedMassDomain := mixedMass c
  refine ⟨((c : ℝ), (m : ℝ)), ?_, ?_⟩
  · refine ⟨c.property, m.property, mixedMass_equation c, ?_⟩
    simpa [c, m, us, mixedUpperCurve] using
      mixedRatioAtUpper_equation us
  · rintro ⟨d, n⟩ hd
    let ds : MixedRatioDomain := ⟨d, hd.1⟩
    have hn :
        n = (mixedMass ds : ℝ) := by
      apply mixedMassSide_strictMonoOn.injOn hd.2.1
        (mixedMass ds).property
      exact hd.2.2.1.trans (mixedMass_equation ds).symm
    have hdu : mixedUpperCurve ds = u := by
      unfold mixedUpperCurve
      rw [← hn]
      exact hd.2.2.2
    have hdc : ds = c := by
      apply mixedUpperCurve_strictAnti.injective
      exact hdu.trans (by
        simpa [c, us] using (mixedRatioAtUpper_equation us).symm)
    apply Prod.ext
    · exact congrArg Subtype.val hdc
    · exact hn.trans (congrArg (fun x : MixedRatioDomain =>
        (mixedMass x : ℝ)) hdc)

end

end SchedulingPaper
