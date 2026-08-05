import SchedulingPaper.BankAccounting

/-!
# Raw-state bounds along Taylor steps
-/

namespace SchedulingPaper

noncomputable section

namespace AnalysisState

def etaNumerator (s : AnalysisState) : ℝ :=
  s.deferred - RStar * s.substantive

def yNumerator (s : AnalysisState) : ℝ :=
  s.deferred - RStar * s.substantive - RStar * s.epsilon

theorem eta_eq_etaNumerator_div (s : AnalysisState) :
    s.eta = s.etaNumerator / s.x := by
  rfl

theorem y_eq_yNumerator_div (s : AnalysisState) :
    s.y = s.yNumerator / s.x := by
  unfold y yNumerator eta b
  ring

theorem etaNumerator_nonpos {s : AnalysisState} (hs : s.Feasible) :
    s.etaNumerator ≤ 0 := by
  unfold etaNumerator
  have hR : 1 ≤ RStar := one_lt_RStar.le
  have hRS : s.substantive ≤ RStar * s.substantive := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hs.2.1]
  linarith [hs.2.2.2.2]

theorem yNumerator_nonpos {s : AnalysisState} (hs : s.Feasible) :
    s.yNumerator ≤ 0 := by
  unfold yNumerator
  have hη := etaNumerator_nonpos hs
  unfold etaNumerator at hη
  have hRe : 0 ≤ RStar * s.epsilon :=
    mul_nonneg (lt_trans zero_lt_one one_lt_RStar).le hs.2.2.1
  linarith

/-- The affine segment from a raw state to one of its four unit updates. -/
def interpolatedStep (s : AnalysisState) (q : BoundaryOutcome)
    (t : ℝ) : AnalysisState :=
  match q with
  | .zero =>
      { s with x := s.x - t }
  | .epsilon =>
      { s with x := s.x - t, epsilon := s.epsilon + t }
  | .immediate =>
      { s with x := s.x - t, substantive := s.substantive + t }
  | .deferred =>
      { s with
        x := s.x - t
        substantive := s.substantive + t
        deferred := s.deferred + t }

@[simp] theorem interpolatedStep_one
    (s : AnalysisState) (q : BoundaryOutcome) :
    s.interpolatedStep q 1 = s.step q := by
  cases q <;> rfl

@[simp] theorem interpolatedStep_zero
    (s : AnalysisState) (q : BoundaryOutcome) :
    s.interpolatedStep q 0 = s := by
  cases s
  cases q <;> simp [interpolatedStep]

/-- Feasibility is preserved along every unit-step segment while at least
two units of mass remain. -/
theorem interpolatedStep_feasible
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s.interpolatedStep q t).Feasible := by
  rcases hs with ⟨hx0, hS, he, hd, hdS⟩
  cases q <;>
    simp only [interpolatedStep, Feasible] <;>
    constructor
  · linarith [ht.2]
  · exact ⟨hS, he, hd, hdS⟩
  · linarith [ht.2]
  · exact ⟨hS, by linarith [ht.1], hd, hdS⟩
  · linarith [ht.2]
  · exact ⟨by linarith [ht.1], he, hd, by linarith [ht.1]⟩
  · linarith [ht.2]
  · exact ⟨by linarith [ht.1], he, by linarith [ht.1],
      by linarith⟩

theorem step_feasible
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) :
    (s.step q).Feasible := by
  have h := interpolatedStep_feasible hs hx q
    (t := 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  simpa using h

def etaStepRate : BoundaryOutcome → ℝ
  | .zero | .epsilon => 0
  | .immediate => -RStar
  | .deferred => 1 - RStar

def yStepRate : BoundaryOutcome → ℝ
  | .zero => 0
  | .epsilon | .immediate => -RStar
  | .deferred => 1 - RStar

/-- Exact fractional-linear form of `η` along an interpolated step. -/
theorem interpolatedStep_eta_formula
    {s : AnalysisState} (q : BoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).eta =
      (s.x * s.eta + etaStepRate q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, etaStepRate, eta] <;>
    field_simp [hx, hxt] <;>
    ring

/-- Exact fractional-linear form of `y` along an interpolated step. -/
theorem interpolatedStep_y_formula
    {s : AnalysisState} (q : BoundaryOutcome) (t : ℝ)
    (hx : s.x ≠ 0) (hxt : s.x - t ≠ 0) :
    (s.interpolatedStep q t).y =
      (s.x * s.y + yStepRate q * t) / (s.x - t) := by
  cases q <;>
    simp only [interpolatedStep, yStepRate, y, eta, b] <;>
    field_simp [hx, hxt] <;>
    ring

private theorem linearFraction_antitone
    {x z δ t u : ℝ}
    (hx : 1 < x) (hzδ : z + δ ≤ 0)
    (htu : t ≤ u) (hu : u ≤ 1) :
    (x * z + δ * u) / (x - u) ≤
      (x * z + δ * t) / (x - t) := by
  have hxu : 0 < x - u := by linarith
  have hxt : 0 < x - t := by linarith
  apply (div_le_div_iff₀ hxu hxt).2
  have hprod :
      0 ≤ x * (u - t) * (-(z + δ)) :=
    mul_nonneg
      (mul_nonneg (by linarith) (sub_nonneg.mpr htu))
      (neg_nonneg.mpr hzδ)
  nlinarith

/-- `η` is antitone on the whole interpolated unit-step segment. -/
theorem eta_interpolatedStep_antitone
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t u : ℝ}
    (htu : t ≤ u) (hu : u ≤ 1) :
    (s.interpolatedStep q u).eta ≤
      (s.interpolatedStep q t).eta := by
  have hx1 : 1 < s.x := lt_of_lt_of_le (by norm_num) hx
  have hxu : s.x - u ≠ 0 := ne_of_gt (by linarith)
  have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith)
  rw [interpolatedStep_eta_formula q u hs.1.ne' hxu,
    interpolatedStep_eta_formula q t hs.1.ne' hxt]
  apply linearFraction_antitone hx1
  · have hη := eta_nonpos hs
    cases q <;> simp only [etaStepRate] <;>
      nlinarith [one_lt_RStar]
  · exact htu
  · exact hu

/-- `y` is antitone on the whole interpolated unit-step segment. -/
theorem y_interpolatedStep_antitone
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t u : ℝ}
    (htu : t ≤ u) (hu : u ≤ 1) :
    (s.interpolatedStep q u).y ≤
      (s.interpolatedStep q t).y := by
  have hx1 : 1 < s.x := lt_of_lt_of_le (by norm_num) hx
  have hxu : s.x - u ≠ 0 := ne_of_gt (by linarith)
  have hxt : s.x - t ≠ 0 := ne_of_gt (by linarith)
  rw [interpolatedStep_y_formula q u hs.1.ne' hxu,
    interpolatedStep_y_formula q t hs.1.ne' hxt]
  apply linearFraction_antitone hx1
  · have hy := y_nonpos hs
    cases q <;> simp only [yStepRate] <;>
      nlinarith [one_lt_RStar]
  · exact htu
  · exact hu

/-- `η` is nonincreasing along every point of each unit-step segment. -/
theorem eta_interpolatedStep_le
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s.interpolatedStep q t).eta ≤ s.eta := by
  have h := eta_interpolatedStep_antitone hs hx q
    (t := 0) (u := t) ht.1 ht.2
  simpa using h

/-- `y` is nonincreasing along every point of each unit-step segment. -/
theorem y_interpolatedStep_le
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s.interpolatedStep q t).y ≤ s.y := by
  have h := y_interpolatedStep_antitone hs hx q
    (t := 0) (u := t) ht.1 ht.2
  simpa using h

theorem eta_step_le
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) :
    (s.step q).eta ≤ s.eta := by
  have h := eta_interpolatedStep_le hs hx q
    (t := 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  simpa using h

theorem y_step_le
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) :
    (s.step q).y ≤ s.y := by
  have h := y_interpolatedStep_le hs hx q
    (t := 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  simpa using h

theorem normalized_step_mono
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) :
    (s.step q).y ≤ s.y ∧ (s.step q).eta ≤ s.eta :=
  ⟨y_step_le hs hx q, eta_step_le hs hx q⟩

theorem flat_persists_interpolated
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : s.y < -1) :
    (s.interpolatedStep q t).y < -1 :=
  lt_of_le_of_lt (y_interpolatedStep_le hs hx q ht) hy

theorem flat_persists_after_step
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) (hy : s.y < -1) :
    (s.step q).y < -1 :=
  lt_of_le_of_lt (y_step_le hs hx q) hy

theorem y_le_eta {s : AnalysisState} (hs : s.Feasible) :
    s.y ≤ s.eta := by
  rw [eta_eq_y_add s]
  exact le_add_of_nonneg_right
    (mul_nonneg (lt_trans zero_lt_one one_lt_RStar).le (b_nonneg hs))

/-- Feasible active normalized coordinates lie in the fixed triangle
`-1 ≤ y ≤ η ≤ 0`, with `0 ≤ b ≤ 1 / RStar`. -/
theorem active_eta_b_bounds
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    -1 ≤ s.y ∧ s.y ≤ s.eta ∧ s.eta ≤ 0 ∧
      0 ≤ s.b ∧ s.b ≤ 1 / RStar := by
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  have hyη := y_le_eta hs
  have hη := eta_nonpos hs
  have hb := b_nonneg hs
  have hetaEq := eta_eq_y_add s
  have hRb : RStar * s.b ≤ -s.y := by linarith
  have hbUpper : s.b ≤ 1 / RStar := by
    apply (le_div_iff₀ hR).2
    nlinarith
  exact ⟨hy, hyη, hη, hb, hbUpper⟩

/-- Raw form of `y ≥ -1`, used to put the active region in a fixed box. -/
theorem active_weighted_counters_le_x
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    RStar * (s.substantive + s.epsilon) - s.deferred ≤ s.x := by
  have hy' : -1 ≤ s.yNumerator / s.x := by
    simpa only [← y_eq_yNumerator_div] using hy
  have hyRaw : -s.x ≤ s.yNumerator := by
    have h := (le_div_iff₀ hs.1).1 hy'
    norm_num at h
    exact h
  unfold yNumerator at hyRaw
  nlinarith

theorem active_raw_counter_bounds
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    rhoStar * s.substantive ≤ s.x ∧
      RStar * s.epsilon ≤ s.x ∧
      rhoStar * s.deferred ≤ s.x := by
  have hweighted := active_weighted_counters_le_x hs hy
  have htotal :
      RStar * s.substantive + RStar * s.epsilon -
          s.deferred ≤
        s.x := by
    nlinarith
  have hR : 0 ≤ RStar := (lt_trans zero_lt_one one_lt_RStar).le
  have hRe : 0 ≤ RStar * s.epsilon :=
    mul_nonneg hR hs.2.2.1
  have hSleRS : s.substantive ≤ RStar * s.substantive := by
    have hRm1 : 0 ≤ RStar - 1 := sub_nonneg.mpr one_lt_RStar.le
    nlinarith [mul_nonneg hRm1 hs.2.1]
  have hbase : 0 ≤ RStar * s.substantive - s.deferred := by
    linarith [hs.2.2.2.2]
  have hρS : rhoStar * s.substantive ≤ s.x := by
    calc
      rhoStar * s.substantive =
          (RStar - 1) * s.substantive := by
            unfold RStar
            ring
      _ ≤ RStar * s.substantive - s.deferred := by
        nlinarith [hs.2.2.2.2]
      _ ≤ RStar * s.substantive + RStar * s.epsilon -
          s.deferred := by linarith
      _ ≤ s.x := htotal
  refine ⟨hρS, ?_, ?_⟩
  · linarith
  · have hdS :
        rhoStar * s.deferred ≤ rhoStar * s.substantive :=
      mul_le_mul_of_nonneg_left hs.2.2.2.2 rhoStar_pos.le
    exact hdS.trans hρS

theorem substantive_normalized_mem
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    0 ≤ s.substantive / s.x ∧
      s.substantive / s.x ≤ 1 / rhoStar := by
  constructor
  · exact div_nonneg hs.2.1 hs.1.le
  · apply (div_le_div_iff₀ hs.1 rhoStar_pos).2
    have h := (active_raw_counter_bounds hs hy).1
    simpa [mul_comm] using h

theorem epsilon_normalized_mem
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    0 ≤ s.epsilon / s.x ∧
      s.epsilon / s.x ≤ 1 / RStar := by
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  constructor
  · exact div_nonneg hs.2.2.1 hs.1.le
  · apply (div_le_div_iff₀ hs.1 hR).2
    have h := (active_raw_counter_bounds hs hy).2.1
    simpa [mul_comm] using h

theorem deferred_normalized_mem
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    0 ≤ s.deferred / s.x ∧
      s.deferred / s.x ≤ 1 / rhoStar := by
  constructor
  · exact div_nonneg hs.2.2.2.1 hs.1.le
  · apply (div_le_div_iff₀ hs.1 rhoStar_pos).2
    have h := (active_raw_counter_bounds hs hy).2.2
    simpa [mul_comm] using h

/-- The three normalized raw counters stay in fixed compact intervals
throughout the active region `-1 ≤ y ≤ 0`.  The upper endpoint `y ≤ 0`
follows from feasibility. -/
theorem active_normalized_bounds
    {s : AnalysisState} (hs : s.Feasible) (hy : -1 ≤ s.y) :
    (0 ≤ s.substantive / s.x ∧
        s.substantive / s.x ≤ 1 / rhoStar) ∧
      (0 ≤ s.epsilon / s.x ∧
        s.epsilon / s.x ≤ 1 / RStar) ∧
      (0 ≤ s.deferred / s.x ∧
        s.deferred / s.x ≤ 1 / rhoStar) :=
  ⟨substantive_normalized_mem hs hy,
    epsilon_normalized_mem hs hy,
    deferred_normalized_mem hs hy⟩

/-- Every active point of an interpolated unit step obeys the same uniform
box bounds. -/
theorem active_interpolated_normalized_bounds
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (q : BoundaryOutcome) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hy : -1 ≤ (s.interpolatedStep q t).y) :
    (0 ≤ (s.interpolatedStep q t).substantive /
          (s.interpolatedStep q t).x ∧
        (s.interpolatedStep q t).substantive /
            (s.interpolatedStep q t).x ≤
          1 / rhoStar) ∧
      (0 ≤ (s.interpolatedStep q t).epsilon /
          (s.interpolatedStep q t).x ∧
        (s.interpolatedStep q t).epsilon /
            (s.interpolatedStep q t).x ≤
          1 / RStar) ∧
      (0 ≤ (s.interpolatedStep q t).deferred /
          (s.interpolatedStep q t).x ∧
        (s.interpolatedStep q t).deferred /
            (s.interpolatedStep q t).x ≤
          1 / rhoStar) :=
  active_normalized_bounds (interpolatedStep_feasible hs hx q ht) hy

end AnalysisState

end

end SchedulingPaper
