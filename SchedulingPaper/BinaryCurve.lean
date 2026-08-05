import SchedulingPaper.LowRegime

/-!
# Algebraic core of the binary stopping lower bound

This file formalizes the exact scalar optimization used after the adversarial
trace accounting in the paper's Raw-safe hidden stopping lemma.  The online
adversary and its first-crossing/replay argument live in separate modules;
the results here certify every quadratic minimization and tangency equation
that produces the first four branches of the finite curve.
-/

namespace SchedulingPaper

noncomputable section

/-- Equation (4.11) of the paper. -/
def stoppingF (u ρ y b : ℝ) : ℝ :=
  1 - ρ + 2 * y + (u - 1) * (1 - ρ) * y ^ 2 +
    b ^ 2 + 2 * b * (u - 1 - u * y)

/-- The algorithm's minimizing completion mass, equation (4.12). -/
def stoppingMinimizer (u y : ℝ) : ℝ := max 0 (u * y - (u - 1))

/-- The upper constraint `b ≤ y` never binds on the unit interval. -/
theorem stoppingMinimizer_le_y {u y : ℝ} (hu : 1 ≤ u)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    stoppingMinimizer u y ≤ y := by
  unfold stoppingMinimizer
  rw [max_le_iff]
  constructor
  · exact hy0
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hy1)]

theorem stoppingMinimizer_nonneg (u y : ℝ) :
    0 ≤ stoppingMinimizer u y := by
  exact le_max_left _ _

/-- Completing the square proves that `stoppingMinimizer` minimizes the
adversary's quadratic over all `b ≥ 0`. -/
theorem stoppingF_minimized {u ρ y b : ℝ} (hb : 0 ≤ b) :
    stoppingF u ρ y (stoppingMinimizer u y) ≤ stoppingF u ρ y b := by
  unfold stoppingMinimizer
  by_cases hq : 0 ≤ u * y - (u - 1)
  · rw [max_eq_right hq]
    unfold stoppingF
    nlinarith [sq_nonneg (b - (u * y - (u - 1)))]
  · have hq' : u * y - (u - 1) ≤ 0 := le_of_not_ge hq
    rw [max_eq_left hq']
    unfold stoppingF
    nlinarith [mul_nonneg hb (sub_nonneg.mpr (by nlinarith :
      0 ≤ b + 2 * (u - 1 - u * y)))]

/-- `A_u` from the positive-completion branch. -/
def stoppingA (u : ℝ) : ℝ := u ^ 2 - u + 1

/-- `D_{u,ρ}` from the positive-completion branch. -/
def stoppingD (u ρ : ℝ) : ℝ := stoppingA u + (u - 1) * ρ

/-- The minimized positive branch, equation (4.13). -/
def positiveStoppingEnvelope (u ρ y : ℝ) : ℝ :=
  1 - ρ - (u - 1) ^ 2 + 2 * stoppingA u * y - stoppingD u ρ * y ^ 2

/-- The zero-completion branch. -/
def zeroStoppingEnvelope (u ρ y : ℝ) : ℝ :=
  1 - ρ + 2 * y + (u - 1) * (1 - ρ) * y ^ 2

theorem stoppingF_zero (u ρ y : ℝ) :
    stoppingF u ρ y 0 = zeroStoppingEnvelope u ρ y := by
  unfold stoppingF zeroStoppingEnvelope
  ring

theorem stoppingF_positive_branch (u ρ y : ℝ) :
    stoppingF u ρ y (u * y - (u - 1)) =
      positiveStoppingEnvelope u ρ y := by
  unfold stoppingF positiveStoppingEnvelope stoppingD stoppingA
  ring

/-- The exact completed-square identity behind the positive-branch
maximization. -/
theorem positiveStoppingEnvelope_completeSquare (u ρ y : ℝ) :
    stoppingD u ρ * positiveStoppingEnvelope u ρ y =
      (1 - ρ - (u - 1) ^ 2) * stoppingD u ρ + stoppingA u ^ 2 -
        (stoppingD u ρ * y - stoppingA u) ^ 2 := by
  unfold positiveStoppingEnvelope
  ring

/-- The tangency expression in equation (4.14). -/
def stoppingTangency (u ρ : ℝ) : ℝ :=
  (1 - ρ - (u - 1) ^ 2) * stoppingD u ρ + stoppingA u ^ 2

theorem positiveStoppingEnvelope_le_zero_of_tangent
    {u ρ y : ℝ} (hD : 0 < stoppingD u ρ)
    (htangent : stoppingTangency u ρ = 0) :
    positiveStoppingEnvelope u ρ y ≤ 0 := by
  have hs := positiveStoppingEnvelope_completeSquare u ρ y
  rw [show (1 - ρ - (u - 1) ^ 2) * stoppingD u ρ + stoppingA u ^ 2 =
    stoppingTangency u ρ by rfl, htangent] at hs
  have hmul : stoppingD u ρ * positiveStoppingEnvelope u ρ y ≤ 0 := by
    rw [hs]
    nlinarith [sq_nonneg (stoppingD u ρ * y - stoppingA u)]
  by_contra h
  have henv : 0 < positiveStoppingEnvelope u ρ y := lt_of_not_ge h
  have := mul_pos hD henv
  linarith

theorem positiveStoppingEnvelope_at_tangent
    {u ρ : ℝ} (hD : stoppingD u ρ ≠ 0)
    (htangent : stoppingTangency u ρ = 0) :
    positiveStoppingEnvelope u ρ (stoppingA u / stoppingD u ρ) = 0 := by
  have hs := positiveStoppingEnvelope_completeSquare
    u ρ (stoppingA u / stoppingD u ρ)
  rw [show (1 - ρ - (u - 1) ^ 2) * stoppingD u ρ + stoppingA u ^ 2 =
    stoppingTangency u ρ by rfl, htangent] at hs
  have hzero : stoppingD u ρ * (stoppingA u / stoppingD u ρ) -
      stoppingA u = 0 := by
    field_simp [hD]
    ring
  rw [hzero] at hs
  norm_num at hs
  exact hs.resolve_left hD

/-- Polynomial `T_s` defining the algebraic branch. -/
def rhoPolynomial (s ρ : ℝ) : ℝ :=
  s * ρ ^ 2 + (s ^ 3 + s ^ 2 + 1) * ρ -
    (s ^ 2 + s + 1) * (s + 2)

/-- Expanding the positive tangency gives exactly `T_{u-1}(ρ)=0`. -/
theorem stoppingTangency_eq_neg_rhoPolynomial (u ρ : ℝ) :
    stoppingTangency u ρ = -rhoPolynomial (u - 1) ρ := by
  unfold stoppingTangency stoppingD stoppingA rhoPolynomial
  ring

theorem stoppingTangency_iff_rhoPolynomial (u ρ : ℝ) :
    stoppingTangency u ρ = 0 ↔ rhoPolynomial (u - 1) ρ = 0 := by
  rw [stoppingTangency_eq_neg_rhoPolynomial]
  constructor <;> intro h <;> linarith

/-- Positive `s` and positive `ρ` make the denominator of the tangent point
strictly positive. -/
theorem stoppingD_pos {u ρ : ℝ} (hu : 1 < u) (hρ : 0 < ρ) :
    0 < stoppingD u ρ := by
  unfold stoppingD stoppingA
  have hquad : 0 < u ^ 2 - u + 1 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hprod : 0 < (u - 1) * ρ := mul_pos (sub_pos.mpr hu) hρ
  linarith

/-- Exact zero-branch tangency value from equation (4.15). -/
theorem zeroStoppingEnvelope_tangent {s : ℝ} (hs : 0 < s) :
    zeroStoppingEnvelope (s + 1) (1 + 1 / Real.sqrt s)
      (1 / Real.sqrt s) = 0 := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have ht_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  unfold zeroStoppingEnvelope
  field_simp [ht.ne']
  nlinarith

/-- The algebraic condition ensuring that the zero-branch tangent really has
minimizer `b = 0`. -/
theorem zero_tangent_in_zero_branch {s : ℝ} (hs : 0 < s)
    (hbranch : (s + 1) ^ 2 ≤ s ^ 3) :
    (s + 1) * (1 / Real.sqrt s) - s ≤ 0 := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have ht_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hnonneg : 0 ≤ s * Real.sqrt s + (s + 1) := by positivity
  have hfac : 0 ≤ (s * Real.sqrt s - (s + 1)) *
      (s * Real.sqrt s + (s + 1)) := by
    nlinarith
  have hright : s + 1 ≤ s * Real.sqrt s := by
    by_contra h
    have hneg : s * Real.sqrt s - (s + 1) < 0 := by linarith
    exact (not_lt_of_ge hfac) (mul_neg_of_neg_of_pos hneg (by positivity))
  apply sub_nonpos.mpr
  simpa [div_eq_mul_inv] using (div_le_iff₀ ht).2 hright

/-- The exact transition point between the `u` and algebraic branches. -/
def uDiamond : ℝ := (1 + Real.sqrt (3 + 2 * Real.sqrt 5)) / 2

theorem uDiamond_mul_sub_one :
    uDiamond * (uDiamond - 1) = goldenRatio := by
  have h5 : 0 ≤ (5 : ℝ) := by norm_num
  have hs5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt h5
  have hinner : 0 ≤ 3 + 2 * Real.sqrt 5 := by positivity
  have hsinner : (Real.sqrt (3 + 2 * Real.sqrt 5)) ^ 2 =
      3 + 2 * Real.sqrt 5 := Real.sq_sqrt hinner
  unfold uDiamond goldenRatio
  nlinarith

theorem uDiamond_transition_polynomial :
    (uDiamond * (uDiamond - 1)) ^ 2 -
      uDiamond * (uDiamond - 1) - 1 = 0 := by
  rw [uDiamond_mul_sub_one]
  nlinarith [goldenRatio_sq]

/-- For `ρ=u`, the positive-branch tangency expression is the negation of
the simple transition polynomial from the paper. -/
theorem stoppingTangency_at_ratio_u (u : ℝ) :
    stoppingTangency u u =
      -((u * (u - 1)) ^ 2 - u * (u - 1) - 1) := by
  unfold stoppingTangency stoppingD stoppingA
  ring

/-- Polynomial whose unique root above two determines `s₀`. -/
def sZeroPolynomial (s : ℝ) : ℝ := s ^ 3 - (s + 1) ^ 2

theorem sZeroPolynomial_strictMono_above_two {x y : ℝ}
    (hx : 2 < x) (hxy : x < y) :
    sZeroPolynomial x < sZeroPolynomial y := by
  have hy : 2 < y := hx.trans hxy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxpart : x < x ^ 2 - x := by
    have hmul : 0 < x * (x - 2) := mul_pos hx0 (sub_pos.mpr hx)
    nlinarith
  have hypart : y < y ^ 2 - y := by
    have hmul : 0 < y * (y - 2) := mul_pos hy0 (sub_pos.mpr hy)
    nlinarith
  have hprod : 0 < x * y := mul_pos hx0 hy0
  have hbracket : 0 < y ^ 2 + y * x + x ^ 2 - y - x - 2 := by
    nlinarith
  have hfactor :
      sZeroPolynomial y - sZeroPolynomial x =
        (y - x) * (y ^ 2 + y * x + x ^ 2 - y - x - 2) := by
    unfold sZeroPolynomial
    ring
  have hdiff : 0 < sZeroPolynomial y - sZeroPolynomial x := by
    rw [hfactor]
    exact mul_pos (sub_pos.mpr hxy) hbracket
  linarith

theorem exists_unique_sZero :
    ∃! s : ℝ, 2 < s ∧ s < 3 ∧ sZeroPolynomial s = 0 := by
  have hcont : Continuous sZeroPolynomial := by
    unfold sZeroPolynomial
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc (sZeroPolynomial 2) (sZeroPolynomial 3) := by
    norm_num [sZeroPolynomial]
  rcases intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3)
      hcont.continuousOn hmem with ⟨s, hsIcc, hsroot⟩
  have hs2 : 2 < s := by
    rcases hsIcc with ⟨hs2, hs3⟩
    refine lt_of_le_of_ne hs2 ?_
    intro heq
    subst s
    norm_num [sZeroPolynomial] at hsroot
  have hs3 : s < 3 := by
    rcases hsIcc with ⟨hs2le, hs3⟩
    refine lt_of_le_of_ne hs3 ?_
    intro heq
    subst s
    norm_num [sZeroPolynomial] at hsroot
  refine ⟨s, ⟨hs2, hs3, hsroot⟩, ?_⟩
  intro y hy
  rcases hy with ⟨hy2, _hy3, hyroot⟩
  by_cases hsy : s < y
  · have hlt := sZeroPolynomial_strictMono_above_two hs2 hsy
    rw [hsroot, hyroot] at hlt
    linarith
  · by_cases hys : y < s
    · have hlt := sZeroPolynomial_strictMono_above_two hy2 hys
      rw [hsroot, hyroot] at hlt
      linarith
    · exact le_antisymm (le_of_not_gt hsy) (le_of_not_gt hys)

/-- The unique transition parameter satisfying `s₀³ = (s₀+1)²`. -/
def sZero : ℝ := Classical.choose exists_unique_sZero

theorem sZero_spec :
    2 < sZero ∧ sZero < 3 ∧ sZero ^ 3 = (sZero + 1) ^ 2 := by
  unfold sZero
  have hs := (Classical.choose_spec exists_unique_sZero).1
  rcases hs with ⟨h2, h3, hroot⟩
  exact ⟨h2, h3, sub_eq_zero.mp hroot⟩

def uZero : ℝ := 1 + sZero

theorem uZero_bounds : 3 < uZero ∧ uZero < 4 := by
  unfold uZero
  rcases sZero_spec with ⟨h2, h3, _⟩
  constructor <;> linarith

end

end SchedulingPaper
