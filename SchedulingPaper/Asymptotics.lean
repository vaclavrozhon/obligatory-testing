import SchedulingPaper.UnifiedOffline

/-!
# Size-asymptotic and additive conventions

The paper repeatedly turns an estimate `ALG ≤ c OPT + C n` into a
size-asymptotic coefficient.  This file states that step independently of any
particular online algorithm.  It also records why every coefficient `c + ε`
is admissible in the additive-constant convention, while `c` itself need not
be.
-/

namespace SchedulingPaper

universe u

/-- Epsilon formulation of an asymptotic upper competitive coefficient.
It is the upper-bound direction of the paper's limsup definition. -/
def SizeAsymptoticUpper {Family : ℕ → Type u}
    (alg opt : ∀ n, Family n → ℝ) (c : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ I, alg n I ≤ (c + ε) * opt n I

/-- Additive-constant admissibility from equation (3.9). -/
def AdditivelyAdmissible {Family : ℕ → Type u}
    (alg opt : ∀ n, Family n → ℝ) (c : ℝ) : Prop :=
  ∃ B : ℝ, ∀ n I, alg n I ≤ c * opt n I + B

/-- Abstract form of the paper's per-instance estimate with an `O(n)` term. -/
def HasLinearRemainder {Family : ℕ → Type u}
    (alg opt : ∀ n, Family n → ℝ) (c C : ℝ) : Prop :=
  ∀ n I, alg n I ≤ c * opt n I + C * n

/-- The uniform quadratic lower bound on the optimum. -/
def HasQuadraticOptLower {Family : ℕ → Type u}
    (opt : ∀ n, Family n → ℝ) (a : ℝ) : Prop :=
  ∀ n I, a * triangular n ≤ opt n I

/-- A linear remainder is negligible compared with a positive quadratic
lower bound on `OPT`. -/
theorem sizeAsymptoticUpper_of_linearRemainder
    {Family : ℕ → Type u} {alg opt : ∀ n, Family n → ℝ}
    {c C a : ℝ} (ha : 0 < a)
    (hlin : HasLinearRemainder alg opt c C)
    (hquad : HasQuadraticOptLower opt a) :
    SizeAsymptoticUpper alg opt c := by
  intro ε hε
  rcases exists_nat_ge (2 * C / (a * ε)) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn I
  have hncast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hthreshold : 2 * C / (a * ε) ≤ (n : ℝ) := hN.trans hncast
  have hae : 0 < a * ε := mul_pos ha hε
  have htwoc : 2 * C ≤ (n : ℝ) * (a * ε) :=
    (div_le_iff₀ hae).mp hthreshold
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hrem : C * (n : ℝ) ≤ ε * opt n I := by
    have hmul := mul_le_mul_of_nonneg_right htwoc hn0
    have htri : C * (n : ℝ) ≤ ε * (a * triangular n) := by
      unfold triangular
      nlinarith
    exact htri.trans (mul_le_mul_of_nonneg_left (hquad n I) hε.le)
  calc
    alg n I ≤ c * opt n I + C * n := hlin n I
    _ ≤ c * opt n I + ε * opt n I := add_le_add le_rfl hrem
    _ = (c + ε) * opt n I := by ring

/-- Young's inequality in the exact scalar form needed to absorb a linear
remainder into a quadratic optimum plus one finite constant. -/
theorem linear_le_quadratic_add_constant {C d x : ℝ}
    (hd : 0 < d) :
    C * x ≤ d * x ^ 2 / 2 + C ^ 2 / (2 * d) := by
  have hden : 0 ≤ 2 * d := (mul_pos zero_lt_two hd).le
  have hsquare : 0 ≤ (d * x - C) ^ 2 / (2 * d) :=
    div_nonneg (sq_nonneg _) hden
  calc
    C * x ≤ C * x + (d * x - C) ^ 2 / (2 * d) := le_add_of_nonneg_right hsquare
    _ = d * x ^ 2 / 2 + C ^ 2 / (2 * d) := by
      field_simp [hd.ne']
      ring

/-- From the same `O(n)` estimate, every strictly larger coefficient is
admissible with one finite additive constant. -/
theorem additivelyAdmissible_of_linearRemainder
    {Family : ℕ → Type u} {alg opt : ∀ n, Family n → ℝ}
    {c C a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hlin : HasLinearRemainder alg opt c C)
    (hquad : HasQuadraticOptLower opt a) :
    AdditivelyAdmissible alg opt (c + ε) := by
  refine ⟨C ^ 2 / (2 * (a * ε)), ?_⟩
  intro n I
  have hae : 0 < a * ε := mul_pos ha hε
  have hyoung := linear_le_quadratic_add_constant
    (C := C) (d := a * ε) (x := (n : ℝ)) hae
  have htri : a * (n : ℝ) ^ 2 / 2 ≤ a * triangular n := by
    unfold triangular
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith [ha.le]
  have hopt : a * (n : ℝ) ^ 2 / 2 ≤ opt n I :=
    htri.trans (hquad n I)
  have habsorb : C * (n : ℝ) ≤
      ε * opt n I + C ^ 2 / (2 * (a * ε)) := by
    calc
      C * (n : ℝ) ≤
          (a * ε) * (n : ℝ) ^ 2 / 2 + C ^ 2 / (2 * (a * ε)) := hyoung
      _ = ε * (a * (n : ℝ) ^ 2 / 2) + C ^ 2 / (2 * (a * ε)) := by ring
      _ ≤ ε * opt n I + C ^ 2 / (2 * (a * ε)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hopt hε.le) le_rfl
  calc
    alg n I ≤ c * opt n I + C * n := hlin n I
    _ ≤ c * opt n I +
        (ε * opt n I + C ^ 2 / (2 * (a * ε))) := add_le_add le_rfl habsorb
    _ = (c + ε) * opt n I + C ^ 2 / (2 * (a * ε)) := by ring

end SchedulingPaper
