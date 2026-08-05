import SchedulingPaper.BankAccounting
import Mathlib.Tactic

/-!
# Finite Taylor remainder of the saturated bank
-/

namespace SchedulingPaper

noncomputable section

/-- The square of the positive part has a global one-sided quadratic
Taylor remainder. -/
theorem positivePart_sq_remainder (a t : ℝ) :
    positivePart (a + t) ^ 2 - positivePart a ^ 2 -
        2 * positivePart a * t ≤
      t ^ 2 := by
  unfold positivePart
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_left hat]
      ring_nf
      exact le_rfl
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_right hat']
      nlinarith [sq_nonneg (a + t)]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right ha']
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_left hat]
      have hfac : 0 ≤ (-a) * (2 * t + a) := by
        exact mul_nonneg (neg_nonneg.mpr ha') (by linarith)
      nlinarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_right hat']
      norm_num
      exact sq_nonneg t

/-- The saturated flat-region bank in raw coordinates `(x,S,d)`. -/
def saturatedBank (x S d : ℝ) : ℝ :=
  x * d + positivePart (x + d - RStar * S) ^ 2 / (2 * RStar)

/-- Its first-order gradient.  The epsilon component vanishes. -/
def saturatedBankGradient (x S d : ℝ) : RawGradient :=
  let p := positivePart (x + d - RStar * S)
  {
    x := d + p / RStar
    substantive := -p
    epsilon := 0
    deferred := x + p / RStar
  }

/-- Positive part commutes with multiplication by a nonnegative scalar. -/
theorem positivePart_mul_of_nonneg {c t : ℝ} (hc : 0 ≤ c) :
    positivePart (c * t) = c * positivePart t := by
  unfold positivePart
  rw [mul_max_of_nonneg t 0 hc]
  simp

/-- For positive `x`, `saturatedBank` is exactly the homogeneous flat
potential from `BankPotential`. -/
theorem saturatedBank_eq_flat_normalized
    {x S d : ℝ} (hx : 0 < x) :
    saturatedBank x S d =
      x * d + x ^ 2 * flatG ((d - RStar * S) / x) := by
  have harg :
      x + d - RStar * S =
        x * (1 + (d - RStar * S) / x) := by
    field_simp [hx.ne']
    ring
  unfold saturatedBank flatG
  rw [harg, positivePart_mul_of_nonneg hx.le]
  ring

/-- Euler's radial identity for the normalized flat potential. -/
theorem flatG_radial_identity (η : ℝ) :
    2 * flatG η - η * flatGPrime η =
      positivePart (1 + η) / RStar := by
  by_cases hη : 0 ≤ 1 + η
  · have hpart : positivePart (1 + η) = 1 + η := by
      unfold positivePart
      exact max_eq_left hη
    rw [flatG, flatGPrime, hpart]
    ring
  · have hpart : positivePart (1 + η) = 0 := by
      unfold positivePart
      exact max_eq_right (le_of_not_ge hη)
    simp [flatG, flatGPrime, hpart]

/-- The explicit saturated gradient agrees with `flatRawGradient` at every
state with positive remaining mass. -/
theorem saturatedBankGradient_eq_flatRawGradient
    (s : AnalysisState) (hx : 0 < s.x) :
    saturatedBankGradient s.x s.substantive s.deferred =
      flatRawGradient s := by
  have harg :
      s.x + s.deferred - RStar * s.substantive =
        s.x * (1 + s.eta) := by
    unfold AnalysisState.eta
    field_simp [hx.ne']
    ring
  have hpart :
      positivePart
          (s.x + s.deferred - RStar * s.substantive) =
        s.x * positivePart (1 + s.eta) := by
    rw [harg, positivePart_mul_of_nonneg hx.le]
  unfold saturatedBankGradient flatRawGradient
  dsimp only
  rw [RawGradient.mk.injEq]
  constructor
  ·
    rw [hpart, flatG_radial_identity]
    ring
  constructor
  ·
    rw [hpart]
    unfold flatGPrime
    have hR : RStar ≠ 0 :=
      ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
    field_simp [hR]
  constructor
  · rfl
  ·
    rw [hpart]
    unfold flatGPrime
    ring

/-- In the flat branch, the glued raw bank is the explicit saturated bank. -/
theorem bankW_eq_saturatedBank_of_flat
    (s : AnalysisState) (hx : 0 < s.x) (hy : s.y < -1) :
    bankW s.x s.substantive s.epsilon s.deferred =
      saturatedBank s.x s.substantive s.deferred := by
  have hyRaw :
      (s.deferred - RStar * s.substantive) / s.x -
          RStar * (s.epsilon / s.x) < -1 := by
    simpa [AnalysisState.y, AnalysisState.eta, AnalysisState.b] using hy
  unfold bankW
  rw [if_neg hx.ne']
  dsimp only
  unfold bankG
  rw [if_neg (not_le.mpr hyRaw)]
  rw [show
    (s.deferred - RStar * s.substantive) / s.x -
          RStar * (s.epsilon / s.x) +
        RStar * (s.epsilon / s.x) =
      (s.deferred - RStar * s.substantive) / s.x by ring]
  exact (saturatedBank_eq_flat_normalized hx).symm

/-- In the flat branch, `bankRawGradient` is the explicit saturated
gradient. -/
theorem bankRawGradient_eq_saturatedBankGradient_of_flat
    (s : AnalysisState) (hx : 0 < s.x) (hy : s.y < -1) :
    bankRawGradient s =
      saturatedBankGradient s.x s.substantive s.deferred := by
  unfold bankRawGradient
  rw [if_neg (not_le.mpr hy)]
  exact (saturatedBankGradient_eq_flatRawGradient s hx).symm

/-- Exact increment: a first-order term, the bilinear remainder
`Δx*Δd`, and the scalar positive-part remainder. -/
theorem saturatedBank_increment (x S d Δx ΔS Δd : ℝ) :
    saturatedBank (x + Δx) (S + ΔS) (d + Δd) -
        saturatedBank x S d =
      (d + positivePart (x + d - RStar * S) / RStar) * Δx -
        positivePart (x + d - RStar * S) * ΔS +
        (x + positivePart (x + d - RStar * S) / RStar) * Δd +
        Δx * Δd +
        (positivePart
              ((x + d - RStar * S) +
                (Δx + Δd - RStar * ΔS)) ^ 2 -
            positivePart (x + d - RStar * S) ^ 2 -
            2 * positivePart (x + d - RStar * S) *
              (Δx + Δd - RStar * ΔS)) /
          (2 * RStar) := by
  have hR : RStar ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
  unfold saturatedBank
  rw [show
    x + Δx + (d + Δd) - RStar * (S + ΔS) =
      (x + d - RStar * S) + (Δx + Δd - RStar * ΔS) by ring]
  field_simp [hR]
  ring

/-- Difference between a finite boundary step and its first-order proxy. -/
def saturatedBankRemainder (s : AnalysisState)
    (q : BoundaryOutcome) : ℝ :=
  saturatedBank (s.step q).x (s.step q).substantive
      (s.step q).deferred -
    saturatedBank s.x s.substantive s.deferred -
    (saturatedBankGradient s.x s.substantive s.deferred).dotDirection q

theorem saturatedBankRemainder_zero (s : AnalysisState) :
    saturatedBankRemainder s .zero =
      (positivePart
            ((s.x + s.deferred - RStar * s.substantive) - 1) ^ 2 -
          positivePart
            (s.x + s.deferred - RStar * s.substantive) ^ 2 +
          2 * positivePart
            (s.x + s.deferred - RStar * s.substantive)) /
        (2 * RStar) := by
  unfold saturatedBankRemainder
  simp only [AnalysisState.step]
  rw [show s.x - 1 = s.x + (-1) by ring]
  have hinc :=
    saturatedBank_increment s.x s.substantive s.deferred (-1) 0 0
  norm_num at hinc
  rw [hinc]
  simp [saturatedBankGradient, RawGradient.dotDirection]
  ring_nf

theorem saturatedBankRemainder_epsilon (s : AnalysisState) :
    saturatedBankRemainder s .epsilon =
      (positivePart
            ((s.x + s.deferred - RStar * s.substantive) - 1) ^ 2 -
          positivePart
            (s.x + s.deferred - RStar * s.substantive) ^ 2 +
          2 * positivePart
            (s.x + s.deferred - RStar * s.substantive)) /
        (2 * RStar) := by
  unfold saturatedBankRemainder
  simp only [AnalysisState.step]
  rw [show s.x - 1 = s.x + (-1) by ring]
  have hinc :=
    saturatedBank_increment s.x s.substantive s.deferred (-1) 0 0
  norm_num at hinc
  rw [hinc]
  simp [saturatedBankGradient, RawGradient.dotDirection]
  ring_nf

theorem saturatedBankRemainder_immediate (s : AnalysisState) :
    saturatedBankRemainder s .immediate =
      (positivePart
            ((s.x + s.deferred - RStar * s.substantive) +
              (-1 - RStar)) ^ 2 -
          positivePart
            (s.x + s.deferred - RStar * s.substantive) ^ 2 -
          2 * positivePart
              (s.x + s.deferred - RStar * s.substantive) *
            (-1 - RStar)) /
        (2 * RStar) := by
  unfold saturatedBankRemainder
  simp only [AnalysisState.step]
  rw [show s.x - 1 = s.x + (-1) by ring]
  have hinc :=
    saturatedBank_increment s.x s.substantive s.deferred (-1) 1 0
  norm_num at hinc
  rw [hinc]
  simp [saturatedBankGradient, RawGradient.dotDirection]
  ring_nf

theorem saturatedBankRemainder_deferred (s : AnalysisState) :
    saturatedBankRemainder s .deferred =
      -1 +
        (positivePart
              ((s.x + s.deferred - RStar * s.substantive) - RStar) ^ 2 -
            positivePart
              (s.x + s.deferred - RStar * s.substantive) ^ 2 +
            2 * RStar * positivePart
              (s.x + s.deferred - RStar * s.substantive)) /
          (2 * RStar) := by
  unfold saturatedBankRemainder
  simp only [AnalysisState.step]
  rw [show s.x - 1 = s.x + (-1) by ring]
  have hinc :=
    saturatedBank_increment s.x s.substantive s.deferred (-1) 1 1
  norm_num at hinc
  rw [hinc]
  simp [saturatedBankGradient, RawGradient.dotDirection]
  ring_nf

def saturatedDirectionRemainder : BoundaryOutcome → ℝ
  | .zero | .epsilon => 1 / (2 * RStar)
  | .immediate => (1 + RStar) ^ 2 / (2 * RStar)
  | .deferred => RStar / 2 - 1

theorem saturatedBankRemainder_zero_le (s : AnalysisState) :
    saturatedBankRemainder s .zero ≤ 1 / (2 * RStar) := by
  rw [saturatedBankRemainder_zero]
  have hden : 0 < 2 * RStar :=
    mul_pos (by norm_num) (lt_trans zero_lt_one one_lt_RStar)
  apply (div_le_div_iff_of_pos_right hden).2
  convert positivePart_sq_remainder
    (s.x + s.deferred - RStar * s.substantive) (-1) using 1
  all_goals ring_nf

theorem saturatedBankRemainder_epsilon_le (s : AnalysisState) :
    saturatedBankRemainder s .epsilon ≤ 1 / (2 * RStar) := by
  rw [saturatedBankRemainder_epsilon]
  have hden : 0 < 2 * RStar :=
    mul_pos (by norm_num) (lt_trans zero_lt_one one_lt_RStar)
  apply (div_le_div_iff_of_pos_right hden).2
  convert positivePart_sq_remainder
    (s.x + s.deferred - RStar * s.substantive) (-1) using 1
  all_goals ring_nf

theorem saturatedBankRemainder_immediate_le (s : AnalysisState) :
    saturatedBankRemainder s .immediate ≤
      (1 + RStar) ^ 2 / (2 * RStar) := by
  rw [saturatedBankRemainder_immediate]
  have hden : 0 < 2 * RStar :=
    mul_pos (by norm_num) (lt_trans zero_lt_one one_lt_RStar)
  apply (div_le_div_iff_of_pos_right hden).2
  convert positivePart_sq_remainder
    (s.x + s.deferred - RStar * s.substantive)
      (-1 - RStar) using 1
  all_goals ring_nf

theorem saturatedBankRemainder_deferred_le (s : AnalysisState) :
    saturatedBankRemainder s .deferred ≤ RStar / 2 - 1 := by
  rw [saturatedBankRemainder_deferred]
  have hden : 0 < 2 * RStar :=
    mul_pos (by norm_num) (lt_trans zero_lt_one one_lt_RStar)
  have hnum :
      positivePart
            ((s.x + s.deferred - RStar * s.substantive) - RStar) ^ 2 -
          positivePart
            (s.x + s.deferred - RStar * s.substantive) ^ 2 +
          2 * RStar * positivePart
            (s.x + s.deferred - RStar * s.substantive) ≤
        RStar ^ 2 := by
    convert positivePart_sq_remainder
      (s.x + s.deferred - RStar * s.substantive)
        (-RStar) using 1
    all_goals ring_nf
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hnum
  calc
    -1 +
          (positivePart
                ((s.x + s.deferred - RStar * s.substantive) - RStar) ^ 2 -
              positivePart
                (s.x + s.deferred - RStar * s.substantive) ^ 2 +
              2 * RStar * positivePart
                (s.x + s.deferred - RStar * s.substantive)) /
            (2 * RStar) ≤
        -1 + RStar ^ 2 / (2 * RStar) := by linarith
    _ = RStar / 2 - 1 := by
      have hR : RStar ≠ 0 :=
        ne_of_gt (lt_trans zero_lt_one one_lt_RStar)
      field_simp [hR]
      ring

/-- All four explicit constants in one theorem. -/
theorem saturatedBankRemainder_le
    (s : AnalysisState) (q : BoundaryOutcome) :
    saturatedBankRemainder s q ≤ saturatedDirectionRemainder q := by
  cases q with
  | zero => exact saturatedBankRemainder_zero_le s
  | epsilon => exact saturatedBankRemainder_epsilon_le s
  | immediate => exact saturatedBankRemainder_immediate_le s
  | deferred => exact saturatedBankRemainder_deferred_le s

/-- A single state-independent constant dominating all four direction
remainders. -/
def saturatedUniformRemainder : ℝ :=
  (1 + RStar) ^ 2 / (2 * RStar)

theorem saturatedDirectionRemainder_le_uniform (q : BoundaryOutcome) :
    saturatedDirectionRemainder q ≤ saturatedUniformRemainder := by
  have hR : 0 < RStar := lt_trans zero_lt_one one_lt_RStar
  have hden : 0 < 2 * RStar := mul_pos (by norm_num) hR
  cases q with
  | zero =>
      unfold saturatedDirectionRemainder saturatedUniformRemainder
      apply (div_le_div_iff_of_pos_right hden).2
      nlinarith [sq_nonneg RStar]
  | epsilon =>
      unfold saturatedDirectionRemainder saturatedUniformRemainder
      apply (div_le_div_iff_of_pos_right hden).2
      nlinarith [sq_nonneg RStar]
  | immediate =>
      rfl
  | deferred =>
      unfold saturatedDirectionRemainder saturatedUniformRemainder
      apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg RStar]

theorem saturatedBankRemainder_le_uniform
    (s : AnalysisState) (q : BoundaryOutcome) :
    saturatedBankRemainder s q ≤ saturatedUniformRemainder :=
  (saturatedBankRemainder_le s q).trans
    (saturatedDirectionRemainder_le_uniform q)

/-- Finite Taylor estimate in the form used by bank accounting. -/
theorem saturatedBank_step_le_gradient_add_remainder
    (s : AnalysisState) (q : BoundaryOutcome) :
    saturatedBank (s.step q).x (s.step q).substantive
        (s.step q).deferred -
      saturatedBank s.x s.substantive s.deferred ≤
        (saturatedBankGradient s.x s.substantive s.deferred).dotDirection q +
          saturatedDirectionRemainder q := by
  have h := saturatedBankRemainder_le s q
  unfold saturatedBankRemainder at h
  linarith

/-- Flat-to-flat steps of the glued bank inherit the explicit saturated
remainder estimate. -/
theorem bankW_flat_step_le_gradient_add_remainder
    (s : AnalysisState) (q : BoundaryOutcome)
    (hx : 0 < s.x) (hy : s.y < -1)
    (hxNext : 0 < (s.step q).x) (hyNext : (s.step q).y < -1) :
    bankW (s.step q).x (s.step q).substantive
        (s.step q).epsilon (s.step q).deferred -
      bankW s.x s.substantive s.epsilon s.deferred ≤
        (bankRawGradient s).dotDirection q +
          saturatedDirectionRemainder q := by
  rw [bankW_eq_saturatedBank_of_flat (s.step q) hxNext hyNext,
    bankW_eq_saturatedBank_of_flat s hx hy,
    bankRawGradient_eq_saturatedBankGradient_of_flat s hx hy]
  exact saturatedBank_step_le_gradient_add_remainder s q

end

end SchedulingPaper
