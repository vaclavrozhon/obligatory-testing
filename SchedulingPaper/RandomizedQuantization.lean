import SchedulingPaper.RandomizedHistogramTransfer
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# The fixed-cutoff histogram quantizer

Zero has its own category, the next `d` categories are intervals of width
`η`, and the last category is overflow.  The construction below is the
literal quantizer used by the unknown-multiset algorithm at cutoff `32`.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

abbrev QuantizedCategory (d : ℕ) := Fin (d + 2)

/-- Category zero for `p=0`, categories `1,...,d` for finite bins, and
category `d+1` for overflow. -/
def quantizedCategory (d : ℕ) (η p : ℝ) (hη : 0 < η) :
    QuantizedCategory d :=
  if hp0 : p = 0 then
    ⟨0, by omega⟩
  else if hcap : p ≤ (d : ℝ) * η then
    ⟨⌈p / η⌉₊, by
      have hratio : p / η ≤ (d : ℝ) := by
        rw [div_le_iff₀ hη]
        simpa [mul_comm] using hcap
      have hceil : ⌈p / η⌉₊ ≤ d := Nat.ceil_le.mpr hratio
      omega⟩
  else
    ⟨d + 1, by omega⟩

/-- Rounded representative.  Overflow is assigned `33`, safely above every
learned threshold (which is at most `16`); its exact representative is never
used in an early moment. -/
def quantizedRepresentative (d : ℕ) (η : ℝ)
    (b : QuantizedCategory d) : ℝ :=
  if b.val = 0 then 0 else if b.val ≤ d then (b.val : ℝ) * η else 33

theorem quantizedRepresentative_nonneg
    (d : ℕ) {η : ℝ} (hη : 0 ≤ η) (b : QuantizedCategory d) :
    0 ≤ quantizedRepresentative d η b := by
  unfold quantizedRepresentative
  split_ifs <;> positivity

@[simp] theorem quantizedCategory_zero
    (d : ℕ) {η : ℝ} (hη : 0 < η) :
    quantizedCategory d η 0 hη = ⟨0, by omega⟩ := by
  simp [quantizedCategory]

@[simp] theorem quantizedRepresentative_zero (d : ℕ) (η : ℝ) :
    quantizedRepresentative d η (⟨0, by omega⟩ : QuantizedCategory d) = 0 := by
  simp [quantizedRepresentative]

theorem quantizedCategory_overflow
    (d : ℕ) {η p : ℝ} (hη : 0 < η)
    (hover : (d : ℝ) * η < p) :
    quantizedCategory d η p hη = ⟨d + 1, by omega⟩ := by
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hover
    have hdη : 0 ≤ (d : ℝ) * η := mul_nonneg (by positivity) hη.le
    linarith
  simp [quantizedCategory, hp0, not_le.mpr hover]

theorem quantizedRepresentative_overflow
    (d : ℕ) (η : ℝ) :
    quantizedRepresentative d η
      (⟨d + 1, by omega⟩ : QuantizedCategory d) = 33 := by
  simp [quantizedRepresentative]

/-- A positive nonoverflow value is rounded upward by less than one bin. -/
theorem quantized_rounding_bounds
    (d : ℕ) {η p : ℝ} (hη : 0 < η) (hp : 0 < p)
    (hcap : p ≤ (d : ℝ) * η) :
    p ≤ quantizedRepresentative d η (quantizedCategory d η p hη) ∧
      quantizedRepresentative d η (quantizedCategory d η p hη) < p + η := by
  have hp0 : p ≠ 0 := hp.ne'
  have hratio0 : 0 ≤ p / η := div_nonneg hp.le hη.le
  have hratio : p / η ≤ (d : ℝ) := by
    rw [div_le_iff₀ hη]
    simpa [mul_comm] using hcap
  have hceilD : ⌈p / η⌉₊ ≤ d := Nat.ceil_le.mpr hratio
  have hceilPos : 0 < ⌈p / η⌉₊ := Nat.ceil_pos.mpr (div_pos hp hη)
  rw [quantizedCategory]
  simp only [hp0, ↓reduceDIte, hcap, quantizedRepresentative]
  simp only [hceilPos.ne', if_false, hceilD, if_true]
  constructor
  · have hle := Nat.le_ceil (p / η)
    have hmul := mul_le_mul_of_nonneg_right hle hη.le
    rw [div_mul_cancel₀ p hη.ne'] at hmul
    exact hmul
  · have hlt := Nat.ceil_lt_add_one hratio0
    have hmul := mul_lt_mul_of_pos_right hlt hη
    have hcancel : (p / η + 1) * η = p + η := by
      field_simp [hη.ne']
    rw [hcancel] at hmul
    exact hmul

/-- Every finite-bin representative is at most the cutoff `dη`. -/
theorem quantizedRepresentative_le_cutoff
    (d : ℕ) {η : ℝ} (hη : 0 ≤ η)
    {b : QuantizedCategory d} (hb : b.val ≤ d) :
    quantizedRepresentative d η b ≤ (d : ℝ) * η := by
  unfold quantizedRepresentative
  by_cases hb0 : b.val = 0
  · simp [hb0, mul_nonneg (by positivity : (0 : ℝ) ≤ d) hη]
  · simp only [hb0, if_false, hb, if_true]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hη

theorem quantizedRepresentative_eq_mul_of_le
    (d : ℕ) (η : ℝ) {b : QuantizedCategory d} (hb : b.val ≤ d) :
    quantizedRepresentative d η b = (b.val : ℝ) * η := by
  unfold quantizedRepresentative
  by_cases hb0 : b.val = 0
  · simp [hb0]
  · simp [hb0, hb]

/-- Any category in a learned closure with threshold at most sixteen is a
finite bin; overflow can never be early. -/
theorem thresholdClosure_excludes_overflow_B32
    (d : ℕ) {η θ : ℝ} (hθ : θ ≤ 16) :
    ¬ thresholdClosure (quantizedRepresentative d η) θ
      (⟨d + 1, by omega⟩ : QuantizedCategory d) := by
  simp only [thresholdClosure, quantizedRepresentative]
  simp
  linarith

/-- Every job classified early by a learned threshold at most sixteen has
the advertised one-bin rounding error.  In particular, a processing time
above the cutoff cannot enter through an unseen overflow category. -/
theorem quantized_selected_rounding_error_B32
    (d : ℕ) {η θ p : ℝ}
    (hη : 0 < η) (hp : 0 ≤ p) (hcutoff : (d : ℝ) * η = 32)
    (hθ : θ ≤ 16)
    (hselected : thresholdClosure (quantizedRepresentative d η) θ
      (quantizedCategory d η p hη)) :
    |p - quantizedRepresentative d η (quantizedCategory d η p hη)| ≤ η := by
  by_cases hp0 : p = 0
  · subst p
    rw [quantizedCategory_zero d hη]
    rw [quantizedRepresentative_zero]
    simp [hη.le]
  have hpPos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  by_cases hcap : p ≤ (d : ℝ) * η
  · obtain ⟨hlower, hupper⟩ := quantized_rounding_bounds d hη hpPos hcap
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  · have hover : (d : ℝ) * η < p := lt_of_not_ge hcap
    have hcat := quantizedCategory_overflow d hη hover
    have hnot := thresholdClosure_excludes_overflow_B32 d (η := η) hθ
    exact False.elim (hnot (by simpa [hcat] using hselected))

/-- Population actual-to-rounded moment loss for the concrete cutoff-32
quantizer. -/
theorem quantized_jobAverage_rounding_error_B32
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (d : ℕ) {η θ : ℝ} (hη : 0 < η)
    (hcutoff : (d : ℝ) * η = 32) (hθ : θ ≤ 16)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    |(∑ a, p a *
          (if thresholdClosure (quantizedRepresentative d η) θ
            (quantizedCategory d η (p a) hη) then 1 else 0)) /
          Fintype.card α -
        selectedMoment
          (fun b => ((categoryClass
            (fun a => quantizedCategory d η (p a) hη) b).card : ℝ) /
              Fintype.card α)
          (quantizedRepresentative d η)
          (thresholdClosure (quantizedRepresentative d η) θ)| ≤ η := by
  apply jobAverage_rounding_error_le p
    (fun a => quantizedCategory d η (p a) hη)
    (quantizedRepresentative d η)
    (thresholdClosure (quantizedRepresentative d η) θ) hη.le
  intro a ha
  exact quantized_selected_rounding_error_B32 d hη (hp a) hcutoff hθ ha

end

end RandomizedObligatory
end SchedulingPaper
