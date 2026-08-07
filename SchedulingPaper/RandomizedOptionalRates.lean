import SchedulingPaper.RandomizedOptionalPermutationUrn
import Mathlib.Tactic

/-!
# Optional testing: one explicit vanishing-error urn rate

The general checkpoint theorem is parameterized by four scales.  This file
records a concrete clean choice on populations of size `R^8`:

* leave `R^6` jobs outside the regulated prefix;
* use checkpoint spacing `R^5`;
* use martingale allowance `R^6` and suffix-mean allowance `1/R`.

The resulting count error is at most `4 R^7 = o(R^8)` and the failure
probability is at most `5/R`.  Perfect eighth powers are only a transparent
finite arithmetic witness; floor/ceiling versions use the same general
checkpoint theorem.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

def eighthPowerCutoff (R : ℕ) (hR : 2 ≤ R) : Fin (R ^ 8) :=
  ⟨R ^ 8 - R ^ 6, Nat.sub_lt (pow_pos (by omega) 8) (pow_pos (by omega) 6)⟩

@[simp] theorem eighthPowerCutoff_val (R : ℕ) (hR : 2 ≤ R) :
    (eighthPowerCutoff R hR).val = R ^ 8 - R ^ 6 := rfl

@[simp] theorem eighthPowerCutoff_suffix_card (R : ℕ) (hR : 2 ≤ R) :
    (suffixPositions (eighthPowerCutoff R hR)).card = R ^ 6 := by
  rw [suffixPositions_card, eighthPowerCutoff_val]
  have hle : R ^ 6 ≤ R ^ 8 :=
    (Nat.pow_lt_pow_right (by omega : 1 < R) (by omega : 6 < 8)).le
  omega

private theorem eighth_power_div_fifth_power
    (R : ℕ) (hR : 0 < R) :
    R ^ 8 / R ^ 5 = R ^ 3 := by
  rw [show R ^ 8 = R ^ 3 * R ^ 5 by ring]
  simpa [mul_comm] using Nat.mul_div_right (R ^ 3) (pow_pos hR 5)

private theorem cutoff_checkpoint_count_le
    (R : ℕ) (hR : 2 ≤ R) :
    (eighthPowerCutoff R hR).val / R ^ 5 + 1 ≤ R ^ 3 + 1 := by
  have hcut : (eighthPowerCutoff R hR).val ≤ R ^ 8 := by
    simp [eighthPowerCutoff]
  have hdiv := Nat.div_le_div_right hcut (c := R ^ 5)
  rw [eighth_power_div_fifth_power R (by omega)] at hdiv
  omega

private theorem eighth_power_checkpoint_failure_le
    (R : ℕ) (hR : 2 ≤ R) :
    (R : ℝ) ^ 8 / ((R : ℝ) ^ 6) ^ 2 +
        ((((eighthPowerCutoff R hR).val / R ^ 5 : ℕ) : ℝ) + 1) *
          (((2 : ℝ) / (R : ℝ) ^ 6) / (1 / (R : ℝ)) ^ 2) ≤
      (5 : ℝ) / (R : ℝ) := by
  have hcountNat := cutoff_checkpoint_count_le R hR
  have hcount :
      (((eighthPowerCutoff R hR).val / R ^ 5 : ℕ) : ℝ) + 1 ≤
        (R : ℝ) ^ 3 + 1 := by
    exact_mod_cast hcountNat
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hfactor0 :
      0 ≤ ((2 : ℝ) / (R : ℝ) ^ 6) / (1 / (R : ℝ)) ^ 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcount hfactor0
  calc
    (R : ℝ) ^ 8 / ((R : ℝ) ^ 6) ^ 2 +
        ((((eighthPowerCutoff R hR).val / R ^ 5 : ℕ) : ℝ) + 1) *
          ((2 / (R : ℝ) ^ 6) / (1 / R) ^ 2) ≤
      (R : ℝ) ^ 8 / ((R : ℝ) ^ 6) ^ 2 +
        ((R : ℝ) ^ 3 + 1) *
          ((2 / (R : ℝ) ^ 6) / (1 / R) ^ 2) :=
      add_le_add_right hmul _
    _ ≤ (5 : ℝ) / (R : ℝ) := by
      have hcube : (1 : ℝ) ≤ (R : ℝ) ^ 3 := by
        have hRone : (1 : ℝ) ≤ R := by
          exact_mod_cast (by omega : 1 ≤ R)
        simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hRone 3
      field_simp [hRpos.ne']
      nlinarith [hcube]

/-- Explicit `o(n)`/`o(1)` predictable-selection estimate. -/
theorem predictable_selected_count_eighth_power_probability_le
    (R : ℕ) (hR : 2 ≤ R)
    (value : Fin (R ^ 8) → ℝ)
    (select : Fin (R ^ 8) → Equiv.Perm (Fin (R ^ 8)) → ℝ)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ positionsThrough (eighthPowerCutoff R hR),
      ∀ σ, select j σ = 0) :
    uniformProbability (fun σ =>
      4 * (R : ℝ) ^ 7 <
        |(∑ j, select j σ * value (σ j)) -
          populationMean value * ∑ j, select j σ|) ≤
      (5 : ℝ) / (R : ℝ) := by
  have hn : 1 < R ^ 8 := by
    exact Nat.pow_lt_pow_right (by omega : 1 < R) (by omega : 0 < 8)
  have hstep : 0 < R ^ 5 := pow_pos (by omega) _
  have hbase := predictable_selected_count_regular_checkpoint_probability_le
    hn value select (eighthPowerCutoff R hR) hstep hPredictable
      hvalue0 hvalue1 hselect0 hselect1 hinactive
      (e := (R : ℝ) ^ 6) (r := 1 / (R : ℝ))
      (by positivity) (by positivity)
  have hthreshold :
      (R : ℝ) ^ 6 +
          (1 / (R : ℝ) +
            2 * (R ^ 5 : ℕ) /
              (suffixPositions (eighthPowerCutoff R hR)).card) *
            (R ^ 8 : ℕ) ≤
        4 * (R : ℝ) ^ 7 := by
    rw [eighthPowerCutoff_suffix_card]
    push_cast
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    field_simp [hRpos.ne']
    nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast (by omega : 1 ≤ R)]
  have hevent : ∀ σ,
      4 * (R : ℝ) ^ 7 <
          |(∑ j, select j σ * value (σ j)) -
            populationMean value * ∑ j, select j σ| →
      (R : ℝ) ^ 6 +
          (1 / (R : ℝ) +
            2 * (R ^ 5 : ℕ) /
              (suffixPositions (eighthPowerCutoff R hR)).card) *
            (R ^ 8 : ℕ) <
          |(∑ j, select j σ * value (σ j)) -
            populationMean value * ∑ j, select j σ| := by
    intro σ hbad
    linarith
  have hprob :
      uniformProbability (fun σ =>
        4 * (R : ℝ) ^ 7 <
          |(∑ j, select j σ * value (σ j)) -
            populationMean value * ∑ j, select j σ|) ≤
      uniformProbability (fun σ =>
        (R : ℝ) ^ 6 +
            (1 / (R : ℝ) +
              2 * (R ^ 5 : ℕ) /
                (suffixPositions (eighthPowerCutoff R hR)).card) *
              (R ^ 8 : ℕ) <
          |(∑ j, select j σ * value (σ j)) -
            populationMean value * ∑ j, select j σ|) :=
    uniformProbability_mono hevent
  refine hprob.trans (hbase.trans ?_)
  rw [eighthPowerCutoff_suffix_card]
  push_cast
  exact eighth_power_checkpoint_failure_le R hR

/-- The same explicit rate for predictably selected blind processing work
in `[0,L]`. -/
theorem predictable_selected_work_eighth_power_probability_le
    (R : ℕ) (hR : 2 ≤ R)
    (processing : Fin (R ^ 8) → ℝ)
    (select : Fin (R ^ 8) → Equiv.Perm (Fin (R ^ 8)) → ℝ)
    (hPredictable : PredictableSelector select)
    {L : ℝ} (hL : 0 < L)
    (hp0 : ∀ i, 0 ≤ processing i)
    (hpL : ∀ i, processing i ≤ L)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ positionsThrough (eighthPowerCutoff R hR),
      ∀ σ, select j σ = 0) :
    uniformProbability (fun σ =>
      4 * L * (R : ℝ) ^ 7 <
        |(∑ j, select j σ * processing (σ j)) -
          populationMean processing * ∑ j, select j σ|) ≤
      (5 : ℝ) / (R : ℝ) := by
  have hn : 1 < R ^ 8 :=
    Nat.pow_lt_pow_right (by omega : 1 < R) (by omega : 0 < 8)
  have hstep : 0 < R ^ 5 := pow_pos (by omega) _
  have hbase := predictable_selected_work_regular_checkpoint_probability_le
    hn processing select (eighthPowerCutoff R hR) hstep hPredictable
      hL hp0 hpL hselect0 hselect1 hinactive
      (e := (R : ℝ) ^ 6) (r := 1 / (R : ℝ))
      (by positivity) (by positivity)
  have hthreshold :
      L * ((R : ℝ) ^ 6 +
          (1 / (R : ℝ) +
            2 * (R ^ 5 : ℕ) /
              (suffixPositions (eighthPowerCutoff R hR)).card) *
            (R ^ 8 : ℕ)) ≤
        4 * L * (R : ℝ) ^ 7 := by
    have hscalar :
        (R : ℝ) ^ 6 +
            (1 / (R : ℝ) +
              2 * (R ^ 5 : ℕ) /
                (suffixPositions (eighthPowerCutoff R hR)).card) *
              (R ^ 8 : ℕ) ≤
          4 * (R : ℝ) ^ 7 := by
      rw [eighthPowerCutoff_suffix_card]
      push_cast
      have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
      field_simp [hRpos.ne']
      nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast (by omega : 1 ≤ R)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hscalar hL.le
  have hevent : ∀ σ,
      4 * L * (R : ℝ) ^ 7 <
          |(∑ j, select j σ * processing (σ j)) -
            populationMean processing * ∑ j, select j σ| →
      L * ((R : ℝ) ^ 6 +
          (1 / (R : ℝ) +
            2 * (R ^ 5 : ℕ) /
              (suffixPositions (eighthPowerCutoff R hR)).card) *
            (R ^ 8 : ℕ)) <
          |(∑ j, select j σ * processing (σ j)) -
            populationMean processing * ∑ j, select j σ| := by
    intro σ hbad
    linarith
  have hprob := uniformProbability_mono hevent
  refine hprob.trans (hbase.trans ?_)
  rw [eighthPowerCutoff_suffix_card]
  push_cast
  exact eighth_power_checkpoint_failure_le R hR

/-! ## Simultaneous grid classes -/

/-- Union of the checked one-category estimate over an arbitrary finite
grid.  This makes the dependence on the number of positive grid cells
explicit; it must be paid when choosing a vanishing mesh. -/
theorem predictable_selected_count_all_categories_eighth_power_probability_le
    {κ : Type*} [Fintype κ]
    (R : ℕ) (hR : 2 ≤ R)
    (value : κ → Fin (R ^ 8) → ℝ)
    (select : Fin (R ^ 8) → Equiv.Perm (Fin (R ^ 8)) → ℝ)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ c i, 0 ≤ value c i)
    (hvalue1 : ∀ c i, value c i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ positionsThrough (eighthPowerCutoff R hR),
      ∀ σ, select j σ = 0) :
    uniformProbability (fun σ => ∃ c,
      4 * (R : ℝ) ^ 7 <
        |(∑ j, select j σ * value c (σ j)) -
          populationMean (value c) * ∑ j, select j σ|) ≤
      Fintype.card κ * ((5 : ℝ) / (R : ℝ)) := by
  classical
  apply uniformProbability_exists_le_card_mul
  intro c
  exact predictable_selected_count_eighth_power_probability_le
    R hR (value c) select hPredictable (hvalue0 c) (hvalue1 c)
      hselect0 hselect1 hinactive

/-- Joint bad-event bound for every grid class and one bounded blind-work
selector. -/
theorem predictable_grid_counts_and_work_eighth_power_probability_le
    {κ : Type*} [Fintype κ]
    (R : ℕ) (hR : 2 ≤ R)
    (value : κ → Fin (R ^ 8) → ℝ)
    (testSelect blindSelect :
      Fin (R ^ 8) → Equiv.Perm (Fin (R ^ 8)) → ℝ)
    (hTestPredictable : PredictableSelector testSelect)
    (hBlindPredictable : PredictableSelector blindSelect)
    (hvalue0 : ∀ c i, 0 ≤ value c i)
    (hvalue1 : ∀ c i, value c i ≤ 1)
    {L : ℝ} (hL : 0 < L)
    (processing : Fin (R ^ 8) → ℝ)
    (hp0 : ∀ i, 0 ≤ processing i)
    (hpL : ∀ i, processing i ≤ L)
    (hTest0 : ∀ j σ, 0 ≤ testSelect j σ)
    (hTest1 : ∀ j σ, testSelect j σ ≤ 1)
    (hBlind0 : ∀ j σ, 0 ≤ blindSelect j σ)
    (hBlind1 : ∀ j σ, blindSelect j σ ≤ 1)
    (hTestInactive : ∀ j ∉ positionsThrough (eighthPowerCutoff R hR),
      ∀ σ, testSelect j σ = 0)
    (hBlindInactive : ∀ j ∉ positionsThrough (eighthPowerCutoff R hR),
      ∀ σ, blindSelect j σ = 0) :
    uniformProbability (fun σ =>
      (∃ c, 4 * (R : ℝ) ^ 7 <
        |(∑ j, testSelect j σ * value c (σ j)) -
          populationMean (value c) * ∑ j, testSelect j σ|) ∨
      4 * L * (R : ℝ) ^ 7 <
        |(∑ j, blindSelect j σ * processing (σ j)) -
          populationMean processing * ∑ j, blindSelect j σ|) ≤
      Fintype.card κ * ((5 : ℝ) / (R : ℝ)) +
        (5 : ℝ) / (R : ℝ) := by
  classical
  calc
    uniformProbability (fun σ =>
        (∃ c, 4 * (R : ℝ) ^ 7 <
          |(∑ j, testSelect j σ * value c (σ j)) -
            populationMean (value c) * ∑ j, testSelect j σ|) ∨
        4 * L * (R : ℝ) ^ 7 <
          |(∑ j, blindSelect j σ * processing (σ j)) -
            populationMean processing * ∑ j, blindSelect j σ|) ≤
      uniformProbability (fun σ => ∃ c,
          4 * (R : ℝ) ^ 7 <
            |(∑ j, testSelect j σ * value c (σ j)) -
              populationMean (value c) * ∑ j, testSelect j σ|) +
        uniformProbability (fun σ =>
          4 * L * (R : ℝ) ^ 7 <
            |(∑ j, blindSelect j σ * processing (σ j)) -
              populationMean processing * ∑ j, blindSelect j σ|) :=
        uniformProbability_or_le _ _
    _ ≤ Fintype.card κ * ((5 : ℝ) / (R : ℝ)) +
        (5 : ℝ) / (R : ℝ) := add_le_add
      (predictable_selected_count_all_categories_eighth_power_probability_le
        R hR value testSelect hTestPredictable hvalue0 hvalue1
          hTest0 hTest1 hTestInactive)
      (predictable_selected_work_eighth_power_probability_le
        R hR processing blindSelect hBlindPredictable hL hp0 hpL
          hBlind0 hBlind1 hBlindInactive)

/-- A grid of at most `S` positive classes is compatible with the checked
`L²` rate when `S² ≤ R`.  Both the union failure and the aggregate vertical
repair error then vanish like `1/S`. -/
theorem eighth_power_grid_union_and_repair_rates
    {K R S : ℕ} (hS : 1 ≤ S) (hK : K ≤ S) (hSR : S ^ 2 ≤ R) :
    (K : ℝ) * ((5 : ℝ) / R) + 5 / R ≤ 10 / S ∧
      ((K : ℝ) + 1) * (4 / R) ≤ 8 / S := by
  have hSpos : (0 : ℝ) < S := by exact_mod_cast (Nat.zero_lt_of_lt hS)
  have hRposNat : 0 < R := lt_of_lt_of_le (pow_pos (Nat.zero_lt_of_lt hS) 2) hSR
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hRposNat
  have hKR : (K : ℝ) + 1 ≤ 2 * S := by
    have hKRnat : K + 1 ≤ 2 * S := by omega
    exact_mod_cast hKRnat
  have hSsq : (S : ℝ) ^ 2 ≤ R := by exact_mod_cast hSR
  constructor
  · rw [show (K : ℝ) * (5 / (R : ℝ)) + 5 / R =
      ((K : ℝ) + 1) * 5 / R by ring]
    rw [div_le_div_iff₀ hRpos hSpos]
    nlinarith [mul_le_mul_of_nonneg_right hKR (show (0 : ℝ) ≤ 5 by norm_num)]
  · rw [show ((K : ℝ) + 1) * (4 / (R : ℝ)) =
      (((K : ℝ) + 1) * 4) / R by ring]
    rw [div_le_div_iff₀ hRpos hSpos]
    nlinarith [mul_le_mul_of_nonneg_right hKR (show (0 : ℝ) ≤ 4 by norm_num)]

end

end RandomizedOptional
end SchedulingPaper
