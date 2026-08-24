import SchedulingPaper.RevealingOptimizationAlgebra
import Mathlib.Tactic

/-!
# Algebraic core of the revealing-optimization survival reduction

After flattening the initial part of the survival function, the only free
quantity is its middle-tail energy `E`.  The paper observes that the resulting
objective is linear-fractional and is therefore maximized at one of the two
endpoints.  This file checks that argument and identifies the endpoints with
the binary families `A` and `B`.
-/

namespace SchedulingPaper
namespace RevealingOptimization

noncomputable section

/-- A linear-fractional function with positive denominator is bounded by
the larger of its endpoint values.  No differentiability is used. -/
theorem linearFractional_le_max_endpoints
    {a c d L E : ℝ}
    (hd : 0 < d) (hL : 0 < L) (hE0 : 0 ≤ E) (hEL : E ≤ L) :
    (a + c * E) / (d + E) ≤
      max (a / d) ((a + c * L) / (d + L)) := by
  have hdE : 0 < d + E := by linarith
  have hdL : 0 < d + L := by linarith
  by_cases hslope : c * d ≤ a
  · apply le_max_of_le_left
    rw [div_le_div_iff₀ hdE hd]
    have hmul := mul_le_mul_of_nonneg_right hslope hE0
    nlinarith
  · apply le_max_of_le_right
    have hslope' : 0 ≤ c * d - a := by linarith
    rw [div_le_div_iff₀ hdE hdL]
    have hgap : 0 ≤ (L - E) * (c * d - a) :=
      mul_nonneg (sub_nonneg.mpr hEL) hslope'
    nlinarith

def survivalMass (τ : ℝ) : ℝ := (τ - 1) / τ

def survivalFamilyB (u τ : ℝ) : ℝ :=
  (τ + (u - τ) * survivalMass τ ^ 2) /
    (1 + (u - 1) * survivalMass τ ^ 2)

theorem survivalFamilyA_eq {τ : ℝ} (hτ : 0 < τ) :
    τ / (1 + τ * survivalMass τ ^ 2) = familyA τ := by
  have hleft : 0 < 1 + τ * survivalMass τ ^ 2 := by positivity
  have hright := familyA_den_pos τ
  unfold familyA
  rw [div_eq_div_iff hleft.ne' hright.ne']
  unfold survivalMass
  field_simp [hτ.ne']
  ring

theorem survivalFamilyB_eq {u τ : ℝ} (hτ : 0 < τ) :
    survivalFamilyB u τ = familyB u τ := by
  unfold survivalFamilyB survivalMass familyB
  field_simp [hτ.ne']
  ring

/-- Exact endpoint reduction in the case `τ < u-1`.  The assumptions on
`E` are precisely the monotone-tail bounds in the paper. -/
theorem middleTail_reduction_le_binary_families
    {u τ E : ℝ}
    (hτ : 1 ≤ τ) (hcase : τ < u - 1)
    (hE0 : 0 ≤ E)
    (hEmax : E ≤ (u - 1 - τ) * survivalMass τ ^ 2) :
    (τ + (u - τ) / (u - 1 - τ) * E) /
        (1 + τ * survivalMass τ ^ 2 + E) ≤
      max (familyA τ) (familyB u τ) := by
  by_cases hτone : τ = 1
  · subst τ
    simp [survivalMass] at hEmax
    have hE : E = 0 := by linarith
    subst E
    apply le_max_of_le_left
    norm_num [survivalMass, familyA]
  let L := u - 1 - τ
  let y := survivalMass τ
  let X := L * y ^ 2
  have hτ0 : 0 < τ := by linarith
  have hτ1 : 1 < τ := lt_of_le_of_ne hτ (Ne.symm hτone)
  have hL : 0 < L := by dsimp [L]; linarith
  have hy : 0 < y := by
    dsimp [y, survivalMass]
    positivity
  have hX : 0 < X := mul_pos hL (sq_pos_of_pos hy)
  have hd : 0 < 1 + τ * y ^ 2 := by positivity
  have hendpoint := linearFractional_le_max_endpoints
    (a := τ) (c := (u - τ) / L) (d := 1 + τ * y ^ 2)
    (L := X) (E := E) hd hX hE0 (by simpa [X, L, y] using hEmax)
  have hleft : τ / (1 + τ * y ^ 2) = familyA τ := by
    simpa [y] using survivalFamilyA_eq hτ0
  have hright :
      (τ + (u - τ) / L * X) / (1 + τ * y ^ 2 + X) =
        familyB u τ := by
    have hLne : L ≠ 0 := hL.ne'
    have hnum : (u - τ) / L * X = (u - τ) * y ^ 2 := by
      dsimp [X]
      field_simp [hLne]
    rw [hnum]
    have hdenX : 1 + τ * y ^ 2 + X =
        1 + (u - 1) * y ^ 2 := by
      dsimp [X, L]
      ring
    rw [hdenX]
    simpa [survivalFamilyB, y] using survivalFamilyB_eq (u := u) hτ0
  rw [hleft, hright] at hendpoint
  simpa [L, y] using hendpoint

/-- In the near-cap case the flat-prefix/tail estimate is exactly the `B`
family.  This packages the monotonicity step independently of how the
survival integrals were obtained. -/
theorem nearCap_reduction_le_familyB
    {u τ numerator denominator : ℝ}
    (hu : 1 ≤ u) (hτ : 1 ≤ τ) (hτu : τ ≤ u)
    (hden : 0 < denominator)
    (hnumerator : numerator ≤
      τ + (u - τ) * survivalMass τ ^ 2)
    (hdenominator :
      1 + (u - 1) * survivalMass τ ^ 2 ≤ denominator) :
    numerator / denominator ≤ familyB u τ := by
  have hτ0 : 0 < τ := by linarith
  have hbase : 0 < 1 + (u - 1) * survivalMass τ ^ 2 := by
    positivity
  have hfamilyNum :
      0 ≤ τ + (u - τ) * survivalMass τ ^ 2 :=
    add_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg _))
  have hB0 : 0 ≤ familyB u τ := by
    rw [← survivalFamilyB_eq (u := u) hτ0]
    unfold survivalFamilyB
    exact div_nonneg hfamilyNum hbase.le
  by_cases hnum0 : 0 ≤ numerator
  · calc
      numerator / denominator ≤ numerator /
          (1 + (u - 1) * survivalMass τ ^ 2) := by
        exact div_le_div_of_nonneg_left hnum0 hbase hdenominator
      _ ≤ (τ + (u - τ) * survivalMass τ ^ 2) /
          (1 + (u - 1) * survivalMass τ ^ 2) := by
        exact div_le_div_of_nonneg_right hnumerator hbase.le
      _ = familyB u τ := by
        simpa [survivalFamilyB] using survivalFamilyB_eq (u := u) hτ0
  · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hnum0) hden.le).trans hB0

end

end RevealingOptimization
end SchedulingPaper
