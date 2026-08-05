import SchedulingPaper.MixedQuotaOracle
import Mathlib.Tactic

/-!
# Uniform rounding bounds for the dynamic mixed quota

At a first crossing, the number of caps differs by at most one quota block
from an exact integral scale.  The dynamically rounded harmonic tail then
differs from the corresponding `A : B` scale by only a parameter-dependent
constant.  These bounds are independent of the strategy and of the ambient
instance size.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- A number of caps lying in the one-job crossing window is bracketed by
two consecutive exact `M`-blocks. -/
theorem quota_cap_count_bounds
    {M A B S C q : ℕ}
    (hM : 0 < M)
    (hden : 0 < M + A + B)
    (hqLower : (M + A + B) * q ≤ S)
    (hqUpper : S < (M + A + B) * (q + 1))
    (hcrossLower :
      (M : ℝ) / (M + A + B : ℕ) * S ≤ C)
    (hcrossUpper :
      (C : ℝ) <
        (M : ℝ) / (M + A + B : ℕ) * S + 1) :
    M * q ≤ C ∧ C ≤ M * (q + 1) := by
  let D : ℕ := M + A + B
  have hD : 0 < D := by simpa [D] using hden
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hqLowerReal : (D : ℝ) * q ≤ S := by
    exact_mod_cast (show D * q ≤ S by simpa [D] using hqLower)
  have hqUpperReal : (S : ℝ) < D * (q + 1) := by
    exact_mod_cast (show S < D * (q + 1) by simpa [D] using hqUpper)
  have hMlower :
      ((M * q : ℕ) : ℝ) ≤ C := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hqLowerReal
        (div_nonneg (by positivity : (0 : ℝ) ≤ M) hDreal.le)
    have hcancel :
        (M : ℝ) / D * ((D : ℝ) * q) = (M * q : ℕ) := by
      field_simp [hDreal.ne']
      norm_num
    rw [hcancel] at hscaled
    exact hscaled.trans (by simpa [D] using hcrossLower)
  have hMupper :
      (C : ℝ) < (M * (q + 1) : ℕ) + 1 := by
    have hscaled :=
      mul_lt_mul_of_pos_left hqUpperReal
        (div_pos hMreal hDreal)
    have hcancel :
        (M : ℝ) / D * ((D : ℝ) * (q + 1)) =
          (M * (q + 1) : ℕ) := by
      field_simp [hDreal.ne']
      norm_num
    have hcrossUpper' :
        (C : ℝ) < (M : ℝ) / D * S + 1 := by
      simpa [D] using hcrossUpper
    rw [hcancel] at hscaled
    linarith
  constructor
  · exact_mod_cast hMlower
  · have hNat : C < M * (q + 1) + 1 := by
      exact_mod_cast hMupper
    omega

/-- After deleting the cap block, the tail size stays within a fixed
parameter-dependent distance of `(A+B)q`. -/
theorem quota_tail_size_bounds
    {M A B S C H q : ℕ}
    (hsize : S = C + H)
    (hqLower : (M + A + B) * q ≤ S)
    (hqUpper : S < (M + A + B) * (q + 1))
    (hcapLower : M * q ≤ C)
    (hcapUpper : C ≤ M * (q + 1)) :
    (A + B) * q ≤ H + M ∧
      H < (A + B) * q + (M + A + B) := by
  subst S
  constructor <;>
    simp only [add_mul, mul_add] at hqLower hqUpper hcapLower hcapUpper ⊢ <;>
    omega

/-- Rounding the positive part of the tail changes the exact `Aq` count by
at most a fixed number of jobs. -/
theorem quota_tailPositiveCount_bounds
    {M A B H q : ℕ}
    (hAB : 0 < A + B)
    (htailLower : (A + B) * q ≤ H + M)
    (htailUpper :
      H < (A + B) * q + (M + A + B)) :
    A * q ≤ tailPositiveCount A B H + M ∧
      tailPositiveCount A B H ≤ A * q + (M + A + B) := by
  let D : ℕ := A + B
  let K : ℕ := tailPositiveCount A B H
  have hD : 0 < D := by simpa [D] using hAB
  have hKLower : D * K ≤ A * H := by
    dsimp [D, K, tailPositiveCount]
    exact Nat.mul_div_le _ _
  have hKUpper : A * H < D * (K + 1) := by
    dsimp [D, K, tailPositiveCount]
    exact Nat.lt_mul_div_succ (A * H) hD
  have hAleD : A ≤ D := by
    dsimp [D]
    omega
  constructor
  · have hAM : A * M ≤ D * M :=
      Nat.mul_le_mul_right M hAleD
    have hscaled :
        D * (A * q) < D * (K + M + 1) := by
      calc
        D * (A * q) = A * (D * q) := by ring
        _ ≤ A * (H + M) :=
          Nat.mul_le_mul_left A (by simpa [D] using htailLower)
        _ = A * H + A * M := by ring
        _ < D * (K + 1) + D * M :=
          Nat.add_lt_add_of_lt_of_le hKUpper hAM
        _ = D * (K + M + 1) := by ring
    have hstrict : A * q < K + M + 1 :=
      Nat.lt_of_mul_lt_mul_left hscaled
    simpa [K] using (Nat.lt_succ_iff.mp (by
      simpa [Nat.add_assoc] using hstrict))
  · have hHle :
        H ≤ D * q + (M + A + B) :=
      Nat.le_of_lt (by simpa [D] using htailUpper)
    have hAD :
        A * (M + A + B) ≤ D * (M + A + B) :=
      Nat.mul_le_mul_right (M + A + B) hAleD
    have hscaled :
        D * K ≤ D * (A * q + (M + A + B)) := by
      calc
        D * K ≤ A * H := hKLower
        _ ≤ A * (D * q + (M + A + B)) :=
          Nat.mul_le_mul_left A hHle
        _ = D * (A * q) + A * (M + A + B) := by ring
        _ ≤ D * (A * q) + D * (M + A + B) :=
          Nat.add_le_add_left hAD _
        _ = D * (A * q + (M + A + B)) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled hD

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
