import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A uniform one-step Taylor bound

The potential proof only needs an `O(1)` remainder, not the sharp factor
`L/2`.  The mean-value theorem therefore gives a particularly robust Lean
interface: if the derivative along every unit transition is at most its
initial value plus a uniform constant, the whole transition has the same
uniform additive loss.
-/

namespace SchedulingPaper

/-- Mean-value form of the unit-step Taylor estimate. -/
theorem unit_taylor_upper_of_deriv_le
    {φ : ℝ → ℝ} {slope C : ℝ}
    (hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1))
    (hdiff : DifferentiableOn ℝ φ (Set.Ioo (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, deriv φ t ≤ slope + C) :
    φ 1 - φ 0 ≤ slope + C := by
  have h :=
    (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
      hcont (by simpa using hdiff) (by
        intro t ht
        exact hderiv t (by simpa using ht))
      0 (by simp) 1 (by simp) (by norm_num)
  norm_num at h
  simpa [mul_one] using h

/-- The same estimate when a named derivative `d` is supplied along the
segment. -/
theorem unit_taylor_upper_of_hasDerivAt
    {φ d : ℝ → ℝ} {C : ℝ}
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (d t) t)
    (hvariation :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, d t ≤ d 0 + C) :
    φ 1 - φ 0 ≤ d 0 + C := by
  apply unit_taylor_upper_of_deriv_le
  · intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact
      (hderiv t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact hvariation t ht

/-- A real-valued Lipschitz estimate for the derivative implies the
variation hypothesis needed above.  This formulation avoids committing the
bank proof to a particular normed-space representation of its raw state. -/
theorem unit_taylor_upper_of_deriv_variation
    {φ d : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (d t) t)
    (hvariation :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, |d t - d 0| ≤ C * |t|) :
    φ 1 - φ 0 ≤ d 0 + C := by
  apply unit_taylor_upper_of_hasDerivAt hderiv
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2.le
  have hvar := hvariation t htIcc
  have hprod : C * |t| ≤ C := by
    nlinarith [mul_le_mul_of_nonneg_left htAbs hC]
  have habove : d t - d 0 ≤ |d t - d 0| := le_abs_self _
  linarith

end SchedulingPaper
