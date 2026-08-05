import SchedulingPaper.BinaryCurve

/-!
# Accounting identities for the hidden stopping adversary

The operational adversary and its first-crossing invariant are separate from
these calculations.  Here `n,v,e,d` are real-valued multiplicities (integer
counts embed into this statement), `x = n-v-e-d`, and the exact canonical
schedule from the paper is compared with its quadratic leading form.
-/

namespace SchedulingPaper

noncomputable section

/-- Exact relaxed online cost in equation (4.7), with
`x = n - v - e - d`. -/
def stoppingAlgExact (u n v e d : ℝ) : ℝ :=
  let x := n - v - e - d
  u * (v * n - v * (v - 1) / 2) +
    (1 + u) * (e * (n - v) - e * (e - 1) / 2) +
    d * (n - v - e) + x * (d + x) - x * (x - 1) / 2 +
    u * d * (d + 1) / 2

/-- Exact offline cost in equation (4.8). -/
def stoppingOptExact (u n e d : ℝ) : ℝ :=
  n * (n + 1) / 2 + (u - 1) * (e + d) * (e + d + 1) / 2

/-- Twice the quadratic online coefficient after normalization. -/
def stoppingAlgLeading (u ν δ ell : ℝ) : ℝ :=
  1 + 2 * δ * (1 - u * ν) + (u - 1) * δ ^ 2 +
    2 * ν * (ν + u - 2) + ell ^ 2 +
    2 * ell * (ν + u - 1 - u * δ)

/-- Twice the quadratic offline coefficient after normalization. -/
def stoppingOptLeading (u ν δ : ℝ) : ℝ :=
  1 + (u - 1) * (δ - ν) ^ 2

/-- The exact online expression differs from its quadratic leading term only
by the displayed diagonal correction. -/
theorem stoppingAlgExact_eq_leading {u n v e d : ℝ} (hn : n ≠ 0) :
    2 * stoppingAlgExact u n v e d =
      n ^ 2 * stoppingAlgLeading u (v / n) ((v + e + d) / n) (e / n) +
        (d * u - d + e * u + n + u * v - v) := by
  unfold stoppingAlgExact stoppingAlgLeading
  dsimp only
  field_simp [hn]
  ring

/-- The analogous exact offline diagonal correction. -/
theorem stoppingOptExact_eq_leading {u n v e d : ℝ} (hn : n ≠ 0) :
    2 * stoppingOptExact u n e d =
      n ^ 2 * stoppingOptLeading u (v / n) ((v + e + d) / n) +
        (d * u - d + e * u - e + n) := by
  unfold stoppingOptExact stoppingOptLeading
  field_simp [hn]
  ring

/-- Equation (4.6): after writing `σ = 1-ν`,
`δ = ν+σy`, and `λ = σb`, the competitive excess splits into the raw
part and the binary stopping quadratic. -/
theorem stoppingLeading_decomposition (u ρ ν y b : ℝ) :
    stoppingAlgLeading u ν (ν + (1 - ν) * y) ((1 - ν) * b) -
        ρ * stoppingOptLeading u ν (ν + (1 - ν) * y) =
      (u - ρ) * (1 - (1 - ν) ^ 2) +
        (1 - ν) ^ 2 * stoppingF u ρ y b := by
  unfold stoppingAlgLeading stoppingOptLeading stoppingF
  ring

/-- Equivalent form using the paper's symbol `σ`. -/
theorem stoppingLeading_decomposition_sigma
    (u ρ σ y b : ℝ) :
    stoppingAlgLeading u (1 - σ) (1 - σ + σ * y) (σ * b) -
        ρ * stoppingOptLeading u (1 - σ) (1 - σ + σ * y) =
      (u - ρ) * (1 - σ ^ 2) + σ ^ 2 * stoppingF u ρ y b := by
  have hσ : 1 - (1 - σ) = σ := by ring
  simpa only [hσ] using
    stoppingLeading_decomposition u ρ (1 - σ) y b

/-- If `ρ ≤ u`, the raw part of the decomposition is nonnegative for
`σ ∈ [0,1]`. -/
theorem stopping_raw_part_nonneg {u ρ σ : ℝ}
    (hρ : ρ ≤ u) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 ≤ (u - ρ) * (1 - σ ^ 2) := by
  exact mul_nonneg (sub_nonneg.mpr hρ)
    (by nlinarith [sq_nonneg σ, mul_self_le_mul_self hσ0 hσ1])

/-- Combining a nonnegative raw part with a nonnegative stopping
certificate gives a nonnegative leading excess. -/
theorem stoppingLeading_excess_nonneg
    {u ρ σ y b : ℝ} (hρ : ρ ≤ u)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hf : 0 ≤ stoppingF u ρ y b) :
    0 ≤ stoppingAlgLeading u (1 - σ) (1 - σ + σ * y) (σ * b) -
      ρ * stoppingOptLeading u (1 - σ) (1 - σ + σ * y) := by
  rw [stoppingLeading_decomposition_sigma]
  exact add_nonneg (stopping_raw_part_nonneg hρ hσ0 hσ1)
    (mul_nonneg (sq_nonneg σ) hf)

end

end SchedulingPaper
