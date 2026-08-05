import SchedulingPaper.Asymptotics

/-!
# Checked algebra from the low finite-cap regimes

This file covers two elementary certificates used in the finite curve:

* the `Raw` policy is optimal for `u ≤ 1` and is `u`-competitive for
  `u ≥ 1`;
* the two one-variable inequalities in the Zero-prefix extension lemma.

It does not yet formalize the endpoint-reduction argument that turns an
arbitrary UTE execution into those scalar inequalities.
-/

namespace SchedulingPaper

noncomputable section

/-- Objective value of the paper's `Raw` policy: every one of `n` jobs is
executed untested for the common duration `u`. -/
def rawValue (u : ℝ) (n : ℕ) : ℝ := prefixCost (List.replicate n u)

theorem rawValue_eq (u : ℝ) (n : ℕ) :
    rawValue u n = u * triangular n := by
  exact prefixCost_replicate n u

/-- At a cap at most one, every clairvoyant effective length is exactly the
raw duration. -/
theorem effectiveLengths_eq_replicate_of_cap_le_one
    (I : Instance) (u : ℝ) (hcap : I.cap = .finite u) (hu : u ≤ 1) :
    I.effectiveLengths = List.replicate I.jobs.length u := by
  unfold Instance.effectiveLengths
  rw [← List.map_const']
  apply List.map_congr_left
  intro job _hj
  rw [hcap]
  simp only [effectiveLength_finite]
  exact min_eq_left (by linarith [job.processingTime_nonneg])

/-- First branch of the finite upper curve: `Raw` attains the offline optimum
when `0 < u ≤ 1`. -/
theorem raw_optimal_of_cap_le_one
    (I : Instance) (u : ℝ) (hcap : I.cap = .finite u) (hu : u ≤ 1) :
    rawValue u I.jobs.length = offlineValue I := by
  have heff := effectiveLengths_eq_replicate_of_cap_le_one I u hcap hu
  have hsorted : (List.replicate I.jobs.length u).Pairwise (· ≤ ·) := by simp
  calc
    rawValue u I.jobs.length =
        prefixCost (List.replicate I.jobs.length u) := rfl
    _ = pairCost (List.replicate I.jobs.length u) :=
      prefixCost_eq_pairCost_of_pairwise hsorted
    _ = pairCost I.effectiveLengths := by rw [heff]
    _ = offlineValue I := (shortestFirst_pair_formula I.effectiveLengths).symm

/-- Second branch's elementary upper certificate: for `u ≥ 1`, the Raw
policy costs at most `u · OPT`. -/
theorem raw_competitive_of_one_le_cap
    (I : Instance) (u : ℝ) (hcap : I.cap = .finite u) (hu : 1 ≤ u) :
    rawValue u I.jobs.length ≤ u * offlineValue I := by
  have hop := finite_offlineValue_quadratic_lower I u hcap
  rw [min_eq_right hu] at hop
  simp only [one_mul] at hop
  rw [rawValue_eq]
  exact mul_le_mul_of_nonneg_left hop (by linarith)

/-- The golden ratio used at the fourth/fifth regime join. -/
def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

theorem goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem goldenRatio_mul_sub_one :
    goldenRatio * (goldenRatio - 1) = 1 := by
  nlinarith [goldenRatio_sq]

/-- First scalar face in the Zero-prefix extension lemma. -/
theorem zeroPrefix_uncapped_face (y : ℝ) :
    (1 + 2 * y) / (1 + y ^ 2) ≤ goldenRatio := by
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  rw [← mul_le_mul_iff_of_pos_left goldenRatio_pos]
  nlinarith [goldenRatio_sq, sq_nonneg (goldenRatio * y - 1)]

/-- Second scalar face in the Zero-prefix extension lemma. -/
theorem zeroPrefix_capped_face {s : ℝ} (hs : 0 < s) (y : ℝ) :
    1 + 2 * y / (1 + s * y ^ 2) ≤ 1 + 1 / Real.sqrt s := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have ht_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hden : 0 < 1 + s * y ^ 2 := by positivity
  have hfrac : 2 * y / (1 + s * y ^ 2) ≤ 1 / Real.sqrt s := by
    rw [div_le_div_iff₀ hden ht]
    nlinarith [sq_nonneg (Real.sqrt s * y - 1)]
  linarith

end

end SchedulingPaper
