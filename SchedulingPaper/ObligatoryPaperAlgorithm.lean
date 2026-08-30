import SchedulingPaper.ObligatoryGrowingCutoffFourThirds
import SchedulingPaper.ObligatoryGrowingCutoffUniversalRates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The single obligatory algorithm used by the paper

The public family in this file has the manuscript parameters

* `k = floor(n^(3/4))`,
* `d = floor(n^(1/4))`,
* `B = 32 + n^(1/20)`, and
* `η = B/d`.

Both its worst-case `4/3` theorem and its bounded instance-optimal theorem
refer to `paperGrowingRunCost` below, so the identity of the algorithm is a
literal definitional fact rather than a prose convention.
-/

namespace SchedulingPaper
namespace ObligatoryPaper

open Randomized
open RandomizedAnnounced
open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.AnnouncedRoundedLower
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace
open ObligatoryInstance

noncomputable section
attribute [local instance] Classical.propDecidable

def paperGrowth (n : ℕ) : ℝ := (fourthRoot n) ^ (1 / 5 : ℝ)

def paperCutoff (n : ℕ) : ℝ := 32 + paperGrowth n

def paperBins (n : ℕ) : ℕ := concreteBins n

def paperPilotSize (n : ℕ) : ℕ := concreteSampleSize n

def paperRest (n : ℕ) : ℕ := n - paperPilotSize n

def paperMesh (n : ℕ) : ℝ := paperCutoff n / paperBins n

def paperGrowingRunCost
    (n : ℕ) (hR : 12 ≤ fourthRoot n) (p : Fin n → ℝ) :
    Equiv.Perm (Fin (paperPilotSize n + paperRest n)) → ℝ :=
  let k := paperPilotSize n
  let r := paperRest n
  let d := paperBins n
  let η := paperMesh n
  let hη : 0 < η := by
    dsimp [η, paperMesh, paperCutoff, paperGrowth, paperBins]
    have hd := (concrete_parameter_bounds n hR).1
    have hdR : (0 : ℝ) < concreteBins n := by exact_mod_cast hd
    have hR0 : 0 ≤ fourthRoot n := by linarith
    have hg : 0 ≤ (fourthRoot n) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hR0 _
    have hnum : 0 < 32 + (fourthRoot n) ^ (1 / 5 : ℝ) := by linarith
    exact div_pos hnum hdR
  let p' : Fin (k + r) → ℝ :=
    fun i => p (Fin.cast (by
      unfold k r paperPilotSize paperRest
      exact concrete_size_eq n hR) i)
  physicalGrowingRunCost (k + r) k d (paperCutoff n) η hη p'

theorem paperMesh_pos (n : ℕ) (hR : 12 ≤ fourthRoot n) :
    0 < paperMesh n := by
  unfold paperMesh paperCutoff paperGrowth paperBins
  have hd : 0 < concreteBins n := (concrete_parameter_bounds n hR).1
  have hdR : (0 : ℝ) < concreteBins n := by exact_mod_cast hd
  have hg : 0 ≤ (fourthRoot n) ^ (1 / 5 : ℝ) := Real.rpow_nonneg
    (by linarith [hR] : 0 ≤ fourthRoot n) _
  exact div_pos (by linarith) hdR

theorem paperCutoff_eq_bins_mul_mesh (n : ℕ)
    (hR : 12 ≤ fourthRoot n) :
    (paperBins n : ℝ) * paperMesh n = paperCutoff n := by
  unfold paperMesh paperBins
  have hd : (concreteBins n : ℝ) ≠ 0 := by
    exact_mod_cast (concrete_parameter_bounds n hR).1.ne'
  field_simp

theorem paperMesh_le_cutoff_div_twelve (n : ℕ)
    (hR : 12 ≤ fourthRoot n) :
    paperMesh n ≤ paperCutoff n / 12 := by
  have hdNat : 12 ≤ concreteBins n := by
    unfold concreteBins
    exact Nat.le_floor hR
  have hd : (12 : ℝ) ≤ concreteBins n := by exact_mod_cast hdNat
  have hB0 : 0 ≤ paperCutoff n := by
    unfold paperCutoff paperGrowth
    have := Real.rpow_nonneg (by linarith [hR] : 0 ≤ fourthRoot n) (1 / 5 : ℝ)
    linarith
  unfold paperMesh paperBins
  exact div_le_div_of_nonneg_left hB0 (by norm_num) hd

/-- Finite worst-case theorem for the literal parameter family printed in
Algorithm 2. -/
theorem paperGrowingPolicy_four_thirds_finite
    (n : ℕ) (hR : 12 ≤ fourthRoot n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    uniformAverage
        (physicalGrowingRunCost
          (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
          (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
      4 / 3 * finiteObligatoryOPT p +
        (paperPilotSize n + paperRest n : ℝ) ^ 2 *
          (paperCutoff n * (paperCutoff n + 1) *
                (3 * paperCutoff n + 8) / 6 *
              Real.sqrt (((paperBins n + 2 : ℕ) : ℝ) /
                (paperPilotSize n : ℝ)) +
            2 / 3 * (paperCutoff n + 2) * paperMesh n) +
        (paperCutoff n + 1) *
          ((paperPilotSize n + paperRest n : ℝ) * paperPilotSize n / 2 +
            (paperPilotSize n : ℝ) ^ 2) := by
  obtain ⟨hd, hk, hklt, _hfixedCutoff, _hfixedMesh, _hmesh12,
      _hmeshR, _hnR, _hkR, _hsqrt⟩ := concrete_parameter_bounds n hR
  have hr : 0 < paperRest n := by
    unfold paperRest paperPilotSize
    omega
  have hcard : 1 < paperPilotSize n + paperRest n := by
    rw [show paperPilotSize n + paperRest n = n by
      simpa [paperPilotSize, paperRest] using concrete_size_eq n hR]
    omega
  apply uniformAverage_physicalGrowingRunCost_four_thirds
    (paperPilotSize n) (paperRest n) (paperBins n) hk hr hcard
      (paperCutoff n) (paperMesh n) (paperMesh_pos n hR)
  · unfold paperCutoff paperGrowth
    have hg := Real.rpow_nonneg
      (by linarith [hR] : 0 ≤ fourthRoot n) (1 / 5 : ℝ)
    linarith
  · exact paperCutoff_eq_bins_mul_mesh n hR
  · exact paperMesh_le_cutoff_div_twelve n hR
  · exact hp

/-- Normalized finite upper-side loss of the manuscript family, including
the `3η` bridge from its fine grid to the exact population optimum. -/
def paperFineNormalizedError (L : ℝ) (n : ℕ) : ℝ :=
  let k := paperPilotSize n
  let d := paperBins n
  let B := paperCutoff n
  let η := paperMesh n
  3 * η +
    6 * ((d + 1 : ℕ) * η + 2) *
      Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) +
    (B + 1) * k / (2 * n) +
    (1 + L) / (2 * n) +
    (B + 1) * ((k : ℝ) / n) ^ 2

def paperScale (n : ℕ) : ℝ := (fourthRoot n) ^ (1 / 4 : ℝ)

theorem fourthRoot_tendsto_atTop :
    Filter.Tendsto fourthRoot Filter.atTop Filter.atTop := by
  unfold fourthRoot
  exact Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem paperScale_tendsto_atTop :
    Filter.Tendsto paperScale Filter.atTop Filter.atTop := by
  unfold paperScale
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    fourthRoot_tendsto_atTop

theorem eventually_fourthRoot_ge (C : ℝ) :
    ∀ᶠ n in Filter.atTop, C ≤ fourthRoot n :=
  fourthRoot_tendsto_atTop.eventually (Filter.eventually_ge_atTop C)

theorem paperScale_pow_four (n : ℕ) : paperScale n ^ 4 = fourthRoot n := by
  unfold paperScale
  convert Real.rpow_inv_natCast_pow (fourthRoot_nonneg n) (by omega : (4 : ℕ) ≠ 0) using 1 <;>
    norm_num

theorem paperScale_pow_sixteen (n : ℕ) : paperScale n ^ 16 = n := by
  calc
    paperScale n ^ 16 = (paperScale n ^ 4) ^ 4 := by ring
    _ = (fourthRoot n) ^ 4 := by rw [paperScale_pow_four]
    _ = n := fourthRoot_pow_four n

/-- Elementary scale bounds used by both vanishing-error proofs. -/
theorem paper_parameter_scale_bounds
    (n : ℕ) (hR : 12 ≤ fourthRoot n) :
    let Q := paperScale n
    1 ≤ Q ∧ paperCutoff n ≤ 33 * Q ∧
      paperMesh n ≤ 66 / Q ^ 3 ∧
      Real.sqrt (((paperBins n + 2 : ℕ) : ℝ) /
        (paperPilotSize n : ℝ)) ≤ 2 / Q ^ 4 ∧
      (paperPilotSize n : ℝ) / n ≤ 1 / Q ^ 4 ∧
      (1 : ℝ) / n = 1 / Q ^ 16 := by
  dsimp only
  let Q := paperScale n
  let R := fourthRoot n
  obtain ⟨hd, hk, hklt, _hfixedCutoff, _hfixedMesh, _hfixedMesh12,
      _hfixedMeshR, hNR, hkR, hsqrt⟩ := concrete_parameter_bounds n hR
  have hR1 : 1 ≤ R := by dsimp [R]; linarith
  have hQ4 : Q ^ 4 = R := by simpa [Q, R] using paperScale_pow_four n
  have hQ0 : 0 < Q := by
    dsimp [Q, paperScale]
    exact Real.rpow_pos_of_pos (by dsimp [R] at hR1 ⊢; linarith) _
  have hQ1 : 1 ≤ Q := by
    dsimp [Q, paperScale]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa [R] using hR1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hGrowthQ : paperGrowth n ≤ Q := by
    unfold paperGrowth
    dsimp [Q, paperScale]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num : (1 / 5 : ℝ) ≤ 1 / 4)
  have hBQ : paperCutoff n ≤ 33 * Q := by
    unfold paperCutoff
    nlinarith [hGrowthQ, mul_le_mul_of_nonneg_left hQ1 (by norm_num : (0 : ℝ) ≤ 32)]
  have hdLower : R - 1 ≤ (paperBins n : ℝ) := by
    dsimp [R, paperBins, concreteBins]
    exact (Nat.lt_floor_add_one (fourthRoot n) :
      fourthRoot n < (⌊fourthRoot n⌋₊ : ℝ) + 1).le
      |> (fun h => by linarith)
  have hhalfD : R / 2 ≤ (paperBins n : ℝ) := by
    have : 2 ≤ R := by dsimp [R]; linarith
    linarith
  have hη0 := (paperMesh_pos n hR).le
  have hmulη := mul_le_mul_of_nonneg_right hhalfD hη0
  have hηQ : paperMesh n ≤ 66 / Q ^ 3 := by
    rw [← paperCutoff_eq_bins_mul_mesh n hR] at hBQ
    have hRQ : R = Q ^ 4 := hQ4.symm
    rw [hRQ] at hmulη
    have hbound : Q ^ 4 / 2 * paperMesh n ≤ 33 * Q :=
      hmulη.trans hBQ
    have hQ3pos : 0 < Q ^ 3 := pow_pos hQ0 3
    rw [le_div_iff₀ hQ3pos]
    nlinarith [hbound]
  have hsqrtQ : Real.sqrt (((paperBins n + 2 : ℕ) : ℝ) /
      (paperPilotSize n : ℝ)) ≤ 2 / Q ^ 4 := by
    simpa [paperBins, paperPilotSize, hQ4, R] using hsqrt
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpilotRatio : (paperPilotSize n : ℝ) / n ≤ 1 / Q ^ 4 := by
    have hNR' : (n : ℝ) = Q ^ 16 := by
      rw [paperScale_pow_sixteen]
    have hkR' : (paperPilotSize n : ℝ) ≤ Q ^ 12 := by
      calc
        (paperPilotSize n : ℝ) ≤ R ^ 3 := by
          simpa [paperPilotSize, R] using hkR
        _ = Q ^ 12 := by rw [← hQ4]; ring
    rw [hNR']
    have hQ4pos : 0 < Q ^ 4 := pow_pos hQ0 4
    have hQ16pos : 0 < Q ^ 16 := pow_pos hQ0 16
    rw [div_le_div_iff₀ hQ16pos hQ4pos]
    nlinarith [mul_le_mul_of_nonneg_right hkR' (pow_nonneg hQ0.le 4)]
  have hinvN : (1 : ℝ) / n = 1 / Q ^ 16 := by
    rw [paperScale_pow_sixteen]
  exact ⟨hQ1, hBQ, hηQ, hsqrtQ, hpilotRatio, hinvN⟩

theorem paperUpperRawError_eq (L : ℝ) (n : ℕ)
    (hR : 12 ≤ fourthRoot n) :
    growingUpperRawError
        (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
        (paperCutoff n) (paperMesh n) L =
      (paperPilotSize n + paperRest n : ℝ) ^ 2 *
        (paperFineNormalizedError L n - 3 * paperMesh n) := by
  have hnR : (0 : ℝ) < n := by
    have hk := (concrete_parameter_bounds n hR).2.1
    have hklt := (concrete_parameter_bounds n hR).2.2.1
    exact_mod_cast (by omega : 0 < n)
  unfold growingUpperRawError paperFineNormalizedError
  dsimp only
  dsimp [paperPilotSize, paperRest, paperBins, paperCutoff, paperMesh]
  push_cast
  have htotal : concreteSampleSize n + (n - concreteSampleSize n) = n :=
    concrete_size_eq n hR
  have htotalR : (concreteSampleSize n : ℝ) + (n - concreteSampleSize n : ℕ) = n := by
    exact_mod_cast htotal
  rw [htotalR]
  field_simp [hnR.ne']
  ring

set_option maxHeartbeats 3000000 in
theorem eventually_paperFineNormalizedError_le
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ n in Filter.atTop,
      0 ≤ paperFineNormalizedError L n ∧
        paperFineNormalizedError L n ≤ (2000 + L) / paperScale n := by
  filter_upwards [eventually_fourthRoot_ge 12] with n hR
  let Q := paperScale n
  let B := paperCutoff n
  let η := paperMesh n
  let d := paperBins n
  let k := paperPilotSize n
  obtain ⟨hQ1, hBQ, hηQ, hsqrtQ, hkRatio, hinvN⟩ :=
    paper_parameter_scale_bounds n hR
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ1
  have hQ3 : Q ≤ Q ^ 3 := by nlinarith [sq_nonneg Q]
  have hQ4 : Q ≤ Q ^ 4 := by
    have := mul_le_mul_of_nonneg_left hQ3 hQ0.le
    nlinarith
  have hQ7 : Q ≤ Q ^ 7 := by
    have hQ6 : 1 ≤ Q ^ 6 := one_le_pow₀ hQ1
    nlinarith [mul_le_mul_of_nonneg_left hQ6 hQ0.le]
  have hQ8 : Q ≤ Q ^ 8 := by
    have hQ7' : 1 ≤ Q ^ 7 := one_le_pow₀ hQ1
    nlinarith [mul_le_mul_of_nonneg_left hQ7' hQ0.le]
  have hQ16 : Q ≤ Q ^ 16 := by
    have hQ15 : 1 ≤ Q ^ 15 := one_le_pow₀ hQ1
    nlinarith [mul_le_mul_of_nonneg_left hQ15 hQ0.le]
  have hinv3 : 1 / Q ^ 3 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ3
  have hinv7 : 1 / Q ^ 7 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ7
  have hinv16 : 1 / Q ^ 16 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ16
  have hB1 : B + 1 ≤ 34 * Q := by nlinarith
  have hηLe66Q : η ≤ 66 * Q := by
    calc
      η ≤ 66 / Q ^ 3 := hηQ
      _ ≤ 66 / Q := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 66)
      _ ≤ 66 * Q := by
        have hinvLe : 1 / Q ≤ Q := by
          rw [div_le_iff₀ hQ0]
          nlinarith
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hinvLe (by norm_num : (0 : ℝ) ≤ 66)
  have hspan : ((d + 1 : ℕ) : ℝ) * η + 2 ≤ 101 * Q := by
    have hgrid := paperCutoff_eq_bins_mul_mesh n hR
    dsimp [B, η, d] at hBQ hηLe66Q hgrid ⊢
    push_cast
    rw [show ((paperBins n : ℝ) + 1) * paperMesh n =
        (paperBins n : ℝ) * paperMesh n + paperMesh n by ring, hgrid]
    nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) :=
    Real.sqrt_nonneg _
  have hspan0 : 0 ≤ ((d + 1 : ℕ) : ℝ) * η + 2 := by
    have hη0 := (paperMesh_pos n hR).le
    positivity
  have hstatMul := mul_le_mul hspan hsqrtQ hsqrt0
    (by positivity : 0 ≤ 101 * Q)
  have hstat : 6 * (((d + 1 : ℕ) : ℝ) * η + 2) *
      Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) ≤ 1212 / Q := by
    have hqCancel : 101 * Q * (2 / Q ^ 4) = 202 / Q ^ 3 := by
      field_simp [hQ0.ne']
      ring
    rw [hqCancel] at hstatMul
    have hscaled := mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 1212)
    have hscaled' : 1212 / Q ^ 3 ≤ 1212 / Q := by
      simpa [div_eq_mul_inv] using hscaled
    dsimp [d, k] at hstatMul
    have hmul6' : 6 * (((d + 1 : ℕ) : ℝ) * η + 2) *
        Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) ≤ 1212 / Q ^ 3 := by
      calc
        6 * (((d + 1 : ℕ) : ℝ) * η + 2) *
            Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) =
            6 * ((((d + 1 : ℕ) : ℝ) * η + 2) *
              Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ))) := by ring
        _ ≤ 6 * (202 / Q ^ 3) :=
          mul_le_mul_of_nonneg_left hstatMul (by norm_num)
        _ = 1212 / Q ^ 3 := by ring
    exact hmul6'.trans hscaled'
  have hkRatio0 : 0 ≤ (k : ℝ) / n := by positivity
  have hinv4_0 : 0 ≤ 1 / Q ^ 4 := by positivity
  have hcrossMul := mul_le_mul hB1 hkRatio hkRatio0
    (by positivity : 0 ≤ 34 * Q)
  have hcross : (B + 1) * k / (2 * n) ≤ 17 / Q := by
    have hcancel : 34 * Q * (1 / Q ^ 4) / 2 = 17 / Q ^ 3 := by
      field_simp [hQ0.ne']
      ring
    have hbase : (B + 1) * ((k : ℝ) / n) / 2 ≤ 17 / Q ^ 3 := by
      rw [← hcancel]
      exact div_le_div_of_nonneg_right hcrossMul (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 17)
    have hscaled' : 17 / Q ^ 3 ≤ 17 / Q := by
      simpa [div_eq_mul_inv] using hscaled
    convert hbase.trans hscaled' using 1 <;> field_simp <;> ring
  have hdiag : (1 + L) / (2 * n) ≤ (1 + L) / (2 * Q) := by
    rw [show (1 + L) / (2 * (n : ℝ)) = (1 + L) / 2 * (1 / n) by ring,
      hinvN]
    have hscaled := mul_le_mul_of_nonneg_left hinv16
      (by linarith : 0 ≤ (1 + L) / 2)
    convert hscaled using 1 <;> ring
  have hkSq : ((k : ℝ) / n) ^ 2 ≤ (1 / Q ^ 4) ^ 2 := by
    nlinarith
  have hpMul := mul_le_mul hB1 hkSq (sq_nonneg _)
    (by positivity : 0 ≤ 34 * Q)
  have hpCancel : 34 * Q * (1 / Q ^ 4) ^ 2 = 34 / Q ^ 7 := by
    field_simp [hQ0.ne']
  have hpTerm : (B + 1) * ((k : ℝ) / n) ^ 2 ≤ 34 / Q := by
    rw [hpCancel] at hpMul
    have hscaled := mul_le_mul_of_nonneg_left hinv7 (by norm_num : (0 : ℝ) ≤ 34)
    exact hpMul.trans (by simpa [div_eq_mul_inv] using hscaled)
  have hmeshTerm : 3 * η ≤ 198 / Q := by
    have hηQ' : η ≤ 66 / Q ^ 3 := by simpa [η, Q] using hηQ
    have h := mul_le_mul_of_nonneg_left hηQ' (by norm_num : (0 : ℝ) ≤ 3)
    have hscaled := mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 198)
    have hscaled' : 198 / Q ^ 3 ≤ 198 / Q := by
      simpa [div_eq_mul_inv] using hscaled
    have h' : 3 * η ≤ 198 / Q ^ 3 := by
      calc
        3 * η ≤ 3 * (66 / Q ^ 3) := h
        _ = 198 / Q ^ 3 := by ring
    exact h'.trans hscaled'
  have herror0 : 0 ≤ paperFineNormalizedError L n := by
    unfold paperFineNormalizedError
    dsimp only
    have hη0 := (paperMesh_pos n hR).le
    have hB0 : 0 ≤ paperCutoff n := by
      unfold paperCutoff paperGrowth
      positivity
    positivity
  refine ⟨herror0, ?_⟩
  unfold paperFineNormalizedError
  dsimp only
  dsimp [Q, B, η, d, k] at hstat hcross hdiag hpTerm hmeshTerm ⊢
  simp only [div_eq_mul_inv] at hstat hcross hdiag hpTerm hmeshTerm ⊢
  have hinvQ0 : 0 ≤ (paperScale n)⁻¹ := by positivity
  have hcoeff :
      198 * (paperScale n)⁻¹ + 1212 * (paperScale n)⁻¹ +
          17 * (paperScale n)⁻¹ +
          (1 + L) * (2 * paperScale n)⁻¹ +
          34 * (paperScale n)⁻¹ ≤
        (2000 + L) * (paperScale n)⁻¹ := by
    have htwo : (2 * paperScale n)⁻¹ = (1 / 2 : ℝ) * (paperScale n)⁻¹ := by
      field_simp [hQ0.ne']
    rw [htwo]
    nlinarith
  nlinarith

theorem paperFineNormalizedError_tendsto_zero
    {L : ℝ} (hL : 0 < L) :
    Filter.Tendsto (paperFineNormalizedError L) Filter.atTop (nhds 0) := by
  have henv : Filter.Tendsto (fun n => (2000 + L) / paperScale n)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop paperScale_tendsto_atTop (2000 + L)
  apply squeeze_zero'
  · exact (eventually_paperFineNormalizedError_le hL).mono fun n h => h.1
  · exact (eventually_paperFineNormalizedError_le hL).mono fun n h => h.2
  · exact henv

theorem paperGrowth_tendsto_atTop :
    Filter.Tendsto paperGrowth Filter.atTop Filter.atTop := by
  unfold paperGrowth
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
    fourthRoot_tendsto_atTop

theorem eventually_paperFineCover (L : ℝ) :
    ∀ᶠ n in Filter.atTop, 1 + L + paperMesh n ≤ paperCutoff n := by
  filter_upwards [eventually_fourthRoot_ge 12,
      paperScale_tendsto_atTop.eventually (Filter.eventually_ge_atTop 5),
      paperGrowth_tendsto_atTop.eventually (Filter.eventually_ge_atTop L)]
      with n hR hQ hGrowth
  have hη := (paper_parameter_scale_bounds n hR).2.2.1
  have hη1 : paperMesh n ≤ 1 := by
    have hQ3 : (125 : ℝ) ≤ paperScale n ^ 3 := by
      have : (5 : ℝ) ^ 3 ≤ paperScale n ^ 3 := by gcongr
      norm_num at this ⊢
      exact this
    have hpos : 0 < paperScale n ^ 3 := by positivity
    have : 66 / paperScale n ^ 3 ≤ 1 := by
      rw [div_le_one hpos]
      linarith
    exact hη.trans this
  unfold paperCutoff
  linarith

def paperInstanceError (L : ℝ) (n : ℕ) : ℝ :=
  concreteUniversalGrowingError L n + paperFineNormalizedError L n

theorem paperInstanceError_tendsto_zero
    {L : ℝ} (hL : 0 < L) :
    Filter.Tendsto (paperInstanceError L) Filter.atTop (nhds 0) := by
  unfold paperInstanceError
  simpa using (concreteUniversalGrowingError_tendsto_zero L).add
    (paperFineNormalizedError_tendsto_zero hL)

/-- Multiplicative loss in the worst-case theorem for the same literal
policy family. -/
def paperWorstCaseError (n : ℕ) : ℝ :=
  let k := paperPilotSize n
  let d := paperBins n
  let B := paperCutoff n
  let η := paperMesh n
  2 * (B * (B + 1) * (3 * B + 8) / 6 *
        Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) +
      2 / 3 * (B + 2) * η +
      (B + 1) * (k / (2 * (n : ℝ)) + ((k : ℝ) / n) ^ 2))

theorem paperGrowingPolicy_four_thirds_multiplicative
    (n : ℕ) (hR : 12 ≤ fourthRoot n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    uniformAverage
        (physicalGrowingRunCost
          (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
          (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
      (4 / 3 + paperWorstCaseError n) * finiteObligatoryOPT p := by
  have hfinite := paperGrowingPolicy_four_thirds_finite n hR p hp
  have htotal : paperPilotSize n + paperRest n = n := by
    simpa [paperPilotSize, paperRest] using concrete_size_eq n hR
  have hoptBase := finiteObligatoryOPT_lower p hp
  have hopt : (n : ℝ) ^ 2 / 2 ≤ finiteObligatoryOPT p := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hbase : (n : ℝ) ^ 2 / 2 ≤ n * (n + 1) / 2 := by nlinarith
    have hcast : (paperPilotSize n + paperRest n : ℝ) = n := by exact_mod_cast htotal
    exact hbase.trans (by simpa [hcast] using hoptBase)
  have herror0 : 0 ≤ paperWorstCaseError n := by
    unfold paperWorstCaseError
    dsimp only
    have hB0 : 0 ≤ paperCutoff n := by unfold paperCutoff paperGrowth; positivity
    have hη0 := (paperMesh_pos n hR).le
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hopt herror0
  have herrorEq :
      paperWorstCaseError n * ((n : ℝ) ^ 2 / 2) =
        (n : ℝ) ^ 2 *
          (paperCutoff n * (paperCutoff n + 1) *
                (3 * paperCutoff n + 8) / 6 *
              Real.sqrt (((paperBins n + 2 : ℕ) : ℝ) /
                (paperPilotSize n : ℝ)) +
            2 / 3 * (paperCutoff n + 2) * paperMesh n) +
        (paperCutoff n + 1) *
          ((n : ℝ) * paperPilotSize n / 2 +
            (paperPilotSize n : ℝ) ^ 2) := by
    unfold paperWorstCaseError
    dsimp only
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le
        (concrete_parameter_bounds n hR).2.1
        (Nat.le_of_lt (concrete_parameter_bounds n hR).2.2.1))
    field_simp [hnR.ne']
  rw [herrorEq] at hscaled
  simp only [Nat.cast_add] at hfinite
  have htotalR : (paperPilotSize n : ℝ) + paperRest n = n := by
    exact_mod_cast htotal
  rw [htotalR] at hfinite
  simp only [Nat.cast_ofNat] at hfinite
  rw [show (paperBins n : ℝ) + 2 = ((paperBins n + 2 : ℕ) : ℝ) by
    push_cast
    rfl] at hfinite
  nlinarith

set_option maxHeartbeats 3000000 in
theorem eventually_paperWorstCaseError_le :
    ∀ᶠ n in Filter.atTop,
      0 ≤ paperWorstCaseError n ∧
        paperWorstCaseError n ≤ 90000 / paperScale n := by
  filter_upwards [eventually_fourthRoot_ge 12] with n hR
  let Q := paperScale n
  let B := paperCutoff n
  let η := paperMesh n
  let d := paperBins n
  let k := paperPilotSize n
  obtain ⟨hQ1, hBQ, hηQ, hsqrtQ, hkRatio, _hinvN⟩ :=
    paper_parameter_scale_bounds n hR
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ1
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hQ3 : Q ≤ Q ^ 3 := by nlinarith [sq_nonneg Q]
  have hQ7 : Q ≤ Q ^ 7 := by
    have hQ6 : 1 ≤ Q ^ 6 := one_le_pow₀ hQ1
    nlinarith [mul_le_mul_of_nonneg_left hQ6 hQ0.le]
  have hinv2 : 1 / Q ^ 2 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ2
  have hinv3 : 1 / Q ^ 3 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ3
  have hinv7 : 1 / Q ^ 7 ≤ 1 / Q :=
    one_div_le_one_div_of_le hQ0 hQ7
  have hB0 : 0 ≤ B := by dsimp [B, paperCutoff, paperGrowth]; positivity
  have hB1 : B + 1 ≤ 34 * Q := by nlinarith
  have hB2 : B + 2 ≤ 35 * Q := by nlinarith
  have hB3 : 3 * B + 8 ≤ 107 * Q := by nlinarith
  have hBQ' : B ≤ 33 * Q := by simpa [B, Q] using hBQ
  have hηQ' : η ≤ 66 / Q ^ 3 := by simpa [η, Q] using hηQ
  have hprod1a := mul_le_mul_of_nonneg_right hBQ'
    (by positivity : 0 ≤ B + 1)
  have hprod1b := mul_le_mul_of_nonneg_left hB1
    (by positivity : 0 ≤ 33 * Q)
  have hprod1 : B * (B + 1) ≤ 33 * Q * (34 * Q) :=
    hprod1a.trans hprod1b
  have hprod2 := mul_le_mul hprod1 hB3 (by positivity : 0 ≤ 3 * B + 8)
    (by positivity : 0 ≤ 33 * Q * (34 * Q))
  have hcubic : B * (B + 1) * (3 * B + 8) / 6 *
      Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) ≤ 40018 / Q := by
    have hcoeff : B * (B + 1) * (3 * B + 8) / 6 ≤
        20009 * Q ^ 3 := by
      nlinarith [hprod2]
    have hsqrt0 : 0 ≤ Real.sqrt (((d + 2 : ℕ) : ℝ) / (k : ℝ)) :=
      Real.sqrt_nonneg _
    have hmul := mul_le_mul hcoeff hsqrtQ hsqrt0
      (by positivity : 0 ≤ 20009 * Q ^ 3)
    have hcancel : 20009 * Q ^ 3 * (2 / Q ^ 4) = 40018 / Q := by
      field_simp [hQ0.ne']
      ring
    rw [hcancel] at hmul
    exact hmul
  have hη0 := (paperMesh_pos n hR).le
  have hη0' : 0 ≤ η := by simpa [η] using hη0
  have hround1 := mul_le_mul_of_nonneg_right hB2 hη0'
  have hround2 := mul_le_mul_of_nonneg_left hηQ'
    (by positivity : 0 ≤ 35 * Q)
  have hroundMul : (B + 2) * η ≤ 35 * Q * (66 / Q ^ 3) :=
    hround1.trans hround2
  have hround : 2 / 3 * (B + 2) * η ≤ 1540 / Q := by
    have hraw : (B + 2) * η ≤ 2310 / Q ^ 2 := by
      have hcancel : 35 * Q * (66 / Q ^ 3) = 2310 / Q ^ 2 := by
        field_simp [hQ0.ne']
        ring
      rwa [hcancel] at hroundMul
    have hscaled := mul_le_mul_of_nonneg_left hinv2 (by norm_num : (0 : ℝ) ≤ 1540)
    have hscaled' : 1540 / Q ^ 2 ≤ 1540 / Q := by
      simpa [div_eq_mul_inv] using hscaled
    have htwoThirds := mul_le_mul_of_nonneg_left hraw
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hfirst : 2 / 3 * ((B + 2) * η) ≤ 1540 / Q ^ 2 := by
      calc
        2 / 3 * ((B + 2) * η) ≤ 2 / 3 * (2310 / Q ^ 2) := htwoThirds
        _ = 1540 / Q ^ 2 := by ring
    exact (by simpa [mul_assoc] using hfirst.trans hscaled')
  have hkRatio0 : 0 ≤ (k : ℝ) / n := by positivity
  have hcrossMul := mul_le_mul hB1 hkRatio hkRatio0
    (by positivity : 0 ≤ 34 * Q)
  have hcross : (B + 1) * k / (2 * n) ≤ 17 / Q := by
    have hcancel : 34 * Q * (1 / Q ^ 4) / 2 = 17 / Q ^ 3 := by
      field_simp [hQ0.ne']
      ring
    have hbase : (B + 1) * ((k : ℝ) / n) / 2 ≤ 17 / Q ^ 3 := by
      rw [← hcancel]
      exact div_le_div_of_nonneg_right hcrossMul (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hinv3 (by norm_num : (0 : ℝ) ≤ 17)
    have hscaled' : 17 / Q ^ 3 ≤ 17 / Q := by
      simpa [div_eq_mul_inv] using hscaled
    convert hbase.trans hscaled' using 1 <;> field_simp <;> ring
  have hkSq : ((k : ℝ) / n) ^ 2 ≤ (1 / Q ^ 4) ^ 2 := by nlinarith
  have hpMul := mul_le_mul hB1 hkSq (sq_nonneg _)
    (by positivity : 0 ≤ 34 * Q)
  have hpilot : (B + 1) * ((k : ℝ) / n) ^ 2 ≤ 34 / Q := by
    have hcancel : 34 * Q * (1 / Q ^ 4) ^ 2 = 34 / Q ^ 7 := by
      field_simp [hQ0.ne']
    rw [hcancel] at hpMul
    have hscaled := mul_le_mul_of_nonneg_left hinv7 (by norm_num : (0 : ℝ) ≤ 34)
    exact hpMul.trans (by simpa [div_eq_mul_inv] using hscaled)
  have herr0 : 0 ≤ paperWorstCaseError n := by
    unfold paperWorstCaseError
    dsimp only
    have hη0 := (paperMesh_pos n hR).le
    positivity
  refine ⟨herr0, ?_⟩
  unfold paperWorstCaseError
  dsimp only
  dsimp [Q, B, η, d, k] at hcubic hround hcross hpilot ⊢
  simp only [div_eq_mul_inv] at hcubic hround hcross hpilot ⊢
  have hinvQ0 : 0 ≤ (paperScale n)⁻¹ := by positivity
  nlinarith

theorem paperWorstCaseError_tendsto_zero :
    Filter.Tendsto paperWorstCaseError Filter.atTop (nhds 0) := by
  have henv : Filter.Tendsto (fun n => 90000 / paperScale n)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop paperScale_tendsto_atTop 90000
  apply squeeze_zero'
  · exact eventually_paperWorstCaseError_le.mono fun n h => h.1
  · exact eventually_paperWorstCaseError_le.mono fun n h => h.2
  · exact henv

/-! ## A grid-independent exact population benchmark -/

def exactObligatoryFluidValue {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  minimumObligatoryTemplateValue (uniformJobWeight n) p

theorem obligatoryTemplateValue_uniform_eq_direct
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (early : Fin n → Bool) :
    obligatoryTemplateValue (uniformJobWeight n) p early =
      (1 + weightedMoment (earlyJobWeight early) p) *
          (1 - weightedMass (earlyJobWeight early) / 2) +
        weightedMinPair (lateJobWeight early) p / 2 := by
  unfold obligatoryTemplateValue templateEarlyMass templateEarlyMoment
    templateLatePair RandomizedOptional.finiteExpectation
    RandomizedOptional.finiteProductExpectation
    weightedMass weightedMoment weightedMinPair earlyJobWeight lateJobWeight
    uniformJobWeight
  congr 1
  · congr 1
    · apply congrArg (fun z : ℝ => 1 + z)
      apply Finset.sum_congr rfl
      intro i _
      cases hi : early i <;> simp [hi] <;> ring
    · apply congrArg (fun z : ℝ => 1 - z / 2)
      apply Finset.sum_congr rfl
      intro i _
      cases hi : early i <;> simp [hi]
  · apply congrArg (fun z : ℝ => z / 2)
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    cases hi : early i <;> cases hj : early j <;>
      simp [hi, hj] <;> ring

theorem weightedMinPair_add
    {ι : Type*} [Fintype ι]
    (u v p : ι → ℝ) :
    weightedMinPair (fun i => u i + v i) p =
      weightedMinPair u p +
        2 * (∑ i, ∑ j, u i * v j * min (p i) (p j)) +
        weightedMinPair v p := by
  unfold weightedMinPair
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hcomm :
      (∑ i, ∑ j, v i * u j * min (p i) (p j)) =
        ∑ i, ∑ j, u i * v j * min (p i) (p j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [min_comm]
    ring
  rw [hcomm]
  ring

theorem weighted_cross_eq_moment_mul_mass_of_ordered
    {ι : Type*} [Fintype ι]
    (u v p : ι → ℝ)
    (hu : ∀ i, u i ≠ 0 → ∀ j, v j ≠ 0 → p i ≤ p j) :
    (∑ i, ∑ j, u i * v j * min (p i) (p j)) =
      (∑ i, u i * p i) * ∑ j, v j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hui : u i = 0
  · simp [hui]
  by_cases hvj : v j = 0
  · simp [hvj]
  rw [min_eq_left (hu i hui j hvj)]
  ring

theorem weightedMass_add
    {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    weightedMass (fun i => u i + v i) = weightedMass u + weightedMass v := by
  unfold weightedMass
  rw [Finset.sum_add_distrib]

theorem weightedMoment_add
    {ι : Type*} [Fintype ι] (u v p : ι → ℝ) :
    weightedMoment (fun i => u i + v i) p =
      weightedMoment u p + weightedMoment v p := by
  unfold weightedMoment
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Adding a block whose values lie between `θ` and `θ+η` to an exact
maximum-density threshold changes the stationary value by at most `η`. -/
theorem stationaryValue_add_near_threshold
    {ι : Type*} [Fintype ι]
    {θ η : ℝ} (p : ι → ℝ) (A X H : ι → ℝ)
    (hη : 0 ≤ η)
    (hmassPartition : weightedMass A + weightedMass X + weightedMass H = 1)
    (hnonnegA : ∀ i, 0 ≤ A i) (hnonnegX : ∀ i, 0 ≤ X i)
    (hnonnegH : ∀ i, 0 ≤ H i)
    (hXlower : ∀ i, X i ≠ 0 → θ ≤ p i)
    (hXupper : ∀ i, X i ≠ 0 → p i ≤ θ + η)
    (hXHorder : ∀ i, X i ≠ 0 → ∀ j, H j ≠ 0 → p i ≤ p j)
    (hdensity : 1 + weightedMoment A p = θ * weightedMass A) :
    (1 + weightedMoment (fun i => A i + X i) p) *
          (1 - weightedMass (fun i => A i + X i) / 2) +
        weightedMinPair H p / 2 ≤
      (1 + weightedMoment A p) *
          (1 - weightedMass A / 2) +
        weightedMinPair (fun i => X i + H i) p / 2 + η := by
  let a := weightedMass A
  let x := weightedMass X
  let h := weightedMass H
  let m := weightedMoment A p
  let mx := weightedMoment X p
  let Kx := weightedMinPair X p
  let Kh := weightedMinPair H p
  have ha0 : 0 ≤ a := by
    dsimp [a]
    unfold weightedMass
    exact Finset.sum_nonneg fun i _ => hnonnegA i
  have hx0 : 0 ≤ x := by
    dsimp [x]
    unfold weightedMass
    exact Finset.sum_nonneg fun i _ => hnonnegX i
  have hh0 : 0 ≤ h := by
    dsimp [h]
    unfold weightedMass
    exact Finset.sum_nonneg fun i _ => hnonnegH i
  have hmass : a + x + h = 1 := by
    simpa [a, x, h] using hmassPartition
  have hmxLower : θ * x ≤ mx := by
    unfold x mx weightedMass weightedMoment
    calc
      θ * ∑ i, X i = ∑ i, θ * X i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, X i * p i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hxi : X i = 0
        · simp [hxi]
        · have := hXlower i hxi
          nlinarith [hnonnegX i]
  have hmxUpper : mx ≤ (θ + η) * x := by
    unfold x mx weightedMass weightedMoment
    calc
      ∑ i, X i * p i ≤ ∑ i, (θ + η) * X i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hxi : X i = 0
        · simp [hxi]
        · have := hXupper i hxi
          nlinarith [hnonnegX i]
      _ = (θ + η) * ∑ i, X i := by rw [Finset.mul_sum]
  have hKxLower : θ * x ^ 2 ≤ Kx :=
    threshold_mul_weightedMass_sq_le_minPair_on_support hnonnegX hXlower
  have hcross := weighted_cross_eq_moment_mul_mass_of_ordered X H p hXHorder
  have hlatePair : weightedMinPair (fun i => X i + H i) p =
      Kx + 2 * mx * h + Kh := by
    rw [weightedMinPair_add X H p, hcross]
    dsimp [Kx, mx, h, Kh]
    unfold weightedMoment weightedMass
    ring
  have hmassAX := weightedMass_add A X
  have hmomentAX := weightedMoment_add A X p
  rw [hmassAX, hmomentAX, hlatePair]
  have hdensity' : 1 + m = θ * a := by
    simpa [m, a] using hdensity
  have hax0 : 0 ≤ a + x := by linarith
  have hax1 : a + x ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hmxScaled := mul_le_mul_of_nonneg_right hmxUpper hax0
  have hxx : x * (a + x) ≤ 1 := by
    have := mul_le_mul hx1 hax1 hax0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hetaBound : η * (x * (a + x)) / 2 ≤ η := by
    have hmul := mul_le_mul_of_nonneg_left hxx hη
    nlinarith
  change (1 + (m + mx)) * (1 - (a + x) / 2) + Kh / 2 ≤
    (1 + m) * (1 - a / 2) + (Kx + 2 * mx * h + Kh) / 2 + η
  have hdelta : mx * (a + x) - θ * a * x - Kx ≤ η * (x * (a + x)) := by
    nlinarith [hmxScaled, hKxLower]
  have hsum : 1 + (m + mx) = θ * a + mx := by linarith [hdensity']
  have hh : h = 1 - a - x := by linarith [hmass]
  calc
    (1 + (m + mx)) * (1 - (a + x) / 2) + Kh / 2 =
        (1 + m) * (1 - a / 2) + (Kx + 2 * mx * h + Kh) / 2 +
          (mx * (a + x) - θ * a * x - Kx) / 2 := by
            rw [hsum, hdensity', hh]
            ring
    _ ≤ (1 + m) * (1 - a / 2) + (Kx + 2 * mx * h + Kh) / 2 +
          η * (x * (a + x)) / 2 := by linarith
    _ ≤ (1 + m) * (1 - a / 2) + (Kx + 2 * mx * h + Kh) / 2 + η := by
      linarith

/-- The exact job-level population objective has a maximum-density threshold
minimizer.  We retain both its density certificate and its literal value so
that a different quantization can be compared to it without identifying the
two grids. -/
theorem exists_exact_threshold_minimizer
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 + populationMean p ∧
      let early : Fin n → Bool := fun i => decide (p i ≤ θ)
      1 + weightedMoment (earlyJobWeight early) p =
          θ * weightedMass (earlyJobWeight early) ∧
        obligatoryTemplateValue (uniformJobWeight n) p early =
          exactObligatoryFluidValue p := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := uniformJobWeight n
  let S := chosenMaximumDensitySubset μ p
  have hmax : IsMaximumDensitySubset μ p S :=
    chosenMaximumDensitySubset_isMaximum μ p
  have hμpos : ∀ i, 0 < μ i := by
    intro i
    dsimp [μ, uniformJobWeight]
    positivity
  have ha : 0 < subsetMass μ S :=
    maximumDensitySubset_mass_pos hμpos hp hmax
  let θ := (1 + subsetMoment μ p S) / subsetMass μ S
  have hθ : 0 < θ := by
    dsimp [θ]
    exact inverseDensity_pos (fun i => (hμpos i).le) hp ha
  have hmassUniv : subsetMass μ Finset.univ = 1 := by
    simpa [subsetMass, weightedMass] using weightedMass_uniformJobWeight hn
  have hmomentUniv : subsetMoment μ p Finset.univ = populationMean p := by
    unfold subsetMoment populationMean μ uniformJobWeight
    simp only [Finset.sum_const_zero, Finset.sum_div, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun i _ => hp i) (by positivity)
  have hmaxUniv := hmax Finset.univ
  have hSdensity : subsetDensity μ p S = 1 / θ := by
    unfold subsetDensity
    dsimp [θ]
    field_simp [ha.ne']
  have hθMean : θ ≤ 1 + populationMean p := by
    rw [hSdensity] at hmaxUniv
    unfold subsetDensity at hmaxUniv
    rw [hmassUniv, hmomentUniv] at hmaxUniv
    have hden : 0 < 1 + populationMean p := by linarith
    rw [div_le_div_iff₀ hden hθ] at hmaxUniv
    nlinarith
  let early : Fin n → Bool := fun i => decide (p i ≤ θ)
  have hclosure := maximumDensity_thresholdClosure_preserves
    (fun i => (hμpos i).le) hp hmax ha (inverseDensity_identity ha)
  have hmass : weightedMass (earlyJobWeight early) =
      selectedMass μ (fun i => p i ≤ θ) := by
    unfold weightedMass selectedMass earlyJobWeight early μ uniformJobWeight
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i ≤ θ <;> simp [hi]
  have hmoment : weightedMoment (earlyJobWeight early) p =
      selectedMoment μ p (fun i => p i ≤ θ) := by
    unfold weightedMoment selectedMoment earlyJobWeight early μ uniformJobWeight
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i ≤ θ <;> simp [hi] <;> ring
  have hdensity : 1 + weightedMoment (earlyJobWeight early) p =
      θ * weightedMass (earlyJobWeight early) := by
    rw [hmass, hmoment]
    simpa [thresholdClosure, θ] using hclosure
  have hμmass : ∑ i, μ i = 1 := by
    simpa [weightedMass] using weightedMass_uniformJobWeight hn
  have hminimal : obligatoryTemplateValue μ p early ≤
      minimumObligatoryTemplateValue μ p := by
    unfold minimumObligatoryTemplateValue
    apply thresholdClosure_minimizes_obligatoryTemplateValue μ p θ
      (fun i => (hμpos i).le) hp hμmass hθ.le
    simpa [early, templateEarlyMoment, templateEarlyMass,
      RandomizedOptional.finiteExpectation, thresholdClosure,
      weightedMoment, weightedMass, earlyJobWeight, μ, uniformJobWeight,
      mul_comm, mul_left_comm, mul_assoc] using hdensity
  have hreverse : minimumObligatoryTemplateValue μ p ≤
      obligatoryTemplateValue μ p early := by
    unfold minimumObligatoryTemplateValue
    exact minimizingObligatoryTemplate_minimizes μ p early
  refine ⟨θ, hθ, hθMean, ?_, ?_⟩
  · exact hdensity
  · change obligatoryTemplateValue μ p early = _
    unfold exactObligatoryFluidValue
    exact le_antisymm hminimal hreverse

/-- Replacing every processing time by an upward approximation of mesh
`η` changes the stationary value of a fixed early/late split by at most
`2η`.  This deliberately uses job-level weights, so no relationship between
this grid and a later adversarial lower-bound grid is needed. -/
theorem categoryTemplate_le_direct_add_two_mesh
    {n d : ℕ} (hn : 0 < n) (η : ℝ) (hη : 0 ≤ η)
    (p : Fin n → ℝ) (category : Fin n → QuantizedCategory d)
    (price : QuantizedCategory d → ℝ) (early : QuantizedCategory d → Bool)
    (hroundLower : ∀ i, p i ≤ price (category i))
    (hroundUpper : ∀ i, price (category i) ≤ p i + η) :
    obligatoryTemplateValue (populationHistogram category) price early ≤
      (1 + weightedMoment
          (earlyJobWeight (fun i => early (category i))) p) *
        (1 - weightedMass
          (earlyJobWeight (fun i => early (category i))) / 2) +
        weightedMinPair
          (lateJobWeight (fun i => early (category i))) p / 2 + 2 * η := by
  let selected : Fin n → Bool := fun i => early (category i)
  let rounded : Fin n → ℝ := fun i => price (category i)
  let e := earlyJobWeight selected
  let l := lateJobWeight selected
  have he0 : ∀ i, 0 ≤ e i := by
    intro i
    dsimp [e]
    unfold earlyJobWeight
    split <;> positivity
  have hl0 : ∀ i, 0 ≤ l i := by
    intro i
    dsimp [l]
    unfold lateJobWeight
    split <;> positivity
  have heMass0 : 0 ≤ weightedMass e := by
    unfold weightedMass
    exact Finset.sum_nonneg fun i _ => he0 i
  have hlMass0 : 0 ≤ weightedMass l := by
    unfold weightedMass
    exact Finset.sum_nonneg fun i _ => hl0 i
  have heMass1 : weightedMass e ≤ 1 := by
    dsimp [e, selected]
    rw [← earlyMassCount_div_eq_weightedMass hn]
    have hc := earlyMassCount_le_card (fun i => early (category i))
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_one hnR).2 hc
  have hlMass1 : weightedMass l ≤ 1 := by
    dsimp [l, selected]
    rw [weightedMass_late_eq_one_sub_early hn]
    have hnonneg : 0 ≤ weightedMass
        (earlyJobWeight fun i => early (category i)) := by
      unfold weightedMass earlyJobWeight
      exact Finset.sum_nonneg fun i _ => by split <;> positivity
    linarith
  have hmoment : weightedMoment e rounded ≤
      weightedMoment e p + η * weightedMass e := by
    unfold weightedMoment weightedMass
    calc
      ∑ i, e i * rounded i ≤ ∑ i, (e i * p i + η * e i) := by
        apply Finset.sum_le_sum
        intro i _
        have hu := hroundUpper i
        nlinarith [he0 i]
      _ = (∑ i, e i * p i) + η * ∑ i, e i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hpair : weightedMinPair l rounded ≤
      weightedMinPair l p + η * weightedMass l ^ 2 := by
    unfold weightedMinPair weightedMass
    calc
      (∑ i, ∑ j, l i * l j * min (rounded i) (rounded j)) ≤
          ∑ i, ∑ j, l i * l j * (min (p i) (p j) + η) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hl0 i) (hl0 j))
        calc
          min (rounded i) (rounded j) ≤ min (p i + η) (p j + η) :=
            min_le_min (by simpa [rounded] using hroundUpper i)
              (by simpa [rounded] using hroundUpper j)
          _ = min (p i) (p j) + η := by
            simp only [min_add_add_right]
      _ = (∑ i, ∑ j, l i * l j * min (p i) (p j)) +
          η * (∑ i, l i) ^ 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        apply congrArg₂ (· + ·) rfl
        calc
          (∑ i, ∑ j, l i * l j * η) =
              ∑ i, (l i * η) * ∑ j, l j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = η * (∑ i, l i) ^ 2 := by
            rw [← Finset.sum_mul]
            rw [show (∑ i, l i * η) = (∑ i, l i) * η by
              rw [Finset.sum_mul]]
            ring
  have hfactor0 : 0 ≤ 1 - weightedMass e / 2 := by linarith
  have hfactor1 : 1 - weightedMass e / 2 ≤ 1 := by linarith
  have hmomentScaled := mul_le_mul_of_nonneg_right hmoment hfactor0
  have hetaEarly : η * weightedMass e *
      (1 - weightedMass e / 2) ≤ η := by
    have hprod : weightedMass e * (1 - weightedMass e / 2) ≤ 1 := by
      nlinarith [heMass0, heMass1, hfactor0, hfactor1]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hprod hη).trans_eq (mul_one η)
  have hlSq : weightedMass l ^ 2 ≤ 1 := by nlinarith [hlMass0, hlMass1]
  have hetaLate : η * weightedMass l ^ 2 / 2 ≤ η := by
    have := mul_le_mul_of_nonneg_left hlSq hη
    nlinarith
  rw [obligatoryTemplateValue,
    ← weightedMass_categoryTemplate_eq hn category early,
    ← weightedMoment_categoryTemplate_eq hn category price early,
    ← weightedMinPair_categoryTemplate_eq hn category price early]
  change (1 + weightedMoment e rounded) *
      (1 - weightedMass e / 2) + weightedMinPair l rounded / 2 ≤ _
  nlinarith

/-- The best template on an arbitrary sufficiently covering growing grid is
within `3η` of the exact, unquantized population optimum. -/
theorem minimumGrowingTemplateValue_le_exact_add_three_mesh
    {n d : ℕ} (hn : 0 < n) (B η L : ℝ) (hη : 0 < η)
    (hBgrid : B ≤ (d : ℝ) * η) (hBcover : 1 + L + η ≤ B)
    (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L) :
    minimumObligatoryTemplateValue
        (populationHistogram (fun i => quantizedCategory d η (p i) hη))
        (Online.growingQuantizedRepresentative d η) ≤
      exactObligatoryFluidValue p + 3 * η := by
  let category := fun i : Fin n => quantizedCategory d η (p i) hη
  let price := Online.growingQuantizedRepresentative d η
  obtain ⟨θ, hθ, hθMean, hdensity, hExact⟩ :=
    exists_exact_threshold_minimizer hn p hp0
  let exactEarly : Fin n → Bool := fun i => decide (p i ≤ θ)
  let fineTemplate : QuantizedCategory d → Bool :=
    fun b => decide (price b ≤ θ + η)
  let fineEarly : Fin n → Bool := fun i => fineTemplate (category i)
  let A := earlyJobWeight exactEarly
  let X : Fin n → ℝ := fun i =>
    if fineEarly i = true ∧ exactEarly i = false then 1 / n else 0
  let H := lateJobWeight fineEarly
  have hmeanL : populationMean p ≤ L :=
    RandomizedOptional.AnnouncedRoundedLower.populationMean_le_scale hn p hpL
  have hθL : θ ≤ 1 + L := hθMean.trans (by linarith)
  have hθηB : θ + η ≤ B := by linarith
  have hgrid : L ≤ (d : ℝ) * η := by linarith
  have hroundLower : ∀ i, p i ≤ price (category i) := by
    intro i
    exact (Online.growingQuantized_rounding_bounds d hη (hp0 i)
      ((hpL i).trans hgrid)).1
  have hroundUpper : ∀ i, price (category i) ≤ p i + η := by
    intro i
    exact (Online.growingQuantized_rounding_bounds d hη (hp0 i)
      ((hpL i).trans hgrid)).2
  have hfineIncludes : ∀ i, exactEarly i = true → fineEarly i = true := by
    intro i hi
    have hpi : p i ≤ θ := by simpa [exactEarly] using hi
    have hqi := hroundUpper i
    have : price (category i) ≤ θ + η := by linarith
    simpa [fineEarly, fineTemplate] using this
  have hAX : (fun i => A i + X i) = earlyJobWeight fineEarly := by
    funext i
    cases he : exactEarly i <;> cases hf : fineEarly i
    · simp [A, X, earlyJobWeight, he, hf]
    · simp [A, X, earlyJobWeight, he, hf]
    · exact False.elim (by simpa [hf] using hfineIncludes i he)
    · simp [A, X, earlyJobWeight, he, hf]
  have hXH : (fun i => X i + H i) = lateJobWeight exactEarly := by
    funext i
    cases he : exactEarly i <;> cases hf : fineEarly i
    · simp [X, H, lateJobWeight, he, hf]
    · simp [X, H, lateJobWeight, he, hf]
    · exact False.elim (by simpa [hf] using hfineIncludes i he)
    · simp [X, H, lateJobWeight, he, hf]
  have hA0 : ∀ i, 0 ≤ A i := by
    intro i
    dsimp [A]
    unfold earlyJobWeight
    split <;> positivity
  have hX0 : ∀ i, 0 ≤ X i := by
    intro i
    dsimp [X]
    split <;> positivity
  have hH0 : ∀ i, 0 ≤ H i := by
    intro i
    dsimp [H]
    unfold lateJobWeight
    split <;> positivity
  have hmassPartition : weightedMass A + weightedMass X + weightedMass H = 1 := by
    calc
      weightedMass A + weightedMass X + weightedMass H =
          weightedMass (fun i => A i + X i) + weightedMass H := by
            rw [weightedMass_add]
      _ = weightedMass (earlyJobWeight fineEarly) +
          weightedMass (lateJobWeight fineEarly) := by rw [hAX]
      _ = 1 := by
        rw [weightedMass_late_eq_one_sub_early hn]
        ring
  have hXcondition : ∀ i, X i ≠ 0 →
      fineEarly i = true ∧ exactEarly i = false := by
    intro i hxi
    by_contra hcond
    simp [X, hcond] at hxi
  have hXlower : ∀ i, X i ≠ 0 → θ ≤ p i := by
    intro i hxi
    have he := (hXcondition i hxi).2
    have : ¬ p i ≤ θ := by simpa [exactEarly] using he
    exact le_of_lt (lt_of_not_ge this)
  have hXupper : ∀ i, X i ≠ 0 → p i ≤ θ + η := by
    intro i hxi
    have hf := (hXcondition i hxi).1
    have hq : price (category i) ≤ θ + η := by
      simpa [fineEarly, fineTemplate] using hf
    exact (hroundLower i).trans hq
  have hXHorder : ∀ i, X i ≠ 0 → ∀ j, H j ≠ 0 → p i ≤ p j := by
    intro i hxi j hHj
    have hfI := (hXcondition i hxi).1
    have hfJ : fineEarly j = false := by
      cases hj : fineEarly j
      · rfl
      · simp [H, lateJobWeight, hj] at hHj
    apply growing_threshold_split_ordered d (θ := θ + η) hη hBgrid
      (by linarith) hθηB
      (hp0 i) (hp0 j)
    · simpa [fineEarly, fineTemplate, price, category, thresholdClosure] using hfI
    · simpa [fineEarly, fineTemplate, price, category, thresholdClosure] using hfJ
  have hstationary := stationaryValue_add_near_threshold p A X H hη.le
    hmassPartition hA0 hX0 hH0 hXlower hXupper hXHorder
    (by simpa [A, exactEarly] using hdensity)
  rw [hAX, hXH] at hstationary
  have hExactDirect :
      (1 + weightedMoment (earlyJobWeight exactEarly) p) *
          (1 - weightedMass (earlyJobWeight exactEarly) / 2) +
        weightedMinPair (lateJobWeight exactEarly) p / 2 =
          exactObligatoryFluidValue p := by
    rw [← obligatoryTemplateValue_uniform_eq_direct hn p exactEarly]
    simpa [exactEarly] using hExact
  rw [hExactDirect] at hstationary
  have hrounded := categoryTemplate_le_direct_add_two_mesh hn η hη.le
    p category price fineTemplate hroundLower hroundUpper
  have htarget : obligatoryTemplateValue
      (populationHistogram category) price fineTemplate ≤
        exactObligatoryFluidValue p + 3 * η := by
    dsimp [fineEarly] at hstationary
    dsimp [category, price, fineTemplate] at hrounded ⊢
    nlinarith
  have hmin := minimizingObligatoryTemplate_minimizes
    (populationHistogram category) price fineTemplate
  exact hmin.trans (by simpa [category, price] using htarget)

/-- Any independently chosen upward-rounded aligned benchmark dominates the
exact unquantized optimum.  In particular, the adversarial lower bound is
free to use a much coarser grid than the algorithm. -/
theorem exactObligatoryFluidValue_le_growingRoundedBenchmark
    {n d : ℕ} (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hcap : ∀ i, p i ≤ (d : ℝ) * η)
    (B : BenchmarkData p
      (growingAlignedRoundedGrid d η hη p hp0 hcap)) :
    exactObligatoryFluidValue p ≤ roundedObligatoryValue B := by
  let category := fun i : Fin n => quantizedCategory d η (p i) hη
  let price := Online.growingQuantizedRepresentative d η
  let early := minimizingObligatoryTemplate
    (populationHistogram category) price
  have hround : ∀ i, p i ≤ price (category i) := by
    intro i
    exact (Online.growingQuantized_rounding_bounds d hη (hp0 i) (hcap i)).1
  have hdirect := directFiniteFluid_le_categoryTemplate
    hn p category price early hround
  have hexactMin := minimizingObligatoryTemplate_minimizes
    (uniformJobWeight n) p (fun i => early (category i))
  have hexactDirect : exactObligatoryFluidValue p ≤
      (1 + weightedMoment
          (earlyJobWeight (fun i => early (category i))) p) *
        (1 - weightedMass
          (earlyJobWeight (fun i => early (category i))) / 2) +
        weightedMinPair
          (lateJobWeight (fun i => early (category i))) p / 2 := by
    unfold exactObligatoryFluidValue minimumObligatoryTemplateValue
    rw [← obligatoryTemplateValue_uniform_eq_direct hn]
    exact hexactMin
  have hgridMin : exactObligatoryFluidValue p ≤
      minimumObligatoryTemplateValue (populationHistogram category) price := by
    unfold minimumObligatoryTemplateValue
    exact hexactDirect.trans (by simpa [category, price, early] using hdirect)
  have hrounded := minimumGrowingTemplateValue_le_roundedObligatoryValue
    hn d η hη p hp0 hcap B
  exact hgridMin.trans (by simpa [category, price] using hrounded)

set_option maxHeartbeats 5000000 in
/-- Finite comparison with two independent grids: the policy uses the fine
grid `(dFine,ηFine)`, while the competitor lower bound is proved on the
coarse grid `(dCoarse,ηCoarse)`.  Their only common object is the exact
unquantized population optimum. -/
theorem exists_fixedPlacement_fineGrowingPolicy_le_coarseCompetitor
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (k r dFine dCoarse : ℕ) (hk : 0 < k) (hr : 0 < r)
    (BFine ηFine ηCoarse L : ℝ)
    (hηFine : 0 < ηFine) (hηCoarse : 0 < ηCoarse)
    (hBFine0 : 0 ≤ BFine)
    (hBFineGrid : BFine ≤ (dFine : ℝ) * ηFine)
    (hFineGrid : L ≤ (dFine : ℝ) * ηFine)
    (hBFineCover : 1 + L + ηFine ≤ BFine)
    (hCoarseGrid : L ≤ (dCoarse : ℝ) * ηCoarse)
    (p : Fin (k + r) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed))
    (cutoff : Fin (k + r)) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e s : ℝ} (he : 0 < e) (hs : 0 < s) :
    let γ := (e + martingaleStep +
      (s + 2 * suffixStep / (suffixPositions cutoff).card) * (k + r) +
      (suffixPositions cutoff).card) / (k + r)
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card *
          ((k + r : ℝ) / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)
    ∃ σ : RandomizedOptional.ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k dFine BFine ηFine hηFine p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            growingLowerUniformError dCoarse ηCoarse L γ base +
            3 * ηFine) +
          growingUpperRawError (k + r) k dFine BFine ηFine L := by
  dsimp only
  have hn : 0 < k + r := by omega
  have hnTwo : 1 < k + r := by omega
  have hcapCoarse : ∀ i, p i ≤ (dCoarse : ℝ) * ηCoarse :=
    fun i => (hpL i).trans hCoarseGrid
  obtain ⟨B, _⟩ := exists_growingAlignedBenchmarkData
    hn dCoarse ηCoarse hηCoarse p hp0 hcapCoarse hmean
  have hupper := uniformAverage_physicalGrowingRunCost_le_minimum
    k r dFine hk hr BFine ηFine L hηFine hBFine0 hBFineGrid
      hFineGrid hBFineCover p hp0 hpL
  have hfineBridge := minimumGrowingTemplateValue_le_exact_add_three_mesh
    hn BFine ηFine L hηFine hBFineGrid hBFineCover p hp0 hpL
  have hupperExact :
      uniformAverage
          (physicalGrowingRunCost (k + r) k dFine BFine ηFine hηFine p) ≤
        (k + r : ℝ) ^ 2 *
            (exactObligatoryFluidValue p + 3 * ηFine) +
          growingUpperRawError (k + r) k dFine BFine ηFine L := by
    dsimp only at hupper hfineBridge
    unfold growingUpperRawError
    simp only [Nat.cast_add, Nat.cast_ofNat] at hupper ⊢
    have hscaled := mul_le_mul_of_nonneg_left hfineBridge
      (sq_nonneg (k + r : ℝ))
    linarith
  obtain ⟨σ, hlower⟩ :=
    exists_fixedPlacement_randomizedCost_ge_growingBenchmark
      hnTwo dCoarse ηCoarse hηCoarse p hp0 hcapCoarse policy htest B
        cutoff hMartingaleStep hSuffixStep he hs
  refine ⟨σ, ?_⟩
  let γ : ℝ :=
    (e + martingaleStep +
      (s + 2 * suffixStep / (suffixPositions cutoff).card) * (k + r) +
      (suffixPositions cutoff).card) / (k + r)
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card *
        ((k + r : ℝ) / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / s ^ 2)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hmeanLe := growingAlignedBenchmark_mean_le hn dCoarse ηCoarse L
    hηCoarse p hp0 hpL hcapCoarse B
  have herror : growingLowerNormalizedError dCoarse ηCoarse B.mean γ base ≤
      growingLowerUniformError dCoarse ηCoarse L γ base := by
    unfold growingLowerNormalizedError growingLowerUniformError
    have hcount0 : 0 ≤ (dCoarse + 2 : ℝ) * γ := by positivity
    have hbad0 : 0 ≤ (dCoarse + 2 : ℝ) * base := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmeanLe hcount0,
      mul_le_mul_of_nonneg_right hmeanLe hbad0]
  have hexactBenchmark := exactObligatoryFluidValue_le_growingRoundedBenchmark
    hn ηCoarse hηCoarse p hp0 hcapCoarse B
  have hexactLower : exactObligatoryFluidValue p ≤
      uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
        growingLowerUniformError dCoarse ηCoarse L γ base := by
    unfold growingLowerNormalizedError at herror
    unfold growingLowerUniformError at herror ⊢
    dsimp only [γ, base] at herror hlower ⊢
    push_cast at herror hlower ⊢
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hexactLower
    (sq_nonneg (k + r : ℝ))
  dsimp only [γ, base] at hscaled ⊢
  linarith

set_option maxHeartbeats 6000000 in
/-- Positive-mean instance comparison for the exact manuscript family.  The
`m≈n^(1/32)` construction appears only inside the proof of the competitor
lower bound; the policy on the left is still the `n^(3/4)`-pilot,
`n^(1/4)`-grid family used by the worst-case theorem. -/
theorem exists_fixedPlacement_paperGrowingPolicy_positive_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hCoarseCover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    ∃ σ : Placement (paperPilotSize n + paperRest n),
      uniformAverage
          (physicalGrowingRunCost
            (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
            (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
        (paperPilotSize n + paperRest n : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            concreteUniversalGrowingError L n + paperFineNormalizedError L n) := by
  let k := paperPilotSize n
  let r := paperRest n
  let dFine := paperBins n
  let BFine := paperCutoff n
  let ηFine := paperMesh n
  let m := concreteUniversalGrowingParameter n
  let M := universalGrowingAccuracy m
  let dCoarse := universalGrowingGridIntervals m
  let ηCoarse := universalGrowingMesh m
  obtain ⟨hm, hnM⟩ := concreteUniversalGrowingParameter_bounds n hroot
  have hM : 2 ≤ M := by dsimp [M, universalGrowingAccuracy]; nlinarith
  obtain ⟨hdFine, hk, hklt, _hfixedCutoff, _hfixedMesh, _hfixedMesh12,
      _hfixedMeshR, _hnR, _hkR, _hsqrt⟩ := concrete_parameter_bounds n hR
  have hr : 0 < r := by dsimp [r, paperRest, paperPilotSize]; omega
  have htotal : k + r = n := by
    simpa [k, r, paperPilotSize, paperRest] using concrete_size_eq n hR
  have hnTotal : M ^ 16 ≤ k + r := by
    simpa [htotal, M, m] using hnM
  obtain ⟨hkTotal, _hkTotalLt, hstepTotal, _⟩ :=
    parameter_scales hM hnTotal
  let cutoff := inverseSquareCutoff (k + r) M hkTotal
  let step := inverseFourthStep (k + r) M
  let e : ℝ := (k + r : ℝ) / (M : ℝ) ^ 2
  let s : ℝ := 1 / (M : ℝ) ^ 2
  have he : 0 < e := by dsimp [e]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hηCoarse : 0 < ηCoarse := by
    dsimp [ηCoarse, universalGrowingMesh]
    positivity
  have hMCast : (M : ℝ) = (m : ℝ) ^ 2 := by
    simp [M, universalGrowingAccuracy]
  have hgridValue : (dCoarse : ℝ) * ηCoarse =
      (m : ℝ) - 1 / m := by
    dsimp [dCoarse, ηCoarse, universalGrowingGridIntervals,
      universalGrowingMesh, M]
    push_cast [Nat.cast_sub (by
      dsimp [universalGrowingAccuracy]
      nlinarith [hm] : 1 ≤ universalGrowingAccuracy m)]
    rw [hMCast]
    field_simp [hmR.ne']
  have hηCoarseOne : ηCoarse ≤ 1 := by
    dsimp [ηCoarse, universalGrowingMesh]
    rw [div_le_one hmR]
    exact_mod_cast (by omega : 1 ≤ m)
  have hCoarseGrid : L ≤ (dCoarse : ℝ) * ηCoarse := by
    rw [hgridValue]
    have hLm : L + 3 ≤ (m : ℝ) := by exact_mod_cast hCoarseCover
    have hinvLe : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmR]
      exact_mod_cast (by omega : 1 ≤ m)
    linarith
  obtain ⟨_hUpperCoarse, hLowerCoarse⟩ :=
    universal_growing_parameter_error_bounds (n := k + r) hm hnTotal hL
  have hFineGrid : L ≤ (dFine : ℝ) * ηFine := by
    rw [show (dFine : ℝ) * ηFine = BFine by
      simpa [dFine, ηFine, BFine] using paperCutoff_eq_bins_mul_mesh n hR]
    dsimp [BFine, ηFine] at hFineCover ⊢
    linarith [paperMesh_pos n hR]
  have hBFine0 : 0 ≤ BFine := by
    dsimp [BFine, paperCutoff, paperGrowth]
    have hg := Real.rpow_nonneg
      (by linarith [hR] : 0 ≤ fourthRoot n) (1 / 5 : ℝ)
    linarith
  obtain ⟨σ, hcomparison⟩ :=
    exists_fixedPlacement_fineGrowingPolicy_le_coarseCompetitor
      k r dFine dCoarse hk hr BFine ηFine ηCoarse L
      (paperMesh_pos n hR) hηCoarse hBFine0
      (by simpa [dFine, ηFine, BFine] using
        (paperCutoff_eq_bins_mul_mesh n hR).ge)
      hFineGrid (by simpa [ηFine, BFine] using hFineCover)
      hCoarseGrid p hp0 hpL hmean policy htest cutoff
      hstepTotal hstepTotal he hs
  refine ⟨σ, ?_⟩
  have hLower : growingLowerUniformError dCoarse ηCoarse L
      ((e + step +
        (s + 2 * step / (suffixPositions cutoff).card) * (k + r) +
        (suffixPositions cutoff).card) / (k + r))
      ((backwardCheckpoints step cutoff).card * ((k + r : ℝ) / e ^ 2) +
        (backwardCheckpoints step cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)) ≤
        concreteUniversalGrowingError L n := by
    simpa [M, m, cutoff, step, e, s, dCoarse, ηCoarse,
      universalGrowingAccuracy, universalGrowingGridIntervals,
      universalGrowingMesh, concreteUniversalGrowingError] using hLowerCoarse
  have hUpperEq :
      growingUpperRawError (k + r) k dFine BFine ηFine L =
        (k + r : ℝ) ^ 2 *
          (paperFineNormalizedError L n - 3 * ηFine) := by
    simpa [k, r, dFine, BFine, ηFine] using paperUpperRawError_eq L n hR
  have hLowerScaled := mul_le_mul_of_nonneg_left hLower
    (sq_nonneg (k + r : ℝ))
  rw [hUpperEq] at hcomparison
  dsimp [step] at hLowerScaled
  have hfinal :
      uniformAverage
          (physicalGrowingRunCost (k + r) k dFine BFine ηFine
            (paperMesh_pos n hR) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            concreteUniversalGrowingError L n + paperFineNormalizedError L n) := by
    nlinarith [hcomparison, hLowerScaled]
  simpa [k, r, dFine, BFine, ηFine] using hfinal

set_option maxHeartbeats 5000000 in
theorem exists_fixedPlacement_paperGrowingPolicy_zero_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    {L : ℝ} (hL : 0 < L)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hmean : populationMean p = 0)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    ∃ σ : Placement (paperPilotSize n + paperRest n),
      uniformAverage
          (physicalGrowingRunCost
            (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
            (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
        (paperPilotSize n + paperRest n : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            concreteUniversalGrowingError L n + paperFineNormalizedError L n) := by
  let k := paperPilotSize n
  let r := paperRest n
  let d := paperBins n
  let B := paperCutoff n
  let η := paperMesh n
  obtain ⟨hd, hk, hklt, _hfixedCutoff, _hfixedMesh, _hfixedMesh12,
      _hfixedMeshR, _hnR, _hkR, _hsqrt⟩ := concrete_parameter_bounds n hR
  have hr : 0 < r := by dsimp [r, paperRest, paperPilotSize]; omega
  have htotal : k + r = n := by
    simpa [k, r, paperPilotSize, paperRest] using concrete_size_eq n hR
  have hnTotal : 0 < k + r := by omega
  have hpzero := processing_eq_zero_of_populationMean_eq_zero
    hnTotal p hp0 hmean
  let zero := RandomizedOptional.UnboundedOperational.zeroProcessing (k + r)
  have hpEq : p = zero := by
    funext job
    simpa [zero, RandomizedOptional.UnboundedOperational.zeroProcessing]
      using hpzero job
  subst p
  have hB0 : 0 ≤ B := by
    dsimp [B, paperCutoff, paperGrowth]
    have hg := Real.rpow_nonneg
      (by linarith [hR] : 0 ≤ fourthRoot n) (1 / 5 : ℝ)
    linarith
  have hBgrid : B ≤ (d : ℝ) * η := by
    simpa [B, d, η] using (paperCutoff_eq_bins_mul_mesh n hR).ge
  have hgrid : L ≤ (d : ℝ) * η := by
    rw [show (d : ℝ) * η = B by
      simpa [B, d, η] using paperCutoff_eq_bins_mul_mesh n hR]
    dsimp [B, η] at hFineCover ⊢
    linarith [paperMesh_pos n hR]
  have hrun := uniformAverage_physicalGrowingRunCost_le_minimum
    k r d hk hr B η L (paperMesh_pos n hR) hB0 hBgrid hgrid
      (by simpa [B, η] using hFineCover) zero
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing, hL.le])
  have hmin := minimumGrowingTemplateValue_le_half_of_eq_zero
    (d := d) hnTotal η (paperMesh_pos n hR) zero
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
  let σ : Placement (k + r) := Equiv.refl (Fin (k + r))
  have hcompetitor :
      uniformAverage (fun seed => normalizedCost zero (policy seed) σ) =
        (k + r + 1 : ℝ) / (2 * (k + r)) := by
    rw [show (fun seed => normalizedCost zero (policy seed) σ) =
        fun _seed : Seeds => (k + r + 1 : ℝ) / (2 * (k + r)) by
      funext seed
      have hz := normalizedCost_zero_eq hnTotal (policy seed) (htest seed) σ
      convert hz using 1 <;> push_cast <;> ring]
    exact uniformAverage_const _
  have hcompetitorHalf : (1 : ℝ) / 2 ≤
      uniformAverage (fun seed => normalizedCost zero (policy seed) σ) := by
    rw [hcompetitor]
    have hnR : (0 : ℝ) < k + r := by exact_mod_cast hnTotal
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) hnR)]
    push_cast
    linarith
  have hUpperEq : growingUpperRawError (k + r) k d B η L =
      (k + r : ℝ) ^ 2 * (paperFineNormalizedError L n - 3 * η) := by
    simpa [k, r, d, B, η] using paperUpperRawError_eq L n hR
  have hδ0 : 0 ≤ concreteUniversalGrowingError L n := by
    unfold concreteUniversalGrowingError growingInverseParameterError
    positivity
  have hη0 : 0 ≤ η := (paperMesh_pos n hR).le
  have hscaledMin := mul_le_mul_of_nonneg_left hmin (sq_nonneg (k + r : ℝ))
  have hscaledCompetitor := mul_le_mul_of_nonneg_left hcompetitorHalf
    (sq_nonneg (k + r : ℝ))
  refine ⟨σ, ?_⟩
  dsimp only at hrun
  unfold growingUpperRawError at hUpperEq
  simp only [Nat.cast_add, Nat.cast_ofNat] at hrun hUpperEq
  have hfinal :
      uniformAverage (physicalGrowingRunCost (k + r) k d B η
          (paperMesh_pos n hR) zero) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost zero (policy seed) σ) +
            concreteUniversalGrowingError L n + paperFineNormalizedError L n) := by
    nlinarith
  simpa [k, r, d, B, η] using hfinal

/-- Uniform finite instance-optimality for all bounded nonnegative inputs,
using literally the same policy as `paperGrowingPolicy_four_thirds_finite`. -/
theorem exists_fixedPlacement_paperGrowingPolicy_all_means_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hCoarseCover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    ∃ σ : Placement (paperPilotSize n + paperRest n),
      uniformAverage
          (physicalGrowingRunCost
            (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
            (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
        (paperPilotSize n + paperRest n : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            concreteUniversalGrowingError L n + paperFineNormalizedError L n) := by
  have hnTotal : 0 < paperPilotSize n + paperRest n := by
    have hk : 0 < paperPilotSize n := by
      simpa [paperPilotSize] using (concrete_parameter_bounds n hR).2.1
    omega
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun i _ => hp0 i) (by positivity)
  by_cases hz : populationMean p = 0
  · exact exists_fixedPlacement_paperGrowingPolicy_zero_rate
      hR hL hFineCover p hp0 hpL hz policy htest
  · exact exists_fixedPlacement_paperGrowingPolicy_positive_rate
      hR hroot hL hCoarseCover hFineCover p hp0 hpL
        (lt_of_le_of_ne hmean0 (Ne.symm hz)) policy htest

/-- Public Theorem 1.2 export, with the single vanishing error coefficient
named explicitly. -/
theorem exists_fixedPlacement_paperGrowingPolicy_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hR : 12 ≤ fourthRoot n)
    (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hCoarseCover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (hFineCover : 1 + L + paperMesh n ≤ paperCutoff n)
    (p : Fin (paperPilotSize n + paperRest n) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    ∃ σ : Placement (paperPilotSize n + paperRest n),
      uniformAverage
          (physicalGrowingRunCost
            (paperPilotSize n + paperRest n) (paperPilotSize n) (paperBins n)
            (paperCutoff n) (paperMesh n) (paperMesh_pos n hR) p) ≤
        (paperPilotSize n + paperRest n : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            paperInstanceError L n) := by
  obtain ⟨σ, hσ⟩ := exists_fixedPlacement_paperGrowingPolicy_all_means_rate
    hR hroot hL hCoarseCover hFineCover p hp0 hpL policy htest
  refine ⟨σ, ?_⟩
  simpa [paperInstanceError, add_assoc] using hσ

theorem thirtySecondRoot_tendsto_atTop :
    Filter.Tendsto thirtySecondRoot Filter.atTop Filter.atTop := by
  unfold thirtySecondRoot sixteenthRoot
  exact Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp
        (Real.tendsto_sqrt_atTop.comp
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))))

/-- For each fixed input bound, all side conditions of the public finite
export hold eventually. -/
theorem eventually_paperGrowingPolicy_side_conditions (L : ℝ) :
    ∀ᶠ n in Filter.atTop,
      12 ≤ fourthRoot n ∧
      2 ≤ thirtySecondRoot n ∧
      L + 3 ≤ concreteUniversalGrowingParameter n ∧
      1 + L + paperMesh n ≤ paperCutoff n := by
  filter_upwards [eventually_fourthRoot_ge 12,
      thirtySecondRoot_tendsto_atTop.eventually (Filter.eventually_ge_atTop 2),
      eventually_concreteUniversalGrowingParameter_covers L,
      eventually_paperFineCover L] with n hR hroot hcoarse hfine
  exact ⟨hR, hroot, hcoarse, hfine⟩

end

end ObligatoryPaper
end SchedulingPaper
