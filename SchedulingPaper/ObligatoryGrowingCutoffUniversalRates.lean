import SchedulingPaper.ObligatoryGrowingCutoffRates
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# An input-size-only obligatory instance-optimal family

The preceding rate theorem permits an `L`-tuned mesh.  This module fixes a
single family independent of the input bound: with accuracy parameter `m`,
use `m^2 - 1` intervals, mesh `1/m`, cutoff `m - 1`, and `n/m^4` pilot jobs.
For every fixed `L`, the same family is valid once `L + 3 <= m`; its checked
normalized error is at most `400 (L+3)^2/m`.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Randomized
open RandomizedAnnounced
open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.AnnouncedRoundedLower
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace

noncomputable section
attribute [local instance] Classical.propDecidable

def universalGrowingAccuracy (m : ℕ) : ℕ := m ^ 2

def universalGrowingPilotSize (n m : ℕ) : ℕ :=
  inverseSquareSize n (universalGrowingAccuracy m)

def universalGrowingGridIntervals (m : ℕ) : ℕ :=
  universalGrowingAccuracy m - 1

def universalGrowingMesh (m : ℕ) : ℝ := 1 / m

def universalGrowingCutoff (m : ℕ) : ℝ := m - 1

set_option maxHeartbeats 3000000 in
/-- Both benchmark errors for the `L`-independent parameter family. -/
theorem universal_growing_parameter_error_bounds
    {n m : ℕ} (hm : 2 ≤ m)
    (hn : (universalGrowingAccuracy m) ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) :
    let M := universalGrowingAccuracy m
    let k := inverseSquareSize n M
    let d := M - 1
    let η := universalGrowingMesh m
    let Bcut := universalGrowingCutoff m
    let cutoff := inverseSquareCutoff n M
      (parameter_scales (by simp [universalGrowingAccuracy]; nlinarith) hn).1
    let step := inverseFourthStep n M
    let e := (n : ℝ) / (M : ℝ) ^ 2
    let s := 1 / (M : ℝ) ^ 2
    let threshold := e + step +
      (s + 2 * step / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints step cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints step cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)
    growingUpperRawError n k d Bcut η L ≤
        (n : ℝ) ^ 2 * growingInverseParameterError L m ∧
      growingLowerUniformError d η L γ base ≤
        growingInverseParameterError L m := by
  dsimp
  let M := universalGrowingAccuracy m
  have hM : 2 ≤ M := by dsimp [M, universalGrowingAccuracy]; nlinarith
  obtain ⟨hkpos, _hklt, _hstep, _hkLower, hkUpper,
      _hdLower, _hdUpper⟩ := parameter_scales hM hn
  let k := inverseSquareSize n M
  let step := inverseFourthStep n M
  let cutoff := inverseSquareCutoff n M hkpos
  let η : ℝ := universalGrowingMesh m
  let δ₀ : ℝ := 30 * (L + 1) / M
  let δ : ℝ := growingInverseParameterError L m
  obtain ⟨_hDiscovery, hCounts, hBad, hLearning, _hInverse,
      _hMesh, _hPilot⟩ := inverse_parameter_error_bounds hM hn hL
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by omega) 16) hn)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hMCast : (M : ℝ) = (m : ℝ) ^ 2 := by
    simp [M, universalGrowingAccuracy]
  have hη : η = 1 / (m : ℝ) := rfl
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one hmR]
    exact_mod_cast (by omega : 1 ≤ m)
  have hkOverN : (k : ℝ) / n ≤ 1 / (M : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hnR (sq_pos_of_pos hMR)]
    nlinarith only [hkUpper]
  have hMInvLe : 1 / (M : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 := by
    rw [hMCast]
    have hmSq : (m : ℝ) ^ 2 ≤ ((m : ℝ) ^ 2) ^ 2 := by
      have hmSqOne : 1 ≤ (m : ℝ) ^ 2 := by
        nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)]
      nlinarith
    exact one_div_le_one_div_of_le (sq_pos_of_pos hmR) hmSq
  have hkOverNRate : (k : ℝ) / n ≤ 1 / (m : ℝ) ^ 2 :=
    hkOverN.trans hMInvLe
  have hkOverN0 : 0 ≤ (k : ℝ) / n := by positivity
  have hδ₀0 : 0 ≤ δ₀ := by dsimp [δ₀]; positivity
  have hlearn : Real.sqrt ((M + 1 : ℝ) / k) ≤ δ₀ := by
    simpa [M, k, δ₀] using hLearning
  have hlearn0 : 0 ≤ Real.sqrt ((M + 1 : ℝ) / k) := Real.sqrt_nonneg _
  have hspan : (M : ℝ) * η + 2 ≤ 2 * m := by
    rw [hη, hMCast]
    field_simp [hmR.ne']
    nlinarith only [show (2 : ℝ) ≤ m by exact_mod_cast hm]
  have hstat :
      6 * ((M : ℝ) * η + 2) * Real.sqrt ((M + 1 : ℝ) / k) ≤
        360 * (L + 3) ^ 2 / m := by
    have hmul := mul_le_mul hspan hlearn hlearn0
      (by positivity : (0 : ℝ) ≤ 2 * m)
    dsimp [δ₀] at hmul
    have hsq : L + 1 ≤ (L + 3) ^ 2 := by nlinarith only [hL]
    calc
      6 * ((M : ℝ) * η + 2) * Real.sqrt ((M + 1 : ℝ) / k) ≤
          6 * (2 * m * (30 * (L + 1) / M)) := by
        nlinarith only [hmul]
      _ = 360 * (L + 1) / m := by
        rw [hMCast]
        field_simp [hmR.ne']
        norm_num
      _ ≤ 360 * (L + 3) ^ 2 / m := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) hmR.le
  have hcross :
      (m : ℝ) * k / (2 * n) ≤ (L + 3) ^ 2 / m := by
    have hmul := mul_le_mul_of_nonneg_left hkOverNRate hmR.le
    have hsq : (1 : ℝ) / 2 ≤ (L + 3) ^ 2 := by nlinarith only [hL]
    calc
      (m : ℝ) * k / (2 * n) = (m * ((k : ℝ) / n)) / 2 := by
        field_simp
      _ ≤ (m * (1 / (m : ℝ) ^ 2)) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((1 : ℝ) / 2) / m := by field_simp [hmR.ne']
      _ ≤ (L + 3) ^ 2 / m :=
        div_le_div_of_nonneg_right hsq hmR.le
  have hmnNat : m ≤ n := by
    have hmM : m ≤ M := by dsimp [M, universalGrowingAccuracy]; nlinarith
    have hMPow : M ≤ M ^ 16 := Nat.le_pow (by omega : 0 < 16)
    exact hmM.trans (hMPow.trans hn)
  have hdiag : (1 + L) / (2 * n) ≤ (L + 3) ^ 2 / m := by
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hmnNat
    have hinv := one_div_le_one_div_of_le hmR hmn
    have hmul := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ 1 + L by linarith only [hL])
    calc
      (1 + L) / (2 * n) = ((1 + L) * (1 / n)) / 2 := by field_simp
      _ ≤ ((1 + L) * (1 / m)) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((1 + L) / 2) / m := by ring
      _ ≤ (L + 3) ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        nlinarith only [hL]
  have hpilot :
      (m : ℝ) * ((k : ℝ) / n) ^ 2 ≤ (L + 3) ^ 2 / m := by
    have hratioSq : ((k : ℝ) / n) ^ 2 ≤ (1 / (m : ℝ) ^ 2) ^ 2 := by
      have hinv0 : 0 ≤ 1 / (m : ℝ) ^ 2 := by positivity
      nlinarith only [hkOverNRate, hkOverN0, hinv0]
    have hmul := mul_le_mul_of_nonneg_left hratioSq hmR.le
    have htarget : (m : ℝ) * (1 / (m : ℝ) ^ 2) ^ 2 ≤ 1 / m := by
      field_simp [hmR.ne']
      have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
    have hq : 1 / (m : ℝ) ≤ (L + 3) ^ 2 / m := by
      apply div_le_div_of_nonneg_right _ hmR.le
      nlinarith only [hL]
    exact hmul.trans (htarget.trans hq)
  let upperNorm : ℝ :=
    6 * ((M : ℝ) * η + 2) * Real.sqrt ((M + 1 : ℝ) / k) +
      (m : ℝ) * k / (2 * n) + (1 + L) / (2 * n) +
      (m : ℝ) * ((k : ℝ) / n) ^ 2
  have hupperNorm : upperNorm ≤ δ := by
    let q : ℝ := (L + 3) ^ 2 / m
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hstatQ :
        6 * ((M : ℝ) * η + 2) * Real.sqrt ((M + 1 : ℝ) / k) ≤
          360 * q := by dsimp [q]; convert hstat using 1 <;> ring
    calc
      upperNorm ≤ 360 * q + q + q + q := by
        dsimp only [upperNorm]
        exact add_le_add (add_le_add (add_le_add hstatQ hcross) hdiag) hpilot
      _ ≤ 400 * q := by linarith only [hq0]
      _ = δ := by dsimp [q, δ, growingInverseParameterError]; ring
  have hupperEq :
      growingUpperRawError n k (M - 1) ((m : ℝ) - 1) η L =
        (n : ℝ) ^ 2 * upperNorm := by
    unfold growingUpperRawError
    dsimp [upperNorm]
    push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
    field_simp [hnR.ne']
    ring
  have hUpper :
      growingUpperRawError n k (M - 1) ((m : ℝ) - 1) η L ≤
        (n : ℝ) ^ 2 * δ := by
    rw [hupperEq]
    exact mul_le_mul_of_nonneg_left hupperNorm (sq_nonneg _)
  let γ : ℝ :=
    ((n : ℝ) / (M : ℝ) ^ 2 + step +
      (1 / (M : ℝ) ^ 2 + 2 * step / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card) / n
  let base : ℝ :=
    (backwardCheckpoints step cutoff).card *
        (n / ((n : ℝ) / (M : ℝ) ^ 2) ^ 2) +
      (backwardCheckpoints step cutoff).card *
        ((2 / (suffixPositions cutoff).card) / (1 / (M : ℝ) ^ 2) ^ 2)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hcount : (M + 1 : ℝ) * γ ≤ δ₀ := by
    simpa [M, step, cutoff, γ, δ₀] using hCounts
  have hbad : (M + 2 : ℝ) * base ≤ δ₀ := by
    simpa [M, step, cutoff, base, δ₀] using hBad
  have hbadOne : (M + 1 : ℝ) * base ≤ δ₀ := by
    have hcoeff : (M + 1 : ℝ) ≤ M + 2 := by norm_num
    exact (mul_le_mul_of_nonneg_right hcoeff hbase0).trans hbad
  have hfactor : 1 + L + η ≤ L + 2 := by linarith only [hη1]
  have hfactor0 : 0 ≤ 1 + L + η := by positivity
  have hcountTerm :
      (M + 1 : ℝ) * γ * (1 + L + η) ≤ (L + 2) * δ₀ := by
    calc
      (M + 1 : ℝ) * γ * (1 + L + η) ≤
          δ₀ * (1 + L + η) :=
        mul_le_mul_of_nonneg_right hcount hfactor0
      _ ≤ δ₀ * (L + 2) :=
        mul_le_mul_of_nonneg_left hfactor hδ₀0
      _ = (L + 2) * δ₀ := by ring
  have hbadTerm :
      (1 + L + η) * ((M + 1 : ℝ) * base) ≤ (L + 2) * δ₀ := by
    calc
      (1 + L + η) * ((M + 1 : ℝ) * base) ≤
          (1 + L + η) * δ₀ :=
        mul_le_mul_of_nonneg_left hbadOne hfactor0
      _ ≤ (L + 2) * δ₀ :=
        mul_le_mul_of_nonneg_right hfactor hδ₀0
  have hlowerRate :
      η + (M + 1 : ℝ) * γ * (1 + L + η) +
          (1 + L + η) * ((M + 1 : ℝ) * base) ≤ δ := by
    let q : ℝ := (L + 3) ^ 2 / m
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hηQ : η ≤ q := by
      rw [hη]
      dsimp [q]
      apply div_le_div_of_nonneg_right _ hmR.le
      nlinarith only [hL]
    have hδRate : δ₀ ≤ 30 * (L + 1) / m := by
      dsimp [δ₀]
      rw [hMCast]
      have hinv : 1 / (m : ℝ) ^ 2 ≤ 1 / m := by
        exact one_div_le_one_div_of_le hmR (by
          nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)])
      have hcoef0 : 0 ≤ 30 * (L + 1) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hinv hcoef0
      convert hmul using 1 <;> ring
    have hprod : (L + 2) * δ₀ ≤ 30 * q := by
      have hmul := mul_le_mul_of_nonneg_left hδRate
        (show 0 ≤ L + 2 by linarith only [hL])
      have hsq : (L + 2) * (L + 1) ≤ (L + 3) ^ 2 := by
        nlinarith only [hL]
      calc
        (L + 2) * δ₀ ≤ (L + 2) * (30 * (L + 1) / m) := hmul
        _ = 30 * ((L + 2) * (L + 1)) / m := by ring
        _ ≤ 30 * q := by
          dsimp [q]
          have hbound := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 30)) hmR.le
          convert hbound using 1 <;> ring
    have hcountQ :
        (M + 1 : ℝ) * γ * (1 + L + η) ≤ 30 * q := by
      calc
        _ ≤ (L + 2) * δ₀ := hcountTerm
        _ ≤ 30 * q := hprod
    have hbadQ :
        (1 + L + η) * ((M + 1 : ℝ) * base) ≤ 30 * q :=
      hbadTerm.trans hprod
    calc
      η + (M + 1 : ℝ) * γ * (1 + L + η) +
          (1 + L + η) * ((M + 1 : ℝ) * base) ≤ q + 30 * q + 30 * q :=
        add_le_add (add_le_add hηQ hcountQ) hbadQ
      _ ≤ 400 * q := by linarith only [hq0]
      _ = δ := by dsimp [q, δ, growingInverseParameterError]; ring
  refine ⟨?_, ?_⟩
  · simpa [M, k, η, δ, universalGrowingGridIntervals,
      universalGrowingCutoff] using hUpper
  · unfold growingLowerUniformError
    convert hlowerRate using 1 <;>
      simp [M, step, cutoff, γ, base, η, δ,
        universalGrowingGridIntervals, universalGrowingCutoff,
        Nat.cast_sub (by omega : 1 ≤ M)] <;> ring

set_option maxHeartbeats 5000000 in
/-- Finite instance-optimality of the input-bound-independent growing policy
on every positive-mean bounded population. -/
theorem exists_fixedPlacement_universalGrowingPolicy_positive_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m)
    (hn : (universalGrowingAccuracy m) ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (universalGrowingPilotSize n m +
      (n - universalGrowingPilotSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := universalGrowingPilotSize n m
    let r := n - k
    let d := universalGrowingGridIntervals m
    let η := universalGrowingMesh m
    let Bcut := universalGrowingCutoff m
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η
            (by change (0 : ℝ) < 1 / m; positivity) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  dsimp only
  let M := universalGrowingAccuracy m
  let k := inverseSquareSize n M
  let r := n - k
  let d := M - 1
  let η : ℝ := 1 / m
  let Bcut : ℝ := (m : ℝ) - 1
  have hM : 2 ≤ M := by dsimp [M, universalGrowingAccuracy]; nlinarith
  obtain ⟨hk, hklt, _hstep, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hM hn
  have htotal : k + r = n := by dsimp [r]; omega
  have hr : 0 < r := by dsimp [r]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hmR]
    exact_mod_cast (by omega : 1 ≤ m)
  have hB0 : 0 ≤ Bcut := by
    dsimp [Bcut]
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ m by omega))
  have hMCast : (M : ℝ) = (m : ℝ) ^ 2 := by
    simp [M, universalGrowingAccuracy]
  have hgridValue : (d : ℝ) * η = (m : ℝ) - 1 / m := by
    dsimp [d, η]
    push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
    rw [hMCast]
    field_simp [hmR.ne']
  have hBgrid : Bcut ≤ (d : ℝ) * η := by
    rw [hgridValue]
    dsimp [Bcut]
    have hinv : 1 / (m : ℝ) ≤ 1 := hη1
    linarith
  have hgrid : L ≤ (d : ℝ) * η := by
    exact (by dsimp [Bcut]; linarith only [hcover] : L ≤ Bcut).trans hBgrid
  have hBcover : 1 + L + η ≤ Bcut := by
    have : L + 2 ≤ (m : ℝ) - 1 := by
      linarith only [hcover]
    dsimp [Bcut]
    linarith only [hη1, this]
  have hnTotal : M ^ 16 ≤ k + r := by simpa [htotal] using hn
  obtain ⟨hkTotal, _hkTotalLt, hstepTotal, _⟩ :=
    parameter_scales hM hnTotal
  let cutoff := inverseSquareCutoff (k + r) M hkTotal
  let step := inverseFourthStep (k + r) M
  let e : ℝ := (k + r : ℝ) / (M : ℝ) ^ 2
  let s : ℝ := 1 / (M : ℝ) ^ 2
  have he : 0 < e := by dsimp [e]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨hUpper, hLower⟩ :=
    universal_growing_parameter_error_bounds hm hnTotal hL
  have hkEq : inverseSquareSize (k + r) M = k := by simp [k, htotal]
  have hkEq' : inverseSquareSize (k + r) (m ^ 2) = k := by
    simpa [M, universalGrowingAccuracy] using hkEq
  apply exists_fixedPlacement_growingPolicy_le_of_error_bounds
      k r d hk hr Bcut η L hη hB0 hBgrid hgrid hBcover
      p hp0 hpL hmean policy htest cutoff hstepTotal hstepTotal he hs
      (growingInverseParameterError_nonneg hL m)
  · simpa [M, hkEq', d, η, Bcut, universalGrowingAccuracy,
      universalGrowingGridIntervals, universalGrowingMesh,
      universalGrowingCutoff] using hUpper
  · simpa [M, cutoff, step, e, s, d, η,
      universalGrowingAccuracy, universalGrowingGridIntervals,
      universalGrowingMesh, universalGrowingCutoff] using hLower

set_option maxHeartbeats 5000000 in
/-- The exact all-zero branch for the same input-size-only policy. -/
theorem exists_fixedPlacement_universalGrowingPolicy_zero_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m)
    (hn : (universalGrowingAccuracy m) ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (universalGrowingPilotSize n m +
      (n - universalGrowingPilotSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (hmean : populationMean p = 0)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := universalGrowingPilotSize n m
    let r := n - k
    let d := universalGrowingGridIntervals m
    let η := universalGrowingMesh m
    let Bcut := universalGrowingCutoff m
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η
            (by change (0 : ℝ) < 1 / m; positivity) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  dsimp only
  let M := universalGrowingAccuracy m
  let k := inverseSquareSize n M
  let r := n - k
  let d := M - 1
  let η : ℝ := 1 / m
  let Bcut : ℝ := (m : ℝ) - 1
  have hM : 2 ≤ M := by dsimp [M, universalGrowingAccuracy]; nlinarith
  obtain ⟨hk, hklt, _hstep, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hM hn
  have htotal : k + r = n := by dsimp [r]; omega
  have hr : 0 < r := by dsimp [r]; omega
  have htotalPos : 0 < k + r := by omega
  have hpzero := processing_eq_zero_of_populationMean_eq_zero
    htotalPos p hp0 hmean
  let zero := RandomizedOptional.UnboundedOperational.zeroProcessing (k + r)
  have hpEq : p = zero := by
    funext job
    simpa [zero, RandomizedOptional.UnboundedOperational.zeroProcessing]
      using hpzero job
  subst p
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hmR]
    exact_mod_cast (by omega : 1 ≤ m)
  have hB0 : 0 ≤ Bcut := by
    dsimp [Bcut]
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ m by omega))
  have hMCast : (M : ℝ) = (m : ℝ) ^ 2 := by
    simp [M, universalGrowingAccuracy]
  have hgridValue : (d : ℝ) * η = (m : ℝ) - 1 / m := by
    dsimp [d, η]
    push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
    rw [hMCast]
    field_simp [hmR.ne']
  have hBgrid : Bcut ≤ (d : ℝ) * η := by
    rw [hgridValue]
    dsimp [Bcut]
    linarith only [hη1]
  have hgrid : L ≤ (d : ℝ) * η := by
    exact (by dsimp [Bcut]; linarith only [hcover] : L ≤ Bcut).trans hBgrid
  have hBcover : 1 + L + η ≤ Bcut := by
    have hL2 : L + 2 ≤ (m : ℝ) - 1 := by linarith only [hcover]
    dsimp [Bcut]
    linarith only [hη1, hL2]
  have hrun := uniformAverage_physicalGrowingRunCost_le_minimum
    k r d hk hr Bcut η L hη hB0 hBgrid hgrid hBcover
      zero (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing, hL.le])
  have hmin := minimumGrowingTemplateValue_le_half_of_eq_zero
    (d := d) htotalPos η hη zero
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
  obtain ⟨hUpper, _hLower⟩ :=
    universal_growing_parameter_error_bounds (n := k + r) hm
      (by simpa [htotal] using hn) hL
  have hUpper' :
      growingUpperRawError (k + r) k d Bcut η L ≤
        (k + r : ℝ) ^ 2 * growingInverseParameterError L m := by
    have hkEq : inverseSquareSize (k + r) M = k := by simp [k, htotal]
    have hkEq' : inverseSquareSize (k + r) (m ^ 2) = k := by
      simpa [M, universalGrowingAccuracy] using hkEq
    simpa [M, hkEq', d, η, Bcut, universalGrowingAccuracy,
      universalGrowingGridIntervals, universalGrowingMesh,
      universalGrowingCutoff] using hUpper
  let σ : ObservedTrace.Placement (k + r) := Equiv.refl (Fin (k + r))
  have hcompetitor :
      uniformAverage (fun seed => normalizedCost zero (policy seed) σ) =
        (k + r + 1 : ℝ) / (2 * (k + r)) := by
    rw [show (fun seed => normalizedCost zero (policy seed) σ) =
        fun _seed : Seeds => (k + r + 1 : ℝ) / (2 * (k + r)) by
      funext seed
      have hz := normalizedCost_zero_eq htotalPos (policy seed) (htest seed) σ
      convert hz using 1 <;> push_cast <;> ring]
    exact uniformAverage_const _
  have hcompetitorHalf :
      (1 : ℝ) / 2 ≤ uniformAverage
        (fun seed => normalizedCost zero (policy seed) σ) := by
    rw [hcompetitor]
    have htotalR : (0 : ℝ) < k + r := by exact_mod_cast htotalPos
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) htotalR)]
    push_cast
    linarith
  have hminScaled := mul_le_mul_of_nonneg_left hmin (sq_nonneg (k + r : ℝ))
  have hcompetitorScaled := mul_le_mul_of_nonneg_left hcompetitorHalf
    (sq_nonneg (k + r : ℝ))
  have hδ0 := growingInverseParameterError_nonneg hL m
  refine ⟨σ, ?_⟩
  dsimp only at hrun
  unfold growingUpperRawError at hUpper'
  push_cast at hrun hUpper' hminScaled hcompetitorScaled
  have hfinal :
      uniformAverage (physicalGrowingRunCost (k + r) k d Bcut η hη zero) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost zero (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
    push_cast
    nlinarith
  simpa [M, k, r, d, η, Bcut, universalGrowingAccuracy,
    universalGrowingPilotSize, universalGrowingGridIntervals,
    universalGrowingMesh, universalGrowingCutoff] using hfinal

/-- Uniform finite instance-optimality for every bounded nonnegative input;
the implemented policy family is independent of `L` and of the multiset. -/
theorem exists_fixedPlacement_universalGrowingPolicy_all_means_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m)
    (hn : (universalGrowingAccuracy m) ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (universalGrowingPilotSize n m +
      (n - universalGrowingPilotSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := universalGrowingPilotSize n m
    let r := n - k
    let d := universalGrowingGridIntervals m
    let η := universalGrowingMesh m
    let Bcut := universalGrowingCutoff m
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η
            (by change (0 : ℝ) < 1 / m; positivity) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  have htotalPos : 0 < universalGrowingPilotSize n m +
      (n - universalGrowingPilotSize n m) := by
    have hM : 2 ≤ universalGrowingAccuracy m := by
      simp [universalGrowingAccuracy]
      nlinarith
    obtain ⟨hk, hklt, _⟩ := parameter_scales hM hn
    omega
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun job _ => hp0 job) (by positivity)
  by_cases hzero : populationMean p = 0
  · exact exists_fixedPlacement_universalGrowingPolicy_zero_rate
      hm hn hL hcover p hp0 hpL hzero policy htest
  · have hmean : 0 < populationMean p := lt_of_le_of_ne hmean0 (Ne.symm hzero)
    exact exists_fixedPlacement_universalGrowingPolicy_positive_rate
      hm hn hL hcover p hp0 hpL hmean policy htest

/-! ## A single input-size-only accuracy parameter -/

def thirtySecondRoot (n : ℕ) : ℝ := Real.sqrt (sixteenthRoot n)

def concreteUniversalGrowingParameter (n : ℕ) : ℕ :=
  ⌊thirtySecondRoot n⌋₊

theorem thirtySecondRoot_nonneg (n : ℕ) : 0 ≤ thirtySecondRoot n := by
  unfold thirtySecondRoot
  positivity

theorem thirtySecondRoot_pow_thirtyTwo (n : ℕ) :
    (thirtySecondRoot n) ^ 32 = n := by
  have hsq : (thirtySecondRoot n) ^ 2 = sixteenthRoot n := by
    unfold thirtySecondRoot
    exact Real.sq_sqrt (sixteenthRoot_nonneg n)
  calc
    (thirtySecondRoot n) ^ 32 = ((thirtySecondRoot n) ^ 2) ^ 16 := by ring
    _ = (sixteenthRoot n) ^ 16 := by rw [hsq]
    _ = n := sixteenthRoot_pow_sixteen n

theorem concreteUniversalGrowingParameter_bounds
    (n : ℕ) (hroot : 2 ≤ thirtySecondRoot n) :
    2 ≤ concreteUniversalGrowingParameter n ∧
      (universalGrowingAccuracy (concreteUniversalGrowingParameter n)) ^ 16 ≤ n := by
  have hm : 2 ≤ concreteUniversalGrowingParameter n := by
    unfold concreteUniversalGrowingParameter
    exact Nat.le_floor hroot
  have hfloor : (concreteUniversalGrowingParameter n : ℝ) ≤
      thirtySecondRoot n := by
    unfold concreteUniversalGrowingParameter
    exact Nat.floor_le (thirtySecondRoot_nonneg n)
  have hpow : (concreteUniversalGrowingParameter n : ℝ) ^ 32 ≤
      (thirtySecondRoot n) ^ 32 := by
    gcongr
  rw [thirtySecondRoot_pow_thirtyTwo] at hpow
  refine ⟨hm, ?_⟩
  unfold universalGrowingAccuracy
  have hnat : (concreteUniversalGrowingParameter n) ^ 32 ≤ n := by
    exact_mod_cast hpow
  convert hnat using 1 <;> ring

theorem concreteUniversalGrowingParameter_tendsto_atTop :
    Filter.Tendsto concreteUniversalGrowingParameter
      Filter.atTop Filter.atTop := by
  unfold concreteUniversalGrowingParameter thirtySecondRoot sixteenthRoot
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp
        (Real.tendsto_sqrt_atTop.comp
          (Real.tendsto_sqrt_atTop.comp
            (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))))

def concreteUniversalGrowingError (L : ℝ) (n : ℕ) : ℝ :=
  growingInverseParameterError L (concreteUniversalGrowingParameter n)

theorem concreteUniversalGrowingError_tendsto_zero (L : ℝ) :
    Filter.Tendsto (concreteUniversalGrowingError L)
      Filter.atTop (nhds 0) := by
  unfold concreteUniversalGrowingError growingInverseParameterError
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp
      concreteUniversalGrowingParameter_tendsto_atTop)
    (400 * (L + 3) ^ 2)

theorem eventually_concreteUniversalGrowingParameter_covers (L : ℝ) :
    ∀ᶠ n in Filter.atTop,
      L + 3 ≤ (concreteUniversalGrowingParameter n : ℝ) := by
  have htend : Filter.Tendsto
      (fun n => (concreteUniversalGrowingParameter n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      concreteUniversalGrowingParameter_tendsto_atTop
  exact htend.eventually (Filter.eventually_ge_atTop (L + 3))

/-- Final input-size-only finite theorem.  Its displayed error coefficient
tends to zero, and for every fixed `L` the two size hypotheses hold
eventually. -/
theorem exists_fixedPlacement_universalGrowingPolicy_concrete_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n : ℕ} (hroot : 2 ≤ thirtySecondRoot n)
    {L : ℝ} (hL : 0 < L)
    (hcover : L + 3 ≤ concreteUniversalGrowingParameter n)
    (p : Fin (universalGrowingPilotSize n
        (concreteUniversalGrowingParameter n) +
      (n - universalGrowingPilotSize n
        (concreteUniversalGrowingParameter n))) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let m := concreteUniversalGrowingParameter n
    let k := universalGrowingPilotSize n m
    let r := n - k
    let d := universalGrowingGridIntervals m
    let η := universalGrowingMesh m
    let Bcut := universalGrowingCutoff m
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d Bcut η
            (by
              change (0 : ℝ) < 1 / concreteUniversalGrowingParameter n
              apply one_div_pos.mpr
              exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
                (concreteUniversalGrowingParameter_bounds n hroot).1)) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * concreteUniversalGrowingError L n) := by
  dsimp only
  let m := concreteUniversalGrowingParameter n
  obtain ⟨hm, hn⟩ := concreteUniversalGrowingParameter_bounds n hroot
  simpa [m, concreteUniversalGrowingError] using
    (exists_fixedPlacement_universalGrowingPolicy_all_means_rate
      (m := m) hm hn hL hcover p hp0 hpL policy htest)

end

end ObligatoryInstance
end SchedulingPaper
