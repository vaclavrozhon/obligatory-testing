import SchedulingPaper.RandomizedOptionalBlindPilot
import SchedulingPaper.RandomizedOptionalInstanceOptimal
import Mathlib.Tactic

/-!
# Unknown-multiset instance optimality for optional testing

The theorem in this file is the finite, fully quantified composition of the
announced-policy lower bound and the universal blind-pilot upper bound.  The
same empirical rounded benchmark appears on both sides; it is eliminated in
the final comparison theorem.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

theorem boundedUniform_blindPilot_le_every_announced_policy
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let roundedScale := L + L / K
    let scale := max 1 roundedScale
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let badBound :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ B : BenchmarkData p G,
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage
          (blindPilotLearnedCost G pilotPositions pilotOrder)) /
          (n : ℝ) ^ 2 ≤
        uniformAverage (normalizedCost p policy) +
          (roundedScale * γ + L / K) +
          (K + 1) * γ * (1 + B.mean) +
          (1 + roundedScale) * ((K + 2) * badBound) +
          24 * (scale + 1) *
            Real.sqrt ((K + 1 : ℝ) / pilotPositions.card) +
          (17 + 63 * scale) / n +
          12 * (scale + 1) * (L / K) +
          2 * pilotPositions.card * L / n := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  let roundedScale : ℝ := L + L / K
  let scale : ℝ := max 1 roundedScale
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let badBound : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  obtain ⟨B, hlower⟩ := exists_boundedUniformBenchmark_uniformAverage_lower
    hn hK hL p hp0 hpL hmean policy cutoff hMartingaleStep hSuffixStep he hr
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmesh : 0 < L / (K : ℝ) := div_pos hL hKR
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  have hprice0 : ∀ i, 0 < G.price i := by
    intro i
    exact uniformGridPrice_pos hmesh i
  have hprice : Function.Injective G.price := by
    intro i j hij
    apply Fin.ext
    dsimp [G, boundedUniformRoundedGrid, uniformRoundedGrid,
      uniformGridPrice] at hij
    have hcast : (i.val : ℝ) = j.val := by
      nlinarith
    exact_mod_cast hcast
  have hscaleOne : 1 ≤ scale := le_max_left _ _
  have hroundedScale0 : 0 ≤ roundedScale := by
    dsimp [roundedScale]
    positivity
  have hroundedLeScale : roundedScale ≤ scale := le_max_right _ _
  have hLLeRounded : L ≤ roundedScale := by
    dsimp [roundedScale]
    have : 0 ≤ L / (K : ℝ) := hmesh.le
    linarith
  have hpScale : ∀ job, p job ≤ scale := by
    intro job
    exact (hpL job).trans (hLLeRounded.trans hroundedLeScale)
  have hroundedScale : ∀ job, G.roundedProcessing job ≤ scale := by
    intro job
    exact (boundedUniformRoundedGrid_roundedProcessing_le
      hK hL p hp0 hpL job).trans hroundedLeScale
  have hpriceScale : ∀ i, G.price i ≤ scale := by
    intro i
    have hiNat : i.val + 1 ≤ K := by omega
    have hiReal : (i.val + 1 : ℝ) ≤ K := by exact_mod_cast hiNat
    have hendpoint : G.price i ≤ L := by
      rw [boundedUniformRoundedGrid_price]
      unfold uniformGridPrice
      have hmul := mul_le_mul_of_nonneg_right hiReal hmesh.le
      rw [mul_div_cancel₀ L hKR.ne'] at hmul
      exact hmul
    exact hendpoint.trans (hLLeRounded.trans hroundedLeScale)
  have hupper := blindPilotLearnedCost_le_benchmark hn G hprice0 hprice
    pilotPositions hpilot B hscaleOne hpScale hroundedScale hpriceScale hpL
  refine ⟨B, ?_⟩
  have hcardOption : (Fintype.card (Option (Fin K)) : ℝ) = K + 1 := by simp
  rw [hcardOption] at hupper
  have hmeshEq : G.mesh = L / (K : ℝ) := rfl
  rw [hmeshEq] at hupper
  exact le_trans hupper (by
    dsimp [roundedScale, scale, threshold, γ, badBound]
    linarith [hlower])

/-- A compact rate-ready wrapper.  If every announced lower-bound error is
at most `δ` and the four learning/implementation errors are also at most
`δ`, the universal blind-pilot schedule is within an explicit multiple of
`δ` of every adaptive announced policy. -/
theorem boundedUniform_blindPilot_le_every_policy_of_error_bounds
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (pilotPositions : Finset (Fin n)) (hpilot : pilotPositions.Nonempty)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r δ : ℝ} (he : 0 < e) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hDiscovery :
      (L + L / K) *
          ((e + martingaleStep +
            (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) + L / K ≤ δ)
    (hCounts :
      (K + 1) *
        ((e + martingaleStep +
          (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card) / n) ≤ δ)
    (hBad :
      (K + 2) *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) ≤ δ)
    (hLearning :
      Real.sqrt ((K + 1 : ℝ) / pilotPositions.card) ≤ δ)
    (hInverse : 1 / (n : ℝ) ≤ δ)
    (hMesh : L / (K : ℝ) ≤ δ)
    (hPilot : pilotPositions.card * L / n ≤ δ) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let scale := max 1 (L + L / K)
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage
        (blindPilotLearnedCost G pilotPositions pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      uniformAverage (normalizedCost p policy) +
        (59 + 101 * scale) * δ := by
  dsimp
  obtain ⟨B, hcomparison⟩ :=
    boundedUniform_blindPilot_le_every_announced_policy hn hK hL p hp0 hpL
      hmean pilotPositions hpilot policy cutoff hMartingaleStep hSuffixStep he hr
  let roundedScale : ℝ := L + L / K
  let scale : ℝ := max 1 roundedScale
  have hscale1 : 1 ≤ scale := le_max_left _ _
  have hroundScale : roundedScale ≤ scale := le_max_right _ _
  have hrounded0 : 0 ≤ roundedScale := by
    dsimp [roundedScale]
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hmesh0 : 0 ≤ L / (K : ℝ) := (div_pos hL hKR).le
    linarith
  have hmeanLe : B.mean ≤ roundedScale := by
    rw [B.mean_def]
    exact populationMean_le_scale (show 0 < n by omega)
      (boundedUniformRoundedGrid hK hL p hp0 hpL).roundedProcessing
      (fun job => boundedUniformRoundedGrid_roundedProcessing_le
        hK hL p hp0 hpL job)
  have hdiscovery' :
      roundedScale *
          ((e + martingaleStep +
            (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) + L / K ≤ δ := by
    simpa [roundedScale] using hDiscovery
  have hcounts' := hCounts
  have hcountTerm :
      (K + 1 : ℝ) *
          ((e + martingaleStep +
            (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) * (1 + B.mean) ≤
        δ * (1 + roundedScale) := by
    exact mul_le_mul hcounts' (by linarith) (by linarith [B.mean_pos]) hδ
  have hbadTerm :
      (1 + roundedScale) *
          ((K + 2 : ℝ) *
            ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
              (backwardCheckpoints suffixStep cutoff).card *
                ((2 / (suffixPositions cutoff).card) / r ^ 2))) ≤
        (1 + roundedScale) * δ :=
    mul_le_mul_of_nonneg_left hBad (by linarith)
  have hlearningTerm :
      24 * (scale + 1) *
          Real.sqrt ((K + 1 : ℝ) / pilotPositions.card) ≤
        24 * (scale + 1) * δ :=
    mul_le_mul_of_nonneg_left hLearning (by positivity)
  have hinverseTerm : (17 + 63 * scale) / (n : ℝ) ≤
      (17 + 63 * scale) * δ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hInverse)
      (by linarith)
  have hmeshTerm : 12 * (scale + 1) * (L / (K : ℝ)) ≤
      12 * (scale + 1) * δ :=
    mul_le_mul_of_nonneg_left hMesh (by positivity)
  have hpilterm : 2 * pilotPositions.card * L / (n : ℝ) ≤ 2 * δ := by
    calc
      2 * pilotPositions.card * L / (n : ℝ) =
          2 * (pilotPositions.card * L / n) := by ring
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hPilot (by norm_num)
  have hconstant :
      δ + δ * (1 + roundedScale) + (1 + roundedScale) * δ +
          24 * (scale + 1) * δ + (17 + 63 * scale) * δ +
          12 * (scale + 1) * δ + 2 * δ ≤
        (59 + 101 * scale) * δ := by
    nlinarith
  simpa [roundedScale, scale] using
    (show _ ≤ _ from (le_trans hcomparison (by
      linarith [hdiscovery', hcountTerm, hbadTerm, hlearningTerm,
        hinverseTerm, hmeshTerm, hpilterm, hconstant])))

end

end RandomizedOptional
end SchedulingPaper
