import SchedulingPaper.RandomizedOptionalAnnouncedExactConcentration
import SchedulingPaper.RandomizedOptionalBenchmarkOptimizer
import Mathlib.Tactic

/-!
# Closed finite announced lower bound on an exact bounded support

This file removes the last abstract benchmark assumptions from the exact-grid
lower bound.  The benchmark is constructed from the empirical histogram and
the bad-event loss is bounded solely in terms of the support bound.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedExactLower

open Randomized
open ObservedEnvelope
open ObservedOnline
open ObservedTrace

noncomputable section
attribute [local instance] Classical.propDecidable

theorem populationMean_le_scale
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) {scale : ℝ}
    (hp : ∀ i, p i ≤ scale) : populationMean p ≤ scale := by
  unfold populationMean
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  calc
    (∑ i, p i) ≤ ∑ _i : Fin n, scale :=
      Finset.sum_le_sum fun i _ => hp i
    _ = scale * n := by simp [mul_comm]

/-- Completely instantiated finite lower bound for every deterministic
complete policy on a positive exact grid.  The existential `B` is the
canonical empirical value: its maximum-density module and optimal tested
fraction are both constructed internally. -/
theorem exists_empiricalBenchmark_uniformAverage_lower_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (hpScale : ∀ i, p i ≤ scale)
    (policy : CompletePolicy p) (G : ExactPositiveGrid ι p)
    (hprice : ∀ i, 0 < G.price i)
    (hmean : 0 < populationMean p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ B : BenchmarkData p G,
      B.value - scale * γ -
          (Fintype.card ι + 1) * γ * (1 + B.mean) -
          (1 + scale) * ((Fintype.card ι + 2) * base) ≤
        uniformAverage (normalizedCost p policy) := by
  dsimp
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  obtain ⟨B, _⟩ := exists_empiricalBenchmarkData hn0 p G hprice hmean
  have hmeanLe : B.mean ≤ scale := by
    rw [B.mean_def]
    exact populationMean_le_scale hn0 p hpScale
  have hvalue : B.value ≤ 1 + scale :=
    (B.value_le_one_add_mean hn0).trans (by linarith)
  have hlower := uniformAverage_normalizedCost_ge_checkpoint_scaled hn p
    hscale hpScale policy G B cutoff hMartingaleStep hSuffixStep he hr
    (U := 1 + scale) (by linarith) hvalue
  exact ⟨B, hlower⟩

end

end AnnouncedExactLower
end RandomizedOptional
end SchedulingPaper
