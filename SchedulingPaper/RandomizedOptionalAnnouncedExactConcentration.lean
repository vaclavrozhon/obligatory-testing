import SchedulingPaper.RandomizedOptionalAnnouncedExactLower
import SchedulingPaper.RandomizedOptionalObservedGlobalGood
import Mathlib.Tactic

/-!
# Simultaneous good-event probability for exact bounded supports

Zero and all positive support classes are combined into `Option ι`, so one
global checkpoint event controls every revelation constraint.  A second
event controls blind work.  This unit-bounded version is the normalization
used by the general bounded theorem.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedExactLower

open Randomized
open ObservedOnline
open ObservedTrace
open TraceBijection
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

def gridIndicator {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : ExactPositiveGrid ι p) :
    Option ι → Fin n → ℝ
  | none, occurrence => if zeroCategory (p occurrence) then 1 else 0
  | some i, occurrence => if G.category i (p occurrence) then 1 else 0

theorem placementGood_bad_probability_le_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (hpScale : ∀ i, p i ≤ scale)
    (policy : CompletePolicy p) (G : ExactPositiveGrid ι p)
    (B : BenchmarkData p G) (cutoff : Fin n)
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
    uniformProbability
        (fun σ => ¬ PlacementGood B policy γ (scale * γ) σ) ≤
      (Fintype.card ι + 2) * base := by
  dsimp
  classical
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  let TestBad : ObservedTrace.Placement n → Prop := fun σ => ∃ c, ∃ j : Fin n,
    threshold <
      |(∑ k ∈ positionsThrough j,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            gridIndicator G c (revealOrder (touchTrace p policy) σ k)) -
        populationMean (gridIndicator G c) *
          ∑ k ∈ positionsThrough j,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)|
  let BlindBad : ObservedTrace.Placement n → Prop := fun σ => ∃ j : Fin n,
    threshold <
      |(∑ k ∈ positionsThrough j,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (p (revealOrder (touchTrace p policy) σ k) / scale)) -
        populationMean (fun occurrence => p occurrence / scale) *
          ∑ k ∈ positionsThrough j,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)|
  have hvalue0 : ∀ c i, 0 ≤ gridIndicator G c i := by
    intro c i
    rcases c with _ | c <;> simp only [gridIndicator] <;>
      split <;> norm_num
  have hvalue1 : ∀ c i, gridIndicator G c i ≤ 1 := by
    intro c i
    rcases c with _ | c <;> simp only [gridIndicator] <;>
      split <;> norm_num
  have htest : uniformProbability TestBad ≤
      (Fintype.card ι + 1) * base := by
    have h := adaptivePolicy_all_categories_global_prefix_probability_le
      hn p policy (gridIndicator G) cutoff hMartingaleStep hSuffixStep
      hvalue0 hvalue1 he hr
    simpa [TestBad, threshold, base] using h
  have hblind : uniformProbability BlindBad ≤ base := by
    have h := adaptivePolicy_blind_global_prefix_probability_le
      hn p policy (fun occurrence => p occurrence / scale) cutoff
      hMartingaleStep hSuffixStep
      (fun occurrence => div_nonneg (G.processing_nonneg occurrence) hscale.le)
      (fun occurrence => (div_le_one hscale).mpr (hpScale occurrence)) he hr
    simpa [BlindBad, threshold, base] using h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hthreshold : threshold = γ * n := by
    dsimp [γ]
    field_simp [hnR.ne']
  have hcontain : ∀ σ,
      ¬ PlacementGood B policy γ (scale * γ) σ →
        TestBad σ ∨ BlindBad σ := by
    intro σ hnotGood
    by_contra hnotUnion
    have hnotTest : ¬ TestBad σ := fun h => hnotUnion (Or.inl h)
    have hnotBlind : ¬ BlindBad σ := fun h => hnotUnion (Or.inr h)
    apply hnotGood
    constructor
    · intro j i
      have hle :
          |(∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                gridIndicator G (some i)
                  (revealOrder (touchTrace p policy) σ k)) -
            populationMean (gridIndicator G (some i)) *
              ∑ k ∈ positionsThrough j,
                compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ)| ≤ threshold :=
        le_of_not_gt fun h => hnotTest ⟨some i, j, h⟩
      simpa [gridIndicator, B.mass_def i, hthreshold] using hle
    · intro j
      have hle :
          |(∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                gridIndicator G none
                  (revealOrder (touchTrace p policy) σ k)) -
            populationMean (gridIndicator G none) *
              ∑ k ∈ positionsThrough j,
                compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ)| ≤ threshold :=
        le_of_not_gt fun h => hnotTest ⟨none, j, h⟩
      have hmeanZero :
          populationMean (gridIndicator G none) = B.zeroMass := by
        change populationMean
          (fun occurrence => if zeroCategory (p occurrence) then 1 else 0) =
            B.zeroMass
        exact B.zeroMass_def.symm
      rw [hmeanZero, hthreshold] at hle
      simpa [gridIndicator] using hle
    · intro j
      have hle :
          |(∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                (p (revealOrder (touchTrace p policy) σ k) / scale)) -
            populationMean (fun occurrence => p occurrence / scale) *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ)| ≤ threshold :=
        le_of_not_gt fun h => hnotBlind ⟨j, h⟩
      have hmeanScale :
          populationMean (fun occurrence => p occurrence / scale) =
            B.mean / scale := by
        rw [B.mean_def]
        unfold populationMean
        rw [Finset.sum_div]
        simp only [div_div]
        rw [mul_comm scale]
        rw [Finset.sum_div]
      rw [hmeanScale] at hle
      let original :=
        (∑ k ∈ positionsThrough j,
            compiledBlindSelector p policy k
                (revealOrder (touchTrace p policy) σ) *
              p (revealOrder (touchTrace p policy) σ k)) -
          B.mean *
            ∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                (revealOrder (touchTrace p policy) σ)
      have hnormalized :
          (∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                (p (revealOrder (touchTrace p policy) σ k) / scale)) -
            (B.mean / scale) *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) =
            original / scale := by
        dsimp [original]
        have hsum :
            (∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                    (revealOrder (touchTrace p policy) σ) *
                  (p (revealOrder (touchTrace p policy) σ k) / scale)) =
              (∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                    (revealOrder (touchTrace p policy) σ) *
                  p (revealOrder (touchTrace p policy) σ k)) / scale := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        rw [hsum]
        ring
      rw [hnormalized, abs_div, abs_of_pos hscale] at hle
      rw [div_le_iff₀ hscale] at hle
      dsimp [original] at hle ⊢
      calc
        |(∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                p (revealOrder (touchTrace p policy) σ k)) -
            B.mean *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ)| ≤
            threshold * scale := hle
        _ = scale * γ * n := by rw [hthreshold]; ring
  calc
    uniformProbability
        (fun σ => ¬ PlacementGood B policy γ (scale * γ) σ) ≤
        uniformProbability (fun σ => TestBad σ ∨ BlindBad σ) :=
      uniformProbability_mono hcontain
    _ ≤ uniformProbability TestBad + uniformProbability BlindBad :=
      uniformProbability_or_le TestBad BlindBad
    _ ≤ (Fintype.card ι + 1) * base + base := add_le_add htest hblind
    _ = (Fintype.card ι + 2) * base := by ring

theorem placementGood_bad_probability_le_unit
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (hp1 : ∀ i, p i ≤ 1)
    (policy : CompletePolicy p) (G : ExactPositiveGrid ι p)
    (B : BenchmarkData p G) (cutoff : Fin n)
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
    uniformProbability
        (fun σ => ¬ PlacementGood B policy γ γ σ) ≤
      (Fintype.card ι + 2) * base := by
  simpa using placementGood_bad_probability_le_scaled hn p (scale := 1)
    (by norm_num) hp1 policy G B cutoff hMartingaleStep hSuffixStep he hr

theorem uniformAverage_normalizedCost_ge_checkpoint_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (hpScale : ∀ i, p i ≤ scale)
    (policy : CompletePolicy p) (G : ExactPositiveGrid ι p)
    (B : BenchmarkData p G) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r U : ℝ} (he : 0 < e) (hr : 0 < r)
    (hU0 : 0 ≤ U) (hvalueU : B.value ≤ U) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    B.value - scale * γ -
        (Fintype.card ι + 1) * γ * (1 + B.mean) -
        U * ((Fintype.card ι + 2) * base) ≤
      uniformAverage (normalizedCost p policy) := by
  dsimp
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hγ : 0 ≤ γ := by
    dsimp [γ, threshold]
    positivity
  have hblind : 0 ≤ scale * γ := mul_nonneg hscale.le hγ
  have hbad := placementGood_bad_probability_le_scaled hn p hscale hpScale
    policy G B cutoff hMartingaleStep hSuffixStep he hr
  have havg := uniformAverage_normalizedCost_ge hn0 p policy G B hγ hblind
    hU0 hvalueU (by simpa [threshold, γ, base] using hbad)
  simpa [threshold, γ, base] using havg

/-- The explicit finite exact-support lower bound obtained by inserting the
global checkpoint probability into `uniformAverage_normalizedCost_ge`. -/
theorem uniformAverage_normalizedCost_ge_checkpoint_unit
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (hp1 : ∀ i, p i ≤ 1)
    (policy : CompletePolicy p) (G : ExactPositiveGrid ι p)
    (B : BenchmarkData p G) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r U : ℝ} (he : 0 < e) (hr : 0 < r)
    (hU0 : 0 ≤ U) (hvalueU : B.value ≤ U) :
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    B.value - γ - (Fintype.card ι + 1) * γ * (1 + B.mean) -
        U * ((Fintype.card ι + 2) * base) ≤
      uniformAverage (normalizedCost p policy) := by
  dsimp
  let threshold : ℝ := e + martingaleStep +
    (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
    (suffixPositions cutoff).card
  let γ : ℝ := threshold / n
  let base : ℝ :=
    (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
      (backwardCheckpoints suffixStep cutoff).card *
        ((2 / (suffixPositions cutoff).card) / r ^ 2)
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hγ : 0 ≤ γ := by
    dsimp [γ, threshold]
    positivity
  have hbad := placementGood_bad_probability_le_unit hn p hp1 policy G B
    cutoff hMartingaleStep hSuffixStep he hr
  have havg := uniformAverage_normalizedCost_ge hn0 p policy G B hγ hγ
    hU0 hvalueU (by simpa [threshold, γ, base] using hbad)
  simpa [threshold, γ, base] using havg

end

end AnnouncedExactLower
end RandomizedOptional
end SchedulingPaper
