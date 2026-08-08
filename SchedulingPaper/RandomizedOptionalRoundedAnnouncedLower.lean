import SchedulingPaper.RandomizedOptionalRoundedBenchmark
import SchedulingPaper.RandomizedOptionalObservedGlobalGood
import SchedulingPaper.RandomizedOptionalGoodEventAverage
import Mathlib.Tactic

/-!
# Finite announced lower bound for an upward-rounded support

The concentration event is stated for the rounded blind work.  Combined
with the operational rounding bridge, it yields a lower bound for schedules
executed with the original (unrounded) processing times.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedRoundedLower

open Randomized
open ObservedOnline
open ObservedTrace
open TraceBijection
open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

def gridIndicator {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) :
    Option ι → Fin n → ℝ
  | none, occurrence => if zeroCategory (p occurrence) then 1 else 0
  | some i, occurrence => if G.category i (p occurrence) then 1 else 0

structure PlacementGood {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (policy : CompletePolicy p)
    (γ blindError : ℝ) (σ : ObservedTrace.Placement n) : Prop where
  class_good : ∀ cutoff i,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if G.category i
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.mass i *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n
  zero_good : ∀ cutoff,
    |(∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          (if zeroCategory
            (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
      B.zeroMass *
        ∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ γ * n
  blind_good : ∀ cutoff,
    |(∑ k ∈ positionsThrough cutoff,
        compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ) *
          G.roundedProcessing
            (revealOrder (touchTrace p policy) σ k)) -
      B.mean *
        ∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
            (revealOrder (touchTrace p policy) σ)| ≤ blindError * n

def normalizedCost {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : ObservedTrace.Placement n) : ℝ :=
  completionCost (placedProcessing p σ)
      (settledRun p policy.strategy σ).config.transcript / (n : ℝ) ^ 2

theorem uniformAverage_normalizedCost_ge
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (G : RoundedPositiveGrid ι p) (B : BenchmarkData p G)
    {γ blindError δ U : ℝ}
    (hγ : 0 ≤ γ) (hblindError : 0 ≤ blindError)
    (hU0 : 0 ≤ U) (hvalueU : B.value ≤ U)
    (hbad : uniformProbability
      (fun σ => ¬ PlacementGood B policy γ blindError σ) ≤ δ) :
    B.value - (blindError + G.mesh) -
        (Fintype.card ι + 1) * γ * (1 + B.mean) - U * δ ≤
      uniformAverage (normalizedCost p policy) := by
  classical
  let Bad : ObservedTrace.Placement n → Prop := fun σ =>
    ¬ PlacementGood B policy γ blindError σ
  let repaired := B.value - (blindError + G.mesh) -
    (Fintype.card ι + 1) * γ * (1 + B.mean)
  have hprocessing : ∀ σ job, 0 ≤ placedProcessing p σ job := by
    intro σ job
    exact G.processing_nonneg (σ job)
  have hcost0 : ∀ σ, 0 ≤ normalizedCost p policy σ := by
    intro σ
    unfold normalizedCost
    apply div_nonneg
    · apply completionCost_nonneg_of_revealsMatch (hprocessing σ)
      dsimp [settledRun]
      exact (run_historyInvariant (placedProcessing p σ) policy.strategy
        (2 * n + 1)).revealsMatch
    · positivity
  have hgood : ∀ σ, ¬ Bad σ → repaired ≤ normalizedCost p policy σ := by
    intro σ hnotBad
    have hplacement : PlacementGood B policy γ blindError σ := by
      simpa [Bad] using hnotBad
    have hpath := settled_cost_ge_fixedFluidMinimum_rounded hn p policy σ G
      B.selected B.mass_def B.zeroMass_def B.mean_def hγ hblindError
      B.tau_pos B.mean_pos B.price_pos B.population_mass B.mean_partition
      hplacement.class_good hplacement.zero_good hplacement.blind_good
      B.density_max B.module_pos B.module_density B.minimizes
    simpa [repaired, BenchmarkData.value, normalizedCost] using hpath
  have hrepairedU : repaired ≤ U := by
    dsimp [repaired]
    have hrepair0 : 0 ≤ blindError + G.mesh +
        (Fintype.card ι + 1 : ℝ) * γ * (1 + B.mean) := by
      have hmean0 : 0 ≤ B.mean := B.mean_pos.le
      exact add_nonneg (add_nonneg hblindError G.mesh_nonneg)
        (mul_nonneg (mul_nonneg (by positivity) hγ) (by linarith))
    linarith
  have haverage := uniformAverage_ge_of_good_event
    (normalizedCost p policy) Bad hcost0 hgood hrepairedU hU0
    (by simpa [Bad] using hbad)
  simpa [repaired, Bad, sub_eq_add_neg, add_assoc] using haverage

theorem placementGood_bad_probability_le_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (policy : CompletePolicy p) (G : RoundedPositiveGrid ι p)
    (hroundedScale : ∀ i, G.roundedProcessing i ≤ scale)
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
            (G.roundedProcessing
              (revealOrder (touchTrace p policy) σ k) / scale)) -
        populationMean (fun occurrence => G.roundedProcessing occurrence / scale) *
          ∑ k ∈ positionsThrough j,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)|
  have hvalue0 : ∀ c i, 0 ≤ gridIndicator G c i := by
    intro c i
    rcases c with _ | c <;> simp only [gridIndicator] <;> split <;> norm_num
  have hvalue1 : ∀ c i, gridIndicator G c i ≤ 1 := by
    intro c i
    rcases c with _ | c <;> simp only [gridIndicator] <;> split <;> norm_num
  have htest : uniformProbability TestBad ≤
      (Fintype.card ι + 1) * base := by
    have h := adaptivePolicy_all_categories_global_prefix_probability_le
      hn p policy (gridIndicator G) cutoff hMartingaleStep hSuffixStep
      hvalue0 hvalue1 he hr
    simpa [TestBad, threshold, base] using h
  have hblind : uniformProbability BlindBad ≤ base := by
    have h := adaptivePolicy_blind_global_prefix_probability_le
      hn p policy (fun occurrence => G.roundedProcessing occurrence / scale)
      cutoff hMartingaleStep hSuffixStep
      (fun occurrence => div_nonneg (G.roundedProcessing_nonneg occurrence)
        hscale.le)
      (fun occurrence => (div_le_one hscale).mpr (hroundedScale occurrence)) he hr
    simpa [BlindBad, threshold, base] using h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hthreshold : threshold = γ * n := by
    dsimp [γ]
    field_simp [hnR.ne']
  have hcontain : ∀ σ,
      ¬ PlacementGood B policy γ (scale * γ) σ → TestBad σ ∨ BlindBad σ := by
    intro σ hnotGood
    by_contra hnotUnion
    have hnotTest : ¬ TestBad σ := fun h => hnotUnion (Or.inl h)
    have hnotBlind : ¬ BlindBad σ := fun h => hnotUnion (Or.inr h)
    apply hnotGood
    constructor
    · intro j i
      have hle := le_of_not_gt fun h => hnotTest ⟨some i, j, h⟩
      simpa [gridIndicator, B.mass_def i, hthreshold] using hle
    · intro j
      have hle := le_of_not_gt fun h => hnotTest ⟨none, j, h⟩
      have hmeanZero : populationMean (gridIndicator G none) = B.zeroMass := by
        change populationMean
          (fun occurrence => if zeroCategory (p occurrence) then 1 else 0) =
            B.zeroMass
        exact B.zeroMass_def.symm
      rw [hmeanZero, hthreshold] at hle
      simpa [gridIndicator] using hle
    · intro j
      have hle := le_of_not_gt fun h => hnotBlind ⟨j, h⟩
      have hmeanScale :
          populationMean (fun occurrence => G.roundedProcessing occurrence / scale) =
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
              G.roundedProcessing
                (revealOrder (touchTrace p policy) σ k)) -
          B.mean *
            ∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                (revealOrder (touchTrace p policy) σ)
      have hnormalized :
          (∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                (G.roundedProcessing
                  (revealOrder (touchTrace p policy) σ k) / scale)) -
            (B.mean / scale) *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) = original / scale := by
        dsimp [original]
        have hsum :
            (∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                    (revealOrder (touchTrace p policy) σ) *
                  (G.roundedProcessing
                    (revealOrder (touchTrace p policy) σ k) / scale)) =
              (∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                    (revealOrder (touchTrace p policy) σ) *
                  G.roundedProcessing
                    (revealOrder (touchTrace p policy) σ k)) / scale := by
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
                G.roundedProcessing
                  (revealOrder (touchTrace p policy) σ k)) -
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

theorem uniformAverage_normalizedCost_ge_checkpoint_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (policy : CompletePolicy p) (G : RoundedPositiveGrid ι p)
    (hroundedScale : ∀ i, G.roundedProcessing i ≤ scale)
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
    B.value - (scale * γ + G.mesh) -
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
  have hbad := placementGood_bad_probability_le_scaled hn p hscale
    policy G hroundedScale B cutoff hMartingaleStep hSuffixStep he hr
  have havg := uniformAverage_normalizedCost_ge hn0 p policy G B hγ hblind
    hU0 hvalueU (by simpa [threshold, γ, base] using hbad)
  simpa [threshold, γ, base] using havg

theorem populationMean_le_scale
    {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) {scale : ℝ}
    (hf : ∀ i, f i ≤ scale) : populationMean f ≤ scale := by
  unfold populationMean
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  calc
    (∑ i, f i) ≤ ∑ _i : Fin n, scale :=
      Finset.sum_le_sum fun i _ => hf i
    _ = scale * n := by simp [mul_comm]

/-- Closed finite rounded-support lower bound: the empirical benchmark is
constructed internally, including its threshold and optimal tested fraction. -/
theorem exists_empiricalBenchmark_uniformAverage_lower_scaled
    {n : ℕ} (hn : 1 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (policy : CompletePolicy p) (G : RoundedPositiveGrid ι p)
    (hroundedScale : ∀ i, G.roundedProcessing i ≤ scale)
    (hprice : ∀ i, 0 < G.price i)
    (hmean : 0 < populationMean G.roundedProcessing) (cutoff : Fin n)
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
      B.value - (scale * γ + G.mesh) -
          (Fintype.card ι + 1) * γ * (1 + B.mean) -
          (1 + scale) * ((Fintype.card ι + 2) * base) ≤
        uniformAverage (normalizedCost p policy) := by
  dsimp
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  obtain ⟨B⟩ := exists_empiricalBenchmarkData hn0 p G hprice hmean
  have hmeanLe : B.mean ≤ scale := by
    rw [B.mean_def]
    exact populationMean_le_scale hn0 G.roundedProcessing hroundedScale
  have hvalue : B.value ≤ 1 + scale :=
    (B.value_le_one_add_mean hn0).trans (by linarith)
  have hlower := uniformAverage_normalizedCost_ge_checkpoint_scaled hn p
    hscale policy G hroundedScale B cutoff hMartingaleStep hSuffixStep he hr
    (U := 1 + scale) (by linarith) hvalue
  exact ⟨B, hlower⟩

end

end AnnouncedRoundedLower
end RandomizedOptional
end SchedulingPaper
