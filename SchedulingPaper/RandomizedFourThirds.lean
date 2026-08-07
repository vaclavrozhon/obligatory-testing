import SchedulingPaper.RandomizedGoodLearned
import SchedulingPaper.RandomizedIidBinaryLower
import SchedulingPaper.RandomizedOnlineBinaryCompiler
import SchedulingPaper.RandomizedOperationalStrategy
import SchedulingPaper.RandomizedOperationalExpected
import SchedulingPaper.RandomizedParameterChoice
import Mathlib.Tactic

/-!
# Public `4/3` randomized obligatory-testing certificates

This is the assembly point for the explicit upper constant and the
unconditional oblivious Yao lower bound.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

/-- Public operational upper bound for the literal sampled strategy.  Unlike
the older abstract assembly theorem below, this statement has no assumed
per-sample `hgood`/`hbad` schedule inequalities: those branches, termination,
and their transcript accounting have all been discharged. -/
theorem unknownMultiset_operational_expectedCost_le_20378
    (k rest d : ℕ) (hk : 0 < k) (hrest : 0 < rest)
    (hnCard : 1 < k + rest)
    (η R : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hηUpper : η ≤ 32 / 12) (hR : 12 ≤ R)
    (hsize : (k + rest : ℝ) ≤ R ^ 4)
    (hsampleSize : (k : ℝ) ≤ R ^ 3)
    (herror : Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) ≤ 2 / R)
    (hrounding : η ≤ 64 / R)
    (p : Fin (k + rest) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage
        (physicalSampledRunCost (k + rest) k d η hη p) ≤
      4 / 3 * finiteObligatoryOPT p + 20378 * R ^ 7 :=
  uniformAverage_physicalSampledRunCost_le_20378
    k rest d hk hrest hnCard η R hη hcutoff hηUpper hR hsize
      hsampleSize herror hrounding p hp

/-- Final upper-bound assembly with the paper's explicit constant.

The good/bad hypotheses are the deterministic per-sample schedule bounds.
The preceding modules prove their ingredients: the complete good-learned
fluid certificate, fallback certificate, bad learned bound, and sample-first
implementation overhead.  This theorem performs the concentration,
good/bad averaging, and final coefficient calculation. -/
theorem unknownMultiset_expectedCost_le_20378
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (samplePositions : Finset α) (category : α → β)
    (hSample : samplePositions.Nonempty)
    (hcard : 1 < Fintype.card α)
    (cost : Equiv.Perm α → ℝ) {opt r : ℝ}
    (hr : 12 ≤ r)
    (hsize : (Fintype.card α : ℝ) ≤ r ^ 4)
    (herrorRate :
      Real.sqrt ((Fintype.card β : ℝ) / samplePositions.card) ≤ 2 / r)
    (hgood : ∀ σ,
      ¬(1 / 1056 < histogramL1Error samplePositions category σ) →
      cost σ ≤ 4 / 3 * opt +
        (Fintype.card α : ℝ) ^ 2 *
          (1024 * histogramL1Error samplePositions category σ + 1408 / r) +
        17 * ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2))
    (hbad : ∀ σ,
      1 / 1056 < histogramL1Error samplePositions category σ →
      cost σ ≤ 4 / 3 * opt + 8 * (Fintype.card α : ℝ) ^ 2 +
        17 * ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2)) :
    uniformAverage cost ≤ 4 / 3 * opt + 20378 * r ^ 7 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hN0 : 0 ≤ (Fintype.card α : ℝ) := by positivity
  have hr4 : 0 ≤ r ^ 4 := by positivity
  have hN2raw := mul_self_le_mul_self hN0 hsize
  have hN2 : (Fintype.card α : ℝ) ^ 2 ≤ r ^ 8 := by
    nlinarith
  have havg := expectedCost_le_histogram_B32
    samplePositions category hSample hcard cost
    (n := (Fintype.card α : ℝ)) (opt := opt) (rounding := 1408 / r)
    (overhead := 17 *
      ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2))
    (by positivity) (by positivity) (by positivity) hgood hbad
  have hsqrtScaled :
      9472 * Real.sqrt ((Fintype.card β : ℝ) / samplePositions.card) ≤
        9472 * (2 / r) :=
    mul_le_mul_of_nonneg_left herrorRate (by norm_num)
  have hn2 : 0 ≤ (Fintype.card α : ℝ) ^ 2 := by positivity
  have hbracket0 :
      0 ≤ 9472 * (2 / r) + 704 * (2 / r) := by positivity
  have hmainScale :
      (Fintype.card α : ℝ) ^ 2 *
          (9472 * (2 / r) + 704 * (2 / r)) ≤
        r ^ 8 * (9472 * (2 / r) + 704 * (2 / r)) :=
    mul_le_mul_of_nonneg_right hN2 hbracket0
  have hoverheadScale :
      17 * ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2) ≤
        17 * (r ^ 4 * r ^ 3 / 2 + (r ^ 3) ^ 2) := by
    have hr3 : 0 ≤ r ^ 3 := by positivity
    have hprod := mul_le_mul_of_nonneg_right hsize hr3
    nlinarith
  have hupper :
      uniformAverage cost ≤ 4 / 3 * opt +
        r ^ 8 * (9472 * (2 / r) + 704 * (2 / r)) +
        17 * (r ^ 4 * r ^ 3 / 2 + (r ^ 3) ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left
      (add_le_add_right hsqrtScaled (1408 / r)) hn2
    have hround : 1408 / r = 704 * (2 / r) := by ring
    rw [hround] at havg hscaled
    exact havg.trans (by nlinarith)
  exact explicit_20378_bound hr hupper

/-- Multiplicative form of the same explicit upper theorem. -/
theorem unknownMultiset_expectedCost_le_multiplicative
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (samplePositions : Finset α) (category : α → β)
    (hSample : samplePositions.Nonempty)
    (hcard : 1 < Fintype.card α)
    (cost : Equiv.Perm α → ℝ) {opt r : ℝ}
    (hr : 12 ≤ r)
    (hsize : (Fintype.card α : ℝ) = r ^ 4)
    (hopt : r ^ 8 / 2 ≤ opt)
    (herrorRate :
      Real.sqrt ((Fintype.card β : ℝ) / samplePositions.card) ≤ 2 / r)
    (hgood : ∀ σ,
      ¬(1 / 1056 < histogramL1Error samplePositions category σ) →
      cost σ ≤ 4 / 3 * opt +
        (Fintype.card α : ℝ) ^ 2 *
          (1024 * histogramL1Error samplePositions category σ + 1408 / r) +
        17 * ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2))
    (hbad : ∀ σ,
      1 / 1056 < histogramL1Error samplePositions category σ →
      cost σ ≤ 4 / 3 * opt + 8 * (Fintype.card α : ℝ) ^ 2 +
        17 * ((Fintype.card α : ℝ) * r ^ 3 / 2 + (r ^ 3) ^ 2)) :
    uniformAverage cost ≤ (4 / 3 + 40756 / r) * opt := by
  have hadd := unknownMultiset_expectedCost_le_20378
    samplePositions category hSample hcard cost hr hsize.le herrorRate hgood hbad
  apply additive_20378_to_multiplicative
    (n := r ^ 4) (nQuarter := r) (alg := uniformAverage cost) (opt := opt)
  · positivity
  · linarith
  · rfl
  · simpa only [show (r ^ 4) ^ 2 = r ^ 8 by ring] using hopt
  · exact hadd

/-- Public unconditional matching lower bound for every finite family of
private random seeds. -/
theorem oblivious_iid_binary_lower
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policy : Seeds → LabelledBinaryPolicy n Finset.univ n) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) * iidBinaryOfflineCost n input ≤
        uniformAverage fun seed => (policy seed).cost input :=
  iid_binary_yao_lower_labelled hn policy

/-- The same unconditional lower bound stated against the literal finite
clairvoyant obligatory-testing optimum of the selected `0/2` vector. -/
theorem oblivious_iid_binary_lower_actualOPT
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policy : Seeds → LabelledBinaryPolicy n Finset.univ n) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) *
          finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
        uniformAverage fun seed => (policy seed).cost input := by
  obtain ⟨input, hinput⟩ := oblivious_iid_binary_lower hn policy
  refine ⟨input, ?_⟩
  rwa [← iidBinaryOfflineCost_eq_finiteObligatoryOPT hn input]

/-- Fully operational Yao lower bound.  Each seed is an arbitrary
public-transcript online strategy; the sole semantic premise is that the
common fuel bound suffices to finish every fair-binary input. -/
theorem oblivious_iid_binary_lower_online_actualOPT
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ seed input job,
      (Online.run .infinite
        (Online.fixedOracle (iidBinaryProcessingTime input))
        (strategy seed) fuel).config.jobs job = .done) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) *
          finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
        uniformAverage fun seed =>
          Online.runCompletionCost .infinite
            (iidBinaryProcessingTime input)
            (Online.run .infinite
              (Online.fixedOracle (iidBinaryProcessingTime input))
              (strategy seed) fuel) :=
  onlineStrategies_oblivious_iid_binary_lower_actualOPT
    hn strategy fuel hdone

end

end RandomizedObligatory
end SchedulingPaper
