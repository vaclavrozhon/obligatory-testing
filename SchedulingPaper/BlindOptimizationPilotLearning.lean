import SchedulingPaper.BlindOptimizationDistribution
import SchedulingPaper.RandomizedHypergeometric
import SchedulingPaper.RandomizedHistogramL1
import Mathlib.Tactic

/-!
# Mean-only pilot learning for blind optimization

Blind optimization needs to learn only the empirical mean.  This module
checks the without-replacement mean estimate and the threshold decision
`OptimizeAll` versus `Raw` for an arbitrary bounded finite population.
-/

namespace SchedulingPaper
namespace BlindOptimization

noncomputable section

open SchedulingPaper.Randomized

def permutationSampleMean {n : ℕ} (positions : Finset (Fin n))
    (processing : Fin n → ℝ) (order : Equiv.Perm (Fin n)) : ℝ :=
  permutationSampleSum positions processing order / positions.card

def learnedBlockLength (u populationMean sampleMean : ℝ) : ℝ :=
  if 1 + sampleMean < u then 1 + populationMean else u

theorem learnedBlockLength_sub_opt_le_abs
    {u μ μhat : ℝ} :
    learnedBlockLength u μ μhat - min u (1 + μ) ≤ |μhat - μ| := by
  unfold learnedBlockLength
  by_cases hsample : 1 + μhat < u
  · rw [if_pos hsample]
    by_cases htrue : 1 + μ ≤ u
    · rw [min_eq_right htrue]
      simp
    · rw [min_eq_left (le_of_not_ge htrue)]
      have habs := neg_le_abs (μhat - μ)
      linarith
  · rw [if_neg hsample]
    have hsample' : u ≤ 1 + μhat := le_of_not_gt hsample
    by_cases htrue : u ≤ 1 + μ
    · rw [min_eq_left htrue]
      simp
    · rw [min_eq_right (le_of_not_ge htrue)]
      have habs := le_abs_self (μhat - μ)
      linarith

theorem min_le_learnedBlockLength {u μ μhat : ℝ} :
    min u (1 + μ) ≤ learnedBlockLength u μ μhat := by
  unfold learnedBlockLength
  split
  · exact min_le_right _ _
  · exact min_le_left _ _

theorem sampleMean_error_eq
    {n : ℕ} (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (processing : Fin n → ℝ) (order : Equiv.Perm (Fin n)) :
    permutationSampleMean positions processing order - populationMean processing =
      (permutationSampleSum positions processing order -
        (positions.card : ℝ) * populationMean processing) /
          positions.card := by
  unfold permutationSampleMean
  have hk : (positions.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hpositions
  field_simp [hk]

theorem centeredPopulation_sq_sum_le
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u) :
    (∑ job, centeredPopulation processing job ^ 2) ≤ n * u ^ 2 := by
  have hmean : populationMean processing ∈ Set.Icc (0 : ℝ) u := by
    have hcard : (0 : ℝ) < n := by exact_mod_cast hn
    unfold populationMean
    simp only [Fintype.card_fin]
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun job _ ↦ (hp job).1) hcard.le
    ·
      rw [div_le_iff₀ hcard]
      calc
        ∑ job, processing job ≤ ∑ _job : Fin n, u :=
          Finset.sum_le_sum fun job _ ↦ (hp job).2
        _ = u * n := by simp [mul_comm]
  have hpoint : ∀ job, centeredPopulation processing job ^ 2 ≤ u ^ 2 := by
    intro job
    unfold centeredPopulation
    have hlower : -u ≤ processing job - populationMean processing := by
      linarith [(hp job).1, hmean.2]
    have hupper : processing job - populationMean processing ≤ u := by
      linarith [(hp job).2, hmean.1]
    nlinarith [sq_nonneg (processing job - populationMean processing + u),
      sq_nonneg (u - (processing job - populationMean processing))]
  calc
    (∑ job, centeredPopulation processing job ^ 2) ≤ ∑ _job : Fin n, u ^ 2 :=
      Finset.sum_le_sum fun job _ ↦ hpoint job
    _ = n * u ^ 2 := by simp

/-- Mean-square error at most `u²/k`, with the finite-population correction
retained in the proof and then discarded. -/
theorem uniformAverage_sampleMean_error_sq_le
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty) :
    uniformAverage (fun order : Equiv.Perm (Fin n) ↦
      (permutationSampleMean positions processing order -
        populationMean processing) ^ 2) ≤ u ^ 2 / positions.card := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hvariance := uniformAverage_permutationSampleSum_variance
    positions processing (by simpa using hn)
  simp only [Fintype.card_fin] at hvariance
  have hk : (0 : ℝ) < positions.card := by
    exact_mod_cast Finset.card_pos.mpr hpositions
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hkn : (positions.card : ℝ) ≤ n := by
    exact_mod_cast (show positions.card ≤ n by simpa using Finset.card_le_univ positions)
  have hcenter := centeredPopulation_sq_sum_le (by omega) hu0 processing hp
  have hfactor0 : 0 ≤
      (positions.card : ℝ) * ((n : ℝ) - positions.card) /
        ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  have hrewrite :
      uniformAverage (fun order : Equiv.Perm (Fin n) ↦
        (permutationSampleMean positions processing order -
          populationMean processing) ^ 2) =
        (1 / (positions.card : ℝ) ^ 2) *
          uniformAverage (fun order : Equiv.Perm (Fin n) ↦
            (permutationSampleSum positions processing order -
              (positions.card : ℝ) * populationMean processing) ^ 2) := by
    rw [← uniformAverage_smul]
    apply congrArg uniformAverage
    funext order
    rw [sampleMean_error_eq positions hpositions]
    ring
  rw [hrewrite, hvariance]
  have hcorrection :
      (n : ℝ) - positions.card ≤ (n : ℝ) - 1 := by
    have hkoneNat : 1 ≤ positions.card := Finset.one_le_card.mpr hpositions
    have hkone : (1 : ℝ) ≤ positions.card := by exact_mod_cast hkoneNat
    linarith
  have hratio :
      ((n : ℝ) - positions.card) / ((n : ℝ) - 1) ≤ 1 := by
    exact (div_le_one (by linarith)).2 hcorrection
  have hcenter' :
      (∑ job, centeredPopulation processing job ^ 2) ≤ (n : ℝ) * u ^ 2 := by
    simpa using hcenter
  have hnonnegCenter : 0 ≤ ∑ job, centeredPopulation processing job ^ 2 :=
    Finset.sum_nonneg fun job _ ↦ sq_nonneg _
  calc
    (1 / (positions.card : ℝ) ^ 2) *
        (((positions.card : ℝ) * ((n : ℝ) - positions.card) /
          ((n : ℝ) * ((n : ℝ) - 1))) *
            ∑ job, centeredPopulation processing job ^ 2) =
      (1 / (positions.card : ℝ)) *
        (((n : ℝ) - positions.card) / ((n : ℝ) - 1)) *
        ((∑ job, centeredPopulation processing job ^ 2) / n) := by
          field_simp [ne_of_gt hk, (by linarith : (n : ℝ) ≠ 0),
            (by linarith : (n : ℝ) - 1 ≠ 0)]
    _ ≤ (1 / (positions.card : ℝ)) * 1 *
        ((∑ job, centeredPopulation processing job ^ 2) / n) := by
      have hmeanSq : 0 ≤
          (∑ job, centeredPopulation processing job ^ 2) / (n : ℝ) :=
        div_nonneg hnonnegCenter (by linarith)
      calc
        (1 / (positions.card : ℝ)) *
            (((n : ℝ) - positions.card) / ((n : ℝ) - 1)) *
              ((∑ job, centeredPopulation processing job ^ 2) / n) =
            (1 / (positions.card : ℝ)) *
              ((((n : ℝ) - positions.card) / ((n : ℝ) - 1)) *
                ((∑ job, centeredPopulation processing job ^ 2) / n)) := by ring
        _ ≤ (1 / (positions.card : ℝ)) *
              (1 * ((∑ job, centeredPopulation processing job ^ 2) / n)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hratio hmeanSq) (by positivity)
        _ = _ := by ring
    _ ≤ (1 / (positions.card : ℝ)) * 1 * u ^ 2 := by
      have hmeanBound :
          (∑ job, centeredPopulation processing job ^ 2) / (n : ℝ) ≤ u ^ 2 :=
        (div_le_iff₀ (by linarith)).2 (by simpa [mul_comm] using hcenter')
      exact mul_le_mul_of_nonneg_left hmeanBound (by positivity)
    _ = u ^ 2 / positions.card := by ring

/-- The learned threshold has mean regret whose square is at most `u²/k`.
This is the statistical core of the universal BO policy. -/
theorem pilot_expected_blockLength_regret_sq_le
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty) :
    let μ := populationMean processing
    (uniformAverage (fun order : Equiv.Perm (Fin n) ↦
        learnedBlockLength u μ
          (permutationSampleMean positions processing order)) -
      min u (1 + μ)) ^ 2 ≤ u ^ 2 / positions.card := by
  dsimp only
  let μ := populationMean processing
  let regret := fun order : Equiv.Perm (Fin n) ↦
    learnedBlockLength u μ
      (permutationSampleMean positions processing order) - min u (1 + μ)
  have hregret : ∀ order, 0 ≤ regret order := by
    intro order
    exact sub_nonneg.mpr min_le_learnedBlockLength
  have hpoint : ∀ order, regret order ≤
      |permutationSampleMean positions processing order - μ| := by
    intro order
    exact learnedBlockLength_sub_opt_le_abs
  have havgPoint := uniformAverage_mono hpoint
  have habsSq := uniformAverage_abs_sq_le_uniformAverage_sq
    (fun order : Equiv.Perm (Fin n) ↦
      permutationSampleMean positions processing order - μ)
  have hmse := uniformAverage_sampleMean_error_sq_le
    hn hu0 processing hp positions hpositions
  have havgNonneg : 0 ≤ uniformAverage regret :=
    uniformAverage_nonneg hregret
  have habsNonneg : 0 ≤ uniformAverage (fun order : Equiv.Perm (Fin n) ↦
      |permutationSampleMean positions processing order - μ|) :=
    uniformAverage_nonneg fun _ ↦ abs_nonneg _
  have hsquare := (sq_le_sq₀ havgNonneg habsNonneg).2 havgPoint
  have hregretAverage :
      uniformAverage regret =
        uniformAverage (fun order : Equiv.Perm (Fin n) ↦
          learnedBlockLength u μ
            (permutationSampleMean positions processing order)) -
          min u (1 + μ) := by
    unfold regret uniformAverage
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      positivity
    field_simp [hcard]
  rw [← hregretAverage]
  exact hsquare.trans (habsSq.trans hmse)

/-- Rate-ready form of the pilot lemma.  The expected block length selected
from the sample is within the square-root mean-estimation error of the better
of `Raw` and `OptimizeAll`. -/
theorem pilot_expected_blockLength_le_sqrt
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty) :
    let μ := populationMean processing
    uniformAverage (fun order : Equiv.Perm (Fin n) ↦
        learnedBlockLength u μ
          (permutationSampleMean positions processing order)) ≤
      min u (1 + μ) + Real.sqrt (u ^ 2 / positions.card) := by
  dsimp only
  let μ := populationMean processing
  let averageLearned := uniformAverage (fun order : Equiv.Perm (Fin n) ↦
    learnedBlockLength u μ
      (permutationSampleMean positions processing order))
  have hnonneg : 0 ≤ averageLearned - min u (1 + μ) := by
    apply sub_nonneg.mpr
    calc
      min u (1 + μ) = uniformAverage (fun _order : Equiv.Perm (Fin n) ↦
          min u (1 + μ)) := (uniformAverage_const _).symm
      _ ≤ averageLearned := by
        dsimp [averageLearned]
        apply uniformAverage_mono
        intro order
        exact min_le_learnedBlockLength
  have hsquare := pilot_expected_blockLength_regret_sq_le hn hu0 processing hp
    positions hpositions
  have hsqrt : averageLearned - min u (1 + μ) ≤
      Real.sqrt (u ^ 2 / positions.card) := by
    apply Real.le_sqrt_of_sq_le
    simpa [averageLearned, μ] using hsquare
  linarith

/-- A looser but elementary `u / √k` presentation of the same rate. -/
theorem pilot_expected_blockLength_le_invSqrt
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty) :
    let μ := populationMean processing
    uniformAverage (fun order : Equiv.Perm (Fin n) ↦
        learnedBlockLength u μ
          (permutationSampleMean positions processing order)) ≤
      min u (1 + μ) + u / Real.sqrt positions.card := by
  dsimp only
  have hbase := pilot_expected_blockLength_le_sqrt hn hu0 processing hp
    positions hpositions
  dsimp only at hbase
  have hk0 : (0 : ℝ) ≤ positions.card := by positivity
  have hsqrtCard : 0 < Real.sqrt (positions.card : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Finset.card_pos.mpr hpositions
  have hsqrtSq : Real.sqrt (positions.card : ℝ) ^ 2 = positions.card := by
    exact Real.sq_sqrt hk0
  have hsqrtDiv : Real.sqrt (u ^ 2 / (positions.card : ℝ)) =
      u / Real.sqrt positions.card := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hu0 hsqrtCard.le)).mp
    rw [Real.sq_sqrt]
    · field_simp [hsqrtCard.ne']
      nlinarith
    · positivity
  rwa [hsqrtDiv] at hbase

/-- A finite schedule envelope for the sample-then-commit policy.  The first
term pays every one of the `k` pilot blocks against all `n` completion
positions; the second is the random-order main schedule selected from the
sample estimate. -/
def pilotScheduleEnvelope
    (n k : ℕ) (u populationMean sampleMean : ℝ) : ℝ :=
  (1 + u) * k * n +
    n * (n + 1) / 2 * learnedBlockLength u populationMean sampleMean

/-- Expected finite pilot envelope with an explicit `u/√k` learning term.
For `k = ⌈n^(2/3)⌉`, both displayed errors are `o_u(n²)`. -/
theorem pilotScheduleEnvelope_expected_le
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty) :
    let μ := populationMean processing
    uniformAverage (fun order : Equiv.Perm (Fin n) ↦
        pilotScheduleEnvelope n positions.card u μ
          (permutationSampleMean positions processing order)) ≤
      n * (n + 1) / 2 * min u (1 + μ) +
        (1 + u) * positions.card * n +
        n * (n + 1) / 2 * (u / Real.sqrt positions.card) := by
  dsimp only
  let μ := populationMean processing
  have hlearn := pilot_expected_blockLength_le_invSqrt hn hu0 processing hp
    positions hpositions
  dsimp only at hlearn
  rw [show (fun order : Equiv.Perm (Fin n) ↦
      pilotScheduleEnvelope n positions.card u μ
        (permutationSampleMean positions processing order)) =
      (fun order ↦
        (1 + u) * positions.card * n +
          (n * (n + 1) / 2) *
            learnedBlockLength u μ
              (permutationSampleMean positions processing order)) by
    funext order
    rfl,
    uniformAverage_add, uniformAverage_const, uniformAverage_smul]
  have htri : 0 ≤ (n : ℝ) * (n + 1) / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlearn htri]

end

end BlindOptimization
end SchedulingPaper
