import SchedulingPaper.RandomizedOptionalCanonicalBenchmark
import Mathlib.Tactic

/-!
# Executing a rounded optional benchmark on the original processing times

The benchmark is computed on an upward grid.  A legal policy observes the
actual tested value, maps it to its grid value, and uses the rounded class for
its decisions, while physical processing still takes the actual duration.
This file proves that the resulting canonical fluid moments differ from the
rounded moments by at most one mesh.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedEnvelope
open ObservedOnline
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Round an arbitrary observed value using the categories of a fixed grid. -/
def gridRoundValue
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) (x : ℝ) : ℝ :=
  ∑ i, G.price i * (if G.category i x then (1 : ℝ) else 0)

@[simp] theorem gridRoundValue_processing
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p) (job : Fin n) :
    gridRoundValue G (p job) = G.roundedProcessing job := rfl

/-- Pull a rounded decision rule back to actual observations. -/
def pullbackRoundedSelector
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (selector : ℝ → Bool) (x : ℝ) : Bool :=
  selector (gridRoundValue G x)

@[simp] theorem pullbackRoundedSelector_processing
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (selector : ℝ → Bool) (job : Fin n) :
    pullbackRoundedSelector G selector (p job) =
      selector (G.roundedProcessing job) := rfl

theorem empiricalSingleAverage_mono
    {n : ℕ} (hn : 0 < n) {f g : Fin n → ℝ}
    (hfg : ∀ i, f i ≤ g i) :
    empiricalSingleAverage f ≤ empiricalSingleAverage g := by
  unfold empiricalSingleAverage
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) ≤ n := by positivity
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => hfg i) hnR

theorem empiricalSingleAverage_le_add
    {n : ℕ} (hn : 0 < n) {f g : Fin n → ℝ} {c : ℝ}
    (hfg : ∀ i, f i ≤ g i + c) :
    empiricalSingleAverage f ≤ empiricalSingleAverage g + c := by
  unfold empiricalSingleAverage
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i, f i) ≤ (∑ i, g i) + n * c := by
    calc
      (∑ i, f i) ≤ ∑ i, (g i + c) :=
        Finset.sum_le_sum fun i _ => hfg i
      _ = (∑ i, g i) + n * c := by
        rw [Finset.sum_add_distrib]
        simp
  calc
    (∑ i, f i) / (n : ℝ) ≤ ((∑ i, g i) + n * c) / n :=
      div_le_div_of_nonneg_right hsum hnR.le
    _ = (∑ i, g i) / n + c := by field_simp [hnR.ne']

theorem empiricalProductPairAverage_mono
    {n : ℕ} (hn : 0 < n) {f g : Fin n → Fin n → ℝ}
    (hfg : ∀ i j, f i j ≤ g i j) :
    empiricalProductPairAverage f ≤ empiricalProductPairAverage g := by
  unfold empiricalProductPairAverage
  simp only [Fintype.card_fin]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hfg i j) (sq_nonneg _)

theorem empiricalProductPairAverage_le_add
    {n : ℕ} (hn : 0 < n) {f g : Fin n → Fin n → ℝ} {c : ℝ}
    (hfg : ∀ i j, f i j ≤ g i j + c) :
    empiricalProductPairAverage f ≤
    empiricalProductPairAverage g + c := by
  unfold empiricalProductPairAverage
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i, ∑ j, f i j) ≤
      (∑ i, ∑ j, g i j) + (n : ℝ) ^ 2 * c := by
    calc
      (∑ i, ∑ j, f i j) ≤ ∑ i, ∑ j, (g i j + c) :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hfg i j
      _ = (∑ i, ∑ j, g i j) + (n : ℝ) ^ 2 * c := by
        simp_rw [Finset.sum_add_distrib]
        simp
        ring
  calc
    (∑ i, ∑ j, f i j) / (n : ℝ) ^ 2 ≤
        ((∑ i, ∑ j, g i j) + (n : ℝ) ^ 2 * c) / n ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = (∑ i, ∑ j, g i j) / n ^ 2 + c := by
      field_simp [hnR.ne']

theorem min_upward_round_le_add_mesh
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (i j : Fin n) :
    min (G.roundedProcessing i) (G.roundedProcessing j) ≤
      min (p i) (p j) + G.mesh := by
  by_cases hij : p i ≤ p j
  · rw [min_eq_left hij]
    exact (min_le_left _ _).trans (G.roundedProcessing_le i)
  · have hji : p j ≤ p i := le_of_not_ge hij
    rw [min_eq_right hji]
    exact (min_le_right _ _).trans (G.roundedProcessing_le j)

/-- Upward rounding, with decisions pulled back through the grid, perturbs
all seven canonical moments by at most one mesh in the component metric. -/
theorem canonicalEmpiricalMoments_upward_round_componentClose
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (low medium high : ℝ → Bool) {scale : ℝ}
    (hscale : 1 ≤ scale) :
    (canonicalEmpiricalMoments p
      (pullbackRoundedSelector G low)
      (pullbackRoundedSelector G medium)
      (pullbackRoundedSelector G high)).ComponentClose
        (canonicalEmpiricalMoments G.roundedProcessing low medium high)
        scale G.mesh := by
  let weight : (ℝ → Bool) → Fin n → ℝ := fun selector job =>
    boolWeight (selector (G.roundedProcessing job))
  have hweight : ∀ selector job, 0 ≤ weight selector job ∧
      weight selector job ≤ 1 := by
    intro selector job
    exact boolWeight_mem_Icc _
  have hsingle : ∀ selector,
      |empiricalSingleAverage (fun job => p job * weight selector job) -
        empiricalSingleAverage (fun job =>
          G.roundedProcessing job * weight selector job)| ≤
        scale * G.mesh := by
    intro selector
    have hle := empiricalSingleAverage_mono hn (fun job =>
      mul_le_mul_of_nonneg_right (G.processing_le_roundedProcessing job)
        (hweight selector job).1)
    have hadd := empiricalSingleAverage_le_add hn (fun job => by
      have hround := G.roundedProcessing_le job
      have hw := (hweight selector job).2
      have hmesh0 := G.mesh_nonneg
      calc
        G.roundedProcessing job * weight selector job ≤
            (p job + G.mesh) * weight selector job :=
          mul_le_mul_of_nonneg_right hround (hweight selector job).1
        _ ≤ p job * weight selector job + G.mesh := by
          nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hmeshScale : G.mesh ≤ scale * G.mesh := by
      nlinarith [G.mesh_nonneg]
    linarith
  have hpair : ∀ selector,
      |empiricalProductPairAverage (fun i j =>
          min (p i) (p j) * weight selector i * weight selector j) -
        empiricalProductPairAverage (fun i j =>
          min (G.roundedProcessing i) (G.roundedProcessing j) *
            weight selector i * weight selector j)| ≤
        2 * scale * G.mesh := by
    intro selector
    have hle :
        empiricalProductPairAverage (fun i j =>
          min (p i) (p j) * weight selector i * weight selector j) ≤
        empiricalProductPairAverage (fun i j =>
          min (G.roundedProcessing i) (G.roundedProcessing j) *
            weight selector i * weight selector j) :=
      empiricalProductPairAverage_mono hn (fun i j => by
      have hmin := min_le_min (G.processing_le_roundedProcessing i)
        (G.processing_le_roundedProcessing j)
      have hprod0 : 0 ≤ weight selector i * weight selector j :=
        mul_nonneg (hweight selector i).1 (hweight selector j).1
      nlinarith)
    have hadd :
        empiricalProductPairAverage (fun i j =>
          min (G.roundedProcessing i) (G.roundedProcessing j) *
            weight selector i * weight selector j) ≤
        empiricalProductPairAverage (fun i j =>
          min (p i) (p j) * weight selector i * weight selector j) +
            G.mesh :=
      empiricalProductPairAverage_le_add hn (fun i j => by
      have hmin := min_upward_round_le_add_mesh G i j
      have hprod0 : 0 ≤ weight selector i * weight selector j :=
        mul_nonneg (hweight selector i).1 (hweight selector j).1
      have hprod1 : weight selector i * weight selector j ≤ 1 :=
        (mul_le_mul (hweight selector i).2 (hweight selector j).2
          (hweight selector j).1 (by norm_num)).trans_eq (by ring)
      have hmeshSlack : 0 ≤ G.mesh *
          (1 - weight selector i * weight selector j) :=
        mul_nonneg G.mesh_nonneg (sub_nonneg.mpr hprod1)
      calc
        min (G.roundedProcessing i) (G.roundedProcessing j) *
            weight selector i * weight selector j =
            min (G.roundedProcessing i) (G.roundedProcessing j) *
              (weight selector i * weight selector j) := by ring
        _ ≤ (min (p i) (p j) + G.mesh) *
              (weight selector i * weight selector j) :=
          mul_le_mul_of_nonneg_right hmin hprod0
        _ ≤ min (p i) (p j) * weight selector i * weight selector j +
              G.mesh := by
          nlinarith)
    have hdiff :
        empiricalProductPairAverage (fun i j =>
          min (p i) (p j) * weight selector i * weight selector j) -
        empiricalProductPairAverage (fun i j =>
          min (G.roundedProcessing i) (G.roundedProcessing j) *
            weight selector i * weight selector j) ≤ 0 := sub_nonpos.mpr hle
    rw [abs_of_nonpos hdiff]
    have hmeshScale : G.mesh ≤ 2 * scale * G.mesh := by
      nlinarith [G.mesh_nonneg]
    linarith
  constructor
  · simpa [canonicalEmpiricalMoments, weight] using G.mesh_nonneg
  · simpa [canonicalEmpiricalMoments, weight] using hsingle low
  · simpa [canonicalEmpiricalMoments, weight] using hsingle medium
  · simpa [canonicalEmpiricalMoments, weight] using G.mesh_nonneg
  · simpa [canonicalEmpiricalMoments, weight, boolWeight] using
      hsingle (fun _ => true)
  · simpa [canonicalEmpiricalMoments, weight] using hpair medium
  · simpa [canonicalEmpiricalMoments, weight] using hpair high

/-! ## A legal upper policy on the original instance -/

/-- The canonical rounded template can be executed on the actual processing
times by pulling its Boolean decisions back through `gridRoundValue`.  Its
expected actual cost is the benchmark plus an explicit finite-kernel term and
one mesh-stability term. -/
theorem exists_actualCanonicalPlacedRunCost_le_benchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    {scale : ℝ} (hscaleOne : 1 ≤ scale)
    (hpScale : ∀ job, p job ≤ scale)
    (hroundedScale : ∀ job, G.roundedProcessing job ≤ scale) :
    ∃ q : ℕ, q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) p
        (pullbackRoundedSelector G (benchmarkLowSelector B))
        (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
          (n : ℝ) ^ 2 ≤
        B.value + (17 + 63 * scale) / n +
          12 * (scale + 1) * G.mesh := by
  let lowR := benchmarkLowSelector B
  let mediumR := benchmarkMediumSelector B
  let highR := canonicalHigh lowR mediumR
  let lowA := pullbackRoundedSelector G lowR
  let mediumA := pullbackRoundedSelector G mediumR
  let highA := canonicalHigh lowA mediumA
  have hhigh : pullbackRoundedSelector G highR = highA := by
    funext x
    rfl
  obtain ⟨q, hq, hrounded⟩ :=
    exists_canonicalPlacedRunCost_le_benchmark_all_regimes
      hn B hprice hroundedScale
  refine ⟨q, hq, ?_⟩
  have hroundedCost :
      canonicalPlacedRunCost (q := q) G.roundedProcessing lowR mediumR =
        canonicalKernelCost q G.roundedProcessing lowR mediumR highR := by
    funext σ
    exact canonicalPlacedRunCost_eq_kernel hq G.roundedProcessing lowR mediumR
      (benchmarkSelectors_disjoint_of_injective B hprice)
      (fun job hzero => benchmarkLowSelector_zero_of_rounded B hzero) σ
  rw [hroundedCost] at hrounded
  have hdisjointA : ∀ x, lowA x = true → mediumA x = false := by
    intro x hlow
    exact benchmarkSelectors_disjoint_of_injective B hprice
      (gridRoundValue G x) hlow
  have hzeroA : ∀ job, p job = 0 → lowA (p job) = true := by
    intro job hzero
    dsimp [lowA, lowR, pullbackRoundedSelector]
    rw [G.roundedProcessing_eq_zero_of_eq_zero hzero]
    exact benchmarkLowSelector_zero B
  have hactualCost :
      canonicalPlacedRunCost (q := q) p lowA mediumA =
        canonicalKernelCost q p lowA mediumA highA := by
    funext σ
    exact canonicalPlacedRunCost_eq_kernel hq p lowA mediumA
      hdisjointA hzeroA σ
  change uniformAverage (canonicalPlacedRunCost (q := q) p lowA mediumA) /
      (n : ℝ) ^ 2 ≤ _
  rw [hactualCost]
  have hactualKernel := canonicalKernelCost_fluid_normalized hn hq p
    lowA mediumA highA G.processing_nonneg hpScale
  have hroundedKernel := canonicalKernelCost_fluid_normalized hn hq
    G.roundedProcessing lowR mediumR highR
      G.roundedProcessing_nonneg hroundedScale
  have hcloseRaw := canonicalEmpiricalMoments_upward_round_componentClose
    (show 0 < n by omega) G lowR mediumR highR hscaleOne
  have hclose :
      (canonicalEmpiricalMoments p lowA mediumA highA).ComponentClose
        (canonicalEmpiricalMoments G.roundedProcessing lowR mediumR highR)
        scale G.mesh := by
    simpa [lowA, mediumA, highA, lowR, mediumR, highR,
      pullbackRoundedSelector, canonicalHigh] using hcloseRaw
  have hscale0 : 0 ≤ scale := le_trans (by norm_num) hscaleOne
  have hmesh0 : 0 ≤ G.mesh := G.mesh_nonneg
  have hboxA := canonicalEmpiricalMoments_inBox (show 0 < n by omega) p
    lowA mediumA highA G.processing_nonneg hpScale
  have hboxR := canonicalEmpiricalMoments_inBox (show 0 < n by omega)
    G.roundedProcessing lowR mediumR highR
      G.roundedProcessing_nonneg hroundedScale
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) / n := by positivity
  have hq1 : (q : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    simpa using (show (q : ℝ) ≤ n by exact_mod_cast hq)
  have hstable := canonicalFluidCost_stable hscale0 hmesh0 hq0 hq1
    hboxA hboxR hclose
  have hAupper := (abs_le.mp hactualKernel).2
  have hRlower := (abs_le.mp hroundedKernel).1
  have hstableUpper := (abs_le.mp hstable).2
  have herr : (7 + 27 * scale) / (n : ℝ) +
      2 * ((5 + 18 * scale) / n) = (17 + 63 * scale) / n := by
    ring
  linarith

/-- Concrete uniform-grid actual-processing upper bound. -/
theorem exists_boundedUniform_actualCanonicalPlacedRunCost_le_benchmark
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (B : BenchmarkData p (boundedUniformRoundedGrid hK hL p hp0 hpL)) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let scale := max 1 (L + L / K)
    ∃ q : ℕ, q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) p
        (pullbackRoundedSelector G (benchmarkLowSelector B))
        (pullbackRoundedSelector G (benchmarkMediumSelector B))) /
          (n : ℝ) ^ 2 ≤
        B.value + (17 + 63 * scale) / n +
          12 * (scale + 1) * (L / K) := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  let scale : ℝ := max 1 (L + L / K)
  have hscaleOne : 1 ≤ scale := le_max_left _ _
  have hLscale : L ≤ scale := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    have hmesh0 : 0 ≤ L / (K : ℝ) := (div_pos hL hKR).le
    exact le_trans (by linarith) (le_max_right _ _)
  have hpScale : ∀ job, p job ≤ scale := fun job =>
    (hpL job).trans hLscale
  have hroundedScale : ∀ job, G.roundedProcessing job ≤ scale := by
    intro job
    exact (boundedUniformRoundedGrid_roundedProcessing_le
      hK hL p hp0 hpL job).trans (le_max_right _ _)
  simpa [G, scale, boundedUniformRoundedGrid_mesh] using
    exists_actualCanonicalPlacedRunCost_le_benchmark hn B
      (by
        have hKR : (0 : ℝ) < K := by exact_mod_cast hK
        exact uniformGridPrice_injective (div_pos hL hKR))
      hscaleOne hpScale hroundedScale

end

end RandomizedOptional
end SchedulingPaper
