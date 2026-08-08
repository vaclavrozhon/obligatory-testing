import SchedulingPaper.RandomizedOptionalRoundedAnnouncedLower
import Mathlib.Tactic

/-!
# A concrete zero-preserving uniform grid on a bounded interval
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace AnnouncedRoundedLower

open ObservedEnvelope

noncomputable section
attribute [local instance] Classical.propDecidable

def uniformGridPrice {K : ℕ} (mesh : ℝ) (i : Fin K) : ℝ :=
  (i.val + 1) * mesh

def IsUniformGridCategory {K : ℕ} (mesh x : ℝ) (i : Fin K) : Prop :=
  0 < x ∧ x ≤ uniformGridPrice mesh i ∧
    ∀ m : ℕ, m < i.val → (m + 1) * mesh < x

def uniformGridCategory {K : ℕ} (mesh : ℝ) (i : Fin K) (x : ℝ) : Bool :=
  decide (IsUniformGridCategory mesh x i)

theorem uniformGridPrice_pos {K : ℕ} {mesh : ℝ} (hmesh : 0 < mesh)
    (i : Fin K) : 0 < uniformGridPrice mesh i := by
  unfold uniformGridPrice
  positivity

theorem uniformGridPrice_nonneg {K : ℕ} {mesh : ℝ} (hmesh : 0 ≤ mesh)
    (i : Fin K) : 0 ≤ uniformGridPrice mesh i := by
  unfold uniformGridPrice
  positivity

/-- The least grid endpoint above `x` exists whenever `x` is below the last
endpoint. -/
theorem exists_unique_uniformGridCategory
    {K : ℕ} (hK : 0 < K) {mesh x : ℝ} (hmesh : 0 < mesh)
    (hx : 0 < x) (hupper : x ≤ K * mesh) :
    ∃! i : Fin K, uniformGridCategory mesh i x = true := by
  have hex : ∃ m : ℕ, m < K ∧ x ≤ (m + 1) * mesh := by
    refine ⟨K - 1, by omega, ?_⟩
    have hKid : K - 1 + 1 = K := by omega
    have hcast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
      exact_mod_cast hKid
    rw [hcast]
    exact hupper
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  have hbefore : ∀ l : ℕ, l < m → (l + 1) * mesh < x := by
    intro l hl
    have hlK : l < K := lt_trans hl hm.1
    by_contra hnot
    have hxl : x ≤ (l + 1) * mesh := le_of_not_gt hnot
    have hmin : m ≤ l := Nat.find_min' hex ⟨hlK, hxl⟩
    omega
  let i : Fin K := ⟨m, hm.1⟩
  have hi : uniformGridCategory mesh i x = true := by
    simp only [uniformGridCategory, decide_eq_true_eq]
    refine ⟨hx, ?_, ?_⟩
    · simpa [uniformGridPrice, i] using hm.2
    · intro l hl
      exact hbefore l (by simpa [i] using hl)
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hiProp : IsUniformGridCategory mesh x i := by
    simpa [uniformGridCategory] using hi
  have hjProp : IsUniformGridCategory mesh x j := by
    simpa [uniformGridCategory] using hj
  apply Fin.ext
  change j.val = m
  apply Nat.le_antisymm
  · by_contra hnot
    have hilt : m < j.val := Nat.lt_of_not_ge hnot
    have hprev := hjProp.2.2 m hilt
    have hiupper := hiProp.2.1
    change x ≤ (m + 1) * mesh at hiupper
    linarith
  · apply Nat.find_min' hex
    exact ⟨j.isLt, by simpa [uniformGridPrice] using hjProp.2.1⟩

theorem uniformGridCategory_upper
    {K : ℕ} {mesh x : ℝ} (hmesh : 0 < mesh) {i : Fin K}
    (hi : uniformGridCategory mesh i x = true) :
    x ≤ uniformGridPrice mesh i ∧ uniformGridPrice mesh i ≤ x + mesh := by
  have hip : IsUniformGridCategory mesh x i := by
    simpa [uniformGridCategory] using hi
  refine ⟨hip.2.1, ?_⟩
  by_cases hi0 : i.val = 0
  · unfold uniformGridPrice
    rw [hi0]
    norm_num
    linarith [hip.1]
  · have him1 : i.val - 1 < i.val := by omega
    have hprev := hip.2.2 (i.val - 1) him1
    have hnat : (i.val - 1 : ℕ) + 1 = i.val := by omega
    have hprev' : (i.val : ℝ) * mesh < x := by
      have hcast : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hnat
      rw [hcast] at hprev
      exact hprev
    unfold uniformGridPrice
    push_cast
    nlinarith

/-- A uniform grid of mesh `mesh` for a population bounded by `K*mesh`. -/
def uniformRoundedGrid
    {n K : ℕ} (hK : 0 < K) (p : Fin n → ℝ) {mesh : ℝ}
    (hmesh : 0 < mesh) (hp0 : ∀ job, 0 ≤ p job)
    (hpUpper : ∀ job, p job ≤ K * mesh) :
    RoundedPositiveGrid (Fin K) p where
  price := uniformGridPrice mesh
  category := uniformGridCategory mesh
  mesh := mesh
  processing_nonneg := hp0
  price_nonneg := fun i => (uniformGridPrice_pos hmesh i).le
  mesh_nonneg := hmesh.le
  category_positive := by
    intro i job hi
    have hip : IsUniformGridCategory mesh (p job) i := by
      simpa [uniformGridCategory] using hi
    exact hip.1
  category_upper := by
    intro i job hi
    exact uniformGridCategory_upper hmesh hi
  category_unique := by
    intro job hp
    exact exists_unique_uniformGridCategory hK hmesh hp (hpUpper job)

/-- The canonical uniform upward grid on `[0,L]`, with mesh `L/K`. -/
def boundedUniformRoundedGrid
    {n K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) :
    RoundedPositiveGrid (Fin K) p := by
  let mesh : ℝ := L / K
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmesh : 0 < mesh := div_pos hL hKR
  apply uniformRoundedGrid hK p hmesh hp0
  intro job
  dsimp [mesh]
  rw [mul_div_cancel₀ L hKR.ne']
  exact hpL job

@[simp] theorem boundedUniformRoundedGrid_mesh
    {n K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) :
    (boundedUniformRoundedGrid hK hL p hp0 hpL).mesh = L / K := rfl

@[simp] theorem boundedUniformRoundedGrid_price
    {n K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) (i : Fin K) :
    (boundedUniformRoundedGrid hK hL p hp0 hpL).price i =
      uniformGridPrice (L / K) i := rfl

/-- A rounded value on the bounded uniform grid is at most one mesh above
the original global bound.  This deliberately avoids any endpoint
arithmetic in downstream concentration theorems. -/
theorem boundedUniformRoundedGrid_roundedProcessing_le
    {n K : ℕ} (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) (job : Fin n) :
    (boundedUniformRoundedGrid hK hL p hp0 hpL).roundedProcessing job ≤
      L + L / K := by
  have hround :=
    (boundedUniformRoundedGrid hK hL p hp0 hpL).roundedProcessing_le job
  rw [boundedUniformRoundedGrid_mesh] at hround
  linarith [hpL job]

/-- Closed announced lower bound for an arbitrary positive-mean population
in `[0,L]`.  The theorem constructs both the uniform upward grid and its
empirical optimum internally; the only remaining choices are the explicit
checkpoint parameters. -/
theorem exists_boundedUniformBenchmark_uniformAverage_lower
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K) {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L) (hmean : 0 < Randomized.populationMean p)
    (policy : ObservedTrace.CompletePolicy p) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    let scale := L + L / K
    let threshold := e + martingaleStep +
      (r + 2 * suffixStep / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2)
    ∃ B : BenchmarkData p G,
      B.value - (scale * γ + L / K) -
          (K + 1) * γ * (1 + B.mean) -
          (1 + scale) * ((K + 2) * base) ≤
        Randomized.uniformAverage (normalizedCost p policy) := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  let scale : ℝ := L + L / K
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmesh : 0 < L / (K : ℝ) := div_pos hL hKR
  have hscale : 0 < scale := by dsimp [scale]; linarith
  have hroundedScale : ∀ job, G.roundedProcessing job ≤ scale := by
    intro job
    exact boundedUniformRoundedGrid_roundedProcessing_le
      hK hL p hp0 hpL job
  have hprice : ∀ i, 0 < G.price i := by
    intro i
    exact uniformGridPrice_pos hmesh i
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hroundedMean : 0 < Randomized.populationMean G.roundedProcessing :=
    lt_of_lt_of_le hmean (G.populationMean_le_roundedProcessing hn0)
  have hbound := exists_empiricalBenchmark_uniformAverage_lower_scaled
    hn p hscale policy G hroundedScale hprice hroundedMean cutoff
      hMartingaleStep hSuffixStep he hr
  simpa [G, scale] using hbound

@[simp] theorem uniformRoundedGrid_price
    {n K : ℕ} (hK : 0 < K) (p : Fin n → ℝ) {mesh : ℝ}
    (hmesh : 0 < mesh) (hp0 : ∀ job, 0 ≤ p job)
    (hpUpper : ∀ job, p job ≤ K * mesh) (i : Fin K) :
    (uniformRoundedGrid hK p hmesh hp0 hpUpper).price i =
      uniformGridPrice mesh i := rfl

@[simp] theorem uniformRoundedGrid_mesh
    {n K : ℕ} (hK : 0 < K) (p : Fin n → ℝ) {mesh : ℝ}
    (hmesh : 0 < mesh) (hp0 : ∀ job, 0 ≤ p job)
    (hpUpper : ∀ job, p job ≤ K * mesh) :
    (uniformRoundedGrid hK p hmesh hp0 hpUpper).mesh = mesh := rfl

end

end AnnouncedRoundedLower
end RandomizedOptional
end SchedulingPaper
