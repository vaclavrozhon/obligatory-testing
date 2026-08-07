import SchedulingPaper.RandomizedHypergeometric
import SchedulingPaper.RandomizedOptionalFluid
import Mathlib.Tactic

/-!
# Optional testing: finite histogram and kernel stability

The finite expected cost of a fixed canonical template is a sum of one-job
and two-distinct-job kernels.  This file proves the distributional estimates
used to compare those kernels with their empirical-product fluid limits.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

def finiteL1 {ι : Type*} [Fintype ι] (μ ν : ι → ℝ) : ℝ :=
  ∑ i, |μ i - ν i|

def finiteExpectation {ι : Type*} [Fintype ι]
    (μ f : ι → ℝ) : ℝ :=
  ∑ i, μ i * f i

def finiteProductExpectation {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (g : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, μ i * μ j * g i j

theorem finiteExpectation_sub
    {ι : Type*} [Fintype ι] (μ ν f : ι → ℝ) :
    finiteExpectation μ f - finiteExpectation ν f =
      ∑ i, (μ i - ν i) * f i := by
  unfold finiteExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A bounded one-draw kernel is Lipschitz in histogram L1 distance. -/
theorem finiteExpectation_lipschitz
    {ι : Type*} [Fintype ι]
    {μ ν f : ι → ℝ} {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    |finiteExpectation μ f - finiteExpectation ν f| ≤
      B * finiteL1 μ ν := by
  rw [finiteExpectation_sub]
  calc
    |∑ i, (μ i - ν i) * f i| ≤
        ∑ i, |(μ i - ν i) * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * |μ i - ν i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)
    _ = B * finiteL1 μ ν := by
      unfold finiteL1
      rw [Finset.mul_sum]

theorem abs_finiteExpectation_le
    {ι : Type*} [Fintype ι]
    {μ f : ι → ℝ} {B : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (hf : ∀ i, |f i| ≤ B) :
    |finiteExpectation μ f| ≤ B := by
  calc
    |finiteExpectation μ f| ≤ ∑ i, |μ i * f i| := by
      unfold finiteExpectation
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, μ i * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hμ i)]
      exact mul_le_mul_of_nonneg_left (hf i) (hμ i)
    _ = B := by
      rw [← Finset.sum_mul, hmass, one_mul]

theorem finiteExpectation_nonneg
    {ι : Type*} [Fintype ι]
    {μ f : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finiteExpectation μ f := by
  unfold finiteExpectation
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (hf i)

theorem finiteExpectation_le_bound
    {ι : Type*} [Fintype ι]
    {μ f : ι → ℝ} {B : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (hf : ∀ i, f i ≤ B) :
    finiteExpectation μ f ≤ B := by
  unfold finiteExpectation
  calc
    (∑ i, μ i * f i) ≤ ∑ i, μ i * B :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hμ i)
    _ = B := by rw [← Finset.sum_mul, hmass, one_mul]

theorem finiteProductExpectation_nonneg
    {ι : Type*} [Fintype ι]
    {μ : ι → ℝ} {g : ι → ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hg : ∀ i j, 0 ≤ g i j) :
    0 ≤ finiteProductExpectation μ g := by
  unfold finiteProductExpectation
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hμ i) (hμ j)) (hg i j)

theorem finiteProductExpectation_le_bound
    {ι : Type*} [Fintype ι]
    {μ : ι → ℝ} {g : ι → ι → ℝ} {B : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hmass : ∑ i, μ i = 1)
    (hg : ∀ i j, g i j ≤ B) :
    finiteProductExpectation μ g ≤ B := by
  unfold finiteProductExpectation
  calc
    (∑ i, ∑ j, μ i * μ j * g i j) ≤
        ∑ i, ∑ j, μ i * μ j * B := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hg i j) (mul_nonneg (hμ i) (hμ j))
    _ = B := by
      calc
        (∑ i, ∑ j, μ i * μ j * B) =
            (∑ i, ∑ j, μ i * μ j) * B := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_mul]
        _ = (∑ i, μ i) * (∑ j, μ j) * B := by
          rw [Fintype.sum_mul_sum]
        _ = B := by rw [hmass]; ring

theorem finiteProductExpectation_telescope
    {ι : Type*} [Fintype ι]
    (μ ν : ι → ℝ) (g : ι → ι → ℝ) :
    finiteProductExpectation μ g - finiteProductExpectation ν g =
      (finiteProductExpectation μ g -
        ∑ i, ∑ j, ν i * μ j * g i j) +
      ((∑ i, ∑ j, ν i * μ j * g i j) -
        finiteProductExpectation ν g) := by
  ring

/-- A bounded two-draw kernel is `2B`-Lipschitz in histogram L1 distance. -/
theorem finiteProductExpectation_lipschitz
    {ι : Type*} [Fintype ι]
    {μ ν : ι → ℝ} {g : ι → ι → ℝ} {B : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμmass : ∑ i, μ i = 1) (hνmass : ∑ i, ν i = 1)
    (hg : ∀ i j, |g i j| ≤ B) :
    |finiteProductExpectation μ g - finiteProductExpectation ν g| ≤
      2 * B * finiteL1 μ ν := by
  let rowμ : ι → ℝ := fun i => finiteExpectation μ (g i)
  let colν : ι → ℝ := fun j => finiteExpectation ν (fun i => g i j)
  have hrow : ∀ i, |rowμ i| ≤ B := by
    intro i
    exact abs_finiteExpectation_le hμ hμmass (hg i)
  have hcol : ∀ j, |colν j| ≤ B := by
    intro j
    exact abs_finiteExpectation_le hν hνmass (fun i => hg i j)
  have hfirst :
      |finiteProductExpectation μ g -
          ∑ i, ∑ j, ν i * μ j * g i j| ≤ B * finiteL1 μ ν := by
    have heq :
        finiteProductExpectation μ g -
            ∑ i, ∑ j, ν i * μ j * g i j =
          finiteExpectation μ rowμ - finiteExpectation ν rowμ := by
      congr 1
      · unfold finiteProductExpectation finiteExpectation rowμ
        apply Finset.sum_congr rfl
        intro i _
        unfold finiteExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · unfold finiteExpectation rowμ
        apply Finset.sum_congr rfl
        intro i _
        unfold finiteExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    rw [heq]
    exact finiteExpectation_lipschitz hrow
  have hsecond :
      |(∑ i, ∑ j, ν i * μ j * g i j) -
          finiteProductExpectation ν g| ≤ B * finiteL1 μ ν := by
    have heq :
        (∑ i, ∑ j, ν i * μ j * g i j) -
            finiteProductExpectation ν g =
          finiteExpectation μ colν - finiteExpectation ν colν := by
      congr 1
      · unfold finiteExpectation colν
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        unfold finiteExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · unfold finiteProductExpectation finiteExpectation colν
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        unfold finiteExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    rw [heq]
    exact finiteExpectation_lipschitz hcol
  rw [finiteProductExpectation_telescope]
  calc
    |(finiteProductExpectation μ g - ∑ i, ∑ j, ν i * μ j * g i j) +
        ((∑ i, ∑ j, ν i * μ j * g i j) -
          finiteProductExpectation ν g)| ≤
        |finiteProductExpectation μ g - ∑ i, ∑ j, ν i * μ j * g i j| +
          |(∑ i, ∑ j, ν i * μ j * g i j) -
            finiteProductExpectation ν g| := abs_add_le _ _
    _ ≤ B * finiteL1 μ ν + B * finiteL1 μ ν :=
      add_le_add hfirst hsecond
    _ = 2 * B * finiteL1 μ ν := by ring

/-! ## Without-replacement versus empirical-product pairs -/

theorem abs_uniformAverage_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f : Ω → ℝ} {B : ℝ} (hf : ∀ ω, |f ω| ≤ B) :
    |uniformAverage f| ≤ B := by
  rw [abs_le]
  constructor
  · have h := uniformAverage_mono
      (f := fun _ : Ω => -B) (g := f)
      (fun ω => (abs_le.mp (hf ω)).1)
    simpa using h
  · have h := uniformAverage_mono
      (f := f) (g := fun _ : Ω => B)
      (fun ω => (abs_le.mp (hf ω)).2)
    simpa using h

theorem abs_fintype_sum_le_card_mul
    {ι : Type*} [Fintype ι]
    {f : ι → ℝ} {B : ℝ} (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ Fintype.card ι * B := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => hf i
    _ = Fintype.card ι * B := by simp

theorem orderedDistinct_add_diagonal
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α → ℝ) :
    (∑ z : OrderedDistinct α, g z.val.1 z.val.2) +
        ∑ i, g i i =
      ∑ i, ∑ j, g i j := by
  have hoff :
      (∑ z : OrderedDistinct α, g z.val.1 z.val.2) =
        ∑ z ∈ (Finset.univ : Finset α).offDiag, g z.1 z.2 := by
    symm
    apply Finset.sum_subtype
    intro z
    simp [Finset.mem_offDiag]
  have hdiag :
      (∑ z ∈ (Finset.univ : Finset α).diag, g z.1 z.2) =
        ∑ i, g i i := by
    rw [Finset.sum_diag]
  rw [hoff, ← hdiag, add_comm]
  rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ)]
  rw [Finset.diag_union_offDiag, Finset.sum_product]

def empiricalProductPairAverage
    {α : Type*} [Fintype α] (g : α → α → ℝ) : ℝ :=
  (∑ i, ∑ j, g i j) / (Fintype.card α : ℝ) ^ 2

/-- Two distinct positions sampled without replacement differ from the
empirical product law by at most `2B/N` for every kernel bounded by `B`.
This is the uniform `O_L(1/n)` primitive behind equation (27a). -/
theorem uniformPermutationPair_empiricalProduct_error
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {i j : α} (hij : i ≠ j)
    (g : α → α → ℝ) {B : ℝ}
    (hg : ∀ x y, |g x y| ≤ B) :
    |uniformAverage (fun σ : Equiv.Perm α => g (σ i) (σ j)) -
        empiricalProductPairAverage g| ≤
      2 * B / Fintype.card α := by
  let N : ℝ := Fintype.card α
  let off : ℝ := ∑ z : OrderedDistinct α, g z.val.1 z.val.2
  let diag : ℝ := ∑ x, g x x
  let avg : ℝ := uniformAverage
    (fun σ : Equiv.Perm α => g (σ i) (σ j))
  have hNnat : 1 < Fintype.card α := by
    exact Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hN1 : 0 < N - 1 := by
    have hcast : (1 : ℝ) < Fintype.card α := by
      exact_mod_cast hNnat
    dsimp [N]
    linarith
  have havg : avg = off / (N * (N - 1)) := by
    dsimp [avg, off, N]
    rw [uniformAverage_perm_apply₂ g hij]
    rw [orderedDistinct_card]
    rw [Nat.cast_mul, Nat.cast_sub hNnat.le]
    norm_num
  have havgAbs : |avg| ≤ B := by
    apply abs_uniformAverage_le
    intro σ
    exact hg (σ i) (σ j)
  have hdiagAbs : |diag| ≤ N * B := by
    dsimp [diag, N]
    exact abs_fintype_sum_le_card_mul (fun x => hg x x)
  have htotal :
      empiricalProductPairAverage g = (off + diag) / N ^ 2 := by
    unfold empiricalProductPairAverage
    rw [← orderedDistinct_add_diagonal g]
  have hidentity :
      avg - empiricalProductPairAverage g =
        avg / N - diag / N ^ 2 := by
    rw [havg, htotal]
    field_simp [hN.ne', hN1.ne']
    ring
  rw [hidentity]
  calc
    |avg / N - diag / N ^ 2| ≤ |avg / N| + |diag / N ^ 2| :=
      abs_sub _ _
    _ = |avg| / N + |diag| / N ^ 2 := by
      rw [abs_div, abs_div, abs_of_pos hN, abs_of_pos (sq_pos_of_pos hN)]
    _ ≤ B / N + (N * B) / N ^ 2 := by
      exact add_le_add
        (div_le_div_of_nonneg_right havgAbs hN.le)
        (div_le_div_of_nonneg_right hdiagAbs (sq_nonneg N))
    _ = 2 * B / N := by
      field_simp [hN.ne']
      ring
    _ = 2 * B / Fintype.card α := by rfl

/-- Exact finite-population correction shared by all three tested/blind pair
coefficients. -/
theorem tested_pair_coefficient_identities
    {n r : ℝ} (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) :
    (r / n) ^ 2 - r * (r - 1) / (n * (n - 1)) =
        r * (n - r) / (n ^ 2 * (n - 1)) ∧
    r * (n - r) / (n * (n - 1)) - (r / n) * (1 - r / n) =
        r * (n - r) / (n ^ 2 * (n - 1)) ∧
    (1 - r / n) ^ 2 -
        (n - r) * (n - r - 1) / (n * (n - 1)) =
      r * (n - r) / (n ^ 2 * (n - 1)) := by
  constructor
  · field_simp [hn, hn1]
    ring
  · constructor <;> field_simp [hn, hn1] <;> ring

/-- The three pair coefficients in (27b) differ from their fluid values by
at most `1/(n-1)` (the draft uses the looser constant `2/(n-1)`). -/
theorem tested_pair_coefficients_close
    {n r : ℝ} (hn : 2 ≤ n) (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    |r * (r - 1) / (n * (n - 1)) - (r / n) ^ 2| ≤ 1 / (n - 1) ∧
    |r * (n - r) / (n * (n - 1)) -
        (r / n) * (1 - r / n)| ≤ 1 / (n - 1) ∧
    |(n - r) * (n - r - 1) / (n * (n - 1)) -
        (1 - r / n) ^ 2| ≤ 1 / (n - 1) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn10 : 0 < n - 1 := by linarith
  have hnr0 : 0 ≤ n - r := sub_nonneg.mpr hrn
  have hprod : r * (n - r) ≤ n ^ 2 := by
    have hleft := mul_le_mul hrn
      (show n - r ≤ n by linarith) hnr0 hn0.le
    nlinarith
  have hcorr0 : 0 ≤ r * (n - r) / (n ^ 2 * (n - 1)) := by positivity
  have hcorr : r * (n - r) / (n ^ 2 * (n - 1)) ≤ 1 / (n - 1) := by
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hn0) hn10) hn10).2
    nlinarith
  obtain ⟨htested, hmixed, hblind⟩ :=
    tested_pair_coefficient_identities hn0.ne' hn10.ne'
  constructor
  · rw [abs_sub_comm, htested, abs_of_nonneg hcorr0]
    exact hcorr
  constructor
  · rw [hmixed, abs_of_nonneg hcorr0]
    exact hcorr
  · rw [abs_sub_comm, hblind, abs_of_nonneg hcorr0]
    exact hcorr

/-! ## Fixed grid-template moments -/

/-- A distribution-independent canonical grid template.  The three selector
functions are allowed to be fractional so boundary atoms are included. -/
structure FluidTemplate (ι : Type*) where
  low : ι → ℝ
  medium : ι → ℝ
  high : ι → ℝ

def templateMoments {ι : Type*} [Fintype ι]
    (D p : ι → ℝ) (T : FluidTemplate ι) : FluidMoments where
  lowMass := finiteExpectation D T.low
  lowMoment := finiteExpectation D (fun i => p i * T.low i)
  mediumMoment := finiteExpectation D (fun i => p i * T.medium i)
  highMass := finiteExpectation D T.high
  mean := finiteExpectation D p
  mediumMinPair := finiteProductExpectation D fun i j =>
    min (p i) (p j) * T.medium i * T.medium j
  highMinPair := finiteProductExpectation D fun i j =>
    min (p i) (p j) * T.high i * T.high j

/-- Every scalar and pair moment of a fixed template is uniformly Lipschitz
in histogram L1 distance, independently of the number of grid cells. -/
theorem templateMoments_lipschitz_components
    {ι : Type*} [Fintype ι]
    {D E p : ι → ℝ} {T : FluidTemplate ι} {L : ℝ}
    (hD : ∀ i, 0 ≤ D i) (hE : ∀ i, 0 ≤ E i)
    (hDmass : ∑ i, D i = 1) (hEmass : ∑ i, E i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hlow0 : ∀ i, 0 ≤ T.low i) (hlow1 : ∀ i, T.low i ≤ 1)
    (hmedium0 : ∀ i, 0 ≤ T.medium i)
    (hmedium1 : ∀ i, T.medium i ≤ 1)
    (hhigh0 : ∀ i, 0 ≤ T.high i) (hhigh1 : ∀ i, T.high i ≤ 1) :
    let M := templateMoments D p T
    let N := templateMoments E p T
    let δ := finiteL1 D E
    |M.lowMass - N.lowMass| ≤ δ ∧
    |M.lowMoment - N.lowMoment| ≤ L * δ ∧
    |M.mediumMoment - N.mediumMoment| ≤ L * δ ∧
    |M.highMass - N.highMass| ≤ δ ∧
    |M.mean - N.mean| ≤ L * δ ∧
    |M.mediumMinPair - N.mediumMinPair| ≤ 2 * L * δ ∧
    |M.highMinPair - N.highMinPair| ≤ 2 * L * δ := by
  dsimp only
  have hExists : ∃ i, D i ≠ 0 := by
    by_contra hnot
    have hforall : ∀ i, D i = 0 := by
      intro i
      by_contra hi
      exact hnot ⟨i, hi⟩
    have hzero : (∑ i, D i) = 0 := by simp [hforall]
    linarith
  let i₀ := hExists.choose
  have hL0 : 0 ≤ L := (hp0 i₀).trans (hpL i₀)
  have hlowAbs : ∀ i, |T.low i| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (hlow0 i)]
    exact hlow1 i
  have hhighAbs : ∀ i, |T.high i| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (hhigh0 i)]
    exact hhigh1 i
  have hlowMomentAbs : ∀ i, |p i * T.low i| ≤ L := by
    intro i
    rw [abs_of_nonneg (mul_nonneg (hp0 i) (hlow0 i))]
    calc
      p i * T.low i ≤ L * 1 :=
        mul_le_mul (hpL i) (hlow1 i) (hlow0 i) hL0
      _ = L := mul_one L
  have hmediumMomentAbs : ∀ i, |p i * T.medium i| ≤ L := by
    intro i
    rw [abs_of_nonneg (mul_nonneg (hp0 i) (hmedium0 i))]
    calc
      p i * T.medium i ≤ L * 1 :=
        mul_le_mul (hpL i) (hmedium1 i) (hmedium0 i) hL0
      _ = L := mul_one L
  have hmeanAbs : ∀ i, |p i| ≤ L := by
    intro i
    rw [abs_of_nonneg (hp0 i)]
    exact hpL i
  have hpairAbs (selector : ι → ℝ)
      (hs0 : ∀ i, 0 ≤ selector i) (hs1 : ∀ i, selector i ≤ 1) :
      ∀ i j, |min (p i) (p j) * selector i * selector j| ≤ L := by
    intro i j
    have hmin0 : 0 ≤ min (p i) (p j) :=
      le_min (hp0 i) (hp0 j)
    have hminL : min (p i) (p j) ≤ L :=
      (min_le_left _ _).trans (hpL i)
    have hsel0 : 0 ≤ selector i * selector j :=
      mul_nonneg (hs0 i) (hs0 j)
    have hsel1 : selector i * selector j ≤ 1 := by
      calc
        selector i * selector j ≤ 1 * 1 :=
          mul_le_mul (hs1 i) (hs1 j) (hs0 j) (by norm_num)
        _ = 1 := by norm_num
    rw [show min (p i) (p j) * selector i * selector j =
        min (p i) (p j) * (selector i * selector j) by ring,
      abs_of_nonneg (mul_nonneg hmin0 hsel0)]
    calc
      min (p i) (p j) * (selector i * selector j) ≤ L * 1 :=
        mul_le_mul hminL hsel1 hsel0 hL0
      _ = L := mul_one L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [templateMoments] using
      (finiteExpectation_lipschitz (μ := D) (ν := E) hlowAbs)
  · simpa [templateMoments] using
      (finiteExpectation_lipschitz (μ := D) (ν := E) hlowMomentAbs)
  · simpa [templateMoments] using
      (finiteExpectation_lipschitz (μ := D) (ν := E) hmediumMomentAbs)
  · simpa [templateMoments] using
      (finiteExpectation_lipschitz (μ := D) (ν := E) hhighAbs)
  · simpa [templateMoments] using
      (finiteExpectation_lipschitz (μ := D) (ν := E) hmeanAbs)
  · simpa [templateMoments] using
      (finiteProductExpectation_lipschitz hD hE hDmass hEmass
        (hpairAbs T.medium hmedium0 hmedium1))
  · simpa [templateMoments] using
      (finiteProductExpectation_lipschitz hD hE hDmass hEmass
        (hpairAbs T.high hhigh0 hhigh1))

structure FluidMoments.InBox (M : FluidMoments) (L : ℝ) : Prop where
  lowMass_nonneg : 0 ≤ M.lowMass
  lowMass_le_one : M.lowMass ≤ 1
  lowMoment_nonneg : 0 ≤ M.lowMoment
  lowMoment_le : M.lowMoment ≤ L
  mediumMoment_nonneg : 0 ≤ M.mediumMoment
  mediumMoment_le : M.mediumMoment ≤ L
  highMass_nonneg : 0 ≤ M.highMass
  highMass_le_one : M.highMass ≤ 1
  mean_nonneg : 0 ≤ M.mean
  mean_le : M.mean ≤ L
  mediumMinPair_nonneg : 0 ≤ M.mediumMinPair
  mediumMinPair_le : M.mediumMinPair ≤ L
  highMinPair_nonneg : 0 ≤ M.highMinPair
  highMinPair_le : M.highMinPair ≤ L

theorem templateMoments_inBox
    {ι : Type*} [Fintype ι]
    {D p : ι → ℝ} {T : FluidTemplate ι} {L : ℝ}
    (hD : ∀ i, 0 ≤ D i) (hDmass : ∑ i, D i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hlow0 : ∀ i, 0 ≤ T.low i) (hlow1 : ∀ i, T.low i ≤ 1)
    (hmedium0 : ∀ i, 0 ≤ T.medium i)
    (hmedium1 : ∀ i, T.medium i ≤ 1)
    (hhigh0 : ∀ i, 0 ≤ T.high i) (hhigh1 : ∀ i, T.high i ≤ 1) :
    (templateMoments D p T).InBox L := by
  have hlowMoment0 : ∀ i, 0 ≤ p i * T.low i :=
    fun i => mul_nonneg (hp0 i) (hlow0 i)
  have hlowMomentL : ∀ i, p i * T.low i ≤ L := by
    intro i
    have hL0 : 0 ≤ L := (hp0 i).trans (hpL i)
    calc
      p i * T.low i ≤ L * 1 :=
        mul_le_mul (hpL i) (hlow1 i) (hlow0 i) hL0
      _ = L := mul_one L
  have hmediumMoment0 : ∀ i, 0 ≤ p i * T.medium i :=
    fun i => mul_nonneg (hp0 i) (hmedium0 i)
  have hmediumMomentL : ∀ i, p i * T.medium i ≤ L := by
    intro i
    have hL0 : 0 ≤ L := (hp0 i).trans (hpL i)
    calc
      p i * T.medium i ≤ L * 1 :=
        mul_le_mul (hpL i) (hmedium1 i) (hmedium0 i) hL0
      _ = L := mul_one L
  have hpairBounds (selector : ι → ℝ)
      (hs0 : ∀ i, 0 ≤ selector i) (hs1 : ∀ i, selector i ≤ 1) :
      (∀ i j, 0 ≤ min (p i) (p j) * selector i * selector j) ∧
      (∀ i j, min (p i) (p j) * selector i * selector j ≤ L) := by
    constructor
    · intro i j
      exact mul_nonneg
        (mul_nonneg (le_min (hp0 i) (hp0 j)) (hs0 i)) (hs0 j)
    · intro i j
      have hL0 : 0 ≤ L := (hp0 i).trans (hpL i)
      have hminL : min (p i) (p j) ≤ L :=
        (min_le_left _ _).trans (hpL i)
      have hfirst0 : 0 ≤ min (p i) (p j) * selector i :=
        mul_nonneg (le_min (hp0 i) (hp0 j)) (hs0 i)
      calc
        min (p i) (p j) * selector i * selector j ≤
            L * 1 * 1 :=
          mul_le_mul
            (mul_le_mul hminL (hs1 i) (hs0 i) hL0)
            (hs1 j) (hs0 j) (mul_nonneg hL0 (by norm_num))
        _ = L := by ring
  have hmediumPair := hpairBounds T.medium hmedium0 hmedium1
  have hhighPair := hpairBounds T.high hhigh0 hhigh1
  constructor
  · exact finiteExpectation_nonneg hD hlow0
  · exact finiteExpectation_le_bound hD hDmass hlow1
  · exact finiteExpectation_nonneg hD hlowMoment0
  · exact finiteExpectation_le_bound hD hDmass hlowMomentL
  · exact finiteExpectation_nonneg hD hmediumMoment0
  · exact finiteExpectation_le_bound hD hDmass hmediumMomentL
  · exact finiteExpectation_nonneg hD hhigh0
  · exact finiteExpectation_le_bound hD hDmass hhigh1
  · exact finiteExpectation_nonneg hD hp0
  · exact finiteExpectation_le_bound hD hDmass hpL
  · exact finiteProductExpectation_nonneg hD hmediumPair.1
  · exact finiteProductExpectation_le_bound hD hDmass hmediumPair.2
  · exact finiteProductExpectation_nonneg hD hhighPair.1
  · exact finiteProductExpectation_le_bound hD hDmass hhighPair.2

/-! ## Stability of the quadratic template objective -/

theorem abs_mul_sub_mul_le
    {a b c d da db A B : ℝ}
    (hda : |a - c| ≤ da) (hdb : |b - d| ≤ db)
    (hb : |b| ≤ B) (hc : |c| ≤ A)
    (hda0 : 0 ≤ da) (hA0 : 0 ≤ A) :
    |a * b - c * d| ≤ da * B + A * db := by
  have hid : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hid]
  calc
    |(a - c) * b + c * (b - d)| ≤
        |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ da * B + A * db := by
      exact add_le_add
        (mul_le_mul hda hb (abs_nonneg _) hda0)
        (mul_le_mul hc hdb (abs_nonneg _) hA0)

structure FluidMoments.ComponentClose
    (M N : FluidMoments) (L δ : ℝ) : Prop where
  lowMass : |M.lowMass - N.lowMass| ≤ δ
  lowMoment : |M.lowMoment - N.lowMoment| ≤ L * δ
  mediumMoment : |M.mediumMoment - N.mediumMoment| ≤ L * δ
  highMass : |M.highMass - N.highMass| ≤ δ
  mean : |M.mean - N.mean| ≤ L * δ
  mediumMinPair :
    |M.mediumMinPair - N.mediumMinPair| ≤ 2 * L * δ
  highMinPair : |M.highMinPair - N.highMinPair| ≤ 2 * L * δ

theorem canonicalLinearCoeff_stable
    {M N : FluidMoments} {L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hM : M.InBox L) (hN : N.InBox L)
    (hclose : M.ComponentClose N L δ) :
    |canonicalLinearCoeff M - canonicalLinearCoeff N| ≤ 4 * L * δ := by
  have hhighShift :
      |(M.highMass - 1) - (N.highMass - 1)| ≤ δ := by
    simpa only [sub_sub_sub_cancel_right] using hclose.highMass
  have hhighAbs : |M.highMass - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hM.highMass_nonneg, hM.highMass_le_one]
  have hmeanAbs : |N.mean| ≤ L := by
    rw [abs_of_nonneg hN.mean_nonneg]
    exact hN.mean_le
  have hproduct :
      |M.mean * (M.highMass - 1) -
          N.mean * (N.highMass - 1)| ≤ 2 * L * δ := by
    have h := abs_mul_sub_mul_le hclose.mean hhighShift hhighAbs hmeanAbs
      (mul_nonneg hL hδ) hL
    nlinarith
  have hid :
      canonicalLinearCoeff M - canonicalLinearCoeff N =
        (M.lowMoment - N.lowMoment) +
        (M.mediumMoment - N.mediumMoment) +
        (M.mean * (M.highMass - 1) -
          N.mean * (N.highMass - 1)) := by
    unfold canonicalLinearCoeff
    ring
  rw [hid]
  have htri :
      |(M.lowMoment - N.lowMoment) +
          (M.mediumMoment - N.mediumMoment) +
          (M.mean * (M.highMass - 1) -
            N.mean * (N.highMass - 1))| ≤
        |M.lowMoment - N.lowMoment| +
          |M.mediumMoment - N.mediumMoment| +
          |M.mean * (M.highMass - 1) -
            N.mean * (N.highMass - 1)| := by
    have h₁ := abs_add_le
      (M.lowMoment - N.lowMoment) (M.mediumMoment - N.mediumMoment)
    have h₂ := abs_add_le
      ((M.lowMoment - N.lowMoment) + (M.mediumMoment - N.mediumMoment))
      (M.mean * (M.highMass - 1) - N.mean * (N.highMass - 1))
    linarith
  exact htri.trans (by nlinarith [hclose.lowMoment,
    hclose.mediumMoment, hproduct])

theorem canonicalQuadraticCoeff_stable
    {M N : FluidMoments} {L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hM : M.InBox L) (hN : N.InBox L)
    (hclose : M.ComponentClose N L δ) :
    |canonicalQuadraticCoeff M - canonicalQuadraticCoeff N| ≤
      (1 + 13 * L) / 2 * δ := by
  have hlowFactor : |1 + M.lowMoment| ≤ 1 + L := by
    rw [abs_of_nonneg (by linarith [hM.lowMoment_nonneg])]
    linarith [hM.lowMoment_le]
  have hlowMassN : |N.lowMass| ≤ 1 := by
    rw [abs_of_nonneg hN.lowMass_nonneg]
    exact hN.lowMass_le_one
  have hlowMomentShift :
      |(1 + M.lowMoment) - (1 + N.lowMoment)| ≤ L * δ := by
    rw [show (1 + M.lowMoment) - (1 + N.lowMoment) =
      M.lowMoment - N.lowMoment by ring]
    exact hclose.lowMoment
  have hlowProduct :
      |M.lowMass * (1 + M.lowMoment) -
          N.lowMass * (1 + N.lowMoment)| ≤ (1 + 2 * L) * δ := by
    have h := abs_mul_sub_mul_le hclose.lowMass
      hlowMomentShift hlowFactor hlowMassN hδ
      (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hhighShift :
      |(M.highMass - 1) - (N.highMass - 1)| ≤ δ := by
    simpa only [sub_sub_sub_cancel_right] using hclose.highMass
  have hhighAbs : |M.highMass - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hM.highMass_nonneg, hM.highMass_le_one]
  have hmediumN : |N.mediumMoment| ≤ L := by
    rw [abs_of_nonneg hN.mediumMoment_nonneg]
    exact hN.mediumMoment_le
  have hmediumProduct :
      |M.mediumMoment * (M.highMass - 1) -
          N.mediumMoment * (N.highMass - 1)| ≤ 2 * L * δ := by
    have h := abs_mul_sub_mul_le hclose.mediumMoment hhighShift
      hhighAbs hmediumN (mul_nonneg hL hδ) hL
    nlinarith
  have hhalfShift :
      |(1 / 2 - M.highMass) - (1 / 2 - N.highMass)| ≤ δ := by
    rw [show (1 / 2 - M.highMass) - (1 / 2 - N.highMass) =
      N.highMass - M.highMass by ring, abs_sub_comm]
    exact hclose.highMass
  have hhalfAbs : |1 / 2 - M.highMass| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hM.highMass_nonneg, hM.highMass_le_one]
  have hmeanN : |N.mean| ≤ L := by
    rw [abs_of_nonneg hN.mean_nonneg]
    exact hN.mean_le
  have hmeanProduct :
      |M.mean * (1 / 2 - M.highMass) -
          N.mean * (1 / 2 - N.highMass)| ≤ 3 / 2 * L * δ := by
    have h := abs_mul_sub_mul_le hclose.mean hhalfShift
      hhalfAbs hmeanN (mul_nonneg hL hδ) hL
    nlinarith
  let x₁ := -(M.lowMass * (1 + M.lowMoment) -
    N.lowMass * (1 + N.lowMoment)) / 2
  let x₂ := M.mediumMoment * (M.highMass - 1) -
    N.mediumMoment * (N.highMass - 1)
  let x₃ := (M.mediumMinPair - N.mediumMinPair) / 2
  let x₄ := M.mean * (1 / 2 - M.highMass) -
    N.mean * (1 / 2 - N.highMass)
  let x₅ := (M.highMinPair - N.highMinPair) / 2
  have hid :
      canonicalQuadraticCoeff M - canonicalQuadraticCoeff N =
        x₁ + x₂ + x₃ + x₄ + x₅ := by
    unfold canonicalQuadraticCoeff x₁ x₂ x₃ x₄ x₅
    ring
  have hx₁ : |x₁| ≤ (1 + 2 * L) * δ / 2 := by
    dsimp [x₁]
    rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right hlowProduct (by norm_num)
  have hx₂ : |x₂| ≤ 2 * L * δ := by
    exact hmediumProduct
  have hx₃ : |x₃| ≤ L * δ := by
    dsimp [x₃]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [hclose.mediumMinPair]
  have hx₄ : |x₄| ≤ 3 / 2 * L * δ := hmeanProduct
  have hx₅ : |x₅| ≤ L * δ := by
    dsimp [x₅]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [hclose.highMinPair]
  rw [hid]
  have h₁ := abs_add_le x₁ x₂
  have h₂ := abs_add_le (x₁ + x₂) x₃
  have h₃ := abs_add_le (x₁ + x₂ + x₃) x₄
  have h₄ := abs_add_le (x₁ + x₂ + x₃ + x₄) x₅
  nlinarith

/-- The fixed-template objective is uniformly Lipschitz in all its moments.
The constant `12(L+1)` is deliberately loose and independent of the grid
size. -/
theorem canonicalFluidCost_stable
    {M N : FluidMoments} {L δ q : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hM : M.InBox L) (hN : N.InBox L)
    (hclose : M.ComponentClose N L δ) :
    |canonicalFluidCost M q - canonicalFluidCost N q| ≤
      12 * (L + 1) * δ := by
  have hlin := canonicalLinearCoeff_stable hL hδ hM hN hclose
  have hquad := canonicalQuadraticCoeff_stable hL hδ hM hN hclose
  have hqAbs : |q| ≤ 1 := by
    rw [abs_of_nonneg hq0]
    exact hq1
  have hqSqAbs : |q ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg q)]
    nlinarith [sq_nonneg (1 - q), mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hmeanTerm : |(M.mean - N.mean) / 2| ≤ L * δ / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right hclose.mean (by norm_num)
  have hlinTerm :
      |(canonicalLinearCoeff M - canonicalLinearCoeff N) * q| ≤
        4 * L * δ := by
    rw [abs_mul]
    exact (mul_le_mul hlin hqAbs (abs_nonneg _) (by positivity)).trans_eq
      (mul_one _)
  have hquadTerm :
      |(canonicalQuadraticCoeff M - canonicalQuadraticCoeff N) * q ^ 2| ≤
        (1 + 13 * L) / 2 * δ := by
    rw [abs_mul]
    exact (mul_le_mul hquad hqSqAbs (abs_nonneg _) (by positivity)).trans_eq
      (mul_one _)
  rw [canonicalFluidCost_quadratic, canonicalFluidCost_quadratic]
  have hid :
      M.mean / 2 + canonicalLinearCoeff M * q +
          canonicalQuadraticCoeff M * q ^ 2 -
        (N.mean / 2 + canonicalLinearCoeff N * q +
          canonicalQuadraticCoeff N * q ^ 2) =
      (M.mean - N.mean) / 2 +
        (canonicalLinearCoeff M - canonicalLinearCoeff N) * q +
        (canonicalQuadraticCoeff M - canonicalQuadraticCoeff N) * q ^ 2 := by
    ring
  rw [hid]
  have h₁ := abs_add_le ((M.mean - N.mean) / 2)
    ((canonicalLinearCoeff M - canonicalLinearCoeff N) * q)
  have h₂ := abs_add_le
    ((M.mean - N.mean) / 2 +
      (canonicalLinearCoeff M - canonicalLinearCoeff N) * q)
    ((canonicalQuadraticCoeff M - canonicalQuadraticCoeff N) * q ^ 2)
  nlinarith [mul_nonneg hL hδ]

/-- Histogram Lipschitz lemma for every fixed grid template.  This is the
formal version of (47), with constant `12(L+1)` instead of the draft's
`20(L+1)`. -/
theorem template_canonicalFluidCost_lipschitz
    {ι : Type*} [Fintype ι]
    {D E p : ι → ℝ} {T : FluidTemplate ι} {L q : ℝ}
    (hD : ∀ i, 0 ≤ D i) (hE : ∀ i, 0 ≤ E i)
    (hDmass : ∑ i, D i = 1) (hEmass : ∑ i, E i = 1)
    (hp0 : ∀ i, 0 ≤ p i) (hpL : ∀ i, p i ≤ L)
    (hlow0 : ∀ i, 0 ≤ T.low i) (hlow1 : ∀ i, T.low i ≤ 1)
    (hmedium0 : ∀ i, 0 ≤ T.medium i)
    (hmedium1 : ∀ i, T.medium i ≤ 1)
    (hhigh0 : ∀ i, 0 ≤ T.high i) (hhigh1 : ∀ i, T.high i ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |canonicalFluidCost (templateMoments D p T) q -
        canonicalFluidCost (templateMoments E p T) q| ≤
      12 * (L + 1) * finiteL1 D E := by
  let M := templateMoments D p T
  let N := templateMoments E p T
  let δ := finiteL1 D E
  have hExists : ∃ i, D i ≠ 0 := by
    by_contra hnot
    have hforall : ∀ i, D i = 0 := by
      intro i
      by_contra hi
      exact hnot ⟨i, hi⟩
    have hzero : (∑ i, D i) = 0 := by simp [hforall]
    linarith
  let i₀ := hExists.choose
  have hL : 0 ≤ L := (hp0 i₀).trans (hpL i₀)
  have hδ : 0 ≤ δ := by
    dsimp [δ, finiteL1]
    positivity
  have hM : M.InBox L := by
    exact templateMoments_inBox hD hDmass hp0 hpL
      hlow0 hlow1 hmedium0 hmedium1 hhigh0 hhigh1
  have hN : N.InBox L := by
    exact templateMoments_inBox hE hEmass hp0 hpL
      hlow0 hlow1 hmedium0 hmedium1 hhigh0 hhigh1
  have hc := templateMoments_lipschitz_components hD hE hDmass hEmass
    hp0 hpL hlow0 hlow1 hmedium0 hmedium1 hhigh0 hhigh1
  dsimp only at hc
  have hclose : M.ComponentClose N L δ := by
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
      hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2⟩
  exact canonicalFluidCost_stable hL hδ hq0 hq1 hM hN hclose

/-- Standard empirical-optimization sandwich.  Uniform template stability
costs one error on each side of the empirical minimization. -/
theorem empirical_minimizer_transfer
    {Template : Type*} {sampleValue targetValue : Template → ℝ}
    {πSample πTarget : Template} {ε : ℝ}
    (hstable : ∀ π, |sampleValue π - targetValue π| ≤ ε)
    (hmin : sampleValue πSample ≤ sampleValue πTarget) :
    targetValue πSample ≤ targetValue πTarget + 2 * ε := by
  have hs₁ := (abs_le.mp (hstable πSample)).1
  have hs₂ := (abs_le.mp (hstable πTarget)).2
  linarith

/-- Taking an infimum over a common nonempty template family preserves the
same Lipschitz constant.  The explicit minimizer form above is what is used by
the finite sampled algorithm. -/
theorem chosen_minima_value_stable
    {Template : Type*} {valueD valueE : Template → ℝ}
    {πD πE : Template} {ε : ℝ}
    (hstable : ∀ π, |valueD π - valueE π| ≤ ε)
    (hD : ∀ π, valueD πD ≤ valueD π)
    (hE : ∀ π, valueE πE ≤ valueE π) :
    |valueD πD - valueE πE| ≤ ε := by
  rw [abs_le]
  constructor
  · have hs := (abs_le.mp (hstable πD)).1
    linarith [hE πD]
  · have hs := (abs_le.mp (hstable πE)).2
    linarith [hD πE]

/-- Expected empirical-optimization sandwich for a finite random pilot.
Pointwise template stability costs twice the histogram error: once for the
sample-chosen template and once for the target minimizer. -/
theorem uniformAverage_empirical_minimizer_transfer
    {Ω Template : Type*} [Fintype Ω] [Nonempty Ω]
    {sampleValue : Ω → Template → ℝ}
    {targetValue : Template → ℝ}
    {chosen : Ω → Template} {targetMin : Template}
    {error : Ω → ℝ} {C : ℝ}
    (hstable : ∀ ω π,
      |sampleValue ω π - targetValue π| ≤ C * error ω)
    (hchosen : ∀ ω π,
      sampleValue ω (chosen ω) ≤ sampleValue ω π) :
    Randomized.uniformAverage (fun ω => targetValue (chosen ω)) ≤
      targetValue targetMin +
        2 * C * Randomized.uniformAverage error := by
  have hpoint : ∀ ω,
      targetValue (chosen ω) ≤ targetValue targetMin + 2 * C * error ω := by
    intro ω
    simpa [mul_assoc] using
      empirical_minimizer_transfer (hstable ω) (hchosen ω targetMin)
  calc
    Randomized.uniformAverage (fun ω => targetValue (chosen ω)) ≤
        Randomized.uniformAverage
          (fun ω => targetValue targetMin + 2 * C * error ω) :=
      Randomized.uniformAverage_mono hpoint
    _ = targetValue targetMin +
        2 * C * Randomized.uniformAverage error := by
      rw [Randomized.uniformAverage_add,
        Randomized.uniformAverage_const,
        Randomized.uniformAverage_smul]

end

end RandomizedOptional
end SchedulingPaper
