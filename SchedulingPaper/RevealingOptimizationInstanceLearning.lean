import SchedulingPaper.RandomizedOptionalGridTemplate
import Mathlib.Tactic

/-!
# Finite learnable templates for revealing optimization

The raw operation in revealing optimization has the public duration `u`.
Consequently its fluid kernel is different from the optional-testing/blind-
execution kernel.  This file isolates the correct finite template family and
proves the model-specific stability statement needed by pilot learning.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace InstanceLearning

open Randomized
open RandomizedOptional

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Executable grid data: a set of positive cells completed immediately after
their tests, and an integral quota of tested jobs.  Zero is kept outside the
positive grid and is always in the immediate class. -/
structure RawTemplate (ι : Type*) (n : ℕ) where
  low : ι → Bool
  quota : Fin (n + 1)
  deriving DecidableEq, Fintype

abbrev Template (ι : Type*) (n : ℕ) := RawTemplate ι n

instance {ι : Type*} {n : ℕ} [Fintype ι] : Nonempty (Template ι n) :=
  ⟨{ low := fun _ => false, quota := ⟨0, by omega⟩ }⟩

def Template.fraction {ι : Type*} {n : ℕ} (T : Template ι n) : ℝ :=
  (T.quota : ℝ) / n

theorem Template.quota_le {ι : Type*} {n : ℕ} (T : Template ι n) :
    T.quota.val ≤ n := by
  omega

theorem Template.fraction_nonneg {ι : Type*} {n : ℕ}
    (T : Template ι n) : 0 ≤ T.fraction := by
  unfold fraction
  positivity

theorem Template.fraction_le_one {ι : Type*} {n : ℕ}
    (hn : 0 < n) (T : Template ι n) : T.fraction ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).2
  simpa using (show (T.quota.val : ℝ) ≤ n by exact_mod_cast T.quota_le)

/-- The zero cell is completed at its test; positive cells use the selector
stored in the template. -/
def Template.lowWithZero {ι : Type*} {n : ℕ}
    (T : Template ι n) : Option ι → Bool
  | none => true
  | some i => T.low i

/-- Symmetric charge of two tested jobs after averaging their relative
discovery order.  Residual tested jobs are drained by SPT. -/
def testedPairChargeFlags (leftLow rightLow : Bool) (p q : ℝ) : ℝ :=
  if leftLow then
    if rightLow then 1 + (p + q) / 2 else 3 / 2 + p
  else if rightLow then 3 / 2 + q else 2 + min p q

def testedPairCharge (low : ℝ → Bool) (p q : ℝ) : ℝ :=
  testedPairChargeFlags (low p) (low q) p q

/-- Fluid unordered-pair charge for a fixed tested fraction `x`.  The four
terms correspond to tested/tested, tested/raw in either orientation, and
raw/raw.  Their coefficients sum to one. -/
def fluidPairChargeFlags (u x : ℝ) (leftLow rightLow : Bool)
    (p q : ℝ) : ℝ :=
  x ^ 2 * testedPairChargeFlags leftLow rightLow p q +
    x * (1 - x) * (1 + p) +
    x * (1 - x) * (1 + q) +
    (1 - x) ^ 2 * u

def fluidPairCharge (u x : ℝ) (low : ℝ → Bool) (p q : ℝ) : ℝ :=
  fluidPairChargeFlags u x (low p) (low q) p q

theorem testedPairCharge_nonneg
    {low : ℝ → Bool} {p q : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) :
    0 ≤ testedPairCharge low p q := by
  cases hp : low p <;> cases hq : low q <;>
    simp [testedPairCharge, testedPairChargeFlags, hp, hq] <;>
    have hmin : 0 ≤ min p q := le_min hp0 hq0 <;> linarith

theorem testedPairCharge_le
    {u p q : ℝ} (hu0 : 0 ≤ u)
    (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u)
    (low : ℝ → Bool) :
    testedPairCharge low p q ≤ u + 2 := by
  cases hp : low p <;> cases hq : low q <;>
    simp [testedPairCharge, testedPairChargeFlags, hp, hq] <;>
    have hmin := min_le_left p q <;> linarith

theorem fluidPairCharge_nonneg
    {u x p q : ℝ} (hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (low : ℝ → Bool) :
    0 ≤ fluidPairCharge u x low p q := by
  unfold fluidPairCharge fluidPairChargeFlags
  have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have htt : 0 ≤ testedPairChargeFlags (low p) (low q) p q := by
    simpa [testedPairCharge] using testedPairCharge_nonneg hp0 hq0
  positivity

theorem fluidPairChargeFlags_le
    {u x p q : ℝ} (hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u) (leftLow rightLow : Bool) :
    fluidPairChargeFlags u x leftLow rightLow p q ≤ u + 2 := by
  let B := u + 2
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have htt : testedPairChargeFlags leftLow rightLow p q ≤ B := by
    cases leftLow <;> cases rightLow <;>
      simp [testedPairChargeFlags, B] <;>
      have hmin := min_le_left p q <;> linarith
  have hp : 1 + p ≤ B := by dsimp [B]; linarith
  have hq : 1 + q ≤ B := by dsimp [B]; linarith
  have hu : u ≤ B := by dsimp [B]; linarith
  have hxSq : 0 ≤ x ^ 2 := sq_nonneg x
  have hcross : 0 ≤ x * (1 - x) :=
    mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have htail : 0 ≤ (1 - x) ^ 2 := sq_nonneg (1 - x)
  have hweighted :
      fluidPairChargeFlags u x leftLow rightLow p q ≤
        x ^ 2 * B + x * (1 - x) * B +
          x * (1 - x) * B + (1 - x) ^ 2 * B := by
    unfold fluidPairChargeFlags
    gcongr
  calc
    fluidPairChargeFlags u x leftLow rightLow p q ≤
        x ^ 2 * B + x * (1 - x) * B +
          x * (1 - x) * B + (1 - x) ^ 2 * B := hweighted
    _ = B := by ring
    _ = u + 2 := rfl

theorem fluidPairCharge_le
    {u x p q : ℝ} (hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp0 : 0 ≤ p) (hpu : p ≤ u)
    (hq0 : 0 ≤ q) (hqu : q ≤ u) (low : ℝ → Bool) :
    fluidPairCharge u x low p q ≤ u + 2 := by
  exact fluidPairChargeFlags_le hu0 hx0 hx1 hp0 hpu hq0 hqu _ _

/-- The cell-indexed kernel applies the template selector directly, so equal
positive grid prices need not be distinguished by an artificial inverse. -/
def gridPairCharge
    {ι : Type*} {n : ℕ} (price : ι → ℝ) (u : ℝ)
    (T : Template ι n) (left right : Option ι) : ℝ :=
  let x := T.fraction
  let p := positiveGridPrice price left
  let q := positiveGridPrice price right
  fluidPairChargeFlags u x (T.lowWithZero left)
    (T.lowWithZero right) p q

/-- Cell-indexed version of the leading normalized cost.  Injectivity of
positive prices will later identify `lowPrice` with the executable cell
selector. -/
def gridTemplateValue
    {ι : Type*} [Fintype ι] {n : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (u : ℝ)
    (T : Template ι n) : ℝ :=
  finiteProductExpectation D (gridPairCharge price u T) / 2

theorem abs_gridPairCharge_le
    {ι : Type*} {n : ℕ} {price : ι → ℝ} {u : ℝ}
    (hu0 : 0 ≤ u) (hprice0 : ∀ i, 0 ≤ price i)
    (hpriceu : ∀ i, price i ≤ u) (T : Template ι n)
    (hn : 0 < n) (left right : Option ι) :
    |gridPairCharge price u T left right| ≤ u + 2 := by
  have hp0 : 0 ≤ positiveGridPrice price left := by
    cases left <;> simp [positiveGridPrice, hprice0]
  have hpu : positiveGridPrice price left ≤ u := by
    cases left <;> simp [positiveGridPrice, hu0, hpriceu]
  have hq0 : 0 ≤ positiveGridPrice price right := by
    cases right <;> simp [positiveGridPrice, hprice0]
  have hqu : positiveGridPrice price right ≤ u := by
    cases right <;> simp [positiveGridPrice, hu0, hpriceu]
  rw [abs_of_nonneg]
  · unfold gridPairCharge
    exact fluidPairChargeFlags_le hu0 T.fraction_nonneg
      (T.fraction_le_one hn) hp0 hpu hq0 hqu _ _
  · unfold gridPairCharge
    have htt0 : 0 ≤ testedPairChargeFlags (T.lowWithZero left)
        (T.lowWithZero right) (positiveGridPrice price left)
          (positiveGridPrice price right) := by
      cases hleft : T.lowWithZero left <;>
        cases hright : T.lowWithZero right <;>
        simp [testedPairChargeFlags, hleft, hright] <;>
        have hmin : 0 ≤ min (positiveGridPrice price left)
            (positiveGridPrice price right) := le_min hp0 hq0 <;> linarith
    have hcross : 0 ≤ T.fraction * (1 - T.fraction) :=
      mul_nonneg T.fraction_nonneg
        (sub_nonneg.mpr (T.fraction_le_one hn))
    have htested : 0 ≤ T.fraction ^ 2 *
        testedPairChargeFlags (T.lowWithZero left) (T.lowWithZero right)
          (positiveGridPrice price left)
          (positiveGridPrice price right) :=
      mul_nonneg (sq_nonneg _) htt0
    have hleft : 0 ≤ T.fraction * (1 - T.fraction) *
        (1 + positiveGridPrice price left) :=
      mul_nonneg hcross (by linarith)
    have hright : 0 ≤ T.fraction * (1 - T.fraction) *
        (1 + positiveGridPrice price right) :=
      mul_nonneg hcross (by linarith)
    have hraw : 0 ≤ (1 - T.fraction) ^ 2 * u :=
      mul_nonneg (sq_nonneg _) hu0
    exact add_nonneg (add_nonneg (add_nonneg htested hleft) hright) hraw

/-- The revealing template objective is uniformly Lipschitz in the empirical
histogram.  This is the model-specific input to the common pilot theorem. -/
theorem gridTemplateValue_lipschitz
    {ι : Type*} [Fintype ι] {n : ℕ}
    {D E : Option ι → ℝ} {price : ι → ℝ} {u : ℝ}
    (hn : 0 < n) (hu0 : 0 ≤ u)
    (hD : ∀ cell, 0 ≤ D cell) (hE : ∀ cell, 0 ≤ E cell)
    (hDmass : ∑ cell, D cell = 1) (hEmass : ∑ cell, E cell = 1)
    (hprice0 : ∀ i, 0 ≤ price i) (hpriceu : ∀ i, price i ≤ u)
    (T : Template ι n) :
    |gridTemplateValue D price u T - gridTemplateValue E price u T| ≤
      (u + 2) * finiteL1 D E := by
  have hproduct := finiteProductExpectation_lipschitz
    hD hE hDmass hEmass
      (abs_gridPairCharge_le hu0 hprice0 hpriceu T hn)
  unfold gridTemplateValue
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

noncomputable def minimizingTemplate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (u : ℝ) : Template ι n :=
  (Finset.exists_min_image (Finset.univ : Finset (Template ι n))
    (gridTemplateValue D price u) Finset.univ_nonempty).choose

theorem minimizingTemplate_minimizes
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (D : Option ι → ℝ) (price : ι → ℝ) (u : ℝ)
    (target : Template ι n) :
    gridTemplateValue D price u (minimizingTemplate (n := n) D price u) ≤
      gridTemplateValue D price u target := by
  exact (Finset.exists_min_image (Finset.univ : Finset (Template ι n))
    (gridTemplateValue D price u) Finset.univ_nonempty).choose_spec.2
      target (by simp)

/-- A uniform pilot learns the best revealing-optimization grid template up
to the standard square-root histogram loss. -/
theorem uniformSample_minimizingTemplate_le
    {α ι : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hnTemplate : 0 < n)
    (S : Finset α) (category : α → Option ι)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    (price : ι → ℝ) {u : ℝ} (hu0 : 0 ≤ u)
    (hprice0 : ∀ i, 0 ≤ price i) (hpriceu : ∀ i, price i ≤ u)
    (target : Template ι n) :
    uniformAverage (fun σ : Equiv.Perm α =>
        gridTemplateValue (populationHistogram category) price u
          (minimizingTemplate (n := n)
            (sampleHistogram S category σ) price u)) ≤
      gridTemplateValue (populationHistogram category) price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / S.card) := by
  let sampleValue : Equiv.Perm α → Template ι n → ℝ := fun σ T =>
    gridTemplateValue (sampleHistogram S category σ) price u T
  let targetValue : Template ι n → ℝ := fun T =>
    gridTemplateValue (populationHistogram category) price u T
  let chosen : Equiv.Perm α → Template ι n := fun σ =>
    minimizingTemplate (n := n) (sampleHistogram S category σ) price u
  have hstable : ∀ σ T,
      |sampleValue σ T - targetValue T| ≤
        (u + 2) * histogramL1Error S category σ := by
    intro σ T
    dsimp [sampleValue, targetValue]
    simpa using gridTemplateValue_lipschitz hnTemplate hu0
      (sampleHistogram_nonneg S category σ)
      (populationHistogram_nonneg category)
      (sampleHistogram_mass_one S hS category σ)
      (populationHistogram_mass_one category)
      hprice0 hpriceu T
  have hchosen : ∀ σ T,
      sampleValue σ (chosen σ) ≤ sampleValue σ T := by
    intro σ T
    exact minimizingTemplate_minimizes
      (sampleHistogram S category σ) price u T
  have hlearn := uniformSample_empirical_minimizer_le S category hS hn
    (show 0 ≤ u + 2 by linarith) hstable hchosen (targetMin := target)
  simpa [sampleValue, targetValue, chosen] using hlearn

end

end InstanceLearning
end RevealingOptimization
end SchedulingPaper
