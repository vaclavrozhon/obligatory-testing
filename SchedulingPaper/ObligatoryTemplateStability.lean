import SchedulingPaper.RandomizedOptionalKernel
import Mathlib.Tactic

/-!
# Histogram stability of obligatory threshold templates

This is the model-specific Lipschitz input to the common pilot-learning
transfer.  A template is just a fixed set of early grid cells.  Its value is
the stationary obligatory fluid formula, whether or not that set is optimal
for the histogram under consideration.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open RandomizedOptional

noncomputable section

def templateEarlyMass {β : Type*} [Fintype β]
    (D : β → ℝ) (early : β → Bool) : ℝ :=
  finiteExpectation D fun b => if early b then 1 else 0

def templateEarlyMoment {β : Type*} [Fintype β]
    (D price : β → ℝ) (early : β → Bool) : ℝ :=
  finiteExpectation D fun b => price b * if early b then 1 else 0

def templateLatePair {β : Type*} [Fintype β]
    (D price : β → ℝ) (early : β → Bool) : ℝ :=
  finiteProductExpectation D fun b c =>
    (if early b then 0 else 1) * (if early c then 0 else 1) *
      min (price b) (price c)

/-- The obligatory stationary fluid objective of one fixed early-cell
template. -/
def obligatoryTemplateValue {β : Type*} [Fintype β]
    (D price : β → ℝ) (early : β → Bool) : ℝ :=
  (1 + templateEarlyMoment D price early) *
      (1 - templateEarlyMass D early / 2) +
    templateLatePair D price early / 2

theorem obligatoryTemplateValue_lipschitz
    {β : Type*} [Fintype β] [Nonempty β]
    {D E price : β → ℝ} {L : ℝ}
    (hD : ∀ b, 0 ≤ D b) (hE : ∀ b, 0 ≤ E b)
    (hDmass : ∑ b, D b = 1) (hEmass : ∑ b, E b = 1)
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L)
    (early : β → Bool) :
    |obligatoryTemplateValue D price early -
        obligatoryTemplateValue E price early| ≤
      3 * (L + 2) * finiteL1 D E := by
  let δ := finiteL1 D E
  let aD := templateEarlyMass D early
  let aE := templateEarlyMass E early
  let mD := templateEarlyMoment D price early
  let mE := templateEarlyMoment E price early
  let kD := templateLatePair D price early
  let kE := templateLatePair E price early
  have hL0 : 0 ≤ L := by
    let b : β := Classical.choice inferInstance
    exact (hprice0 b).trans (hpriceL b)
  have hδ0 : 0 ≤ δ := by
    unfold δ finiteL1
    positivity
  have haDiff : |aD - aE| ≤ δ := by
    have h := finiteExpectation_lipschitz
      (μ := D) (ν := E)
      (f := fun b => if early b then (1 : ℝ) else 0)
      (B := (1 : ℝ)) (fun b => by
        by_cases hb : early b = true <;> simp [hb])
    simpa [aD, aE, templateEarlyMass, δ] using h
  have hmDiff : |mD - mE| ≤ L * δ := by
    have hkernel : ∀ b,
        |price b * if early b then (1 : ℝ) else 0| ≤ L := by
      intro b
      cases hearly : early b
      · simp [hearly, hL0]
      · simp [hearly, abs_of_nonneg (hprice0 b), hpriceL b]
    have h := finiteExpectation_lipschitz
      (μ := D) (ν := E) hkernel
    simpa [mD, mE, templateEarlyMoment, δ] using h
  have hkDiff : |kD - kE| ≤ 2 * L * δ := by
    have hkernel : ∀ b c,
        |(if early b then (0 : ℝ) else 1) *
            (if early c then 0 else 1) * min (price b) (price c)| ≤ L := by
      intro b c
      have hmin0 : 0 ≤ min (price b) (price c) :=
        le_min (hprice0 b) (hprice0 c)
      have hminL : min (price b) (price c) ≤ L :=
        (min_le_left _ _).trans (hpriceL b)
      cases early b <;> cases early c <;>
        simp [abs_of_nonneg hmin0, hminL, hL0]
    have h := finiteProductExpectation_lipschitz
      hD hE hDmass hEmass hkernel
    simpa [kD, kE, templateLatePair, δ] using h
  have haD0 : 0 ≤ aD := by
    apply finiteExpectation_nonneg hD
    intro b
    cases early b <;> simp
  have haD1 : aD ≤ 1 := by
    apply finiteExpectation_le_bound hD hDmass
    intro b
    cases early b <;> norm_num
  have hmE0 : 0 ≤ mE := by
    apply finiteExpectation_nonneg hE
    intro b
    cases hearly : early b <;> simp [hearly, hprice0 b]
  have hmEL : mE ≤ L := by
    apply finiteExpectation_le_bound hE hEmass
    intro b
    cases hearly : early b
    · simp [hearly, hL0]
    · simpa [hearly] using hpriceL b
  have hfactor : |1 - aD / 2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have honeMoment : |1 + mE| ≤ 1 + L := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hfirst :
      |(mD - mE) * (1 - aD / 2)| ≤ L * δ := by
    rw [abs_mul]
    calc
      |mD - mE| * |1 - aD / 2| ≤ (L * δ) * 1 :=
        mul_le_mul hmDiff hfactor (abs_nonneg _) (mul_nonneg hL0 hδ0)
      _ = L * δ := by ring
  have hsecond :
      |(aE - aD) / 2 * (1 + mE)| ≤ (1 + L) * δ / 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have haDiff' : |aE - aD| ≤ δ := by simpa [abs_sub_comm] using haDiff
    have hmul : |aE - aD| * |1 + mE| ≤ δ * (1 + L) :=
      mul_le_mul haDiff' honeMoment (abs_nonneg _) hδ0
    nlinarith
  have hthird : |(kD - kE) / 2| ≤ L * δ := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hidentity :
      obligatoryTemplateValue D price early -
          obligatoryTemplateValue E price early =
        (mD - mE) * (1 - aD / 2) +
          (aE - aD) / 2 * (1 + mE) + (kD - kE) / 2 := by
    simp only [obligatoryTemplateValue, aD, aE, mD, mE, kD, kE]
    ring
  rw [hidentity]
  calc
    |(mD - mE) * (1 - aD / 2) +
        (aE - aD) / 2 * (1 + mE) + (kD - kE) / 2| ≤
        |(mD - mE) * (1 - aD / 2) +
          (aE - aD) / 2 * (1 + mE)| + |(kD - kE) / 2| :=
            abs_add_le _ _
    _ ≤
        |(mD - mE) * (1 - aD / 2)| +
          |(aE - aD) / 2 * (1 + mE)| + |(kD - kE) / 2| := by
            linarith [abs_add_le
              ((mD - mE) * (1 - aD / 2))
              ((aE - aD) / 2 * (1 + mE))]
    _ ≤ L * δ + (1 + L) * δ / 2 + L * δ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ 3 * (L + 2) * δ := by nlinarith [hδ0]

end

end ObligatoryInstance
end SchedulingPaper
