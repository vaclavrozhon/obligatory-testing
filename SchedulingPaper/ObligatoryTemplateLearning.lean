import SchedulingPaper.ObligatoryTemplateStability
import SchedulingPaper.RandomizedOptionalGridTemplate
import Mathlib.Tactic

/-!
# Pilot learning for obligatory threshold templates

The executable grid family is finite: one template is a Boolean decision for
each rounded category.  This file chooses an exact empirical minimizer and
combines the model-specific stability estimate with the common
without-replacement histogram theorem.  The result is the statistical part
of the growing-cutoff obligatory upper bound.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Randomized
open RandomizedOptional

noncomputable section

/-- A finite obligatory grid template decides which rounded categories are
processed immediately after their tests. -/
abbrev ObligatoryTemplate (β : Type*) := β → Bool

/-- A fixed exact minimizer of the obligatory fluid objective over all
Boolean category templates. -/
def minimizingObligatoryTemplate
    {β : Type*} [Fintype β] [DecidableEq β]
    (D price : β → ℝ) : ObligatoryTemplate β :=
  (Finset.exists_min_image
    (Finset.univ : Finset (ObligatoryTemplate β))
    (obligatoryTemplateValue D price) Finset.univ_nonempty).choose

theorem minimizingObligatoryTemplate_minimizes
    {β : Type*} [Fintype β] [DecidableEq β]
    (D price : β → ℝ) (target : ObligatoryTemplate β) :
    obligatoryTemplateValue D price
        (minimizingObligatoryTemplate D price) ≤
      obligatoryTemplateValue D price target := by
  exact (Finset.exists_min_image
    (Finset.univ : Finset (ObligatoryTemplate β))
    (obligatoryTemplateValue D price) Finset.univ_nonempty).choose_spec.2
      target (by simp)

/-- The optimal value over the common finite template family. -/
def minimumObligatoryTemplateValue
    {β : Type*} [Fintype β] [DecidableEq β]
    (D price : β → ℝ) : ℝ :=
  obligatoryTemplateValue D price
    (minimizingObligatoryTemplate D price)

/-- Taking the minimum over the common template family preserves the same
histogram Lipschitz constant as every fixed template. -/
theorem minimumObligatoryTemplateValue_lipschitz
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    {D E price : β → ℝ} {L : ℝ}
    (hD : ∀ b, 0 ≤ D b) (hE : ∀ b, 0 ≤ E b)
    (hDmass : ∑ b, D b = 1) (hEmass : ∑ b, E b = 1)
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L) :
    |minimumObligatoryTemplateValue D price -
        minimumObligatoryTemplateValue E price| ≤
      3 * (L + 2) * finiteL1 D E := by
  let ε := 3 * (L + 2) * finiteL1 D E
  let earlyD := minimizingObligatoryTemplate D price
  let earlyE := minimizingObligatoryTemplate E price
  have hstable : ∀ early : ObligatoryTemplate β,
      |obligatoryTemplateValue D price early -
          obligatoryTemplateValue E price early| ≤ ε := by
    intro early
    exact obligatoryTemplateValue_lipschitz hD hE hDmass hEmass
      hprice0 hpriceL early
  have hminD : ∀ early : ObligatoryTemplate β,
      obligatoryTemplateValue D price earlyD ≤
        obligatoryTemplateValue D price early := by
    intro early
    exact minimizingObligatoryTemplate_minimizes D price early
  have hminE : ∀ early : ObligatoryTemplate β,
      obligatoryTemplateValue E price earlyE ≤
        obligatoryTemplateValue E price early := by
    intro early
    exact minimizingObligatoryTemplate_minimizes E price early
  have h := chosen_minima_value_stable hstable hminD hminE
  simpa [minimumObligatoryTemplateValue, earlyD, earlyE, ε] using h

/-- A uniform without-replacement pilot learns the best obligatory grid
template up to the standard square-root histogram loss. -/
theorem uniformSample_minimizingObligatoryTemplate_le
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (S : Finset α) (category : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    (price : β → ℝ) {L : ℝ}
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L)
    (target : ObligatoryTemplate β) :
    uniformAverage (fun σ : Equiv.Perm α =>
        obligatoryTemplateValue (populationHistogram category) price
          (minimizingObligatoryTemplate
            (sampleHistogram S category σ) price)) ≤
      obligatoryTemplateValue (populationHistogram category) price target +
        6 * (L + 2) *
          Real.sqrt ((Fintype.card β : ℝ) / S.card) := by
  let sampleValue : Equiv.Perm α → ObligatoryTemplate β → ℝ := fun σ early =>
    obligatoryTemplateValue (sampleHistogram S category σ) price early
  let targetValue : ObligatoryTemplate β → ℝ := fun early =>
    obligatoryTemplateValue (populationHistogram category) price early
  let chosen : Equiv.Perm α → ObligatoryTemplate β := fun σ =>
    minimizingObligatoryTemplate (sampleHistogram S category σ) price
  have hL0 : 0 ≤ L := by
    let b : β := Classical.choice inferInstance
    exact (hprice0 b).trans (hpriceL b)
  have hstable : ∀ σ early,
      |sampleValue σ early - targetValue early| ≤
        (3 * (L + 2)) * histogramL1Error S category σ := by
    intro σ early
    dsimp [sampleValue, targetValue]
    simpa using obligatoryTemplateValue_lipschitz
      (sampleHistogram_nonneg S category σ)
      (populationHistogram_nonneg category)
      (sampleHistogram_mass_one S hS category σ)
      (populationHistogram_mass_one category)
      hprice0 hpriceL early
  have hchosen : ∀ σ early,
      sampleValue σ (chosen σ) ≤ sampleValue σ early := by
    intro σ early
    exact minimizingObligatoryTemplate_minimizes
      (sampleHistogram S category σ) price early
  have hlearn := uniformSample_empirical_minimizer_le
    S category hS hn (C := 3 * (L + 2))
    (mul_nonneg (by norm_num) (by linarith)) hstable hchosen
    (targetMin := target)
  dsimp [sampleValue, targetValue, chosen] at hlearn ⊢
  nlinarith

/-- Closed form against the actual population optimum over the common
template family. -/
theorem uniformSample_minimizingObligatoryTemplate_le_minimum
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (S : Finset α) (category : α → β)
    (hS : S.Nonempty) (hn : 1 < Fintype.card α)
    (price : β → ℝ) {L : ℝ}
    (hprice0 : ∀ b, 0 ≤ price b) (hpriceL : ∀ b, price b ≤ L) :
    uniformAverage (fun σ : Equiv.Perm α =>
        obligatoryTemplateValue (populationHistogram category) price
          (minimizingObligatoryTemplate
            (sampleHistogram S category σ) price)) ≤
      minimumObligatoryTemplateValue
          (populationHistogram category) price +
        6 * (L + 2) *
          Real.sqrt ((Fintype.card β : ℝ) / S.card) := by
  simpa [minimumObligatoryTemplateValue] using
    uniformSample_minimizingObligatoryTemplate_le S category hS hn price
      hprice0 hpriceL
      (minimizingObligatoryTemplate (populationHistogram category) price)

end

end ObligatoryInstance
end SchedulingPaper
