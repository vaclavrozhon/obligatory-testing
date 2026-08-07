import SchedulingPaper.RandomizedOptionalFluid
import Mathlib.Tactic

/-!
# Optional testing: the all-class grid-to-envelope bridge

The first grid theorem repaired only residual known classes and assumed an
exact low test module.  A finite urn prefix has sampling error also in its
zero and selected-low outcomes.  This file closes that gap.  It repairs every
positive grid class, upper-bounds the zero count separately, and then embeds
the resulting prefix into the optional fractional knapsack with exactly one
additional discrepancy allowance per grid class (plus one for zero).
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

def selectedPart {ι : Type*} (selected : ι → Bool) (f : ι → ℝ) : ι → ℝ :=
  fun i => if selected i then f i else 0

def residualPart {ι : Type*} (selected : ι → Bool) (f : ι → ℝ) : ι → ℝ :=
  fun i => if selected i then 0 else f i

@[simp] theorem selectedPart_add_residualPart
    {ι : Type*} (selected : ι → Bool) (f : ι → ℝ) (i : ι) :
    selectedPart selected f i + residualPart selected f i = f i := by
  cases h : selected i <;> simp [selectedPart, residualPart, h]

theorem sum_selectedPart_add_sum_residualPart
    {ι : Type*} [Fintype ι] (selected : ι → Bool) (f : ι → ℝ) :
    (∑ i, selectedPart selected f i) +
        ∑ i, residualPart selected f i =
      ∑ i, f i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    selectedPart_add_residualPart selected f i

theorem selectedPart_nonneg
    {ι : Type*} {selected : ι → Bool} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ selectedPart selected f i := by
  intro i
  cases h : selected i <;> simp [selectedPart, h, hf i]

theorem residualPart_nonneg
    {ι : Type*} {selected : ι → Bool} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ residualPart selected f i := by
  intro i
  cases h : selected i <;> simp [residualPart, h, hf i]

theorem selectedPart_le_selectedPart
    {ι : Type*} {selected : ι → Bool} {f g : ι → ℝ}
    (hfg : ∀ i, f i ≤ g i) :
    ∀ i, selectedPart selected f i ≤ selectedPart selected g i := by
  intro i
  cases h : selected i <;> simp [selectedPart, h, hfg i]

theorem residualPart_le_residualPart
    {ι : Type*} {selected : ι → Bool} {f g : ι → ℝ}
    (hfg : ∀ i, f i ≤ g i) :
    ∀ i, residualPart selected f i ≤ residualPart selected g i := by
  intro i
  cases h : selected i <;> simp [residualPart, h, hfg i]

/-- Scaled form of the maximum-density inequality.  It avoids dividing by
the elapsed tested fraction in the zero-prefix case. -/
theorem scaled_discovery_density
    {ι : Type*} [Fintype ι]
    {zeroMass τ t : ℝ} {mass p completion : ι → ℝ}
    (ht : 0 ≤ t)
    (hcompletion : ∀ i, 0 ≤ completion i)
    (hcapacity : ∀ i, completion i ≤ mass i * t)
    (hmax : ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
      τ * RandomizedAnnounced.discoveryMass zeroMass x ≤
        RandomizedAnnounced.discoveryWork p x) :
    τ * (zeroMass * t + ∑ i, completion i) ≤
      t + ∑ i, p i * completion i := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · have hzero : ∀ i, completion i = 0 := by
      intro i
      have hle := hcapacity i
      have h0 := hcompletion i
      simp only [mul_zero] at hle
      linarith
    simp [hzero]
  · let x : ι → ℝ := fun i => completion i / t
    have hx0 : ∀ i, 0 ≤ x i := fun i => div_nonneg (hcompletion i) htpos.le
    have hxcap : ∀ i, x i ≤ mass i := by
      intro i
      rw [div_le_iff₀ htpos]
      simpa [mul_comm] using hcapacity i
    have hdensity := hmax x hx0 hxcap
    have hscaled := mul_le_mul_of_nonneg_left hdensity htpos.le
    unfold RandomizedAnnounced.discoveryMass
      RandomizedAnnounced.discoveryWork at hscaled
    dsimp [x] at hscaled
    have hsumDiv : (∑ i, completion i / t) * t = ∑ i, completion i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      field_simp [htpos.ne']
    have hsumWorkDiv :
        (∑ i, p i * (completion i / t)) * t =
          ∑ i, p i * completion i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      field_simp [htpos.ne']
    have hleft :
        t * (τ * (zeroMass + ∑ i, completion i / t)) =
          τ * (zeroMass * t + ∑ i, completion i) := by
      calc
        t * (τ * (zeroMass + ∑ i, completion i / t)) =
            τ * (zeroMass * t + (∑ i, completion i / t) * t) := by ring
        _ = τ * (zeroMass * t + ∑ i, completion i) := by rw [hsumDiv]
    have hright :
        t * (1 + ∑ i, p i * (completion i / t)) =
          t + ∑ i, p i * completion i := by
      calc
        t * (1 + ∑ i, p i * (completion i / t)) =
            t + (∑ i, p i * (completion i / t)) * t := by ring
        _ = t + ∑ i, p i * completion i := by rw [hsumWorkDiv]
    rw [hleft, hright] at hscaled
    exact hscaled

/-- Complete deterministic form of the finite grid prefix transfer.

`completion i` is the actual processed known mass in positive grid class
`i`; `zeroCompleted` counts zero jobs completed by tests.  Both obey one
common additive discrepancy `γ`.  Every positive class is repaired before
the selected-low and residual pieces are formed.  Consequently the only
vertical loss is `(card ι + 1)γ`, including the separate zero class. -/
theorem optional_all_class_grid_prefix_completion_le_greedy
    {ι : Type*} [Fintype ι]
    {γ zeroMass τ t q blindCompletion μ physicalWork
      actualCompleted : ℝ}
    {mass p completion : ι → ℝ}
    (selected : ι → Bool)
    {zeroCompleted greedyModule greedyBlind pivotCost : ℝ}
    {greedyResidual : ι → ℝ}
    (hγ : 0 ≤ γ)
    (hzeroMass : 0 ≤ zeroMass)
    (hmass : ∀ i, 0 ≤ mass i)
    (hp : ∀ i, 0 ≤ p i)
    (hcompletion : ∀ i, 0 ≤ completion i)
    (ht0 : 0 ≤ t) (htq : t ≤ q)
    (hzeroApprox : zeroCompleted ≤ zeroMass * t + γ)
    (hclassApprox : ∀ i, completion i ≤ mass i * t + γ)
    (hb0 : 0 ≤ blindCompletion) (hbCap : blindCompletion ≤ 1 - q)
    (hactual : actualCompleted ≤
      zeroCompleted + blindCompletion + ∑ i, completion i)
    (hphysical :
      t + μ * blindCompletion + ∑ i, p i * completion i ≤ physicalWork)
    (hmax : ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
      τ * RandomizedAnnounced.discoveryMass zeroMass x ≤
        RandomizedAnnounced.discoveryWork p x)
    (hmodulePositive :
      0 < RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass))
    (hmoduleDensity :
      τ * RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass) =
        RandomizedAnnounced.discoveryWork p
          (selectedPart selected mass))
    (hpivot : 0 < pivotCost)
    (hgreedyWork :
      physicalWork ≤ optionalKnapsackWork τ μ greedyModule greedyBlind
        p greedyResidual)
    (hgreedyLow : ∀ item,
      optionalItemCost τ μ p item < pivotCost →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item =
          optionalItemCapacity q
            (RandomizedAnnounced.discoveryMass zeroMass
              (selectedPart selected mass))
            (residualPart selected mass) item)
    (hgreedyHigh : ∀ item,
      pivotCost < optionalItemCost τ μ p item →
        optionalItemAllocation greedyModule greedyBlind greedyResidual item = 0) :
    actualCompleted ≤
      optionalKnapsackMass greedyModule greedyBlind greedyResidual +
        (Fintype.card ι + 1) * γ := by
  let repaired : ι → ℝ := fun i => repairedCompletion γ (completion i)
  let lowCompletion := selectedPart selected repaired
  let residualCompletion := residualPart selected repaired
  let lowMass := selectedPart selected mass
  let residualMass := residualPart selected mass
  let a := RandomizedAnnounced.discoveryMass zeroMass lowMass
  let w := RandomizedAnnounced.discoveryWork p lowMass
  let yLow := zeroMass * t + ∑ i, lowCompletion i
  let xLow := t + ∑ i, p i * lowCompletion i
  have hrepaired0 : ∀ i, 0 ≤ repaired i := fun i => by
    exact repairedCompletion_nonneg _ _
  have hrepairedCap : ∀ i, repaired i ≤ mass i * t := by
    intro i
    exact repairedCompletion_le (mul_nonneg (hmass i) ht0) (hclassApprox i)
  have hrepairedLe : ∀ i, repaired i ≤ completion i := by
    intro i
    exact repairedCompletion_le_original hγ (hcompletion i)
  have hlow0 : ∀ i, 0 ≤ lowCompletion i :=
    selectedPart_nonneg hrepaired0
  have hresidual0 : ∀ i, 0 ≤ residualCompletion i :=
    residualPart_nonneg hrepaired0
  have hlowCap : ∀ i, lowCompletion i ≤ lowMass i * t := by
    intro i
    cases hs : selected i <;>
      simp [lowCompletion, lowMass, selectedPart, hs, hrepairedCap i]
  have hresidualCap : ∀ i, residualCompletion i ≤ residualMass i * t := by
    intro i
    cases hs : selected i <;>
      simp [residualCompletion, residualMass, residualPart, hs,
        hrepairedCap i]
  have hresidualMass0 : ∀ i, 0 ≤ residualMass i :=
    residualPart_nonneg hmass
  have hy0 : 0 ≤ yLow := by
    dsimp [yLow]
    exact add_nonneg (mul_nonneg hzeroMass ht0)
      (Finset.sum_nonneg fun i _ => hlow0 i)
  have hyCapacity : yLow ≤ a * t := by
    have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hlowCap i
    dsimp [yLow, a, lowMass]
    unfold RandomizedAnnounced.discoveryMass
    rw [add_mul, Finset.sum_mul]
    simpa [lowMass] using add_le_add_left hsum (zeroMass * t)
  have hyDensity : w * yLow ≤ a * xLow := by
    have hdensity : τ * yLow ≤ xLow := by
      dsimp [yLow, xLow]
      exact scaled_discovery_density ht0 hlow0 hlowCap (by
          intro x hx0 hxcap
          apply hmax x hx0
          intro i
          calc
            x i ≤ selectedPart selected mass i := hxcap i
            _ ≤ mass i := by
              cases hs : selected i <;>
                simp [selectedPart, hs, hmass i])
    dsimp [a, w, lowMass]
    rw [← hmoduleDensity]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hdensity hmodulePositive.le
  have hworkRepaired :
      (∑ i, p i * repaired i) ≤ ∑ i, p i * completion i := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrepairedLe i) (hp i)
  have hworkSplit :
      (∑ i, p i * lowCompletion i) +
          ∑ i, p i * residualCompletion i =
        ∑ i, p i * repaired i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_add, selectedPart_add_residualPart selected repaired i]
  have hphysicalRepaired :
      xLow + μ * blindCompletion +
          ∑ i, p i * residualCompletion i ≤ physicalWork := by
    dsimp [xLow]
    linarith
  have hactualRepaired :
      actualCompleted ≤
        optionalKnapsackMass yLow blindCompletion residualCompletion +
          (Fintype.card ι + 1) * γ := by
    have hclassMass :
        (∑ i, completion i) ≤
          (∑ i, repaired i) + Fintype.card ι * γ := by
      have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) =>
        (le_repairedCompletion_add :
          completion i ≤ repairedCompletion γ (completion i) + γ)
      simpa [repaired, Finset.sum_add_distrib] using hsum
    have hsplit := sum_selectedPart_add_sum_residualPart selected repaired
    unfold optionalKnapsackMass
    dsimp [yLow, lowCompletion, residualCompletion]
    linarith
  have henvelope :
      optionalKnapsackMass yLow blindCompletion residualCompletion ≤
        optionalKnapsackMass greedyModule greedyBlind greedyResidual := by
    exact optional_prefix_completion_le_greedy
      hmodulePositive hmoduleDensity ht0 htq hy0 hyCapacity hyDensity
      hb0 hbCap hresidualMass0 hresidual0 hresidualCap hpivot
      hphysicalRepaired hgreedyWork
      (by simpa [a, residualMass, lowMass] using hgreedyLow)
      (by simpa using hgreedyHigh)
  linarith

end

end RandomizedOptional
end SchedulingPaper
