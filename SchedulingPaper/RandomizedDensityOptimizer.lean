import SchedulingPaper.RandomizedThresholdClosure
import Mathlib.Tactic

/-!
# Finite maximum-density sample optimizer

The sampled algorithm maximizes completed sample mass divided by discovery
work.  It is convenient to maximize over all finite subsets: the local
optimality conditions proved below imply that every maximizer is a threshold
set, up to zero-mass and equality categories.  Threshold closure then gives a
canonical decision for categories absent from the sample.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

noncomputable section

def subsetMass {β : Type*} [Fintype β]
    (μ : β → ℝ) (S : Finset β) : ℝ :=
  ∑ b ∈ S, μ b

def subsetMoment {β : Type*} [Fintype β]
    (μ q : β → ℝ) (S : Finset β) : ℝ :=
  ∑ b ∈ S, μ b * q b

def subsetDensity {β : Type*} [Fintype β]
    (μ q : β → ℝ) (S : Finset β) : ℝ :=
  subsetMass μ S / (1 + subsetMoment μ q S)

def IsMaximumDensitySubset {β : Type*} [Fintype β]
    (μ q : β → ℝ) (S : Finset β) : Prop :=
  ∀ T, subsetDensity μ q T ≤ subsetDensity μ q S

theorem exists_maximumDensitySubset
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ q : β → ℝ) :
    ∃ S : Finset β, IsMaximumDensitySubset μ q S := by
  classical
  obtain ⟨S, _hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset : Finset (Finset β))
    (subsetDensity μ q) (by simp)
  refine ⟨S, ?_⟩
  intro T
  exact hmax T (by simp)

/-- A fixed choice of a maximum-density subset.  Keeping the choice as a
function of `(μ,q)` (rather than of a presentation of `μ`) makes permutation
invariance of sampled learners definitional after their histograms are shown
equal. -/
def chosenMaximumDensitySubset
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ q : β → ℝ) : Finset β :=
  Classical.choose (exists_maximumDensitySubset μ q)

theorem chosenMaximumDensitySubset_isMaximum
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ q : β → ℝ) :
    IsMaximumDensitySubset μ q (chosenMaximumDensitySubset μ q) :=
  Classical.choose_spec (exists_maximumDensitySubset μ q)

/-- Defining the inverse density from any positive selected mass gives the
cross-multiplied density identity used throughout the analysis. -/
theorem inverseDensity_identity
    {β : Type*} [Fintype β]
    {μ q : β → ℝ} {S : Finset β}
    (hpositive : 0 < subsetMass μ S) :
    1 + subsetMoment μ q S = subsetMass μ S *
      ((1 + subsetMoment μ q S) / subsetMass μ S) := by
  field_simp [hpositive.ne']

/-- With nonnegative representatives, every positive inverse density is
strictly positive. -/
theorem inverseDensity_pos
    {β : Type*} [Fintype β]
    {μ q : β → ℝ} {S : Finset β}
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hpositive : 0 < subsetMass μ S) :
    0 < (1 + subsetMoment μ q S) / subsetMass μ S := by
  exact div_pos (by
    have : 0 ≤ subsetMoment μ q S := by
      unfold subsetMoment
      exact Finset.sum_nonneg fun b hb => mul_nonneg (hμ b) (hq b)
    linarith) hpositive

/-- At cutoff `B=32`, learned inverse density at most sixteen forces sample
mass at least `1/16`. -/
theorem inverseDensity_le_sixteen_mass_lower
    {a m θ : ℝ}
    (hm : 0 ≤ m) (hθ : 0 ≤ θ) (hθ16 : θ ≤ 16)
    (hdensity : 1 + m = a * θ) :
    1 / 16 ≤ a := by
  have hprod : 0 < a * θ := by linarith
  have ha : 0 < a := by
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.1
    · exact False.elim (not_lt_of_ge hθ hneg.2)
  have hscale := mul_le_mul_of_nonneg_left hθ16 ha.le
  norm_num at hscale ⊢
  nlinarith

theorem subsetMass_nonneg
    {β : Type*} [Fintype β]
    {μ : β → ℝ} (hμ : ∀ b, 0 ≤ μ b) (S : Finset β) :
    0 ≤ subsetMass μ S := by
  unfold subsetMass
  exact Finset.sum_nonneg fun b hb => hμ b

theorem subsetMoment_nonneg
    {β : Type*} [Fintype β]
    {μ q : β → ℝ} (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (S : Finset β) :
    0 ≤ subsetMoment μ q S := by
  unfold subsetMoment
  exact Finset.sum_nonneg fun b hb => mul_nonneg (hμ b) (hq b)

theorem subsetMass_insert
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ : β → ℝ) (S : Finset β) {b : β} (hb : b ∉ S) :
    subsetMass μ (insert b S) = subsetMass μ S + μ b := by
  simp [subsetMass, hb, add_comm]

theorem subsetMoment_insert
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ q : β → ℝ) (S : Finset β) {b : β} (hb : b ∉ S) :
    subsetMoment μ q (insert b S) = subsetMoment μ q S + μ b * q b := by
  simp [subsetMoment, hb, add_comm]

theorem subsetMass_erase_add
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ : β → ℝ) (S : Finset β) {b : β} (hb : b ∈ S) :
    subsetMass μ (S.erase b) + μ b = subsetMass μ S := by
  rw [← subsetMass_insert μ (S.erase b) (by simp)]
  simp [Finset.insert_erase hb]

theorem subsetMoment_erase_add
    {β : Type*} [Fintype β] [DecidableEq β]
    (μ q : β → ℝ) (S : Finset β) {b : β} (hb : b ∈ S) :
    subsetMoment μ q (S.erase b) + μ b * q b = subsetMoment μ q S := by
  rw [← subsetMoment_insert μ q (S.erase b) (by simp)]
  simp [Finset.insert_erase hb]

/-- A positive-mass category strictly below the inverse density must be in a
maximum-density subset. -/
theorem maximumDensitySubset_contains_below
    {β : Type*} [Fintype β] [DecidableEq β]
    {μ q : β → ℝ} {S : Finset β} {θ : ℝ}
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hmax : IsMaximumDensitySubset μ q S)
    (hpositive : 0 < subsetMass μ S)
    (hdensity : 1 + subsetMoment μ q S = subsetMass μ S * θ)
    {b : β} (hμb : 0 < μ b) (hbelow : q b < θ) :
    b ∈ S := by
  classical
  by_contra hb
  have hbnot : b ∉ S := hb
  have hden0 : 0 < 1 + subsetMoment μ q S := by
    have := subsetMoment_nonneg hμ hq S
    linarith
  have hdenInsert0 :
      0 < 1 + subsetMoment μ q (insert b S) := by
    have := subsetMoment_nonneg hμ hq (insert b S)
    linarith
  have hmassInsert := subsetMass_insert μ S hbnot
  have hmomInsert := subsetMoment_insert μ q S hbnot
  have himprove :
      subsetDensity μ q S < subsetDensity μ q (insert b S) := by
    unfold subsetDensity
    rw [div_lt_div_iff₀ hden0 hdenInsert0]
    rw [hmassInsert, hmomInsert]
    nlinarith [mul_pos hμb hpositive]
  exact (not_lt_of_ge (hmax (insert b S))) himprove

/-- A positive-mass category strictly above the inverse density cannot be in
a maximum-density subset. -/
theorem maximumDensitySubset_excludes_above
    {β : Type*} [Fintype β] [DecidableEq β]
    {μ q : β → ℝ} {S : Finset β} {θ : ℝ}
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hmax : IsMaximumDensitySubset μ q S)
    (hpositive : 0 < subsetMass μ S)
    (hdensity : 1 + subsetMoment μ q S = subsetMass μ S * θ)
    {b : β} (hμb : 0 < μ b) (habove : θ < q b) :
    b ∉ S := by
  classical
  intro hb
  let T := S.erase b
  have hmass := subsetMass_erase_add μ S hb
  have hmom := subsetMoment_erase_add μ q S hb
  have hdenS0 : 0 < 1 + subsetMoment μ q S := by
    have := subsetMoment_nonneg hμ hq S
    linarith
  have hdenT0 : 0 < 1 + subsetMoment μ q T := by
    have := subsetMoment_nonneg hμ hq T
    linarith
  have himprove : subsetDensity μ q S < subsetDensity μ q T := by
    unfold subsetDensity
    rw [div_lt_div_iff₀ hdenS0 hdenT0]
    dsimp [T] at hmass hmom ⊢
    nlinarith [mul_pos hμb hpositive]
  exact (not_lt_of_ge (hmax T)) himprove

/-- The full threshold closure of a positive maximum-density subset has the
same inverse-density identity, including all sample-empty bins. -/
theorem maximumDensity_thresholdClosure_preserves
    {β : Type*} [Fintype β] [DecidableEq β]
    {μ q : β → ℝ} {S : Finset β} {θ : ℝ}
    (hμ : ∀ b, 0 ≤ μ b) (hq : ∀ b, 0 ≤ q b)
    (hmax : IsMaximumDensitySubset μ q S)
    (hpositive : 0 < subsetMass μ S)
    (hdensity : 1 + subsetMoment μ q S = subsetMass μ S * θ) :
    1 + selectedMoment μ q (thresholdClosure q θ) =
      θ * selectedMass μ (thresholdClosure q θ) := by
  have hselectedMoment :
      selectedMoment μ q (fun b => b ∈ S) = subsetMoment μ q S := by
    unfold selectedMoment subsetMoment
    simp
  have hselectedMass :
      selectedMass μ (fun b => b ∈ S) = subsetMass μ S := by
    unfold selectedMass subsetMass
    simp
  apply thresholdClosure_preserves_density
      (selected := fun b => b ∈ S) hμ
  · intro b hμb hbelow
    exact maximumDensitySubset_contains_below hμ hq hmax hpositive
      hdensity hμb hbelow
  · intro b hμb habove
    exact maximumDensitySubset_excludes_above hμ hq hmax hpositive
      hdensity hμb habove
  · rw [hselectedMoment, hselectedMass]
    nlinarith

end

end RandomizedObligatory
end SchedulingPaper
