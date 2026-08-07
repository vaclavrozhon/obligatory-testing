import SchedulingPaper.RandomizedFiniteObjective
import SchedulingPaper.RandomizedLearnedThreshold
import Mathlib.Tactic

/-!
# The complete good-learned branch

For one fixed sample permutation on the good histogram event, this module
constructs the actual early predicate from the learned threshold and derives
the robust finite `4/3` fluid certificate.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

def learnedEarly
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) : Bool :=
  decide (thresholdClosure (quantizedRepresentative d η) θHat
    (quantizedCategory d η (p i) hη))

@[simp] theorem learnedEarly_eq_true_iff
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) :
    learnedEarly d η hη p θHat i = true ↔
      thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) := by
  simp [learnedEarly]

@[simp] theorem learnedEarly_eq_false_iff
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (θHat : ℝ) (i : Fin n) :
    learnedEarly d η hη p θHat i = false ↔
      ¬thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) := by
  simp [learnedEarly]

theorem learnedEarly_mass_eq_populationMass
    {n : ℕ} (hn : 0 < n)
    (d : ℕ) {η θHat : ℝ} (hη : 0 < η) (p : Fin n → ℝ) :
    weightedMass (earlyJobWeight (learnedEarly d η hη p θHat)) =
      selectedMass
        (fun b => ((categoryClass
          (fun i => quantizedCategory d η (p i) hη) b).card : ℝ) / n)
        (thresholdClosure (quantizedRepresentative d η) θHat) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpopulation := selectedMass_population_eq_jobAverage
    (fun i => quantizedCategory d η (p i) hη)
    (thresholdClosure (quantizedRepresentative d η) θHat)
  simp only [Fintype.card_fin] at hpopulation
  unfold weightedMass earlyJobWeight learnedEarly
  rw [hpopulation]
  rw [show (fun i =>
      if decide (thresholdClosure (quantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη)) = true then 1 / (n : ℝ) else 0) =
    (fun i => (if thresholdClosure (quantizedRepresentative d η) θHat
      (quantizedCategory d η (p i) hη) then (1 : ℝ) else 0) / (n : ℝ)) by
      funext i
      by_cases hi : thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) <;> simp [hi]]
  rw [Finset.sum_div]

theorem learnedEarly_moment_eq_populationMoment
    {n : ℕ} (d : ℕ) {η θHat : ℝ} (hη : 0 < η) (p : Fin n → ℝ) :
    weightedMoment (earlyJobWeight (learnedEarly d η hη p θHat)) p =
      (∑ i, p i *
        (if thresholdClosure (quantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη) then 1 else 0)) / n := by
  unfold weightedMoment earlyJobWeight learnedEarly
  rw [show (fun i =>
      (if decide (thresholdClosure (quantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη)) = true then 1 / (n : ℝ) else 0) *
        p i) =
    (fun i => (p i *
      (if thresholdClosure (quantizedRepresentative d η) θHat
        (quantizedCategory d η (p i) hη) then 1 else 0)) / n) by
      funext i
      by_cases hi : thresholdClosure (quantizedRepresentative d η) θHat
          (quantizedCategory d η (p i) hη) <;> simp [hi] <;> ring]
  rw [Finset.sum_div]

/-- A good learned sample yields the robust finite fluid bound with
`s = 1536 Δ + 33 η`. -/
theorem goodLearned_fluid_certificate_B32
    {n : ℕ} (hn : 0 < n)
    (samplePositions : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (d : ℕ) {η θHat : ℝ} (hη : 0 < η)
    (hcutoff : (d : ℝ) * η = 32)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hθHat0 : 0 ≤ θHat) (hθHat16 : θHat ≤ 16)
    (haHat :
      1 / 16 ≤ selectedMass
        (fun b => sampleCategoryFraction samplePositions
          (categoryClass (fun i => quantizedCategory d η (p i) hη) b) σ)
        (thresholdClosure (quantizedRepresentative d η) θHat))
    (hDensityHat :
      1 + selectedMoment
        (fun b => sampleCategoryFraction samplePositions
          (categoryClass (fun i => quantizedCategory d η (p i) hη) b) σ)
        (quantizedRepresentative d η)
        (thresholdClosure (quantizedRepresentative d η) θHat) =
      selectedMass
        (fun b => sampleCategoryFraction samplePositions
          (categoryClass (fun i => quantizedCategory d η (p i) hη) b) σ)
        (thresholdClosure (quantizedRepresentative d η) θHat) * θHat)
    (hgood : histogramL1Error samplePositions
      (fun i => quantizedCategory d η (p i) hη) σ ≤ 1 / (32 * 33)) :
    let early := learnedEarly d η hη p θHat
    let a := weightedMass (earlyJobWeight early)
    let m := weightedMoment (earlyJobWeight early) p
    let θ := (1 + m) / a
    stationaryFluidCost θ a (weightedMinPair (lateJobWeight early) p) ≤
      4 / 3 * finiteOfflineFluid p +
        2 / 3 * (1536 * histogramL1Error samplePositions
          (fun i => quantizedCategory d η (p i) hη) σ + 33 * η) := by
  dsimp only
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let c := fun i => quantizedCategory d η (p i) hη
  let q := quantizedRepresentative d η
  let selected := thresholdClosure q θHat
  let μ := fun b => ((categoryClass c b).card : ℝ) / n
  let μHat := fun b => sampleCategoryFraction samplePositions
    (categoryClass c b) σ
  let Δ := histogramL1Error samplePositions c σ
  let early := learnedEarly d η hη p θHat
  let a := weightedMass (earlyJobWeight early)
  let m := weightedMoment (earlyJobWeight early) p
  let θ := (1 + m) / a
  let distance := 1536 * Δ + 32 * η
  let s := distance + η
  have htransfer := learned_histogram_transfer_B32
    samplePositions σ d hη hcutoff hθHat16 p hp
  dsimp only at htransfer
  have haEq : a = selectedMass μ selected := by
    dsimp [a, early, μ, selected, c, q]
    exact learnedEarly_mass_eq_populationMass hn d hη p
  have hmEq : m =
      (∑ i, p i * (if selected (c i) then 1 else 0)) / n := by
    dsimp [m, early, selected, c, q]
    exact learnedEarly_moment_eq_populationMoment d hη p
  have hMass : |a - selectedMass μHat selected| ≤ Δ := by
    rw [haEq]
    simpa [μ, μHat, selected, c, Δ] using htransfer.1
  have hMoment : |m - selectedMoment μHat q selected| ≤ 32 * Δ + η := by
    rw [hmEq]
    simpa [μHat, selected, c, q, Δ] using htransfer.2
  have hdistance : |θ - θHat| ≤ distance := by
    dsimp [θ, distance]
    exact learned_true_threshold_distance_B32 haHat hθHat0 hθHat16 hgood
      hMass hMoment hDensityHat
  have haLower : 1 / 32 ≤ a :=
    learned_mass_lower_B32 haHat hgood hMass
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  have hDensity : m = a * θ - 1 := by
    dsimp [θ]
    field_simp [haPos.ne']
    ring
  have hs0 : 0 ≤ s := by
    have hdist0 : 0 ≤ distance :=
      (abs_nonneg (θ - θHat)).trans hdistance
    dsimp [s]
    linarith
  have hθPos : 0 < θ := by
    have hm0 : 0 ≤ m := by
      unfold m weightedMoment
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (by
          unfold earlyJobWeight early learnedEarly
          split_ifs <;> positivity) (hp i)
    dsimp [θ]
    exact div_pos (by linarith) haPos
  have hEarly : ∀ i, early i = true → p i ≤ θ + s := by
    intro i hi
    have hsel : selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hpHat := quantized_early_actual_le_threshold
      d hη (hp i) hθHat16 hsel
    have hrobust := robust_separation_from_threshold_distance
      (p := p i) hdistance hη.le
    dsimp [s, distance]
    nlinarith [hrobust.1 hpHat]
  have hLate : ∀ i, early i = false → θ - s ≤ p i := by
    intro i hi
    have hlate : ¬ selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hpHat := quantized_late_actual_ge_threshold_sub_eta_B32
      d hη (hp i) hcutoff hθHat16 hlate
    have hrobust := robust_separation_from_threshold_distance
      (p := p i) hdistance hη.le
    dsimp [s, distance]
    nlinarith [hrobust.2 hpHat]
  have hordered : ∀ i j, early i = true → early j = false → p i ≤ p j := by
    intro i j hi hj
    have hsel : selected (c i) := by
      dsimp [early, selected, c, q] at hi ⊢
      simpa using hi
    have hlate : ¬ selected (c j) := by
      dsimp [early, selected, c, q] at hj ⊢
      simpa using hj
    exact quantized_threshold_split_ordered_B32 d hη hcutoff
      hθHat0 hθHat16 (hp i) (hp j) hsel hlate
  have hcert := finiteApproximateThreshold_fluid_le_four_thirds
    hn p hp early hθPos hs0 hEarly hLate hordered hDensity
  dsimp [s, distance, Δ, c, early, a, m, θ] at hcert ⊢
  convert hcert using 1 <;> ring

end

end RandomizedObligatory
end SchedulingPaper
