import SchedulingPaper.RandomizedObligatoryUpper
import SchedulingPaper.RandomizedStationaryCost
import SchedulingPaper.UnifiedOffline
import Mathlib.Tactic

/-!
# Exact finite objective and early/late decomposition

This file turns the normalized fluid quantities into the exact finite
completion-time objective.  It also proves the cross-pair identity for an
ordered early/late split.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open RandomizedAnnounced

noncomputable section

def weightedCrossMin {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → ℝ) (ν : κ → ℝ) (p : ι → ℝ) (q : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, μ i * ν j * min (p i) (q j)

theorem weightedMinPair_add
    {ι : Type*} [Fintype ι]
    (μ ν p : ι → ℝ) :
    weightedMinPair (fun i => μ i + ν i) p =
      weightedMinPair μ p + weightedCrossMin μ ν p p +
        weightedCrossMin ν μ p p + weightedMinPair ν p := by
  unfold weightedMinPair weightedCrossMin
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem weightedCrossMin_swap_same
    {ι : Type*} [Fintype ι]
    (μ ν p : ι → ℝ) :
    weightedCrossMin ν μ p p = weightedCrossMin μ ν p p := by
  unfold weightedCrossMin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [min_comm]
  ring

/-- If every positive-mass early value is no larger than every
positive-mass late value, the cross minimum factors as `m*h`. -/
theorem weightedCrossMin_eq_moment_mul_mass
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : ι → ℝ} {ν : κ → ℝ} {p : ι → ℝ} {q : κ → ℝ}
    (hordered : ∀ i j, μ i ≠ 0 → ν j ≠ 0 → p i ≤ q j) :
    weightedCrossMin μ ν p q =
      weightedMoment μ p * weightedMass ν := by
  unfold weightedCrossMin weightedMoment weightedMass
  calc
    (∑ i, ∑ j, μ i * ν j * min (p i) (q j)) =
        ∑ i, ∑ j, (μ i * p i) * ν j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hμi : μ i = 0
      · simp [hμi]
      by_cases hνj : ν j = 0
      · simp [hνj]
      rw [min_eq_left (hordered i j hμi hνj)]
      ring
    _ = (∑ i, μ i * p i) * ∑ j, ν j := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]

/-- Uniform normalized mass on `Fin n`. -/
def uniformJobWeight (n : ℕ) (_i : Fin n) : ℝ := 1 / n

def earlyJobWeight {n : ℕ} (early : Fin n → Bool) (i : Fin n) : ℝ :=
  if early i then 1 / n else 0

def lateJobWeight {n : ℕ} (early : Fin n → Bool) (i : Fin n) : ℝ :=
  if early i then 0 else 1 / n

theorem early_add_late_weight
    {n : ℕ} (early : Fin n → Bool) (i : Fin n) :
    earlyJobWeight early i + lateJobWeight early i = uniformJobWeight n i := by
  cases h : early i <;> simp [earlyJobWeight, lateJobWeight, uniformJobWeight, h]

theorem weightedMass_uniformJobWeight {n : ℕ} (hn : 0 < n) :
    weightedMass (uniformJobWeight n) = 1 := by
  unfold weightedMass uniformJobWeight
  simp
  field_simp

theorem weightedMass_late_eq_one_sub_early
    {n : ℕ} (hn : 0 < n) (early : Fin n → Bool) :
    weightedMass (lateJobWeight early) =
      1 - weightedMass (earlyJobWeight early) := by
  have hadd :
      weightedMass (earlyJobWeight early) + weightedMass (lateJobWeight early) =
        weightedMass (uniformJobWeight n) := by
    unfold weightedMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact early_add_late_weight early i
  rw [weightedMass_uniformJobWeight hn] at hadd
  linarith

/-- Ordered early/late split of the complete processing pair moment. -/
theorem uniformMinPair_split
    {n : ℕ} (early : Fin n → Bool) (p : Fin n → ℝ)
    (hordered : ∀ i j, early i = true → early j = false → p i ≤ p j) :
    weightedMinPair (uniformJobWeight n) p =
      weightedMinPair (earlyJobWeight early) p +
        2 * weightedMass (lateJobWeight early) *
          weightedMoment (earlyJobWeight early) p +
        weightedMinPair (lateJobWeight early) p := by
  have hweight : (fun i => earlyJobWeight early i + lateJobWeight early i) =
      uniformJobWeight n := by
    funext i
    exact early_add_late_weight early i
  rw [← hweight, weightedMinPair_add]
  have hcross :
      weightedCrossMin (earlyJobWeight early) (lateJobWeight early) p p =
        weightedMoment (earlyJobWeight early) p *
          weightedMass (lateJobWeight early) := by
    apply weightedCrossMin_eq_moment_mul_mass
    intro i j hEi hLj
    have hi : early i = true := by
      cases h : early i
      · simp [earlyJobWeight, h] at hEi
      · rfl
    have hj : early j = false := by
      cases h : early j
      · rfl
      · simp [lateJobWeight, h] at hLj
    exact hordered i j hi hj
  rw [weightedCrossMin_swap_same
    (earlyJobWeight early) (lateJobWeight early) p, hcross]
  ring

/-- Normalized quadratic part of the exact clairvoyant objective. -/
def finiteOfflineFluid {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  (1 + weightedMinPair (uniformJobWeight n) p) / 2

/-- Exact diagonal correction. -/
def finiteOfflineCorrection {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ((n : ℝ) + ∑ i, p i) / 2

/-- Equation (2.3), used as the exact obligatory clairvoyant value. -/
def finiteObligatoryOPT {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  (n : ℝ) ^ 2 * finiteOfflineFluid p + finiteOfflineCorrection p

/-- Ordered two-draw minimum sum for a list. -/
def listFullMinCost (xs : List ℝ) : ℝ :=
  (xs.map fun x => (xs.map (min x)).sum).sum

theorem listFullMinCost_eq_sum_add_two_pairMinCost (xs : List ℝ) :
    listFullMinCost xs = xs.sum + 2 * pairMinCost xs := by
  induction xs with
  | nil => simp [listFullMinCost]
  | cons x xs ih =>
      have hsym :
          (xs.map fun y => min y x).sum = (xs.map (min x)).sum := by
        congr 1
        exact List.map_congr_left fun y _ => min_comm y x
      have hrec :
          listFullMinCost (x :: xs) =
            x + 2 * (xs.map (min x)).sum + listFullMinCost xs := by
        unfold listFullMinCost
        simp only [List.map_cons, List.sum_cons, min_self]
        rw [List.sum_map_add, hsym]
        ring
      rw [hrec, ih]
      simp only [List.sum_cons, pairMinCost_cons]
      ring

theorem listFullMinCost_ofFn {n : ℕ} (p : Fin n → ℝ) :
    listFullMinCost (List.ofFn p) = ∑ i, ∑ j, min (p i) (p j) := by
  unfold listFullMinCost
  rw [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp [Function.comp_apply, List.map_ofFn, List.sum_ofFn]

/-- The normalized uniform pair moment is exactly the list pair expression
divided by `n²`. -/
theorem weightedMinPair_uniform_eq
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) :
    weightedMinPair (uniformJobWeight n) p =
      ((List.ofFn p).sum + 2 * pairMinCost (List.ofFn p)) / (n : ℝ) ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold weightedMinPair uniformJobWeight
  have hfactor :
      (∑ i, ∑ j, (1 / (n : ℝ)) * (1 / (n : ℝ)) * min (p i) (p j)) =
        (∑ i, ∑ j, min (p i) (p j)) / (n : ℝ) ^ 2 := by
    rw [show (fun i => ∑ j,
        (1 / (n : ℝ)) * (1 / (n : ℝ)) * min (p i) (p j)) =
      (fun i => (∑ j, min (p i) (p j)) / (n : ℝ) ^ 2) by
        funext i
        rw [show (fun j => (1 / (n : ℝ)) * (1 / (n : ℝ)) *
            min (p i) (p j)) =
          (fun j => min (p i) (p j) / (n : ℝ) ^ 2) by
            funext j
            field_simp [hnR]]
        rw [Finset.sum_div]]
    rw [Finset.sum_div]
  rw [hfactor]
  rw [← listFullMinCost_ofFn p,
    listFullMinCost_eq_sum_add_two_pairMinCost]

/-- Adding the compulsory unit test to every processing time converts the
SPT pair objective to `triangular n + sum p + pairMinCost p`. -/
theorem pairCost_one_add (xs : List ℝ) :
    pairCost (xs.map fun p => 1 + p) =
      triangular xs.length + xs.sum + pairMinCost xs := by
  induction xs with
  | nil => simp [pairCost]
  | cons x xs ih =>
      unfold pairCost at ih ⊢
      simp only [List.map_cons, List.sum_cons, pairMinCost_cons,
        List.length_cons, triangular_succ]
      have hrow :
          ((xs.map fun p => 1 + p).map (min (1 + x))).sum =
            (xs.length : ℝ) + (xs.map (min x)).sum := by
        rw [List.map_map]
        rw [show (min (1 + x) ∘ fun p => 1 + p) =
            (fun p => 1 + min x p) by
          funext p
          simp [Function.comp_apply, min_add_add_left],
          List.sum_map_add]
        simp
      rw [hrow]
      push_cast
      linarith

/-- The normalized formula `finiteObligatoryOPT` is the actual clairvoyant
SPT objective on effective lengths `1+p`. -/
theorem finiteObligatoryOPT_eq_pairCost
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) :
    finiteObligatoryOPT p = pairCost (List.ofFn fun i => 1 + p i) := by
  rw [show (List.ofFn fun i => 1 + p i) =
      (List.ofFn p).map (fun x => 1 + x) by
        rw [List.map_ofFn]
        rfl,
    pairCost_one_add]
  unfold finiteObligatoryOPT finiteOfflineFluid finiteOfflineCorrection
  rw [weightedMinPair_uniform_eq hn, List.sum_ofFn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [List.length_ofFn, triangular]
  field_simp [hnR]
  ring

theorem finiteObligatoryOPT_lower
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (n : ℝ) * (n + 1) / 2 ≤ finiteObligatoryOPT p := by
  have hK : 0 ≤ weightedMinPair (uniformJobWeight n) p := by
    unfold weightedMinPair uniformJobWeight
    have hw : 0 ≤ 1 / (n : ℝ) := by positivity
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      exact mul_nonneg (mul_nonneg hw hw) (le_min (hp i) (hp j))
  have hsum : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => hp i
  unfold finiteObligatoryOPT finiteOfflineFluid finiteOfflineCorrection
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  nlinarith [sq_nonneg (n : ℝ)]

/-- In particular `OPT ≥ n²/2`, the conversion used in Theorem 1. -/
theorem finiteObligatoryOPT_sq_lower
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (n : ℝ) ^ 2 / 2 ≤ finiteObligatoryOPT p := by
  have htri := finiteObligatoryOPT_lower p hp
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  nlinarith

/-- Finite-instance robust `4/3` fluid certificate for an ordered split. -/
theorem finiteApproximateThreshold_fluid_le_four_thirds
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (early : Fin n → Bool) {θ s : ℝ}
    (hθ : 0 < θ) (hs : 0 ≤ s)
    (hEarly : ∀ i, early i = true → p i ≤ θ + s)
    (hLate : ∀ i, early i = false → θ - s ≤ p i)
    (hordered : ∀ i j, early i = true → early j = false → p i ≤ p j)
    (hDensity :
      weightedMoment (earlyJobWeight early) p =
        weightedMass (earlyJobWeight early) * θ - 1) :
    stationaryFluidCost θ (weightedMass (earlyJobWeight early))
        (weightedMinPair (lateJobWeight early) p) ≤
      4 / 3 * finiteOfflineFluid p + 2 / 3 * s := by
  have hw : 0 ≤ 1 / (n : ℝ) := by positivity
  have hμE : ∀ i, 0 ≤ earlyJobWeight early i := by
    intro i
    cases h : early i <;> simp [earlyJobWeight, h, hw]
  have hμL : ∀ i, 0 ≤ lateJobWeight early i := by
    intro i
    cases h : early i <;> simp [lateJobWeight, h, hw]
  have ha0 : 0 ≤ weightedMass (earlyJobWeight early) :=
    Finset.sum_nonneg fun i _ => hμE i
  have hmass := weightedMass_late_eq_one_sub_early hn early
  have ha1 : weightedMass (earlyJobWeight early) ≤ 1 := by
    have hlate0 : 0 ≤ weightedMass (lateJobWeight early) :=
      Finset.sum_nonneg fun i _ => hμL i
    linarith
  have hEarlyPair :
      weightedMoment (earlyJobWeight early) p ^ 2 ≤
        (θ + s) * weightedMinPair (earlyJobWeight early) p := by
    apply weightedMoment_sq_le_threshold_mul_minPair_on_support hμE hp
    intro i hweight
    have hi : early i = true := by
      cases hi : early i
      · simp [earlyJobWeight, hi] at hweight
      · rfl
    exact hEarly i hi
  have hEarlyMass :
      weightedMinPair (earlyJobWeight early) p ≤
        weightedMass (earlyJobWeight early) *
          weightedMoment (earlyJobWeight early) p :=
    weightedMinPair_le_mass_mul_moment hμE hp
  have hLatePair :
      (θ - s) * weightedMass (lateJobWeight early) ^ 2 ≤
        weightedMinPair (lateJobWeight early) p := by
    apply threshold_mul_weightedMass_sq_le_minPair_on_support hμL
    intro i hweight
    have hi : early i = false := by
      cases hi : early i
      · rfl
      · simp [lateJobWeight, hi] at hweight
    exact hLate i hi
  have hcert := stationaryFluidCost_le_four_thirds_add_slack
    hθ ha0 ha1 hs hmass hDensity hEarlyPair hEarlyMass hLatePair
  have hsplit := uniformMinPair_split early p hordered
  have hoffline :
      offlineFluidCost
          (weightedMoment (earlyJobWeight early) p)
          (weightedMass (lateJobWeight early))
          (weightedMinPair (earlyJobWeight early) p)
          (weightedMinPair (lateJobWeight early) p) =
        finiteOfflineFluid p := by
    unfold offlineFluidCost finiteOfflineFluid
    rw [hsplit]
    ring
  rw [hoffline] at hcert
  exact hcert

/-- The finite diagonal correction of the stationary policy is dominated by
`4/3` times the offline diagonal correction. -/
theorem finite_stationaryCorrection_le_four_thirds
    {n e sumP : ℝ}
    (hn : 0 ≤ n) (he0 : 0 ≤ e) (he : e ≤ n) (hsum : 0 ≤ sumP) :
    (e + sumP) / 2 ≤ 4 / 3 * ((n + sumP) / 2) := by
  nlinarith

/-- Good-learned finite cost after adding the exact diagonal correction and
an arbitrary implementation overhead. -/
theorem finite_goodLearned_cost_bound
    {n e sumP P O s ideal actual overhead : ℝ}
    (hn : 0 ≤ n) (he0 : 0 ≤ e) (he : e ≤ n) (hsum : 0 ≤ sumP)
    (hs : 0 ≤ s)
    (hfluid : P ≤ 4 / 3 * O + 2 / 3 * s)
    (hideal : ideal = n ^ 2 * P + (e + sumP) / 2)
    (hactual : actual ≤ ideal + overhead)
    (hopt : finiteOpt = n ^ 2 * O + (n + sumP) / 2) :
    actual ≤ 4 / 3 * finiteOpt + 2 / 3 * n ^ 2 * s + overhead := by
  have hcorr := finite_stationaryCorrection_le_four_thirds hn he0 he hsum
  have hbase := finiteCost_le_four_thirds_add_slack hn hs hfluid
    (alg := actual - overhead)
    (opt := finiteOpt)
    (earlyCorrection := (e + sumP) / 2)
    (offlineCorrection := (n + sumP) / 2)
    (by rw [hideal] at hactual; linarith) hopt hcorr
  linarith

end

end RandomizedObligatory
end SchedulingPaper
