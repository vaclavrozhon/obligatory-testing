import SchedulingPaper.BlindOptimizationAdversary
import SchedulingPaper.BlindOptimizationDeterministicUpper
import SchedulingPaper.BlindOptimizationPlan
import SchedulingPaper.BlindOptimizationPilotLearning

/-!
# Finite randomized pilot upper bound for blind optimization

The pilot and the main schedule use independent private orders.  Conditioning
on the sampled set, the remaining labels are therefore uniformly ordered.
This file averages the literal completion-time list and connects it to the
mean-estimation theorem in `BlindOptimizationPilotLearning`.
-/

namespace SchedulingPaper
namespace BlindOptimization

open Randomized

noncomputable section

def randomOrderValues {α : Type*} [Fintype α]
    (duration : α → ℝ) (order : Equiv.Perm α) : List ℝ :=
  List.ofFn fun position : Fin (Fintype.card α) ↦
    duration (order ((Fintype.equivFin α).symm position))

def randomOrderCost {α : Type*} [Fintype α]
    (duration : α → ℝ) (order : Equiv.Perm α) : ℝ :=
  prefixCost (randomOrderValues duration order)

@[simp] theorem randomOrderValues_length
    {α : Type*} [Fintype α] (duration : α → ℝ) (order : Equiv.Perm α) :
    (randomOrderValues duration order).length = Fintype.card α := by
  simp [randomOrderValues]

theorem randomOrderValues_sum
    {α : Type*} [Fintype α] (duration : α → ℝ) (order : Equiv.Perm α) :
    (randomOrderValues duration order).sum = ∑ job, duration job := by
  unfold randomOrderValues
  rw [List.sum_ofFn]
  calc
    (∑ position : Fin (Fintype.card α),
        duration (order ((Fintype.equivFin α).symm position))) =
        ∑ job : α, duration (order job) := by
          exact Fintype.sum_equiv (Fintype.equivFin α).symm _ _
            (fun _ ↦ rfl)
    _ = ∑ job : α, duration job := Equiv.sum_comp order duration

/-- A uniformly random order of an arbitrary nonempty finite type has the
usual triangular expected completion cost. -/
theorem uniformAverage_randomOrderCost
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (duration : α → ℝ) :
    uniformAverage (randomOrderCost duration) =
      (Fintype.card α + 1 : ℝ) / 2 * ∑ job, duration job := by
  let N := Fintype.card α
  let positionJob : Fin N → α := fun position ↦
    (Fintype.equivFin α).symm position
  unfold randomOrderCost randomOrderValues
  simp_rw [Adversary.prefixCost_ofFn_eq_weighted_sum]
  rw [uniformAverage_fintype_sum]
  have hposition : ∀ position : Fin N,
      uniformAverage (fun order : Equiv.Perm α ↦
        ((N - position.val : ℕ) : ℝ) *
          duration (order (positionJob position))) =
        ((N - position.val : ℕ) : ℝ) *
          ((∑ job, duration job) / N) := by
    intro position
    rw [uniformAverage_smul]
    congr 1
    simpa [positionJob, N] using
      uniformAverage_perm_apply duration (positionJob position)
  have hsum :
      (∑ position : Fin N,
        uniformAverage (fun order : Equiv.Perm α ↦
          ((N - position.val : ℕ) : ℝ) *
            duration (order (positionJob position)))) =
      ∑ position : Fin N,
        ((N - position.val : ℕ) : ℝ) *
          ((∑ job, duration job) / N) := by
    exact Finset.sum_congr rfl fun position _ ↦ hposition position
  rw [hsum]
  rw [← Finset.sum_mul]
  have hweights :
      (∑ position : Fin N, ((N - position.val : ℕ) : ℝ)) =
        (N : ℝ) * (N + 1) / 2 := by
    have h : 2 * (∑ position : Fin N,
        ((N - position.val : ℕ) : ℝ)) = (N : ℝ) * (N + 1) := by
      exact_mod_cast Adversary.two_mul_sum_fin_reverse_weights N
    linarith
  rw [hweights]
  have hN : (N : ℝ) ≠ 0 := by positivity
  field_simp
  dsimp [N]
  ring

/-- The same identity without a `Nonempty` type-class argument.  The empty
case is vacuous; exposing it here avoids expensive instance search for
dependent remaining-job subtypes. -/
theorem uniformAverage_randomOrderCost_total
    {α : Type*} [Fintype α] [DecidableEq α] (duration : α → ℝ) :
    uniformAverage (randomOrderCost duration) =
      (Fintype.card α + 1 : ℝ) / 2 * ∑ job, duration job := by
  cases isEmpty_or_nonempty α with
  | inl hempty =>
      letI : IsEmpty α := hempty
      have hcard : Fintype.card α = 0 := Fintype.card_eq_zero
      simp [randomOrderCost, randomOrderValues, uniformAverage, hcard]
  | inr hnonempty =>
      letI : Nonempty α := hnonempty
      exact uniformAverage_randomOrderCost duration

/-- A random-order block costs at most the ambient triangular factor times
any nonnegative upper bound on its average total work.  Keeping this lemma
independent of the pilot subtype makes the later dependent construction
both faster to elaborate and easier to reuse. -/
theorem uniformAverage_randomOrderCost_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (duration : α → ℝ) {n : ℕ} {blockLength : ℝ}
    (hcard : Fintype.card α ≤ n)
    (hsum0 : 0 ≤ ∑ job, duration job)
    (hsum : (∑ job, duration job) ≤ n * blockLength) :
    uniformAverage (randomOrderCost duration) ≤
      n * (n + 1) / 2 * blockLength := by
  rw [uniformAverage_randomOrderCost_total]
  have hcard' : (Fintype.card α + 1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.add_le_add_right hcard 1
  calc
    (Fintype.card α + 1 : ℝ) / 2 * (∑ job, duration job) ≤
        (n + 1 : ℝ) / 2 * (∑ job, duration job) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcard' (by norm_num)) hsum0
    _ ≤ (n + 1 : ℝ) / 2 * ((n : ℝ) * blockLength) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (n : ℝ) * (n + 1) / 2 * blockLength := by ring

/-- Randomly ordering any nonempty subset and optimizing every job in it is
bounded by the ambient triangular factor times the full-population optimized
mean. -/
theorem uniformAverage_subsetOptimizedCost_le
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job)
    (remaining : Finset (Fin n)) (hremaining : remaining.Nonempty) :
    uniformAverage (randomOrderCost
      (fun job : ↥remaining ↦ 1 + processing job)) ≤
      n * (n + 1) / 2 * (1 + populationMean processing) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hcard : Fintype.card ↥remaining ≤ n := by
    rw [Fintype.card_coe]
    simpa using remaining.card_le_univ
  have hsum0 : 0 ≤ ∑ job : ↥remaining, (1 + processing job) :=
    Finset.sum_nonneg fun job _ ↦ by linarith [hp0 job]
  have hsumSubset : (∑ job : ↥remaining, (1 + processing job)) ≤
      ∑ job : Fin n, (1 + processing job) := by
    have hsumEq : (∑ job : ↥remaining, (1 + processing job)) =
        ∑ job ∈ remaining, (1 + processing job) := by
      symm
      apply Finset.sum_subtype
      intro job
      simp
    rw [hsumEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ remaining)
      (fun job _ _ ↦ by linarith [hp0 job])
  have hsumAll : (∑ job : Fin n, (1 + processing job)) =
      n * (1 + populationMean processing) := by
    unfold populationMean
    simp only [Fintype.card_fin, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnR]
  have hcard' : (Fintype.card ↥remaining + 1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.add_le_add_right hcard 1
  calc
    uniformAverage (randomOrderCost
        (fun job : ↥remaining ↦ 1 + processing job)) =
        (Fintype.card ↥remaining + 1 : ℝ) / 2 *
          (∑ job : ↥remaining, (1 + processing job)) :=
      uniformAverage_randomOrderCost_total
        (α := ↥remaining) (fun job ↦ 1 + processing job)
    _ ≤ (n + 1 : ℝ) / 2 *
          (∑ job : ↥remaining, (1 + processing job)) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcard' (by norm_num)) hsum0
    _ ≤ (n + 1 : ℝ) / 2 *
        ((n : ℝ) * (1 + populationMean processing)) := by
      exact mul_le_mul_of_nonneg_left
        (hsumSubset.trans_eq hsumAll) (by positivity)
    _ = (n : ℝ) * (n + 1) / 2 *
        (1 + populationMean processing) := by ring

/-- The analogous ambient bound for a raw block of any nonempty subset. -/
theorem uniformAverage_subsetRawCost_le
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (remaining : Finset (Fin n)) (hremaining : remaining.Nonempty) :
    uniformAverage (randomOrderCost (fun _job : ↥remaining ↦ u)) ≤
      n * (n + 1) / 2 * u := by
  have hcard : Fintype.card ↥remaining ≤ n := by
    rw [Fintype.card_coe]
    simpa using remaining.card_le_univ
  have hsum0 : 0 ≤ ∑ _job : ↥remaining, u := by positivity
  have hsum : (∑ _job : ↥remaining, u) ≤ n * u := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hu0
  have hcard' : (Fintype.card ↥remaining + 1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.add_le_add_right hcard 1
  calc
    uniformAverage (randomOrderCost (fun _job : ↥remaining ↦ u)) =
        (Fintype.card ↥remaining + 1 : ℝ) / 2 *
          (∑ _job : ↥remaining, u) :=
      uniformAverage_randomOrderCost_total
        (α := ↥remaining) (fun _job ↦ u)
    _ ≤ (n + 1 : ℝ) / 2 * (∑ _job : ↥remaining, u) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcard' (by norm_num)) hsum0
    _ ≤ (n + 1 : ℝ) / 2 * ((n : ℝ) * u) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (n : ℝ) * (n + 1) / 2 * u := by ring

def sampleJobs {n : ℕ} (positions : Finset (Fin n))
    (sampleOrder : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  positions.image sampleOrder

theorem sampleJobs_card {n : ℕ} (positions : Finset (Fin n))
    (sampleOrder : Equiv.Perm (Fin n)) :
    (sampleJobs positions sampleOrder).card = positions.card := by
  exact Finset.card_image_of_injective positions sampleOrder.injective

def pilotDurations {n : ℕ} (positions : Finset (Fin n))
    (processing : Fin n → ℝ) (sampleOrder : Equiv.Perm (Fin n)) : List ℝ :=
  positions.toList.map fun position ↦ 1 + processing (sampleOrder position)

/-- The empirical processing mean reconstructed solely from the completed
pilot-block durations. -/
def observedPilotMean (positions : Finset (Fin n))
    (durations : List ℝ) : ℝ :=
  (durations.map fun duration ↦ duration - 1).sum / positions.card

theorem observedPilotMean_pilotDurations
    {n : ℕ} (positions : Finset (Fin n))
    (processing : Fin n → ℝ) (sampleOrder : Equiv.Perm (Fin n)) :
    observedPilotMean positions
        (pilotDurations positions processing sampleOrder) =
      permutationSampleMean positions processing sampleOrder := by
  unfold observedPilotMean pilotDurations permutationSampleMean
  simp only [List.map_map, Function.comp_apply]
  congr 1
  rw [← List.sum_toFinset _ positions.nodup_toList]
  simp only [Finset.toList_toFinset]
  unfold permutationSampleSum
  rw [show (∑ i : ↥positions, processing (sampleOrder i.val)) =
      ∑ i ∈ positions, processing (sampleOrder i) by
    symm
    apply Finset.sum_subtype
    intro i
    simp]
  apply Finset.sum_congr rfl
  intro position hposition
  change (1 + processing (sampleOrder position)) - 1 =
    processing (sampleOrder position)
  ring

@[simp] theorem pilotDurations_length {n : ℕ}
    (positions : Finset (Fin n)) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n)) :
    (pilotDurations positions processing sampleOrder).length = positions.card := by
  simp [pilotDurations]

theorem pilotDurations_nonneg_le
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (positions : Finset (Fin n)) (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (sampleOrder : Equiv.Perm (Fin n)) :
    (∀ x ∈ pilotDurations positions processing sampleOrder, 0 ≤ x) ∧
      (pilotDurations positions processing sampleOrder).sum ≤
        positions.card * (1 + u) := by
  have hpoint : ∀ position ∈ positions,
      (0 : ℝ) ≤ 1 + processing (sampleOrder position) ∧
        1 + processing (sampleOrder position) ≤ 1 + u := by
    intro position hposition
    constructor
    · linarith [(hp (sampleOrder position)).1]
    · linarith [(hp (sampleOrder position)).2]
  constructor
  · intro x hx
    rcases List.mem_map.mp hx with ⟨position, hposition, rfl⟩
    exact (hpoint position (by simpa [pilotDurations] using hposition)).1
  · unfold pilotDurations
    rw [← List.sum_toFinset _ positions.nodup_toList]
    simp only [Finset.toList_toFinset]
    calc
      (∑ position ∈ positions, (1 + processing (sampleOrder position))) ≤
          ∑ _position ∈ positions, (1 + u) :=
        Finset.sum_le_sum fun position hposition ↦ (hpoint position hposition).2
      _ = positions.card * (1 + u) := by simp; ring

theorem prefixCost_le_length_mul_sum
    (values : List ℝ) (hvalues : ∀ x ∈ values, 0 ≤ x) :
    prefixCost values ≤ values.length * values.sum := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hvalues x (by simp)
      have hxs : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hvalues y (by simp [hy])
      have htail := ih hxs
      simp only [prefixCost_cons, List.length_cons, List.sum_cons]
      push_cast
      have hsum : 0 ≤ xs.sum := List.sum_nonneg hxs
      nlinarith

def pilotUsesOptimized {n : ℕ} (positions : Finset (Fin n))
    (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n)) : Bool :=
  decide (1 + permutationSampleMean positions processing sampleOrder < u)

/-- Consequently the main-mode decision is measurable from the public cap
and the literal pilot completion history. -/
theorem pilotUsesOptimized_eq_observed
    {n : ℕ} (positions : Finset (Fin n)) (u : ℝ)
    (processing : Fin n → ℝ) (sampleOrder : Equiv.Perm (Fin n)) :
    pilotUsesOptimized positions u processing sampleOrder =
      decide (1 + observedPilotMean positions
        (pilotDurations positions processing sampleOrder) < u) := by
  unfold pilotUsesOptimized
  rw [observedPilotMean_pilotDurations]

def pilotMainCost {n : ℕ} (positions : Finset (Fin n))
    (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) : ℝ :=
  let pilot := pilotDurations positions processing sampleOrder
  let duration : ↥(sampleJobs positions sampleOrder)ᶜ → ℝ :=
    if pilotUsesOptimized positions u processing sampleOrder then
      fun job ↦ 1 + processing job
    else fun _job ↦ u
  prefixCost (pilot ++ randomOrderValues duration mainOrder)

def conditionalExpectedPilotCost {n : ℕ}
    (positions : Finset (Fin n)) (hproper : positions.card < n)
    (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n)) : ℝ := by
  let Rest := ↥(sampleJobs positions sampleOrder)ᶜ
  have hcardRest : 0 < Fintype.card Rest := by
    dsimp [Rest]
    rw [Fintype.card_coe, Finset.card_compl, sampleJobs_card,
      Fintype.card_fin]
    omega
  letI : Nonempty Rest := Fintype.card_pos_iff.mp hcardRest
  exact uniformAverage (fun mainOrder : Equiv.Perm Rest ↦
    pilotMainCost positions u processing sampleOrder mainOrder)

/-- Conditional on the pilot order (hence on the sampled set and estimate),
the independent main order is bounded by the finite pilot envelope. -/
theorem conditionalExpectedPilotCost_le_envelope
    {n : ℕ} {u : ℝ} (hu0 : 0 ≤ u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (hproper : positions.card < n)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (sampleOrder : Equiv.Perm (Fin n)) :
    conditionalExpectedPilotCost positions hproper u processing sampleOrder ≤
      pilotScheduleEnvelope n positions.card u (populationMean processing)
        (permutationSampleMean positions processing sampleOrder) := by
  classical
  let sample := sampleJobs positions sampleOrder
  let Rest := ↥sampleᶜ
  let pilot := pilotDurations positions processing sampleOrder
  let learned := learnedBlockLength u (populationMean processing)
    (permutationSampleMean positions processing sampleOrder)
  let duration : Rest → ℝ :=
    if pilotUsesOptimized positions u processing sampleOrder then
      fun job ↦ 1 + processing job
    else fun _job ↦ u
  have hsampleCard : sample.card = positions.card := by
    exact sampleJobs_card positions sampleOrder
  have hrestCard : Fintype.card Rest = n - positions.card := by
    dsimp [Rest, sample]
    rw [Fintype.card_coe, Finset.card_compl, hsampleCard, Fintype.card_fin]
  have hrestPos : 0 < Fintype.card Rest := by rw [hrestCard]; omega
  letI : Nonempty Rest := Fintype.card_pos_iff.mp hrestPos
  have hcardSum : positions.card + Fintype.card Rest = n := by
    rw [hrestCard]
    omega
  have hpilotBounds := pilotDurations_nonneg_le hu0 positions processing hp
    sampleOrder
  have hpilotNonneg : ∀ x ∈ pilot, 0 ≤ x := by
    simpa [pilot] using hpilotBounds.1
  have hpilotSum : pilot.sum ≤ positions.card * (1 + u) := by
    simpa [pilot] using hpilotBounds.2
  have hpilotSum0 : 0 ≤ pilot.sum := List.sum_nonneg hpilotNonneg
  have hpilotPrefix := prefixCost_le_length_mul_sum pilot hpilotNonneg
  rw [show pilot.length = positions.card by simp [pilot]] at hpilotPrefix
  have hpilotOverhead :
      prefixCost pilot + Fintype.card Rest * pilot.sum ≤
        (1 + u) * positions.card * n := by
    have hfirst : prefixCost pilot + Fintype.card Rest * pilot.sum ≤
        (positions.card + Fintype.card Rest : ℕ) * pilot.sum := by
      push_cast
      nlinarith
    rw [hcardSum] at hfirst
    have hsecond : (n : ℝ) * pilot.sum ≤
        n * (positions.card * (1 + u)) :=
      mul_le_mul_of_nonneg_left hpilotSum (by positivity)
    calc
      prefixCost pilot + Fintype.card Rest * pilot.sum ≤
          (n : ℝ) * pilot.sum := hfirst
      _ ≤ (n : ℝ) * (positions.card * (1 + u)) := hsecond
      _ = (1 + u) * positions.card * n := by ring
  have hcostPoint : ∀ mainOrder : Equiv.Perm Rest,
      pilotMainCost positions u processing sampleOrder mainOrder =
        prefixCost pilot + Fintype.card Rest * pilot.sum +
          randomOrderCost duration mainOrder := by
    intro mainOrder
    unfold pilotMainCost randomOrderCost
    dsimp [pilot, duration, Rest, sample]
    rw [prefixCost_append]
    simp
  have hconditionalEq :
      conditionalExpectedPilotCost positions hproper u processing sampleOrder =
        prefixCost pilot + Fintype.card Rest * pilot.sum +
          uniformAverage (randomOrderCost duration) := by
    unfold conditionalExpectedPilotCost
    dsimp only
    rw [show (fun mainOrder : Equiv.Perm Rest ↦
        pilotMainCost positions u processing sampleOrder mainOrder) =
      (fun mainOrder ↦
        (prefixCost pilot + Fintype.card Rest * pilot.sum) +
          randomOrderCost duration mainOrder) by
        funext mainOrder
        exact hcostPoint mainOrder,
      uniformAverage_add, uniformAverage_const]
  have hmainAverage : uniformAverage (randomOrderCost duration) ≤
      n * (n + 1) / 2 * learned := by
    have hn0 : 0 < n := by omega
    have hremaining : sampleᶜ.Nonempty := by
      apply Finset.card_pos.mp
      have : 0 < (sampleᶜ).card := by
        rw [← Fintype.card_coe]
        exact hrestPos
      exact this
    by_cases hoptimized :
        pilotUsesOptimized positions u processing sampleOrder = true
    · have hcondition : 1 + permutationSampleMean positions processing
          sampleOrder < u := by
        simpa [pilotUsesOptimized] using hoptimized
      have hlearned : learned = 1 + populationMean processing := by
        simp [learned, learnedBlockLength, hcondition]
      simpa [duration, Rest, hoptimized, hlearned] using
        uniformAverage_subsetOptimizedCost_le hn0 processing
          (fun job ↦ (hp job).1) sampleᶜ hremaining
    · have hcondition : ¬(1 + permutationSampleMean positions processing
          sampleOrder < u) := by
        simpa [pilotUsesOptimized] using hoptimized
      have hlearned : learned = u := by
        simp [learned, learnedBlockLength, hcondition]
      simpa [duration, Rest, hoptimized, hlearned] using
        uniformAverage_subsetRawCost_le hu0 sampleᶜ hremaining
  rw [hconditionalEq]
  unfold pilotScheduleEnvelope
  nlinarith

/-- Averaging also over the pilot permutation gives the finite universal
sample-then-commit upper bound. -/
theorem pilotPolicy_expectedCost_le
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (hproper : positions.card < n) :
    uniformAverage (fun sampleOrder : Equiv.Perm (Fin n) ↦
      conditionalExpectedPilotCost positions hproper u processing sampleOrder) ≤
      n * (n + 1) / 2 *
          min u (1 + populationMean processing) +
        (1 + u) * positions.card * n +
        n * (n + 1) / 2 *
          (u / Real.sqrt positions.card) := by
  have hpoint : ∀ sampleOrder : Equiv.Perm (Fin n),
      conditionalExpectedPilotCost positions hproper u processing sampleOrder ≤
        pilotScheduleEnvelope n positions.card u (populationMean processing)
          (permutationSampleMean positions processing sampleOrder) :=
    conditionalExpectedPilotCost_le_envelope hu0 positions hpositions hproper
      processing hp
  exact (uniformAverage_mono hpoint).trans
    (pilotScheduleEnvelope_expected_le hn hu0 processing hp positions hpositions)

/-- The ordered-pair leading term of the exact clairvoyant finite optimum is
always a lower bound on that optimum; the omitted diagonal is nonnegative. -/
theorem empiricalOfflinePair_leading_le_offlineCost
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu0 : 0 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u) :
    (n : ℝ) ^ 2 / 2 * empiricalOfflinePair u processing ≤
      Online.offlineCost u processing := by
  let offlinePair := empiricalOfflinePair u processing
  have hoffline :
      Online.offlineCost u processing =
        (n : ℝ) ^ 2 / 2 * offlinePair +
          (∑ job, Online.effectiveLength u (processing job)) / 2 := by
    unfold Online.offlineCost
    have htwo := two_mul_pairCost_ofFn
      (fun job : Fin n ↦ Online.effectiveLength u (processing job))
    dsimp [empiricalOfflinePair, offlinePair]
    simp only [Fintype.card_fin]
    simp_rw [onlineEffective_eq_distributionEffective] at htwo ⊢
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnreal] at htwo ⊢
    linarith
  rw [hoffline]
  apply le_add_of_nonneg_right
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro job _
    unfold Online.effectiveLength
    exact le_min hu0 (by linarith [(hp job).1])
  · norm_num

/-- Finite randomized blind-optimization curve upper bound.  The leading
term is exactly `randomizedCurve u · OPT`; all remaining terms are explicit
and become `o_u(n²)` for any pilot size `k→∞`, `k=o(n)`. -/
theorem pilotPolicy_expectedCost_le_curve
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 1 < u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (hproper : positions.card < n) :
    uniformAverage (fun sampleOrder : Equiv.Perm (Fin n) ↦
      conditionalExpectedPilotCost positions hproper u processing sampleOrder) ≤
      randomizedCurve u * Online.offlineCost u processing +
        (1 + u) * positions.card * n +
        n * (n + 1) / 2 * (u / Real.sqrt positions.card) +
        n * u / 2 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hu0 : 0 ≤ u := by linarith
  have hpilot := pilotPolicy_expectedCost_le hn hu0 processing hp
    positions hpositions hproper
  have hmean := empiricalMean_mem_Icc processing hu0 hp
  have hbest0 : 0 ≤ min u (1 + populationMean processing) := by
    have hmeans : populationMean processing = empiricalMean processing := by
      rfl
    rw [hmeans]
    exact le_min hu0 (by linarith [hmean.1])
  have hoffLower := empiricalOfflinePair_ge_mean_square processing hu hp
  have hbase : 0 < 1 + (u - 1) * (empiricalMean processing / u) ^ 2 := by
    have : 0 ≤ (u - 1) * (empiricalMean processing / u) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hoffPos : 0 < empiricalOfflinePair u processing :=
    hbase.trans_le hoffLower
  have hratio := randomizedDistributionRatio_le_curve processing hu hp
  have hbestCurve : min u (1 + populationMean processing) ≤
      randomizedCurve u * empiricalOfflinePair u processing := by
    have hmeans : populationMean processing = empiricalMean processing := rfl
    rw [hmeans]
    unfold randomizedDistributionRatio at hratio
    exact (div_le_iff₀ hoffPos).mp hratio
  have hcurve0 : 0 ≤ randomizedCurve u := by
    have hratio0 : 0 ≤ randomizedDistributionRatio u processing := by
      unfold randomizedDistributionRatio
      exact div_nonneg hbest0 hoffPos.le
    exact hratio0.trans hratio
  have hoffline := empiricalOfflinePair_leading_le_offlineCost
    (by omega) hu0 processing hp
  have hleading :
      (n : ℝ) * (n + 1) / 2 *
          min u (1 + populationMean processing) ≤
        randomizedCurve u * Online.offlineCost u processing + n * u / 2 := by
    have hminu : min u (1 + populationMean processing) ≤ u := min_le_left _ _
    calc
      (n : ℝ) * (n + 1) / 2 *
          min u (1 + populationMean processing) =
          (n : ℝ) ^ 2 / 2 * min u (1 + populationMean processing) +
            n / 2 * min u (1 + populationMean processing) := by ring
      _ ≤ (n : ℝ) ^ 2 / 2 *
            (randomizedCurve u * empiricalOfflinePair u processing) +
            n / 2 * u := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hbestCurve (by positivity))
            (mul_le_mul_of_nonneg_left hminu (by positivity))
      _ = randomizedCurve u *
            ((n : ℝ) ^ 2 / 2 * empiricalOfflinePair u processing) +
            n * u / 2 := by ring
      _ ≤ randomizedCurve u * Online.offlineCost u processing +
            n * u / 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hoffline hcurve0) le_rfl
  linarith

/-- The normalized finite remainder in
`pilotPolicy_expectedCost_le_curve`. -/
def pilotNormalizedError (u : ℝ) (n k : ℕ) : ℝ :=
  (1 + u) * k / n +
    ((n + 1 : ℝ) / (2 * n)) * (u / Real.sqrt k) +
    u / (2 * n)

theorem pilotPolicy_expectedCost_le_curve_normalized
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 1 < u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (hproper : positions.card < n) :
    uniformAverage (fun sampleOrder : Equiv.Perm (Fin n) ↦
      conditionalExpectedPilotCost positions hproper u processing sampleOrder) ≤
      randomizedCurve u * Online.offlineCost u processing +
        pilotNormalizedError u n positions.card * n ^ 2 := by
  have hfinite := pilotPolicy_expectedCost_le_curve hn hu processing hp
    positions hpositions hproper
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold pilotNormalizedError
  convert hfinite using 1 <;> field_simp [hnR] <;> ring

/-- Any growing sublinear pilot size makes the checked finite remainder
vanish.  This is the abstract rate statement used by the instance-optimal
and competitive-ratio asymptotics. -/
theorem pilotNormalizedError_tendsto_zero
    {u : ℝ} (hu0 : 0 ≤ u) (pilotSize : ℕ → ℕ)
    (hgrows : Filter.Tendsto pilotSize Filter.atTop Filter.atTop)
    (hsublinear : Filter.Tendsto
      (fun n : ℕ ↦ (pilotSize n : ℝ) / n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ pilotNormalizedError u n (pilotSize n))
      Filter.atTop (nhds 0) := by
  have hfirst : Filter.Tendsto
      (fun n : ℕ ↦ (1 + u) * ((pilotSize n : ℝ) / n))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsublinear)
  have hpReal : Filter.Tendsto (fun n : ℕ ↦ (pilotSize n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hgrows
  have hsqrtTop : Filter.Tendsto
      (fun n : ℕ ↦ Real.sqrt (pilotSize n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hpReal
  have hinvSqrt : Filter.Tendsto
      (fun n : ℕ ↦ u / Real.sqrt (pilotSize n : ℝ))
      Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto
        (fun n : ℕ ↦ (Real.sqrt (pilotSize n : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hsqrtTop
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  have hreciprocal : Filter.Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / (2 * n))
      Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun n : ℕ ↦ (2 * n : ℝ))
        Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        (tendsto_natCast_atTop_atTop : Filter.Tendsto
          (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
    exact Filter.Tendsto.const_div_atTop hden 1
  have hfactor : Filter.Tendsto
      (fun n : ℕ ↦ (n + 1 : ℝ) / (2 * n))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hsum := (tendsto_const_nhds : Filter.Tendsto
      (fun _n : ℕ ↦ (1 / 2 : ℝ)) Filter.atTop (nhds (1 / 2))).add
        hreciprocal
    have hsum' : Filter.Tendsto
        (fun n : ℕ ↦ (1 / 2 : ℝ) + 1 / (2 * n))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by simpa using hsum
    apply hsum'.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp [hnR]
  have hsecond : Filter.Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℝ) / (2 * n)) *
        (u / Real.sqrt (pilotSize n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hfactor.mul hinvSqrt
  have hthird : Filter.Tendsto
      (fun n : ℕ ↦ u / (2 * n : ℝ))
      Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun n : ℕ ↦ (2 * n : ℝ))
        Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        (tendsto_natCast_atTop_atTop : Filter.Tendsto
          (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
    exact Filter.Tendsto.const_div_atTop hden u
  unfold pilotNormalizedError
  simpa [mul_div_assoc] using (hfirst.add hsecond).add hthird

end


end BlindOptimization
end SchedulingPaper
