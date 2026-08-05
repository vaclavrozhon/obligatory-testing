import SchedulingPaper.ObligatoryPairAccounting

/-!
# Endpoint reduction for a fixed AdaptiveThreshold decision word

The coordinatewise-convexity theorem in `ObligatoryPairAccounting` handles
bounded immediate coordinates.  Deferred coordinates have an even simpler
property: lowering any collection of them can only increase the competitive
excess.  This file supplies that missing unbounded-coordinate argument and
packages the two facts into a closed-box reduction in which every deferred
coordinate has already been moved to its live threshold.
-/

namespace SchedulingPaper

noncomputable section

open Set

/-- `reduced` is obtained from `processing` solely by weakly lowering
coordinates whose symbolic decision is `deferred`. -/
def IsDeferredLowering {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (processing reduced : Fin n → ℝ) : Prop :=
  (∀ i, reduced i ≤ processing i) ∧
  (∀ i, outcome i ≠ .deferred → reduced i = processing i)

theorem obligatorySelfExcessAt_antitone
    {p q : ℝ} (hpq : q ≤ p) :
    obligatorySelfExcessAt p ≤ obligatorySelfExcessAt q := by
  unfold obligatorySelfExcessAt RStar
  nlinarith [mul_nonneg rhoStar_pos.le (sub_nonneg.mpr hpq)]

/-- A pair excess can only increase when values are lowered exclusively at
deferred coordinates. -/
theorem obligatoryPairExcessAt_le_of_deferredLowering
    {left right : BoundaryOutcome}
    {p q p' q' : ℝ}
    (hp : p' ≤ p) (hq : q' ≤ q)
    (hpEq : left ≠ .deferred → p' = p)
    (hqEq : right ≠ .deferred → q' = q) :
    obligatoryPairExcessAt left right p q ≤
      obligatoryPairExcessAt left right p' q' := by
  have hmin : min p' q' ≤ min p q :=
    min_le_min hp hq
  have hR : 0 ≤ RStar :=
    (lt_trans zero_lt_one one_lt_RStar).le
  cases left with
  | zero =>
      have hp' := hpEq (by simp)
      subst p'
      cases right <;>
        simp only [obligatoryPairExcessAt,
          obligatoryALGPairCharge, obligatoryOPTPairCharge] at hmin ⊢ <;>
        nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
  | epsilon =>
      have hp' := hpEq (by simp)
      subst p'
      cases right <;>
        simp only [obligatoryPairExcessAt,
          obligatoryALGPairCharge, obligatoryOPTPairCharge] at hmin ⊢ <;>
        nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
  | immediate =>
      have hp' := hpEq (by simp)
      subst p'
      cases right <;>
        simp only [obligatoryPairExcessAt,
          obligatoryALGPairCharge, obligatoryOPTPairCharge] at hmin ⊢ <;>
        nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
  | deferred =>
      cases right with
      | zero =>
          have hq' := hqEq (by simp)
          subst q'
          simp only [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
      | epsilon =>
          have hq' := hqEq (by simp)
          subst q'
          simp only [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
      | immediate =>
          have hq' := hqEq (by simp)
          subst q'
          simp only [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          nlinarith [mul_nonneg hR (sub_nonneg.mpr hmin)]
      | deferred =>
          simp only [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          unfold RStar
          nlinarith [mul_nonneg rhoStar_pos.le
            (sub_nonneg.mpr hmin)]

/-- Simultaneously lowering an arbitrary set of deferred values weakly
increases the exact fixed-word excess. -/
theorem obligatoryFixedWordExcess_le_of_deferredLowering
    {n : ℕ} {outcome : Fin n → BoundaryOutcome}
    {processing reduced : Fin n → ℝ}
    (h : IsDeferredLowering outcome processing reduced) :
    obligatoryFixedWordExcess outcome processing ≤
      obligatoryFixedWordExcess outcome reduced := by
  classical
  unfold obligatoryFixedWordExcess
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _hi
    exact obligatorySelfExcessAt_antitone (h.1 i)
  · apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j hj
    exact obligatoryPairExcessAt_le_of_deferredLowering
      (h.1 i) (h.1 j) (h.2 i) (h.2 j)

/-- Replace every deferred coordinate by its prescribed live threshold. -/
def lowerDeferredCoordinates {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (threshold processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if outcome i = .deferred then threshold i else processing i

theorem lowerDeferredCoordinates_isDeferredLowering
    {n : ℕ} {outcome : Fin n → BoundaryOutcome}
    {threshold processing : Fin n → ℝ}
    (hdeferred :
      ∀ i, outcome i = .deferred → threshold i ≤ processing i) :
    IsDeferredLowering outcome processing
      (lowerDeferredCoordinates outcome threshold processing) := by
  constructor
  · intro i
    unfold lowerDeferredCoordinates
    split_ifs with hi
    · exact hdeferred i hi
    · exact le_rfl
  · intro i hi
    simp [lowerDeferredCoordinates, hi]

/-- The compact box left after deferred coordinates have been lowered.
Zeros and deferred coordinates are singletons; a positive-immediate
coordinate ranges from its one-sided zero endpoint to its live threshold. -/
def obligatoryReducedLower {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (threshold : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    match outcome i with
    | .zero | .epsilon | .immediate => 0
    | .deferred => threshold i

def obligatoryReducedUpper {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (threshold : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    match outcome i with
    | .zero | .epsilon => 0
    | .immediate | .deferred => threshold i

theorem obligatoryReducedLower_le_upper
    {n : ℕ} {outcome : Fin n → BoundaryOutcome}
    {threshold : Fin n → ℝ}
    (hthreshold : ∀ i, 0 ≤ threshold i) :
    ∀ i,
      obligatoryReducedLower outcome threshold i ≤
        obligatoryReducedUpper outcome threshold i := by
  intro i
  cases h : outcome i <;>
    simp [obligatoryReducedLower, obligatoryReducedUpper, h,
      hthreshold i]

/-- Closed-box endpoint reduction after the unbounded deferred directions
have been discharged. -/
theorem exists_obligatory_reduced_endpoint_ge
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (threshold processing : Fin n → ℝ)
    (hthreshold : ∀ i, 0 ≤ threshold i)
    (hzero :
      ∀ i, outcome i = .zero ∨ outcome i = .epsilon →
        processing i = 0)
    (himmediate :
      ∀ i, outcome i = .immediate →
        0 ≤ processing i ∧ processing i ≤ threshold i)
    (hdeferred :
      ∀ i, outcome i = .deferred →
        threshold i ≤ processing i) :
    ∃ vertex,
      vertex ∈ coordinateBox
        (obligatoryReducedLower outcome threshold)
        (obligatoryReducedUpper outcome threshold) ∧
      IsBoxVertex
        (obligatoryReducedLower outcome threshold)
        (obligatoryReducedUpper outcome threshold) vertex ∧
      obligatoryFixedWordExcess outcome processing ≤
        obligatoryFixedWordExcess outcome vertex := by
  let reduced :=
    lowerDeferredCoordinates outcome threshold processing
  have hlower :
      IsDeferredLowering outcome processing reduced :=
    lowerDeferredCoordinates_isDeferredLowering hdeferred
  have hfirst :
      obligatoryFixedWordExcess outcome processing ≤
        obligatoryFixedWordExcess outcome reduced :=
    obligatoryFixedWordExcess_le_of_deferredLowering hlower
  have hbox :
      reduced ∈ coordinateBox
        (obligatoryReducedLower outcome threshold)
        (obligatoryReducedUpper outcome threshold) := by
    intro i
    cases hi : outcome i with
    | zero =>
        have hp := hzero i (Or.inl hi)
        simp [reduced, lowerDeferredCoordinates,
          obligatoryReducedLower, obligatoryReducedUpper, hi, hp]
    | epsilon =>
        have hp := hzero i (Or.inr hi)
        simp [reduced, lowerDeferredCoordinates,
          obligatoryReducedLower, obligatoryReducedUpper, hi, hp]
    | immediate =>
        have hp := himmediate i hi
        simpa [reduced, lowerDeferredCoordinates,
          obligatoryReducedLower, obligatoryReducedUpper, hi] using hp
    | deferred =>
        simp [reduced, lowerDeferredCoordinates,
          obligatoryReducedLower, obligatoryReducedUpper, hi]
  obtain ⟨vertex, hvbox, hvvertex, hvge⟩ :=
    exists_obligatoryFixedWord_endpoint_ge outcome
      (obligatoryReducedLower outcome threshold)
      (obligatoryReducedUpper outcome threshold)
      reduced
      (obligatoryReducedLower_le_upper hthreshold)
      hbox
  exact ⟨vertex, hvbox, hvvertex, hfirst.trans hvge⟩

/-! ## Finite-vector and recursive-list normal forms -/

def obligatoryJobsOfFunctions {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : List ObligatoryBoundaryJob :=
  List.ofFn fun i => ⟨outcome i, processing i⟩

private theorem obligatory_pair_rows_ofFn
    {n : ℕ} (outcome : Fin (n + 1) → BoundaryOutcome)
    (processing : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1),
      ∑ j ∈ Finset.univ.filter (fun j => i < j),
        obligatoryPairExcessAt
          (outcome i) (outcome j) (processing i) (processing j)) =
      (∑ j : Fin n,
        obligatoryPairExcessAt
          (outcome 0) (outcome j.succ)
          (processing 0) (processing j.succ)) +
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        obligatoryPairExcessAt
          (outcome i.succ) (outcome j.succ)
          (processing i.succ) (processing j.succ) := by
  rw [Fin.sum_univ_succ]
  congr 1
  · classical
    simp_rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp
  · apply Finset.sum_congr rfl
    intro i _hi
    classical
    simp_rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp

/-- The `Finset` fixed-word excess is exactly the difference of the two
recursive literal pair objectives on the corresponding job list. -/
theorem obligatoryFixedWordExcess_eq_pairObjectives
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) :
    obligatoryFixedWordExcess outcome processing =
      obligatoryALGPairObjective
          (obligatoryJobsOfFunctions outcome processing) -
        RStar *
          obligatoryOPTPairObjective
            (obligatoryJobsOfFunctions outcome processing) := by
  induction n with
  | zero =>
      simp [obligatoryFixedWordExcess,
        obligatoryJobsOfFunctions,
        obligatoryALGPairObjective,
        obligatoryOPTPairObjective]
  | succ n ih =>
      let tailOutcome : Fin n → BoundaryOutcome :=
        fun i => outcome i.succ
      let tailProcessing : Fin n → ℝ :=
        fun i => processing i.succ
      have htail := ih tailOutcome tailProcessing
      rw [obligatoryFixedWordExcess]
      rw [Fin.sum_univ_succ]
      rw [obligatory_pair_rows_ofFn]
      rw [show obligatoryJobsOfFunctions outcome processing =
          ⟨outcome 0, processing 0⟩ ::
            obligatoryJobsOfFunctions tailOutcome tailProcessing by
        simp [obligatoryJobsOfFunctions, tailOutcome, tailProcessing,
          List.ofFn_succ]]
      simp only [obligatoryALGPairObjective,
        obligatoryOPTPairObjective]
      have htailExpanded :
          (∑ i : Fin n,
              obligatorySelfExcessAt (tailProcessing i)) +
              ∑ i : Fin n,
                ∑ j ∈ Finset.univ.filter (fun j => i < j),
                  obligatoryPairExcessAt
                    (tailOutcome i) (tailOutcome j)
                    (tailProcessing i) (tailProcessing j) =
            obligatoryALGPairObjective
                (obligatoryJobsOfFunctions tailOutcome tailProcessing) -
              RStar *
                obligatoryOPTPairObjective
                  (obligatoryJobsOfFunctions
                    tailOutcome tailProcessing) := by
        rw [← htail]
        rfl
      have hALGRow :
          (List.map
            (obligatoryALGPairCharge
              ⟨outcome 0, processing 0⟩)
            (obligatoryJobsOfFunctions
              tailOutcome tailProcessing)).sum =
            ∑ j : Fin n,
              obligatoryALGPairCharge
                ⟨outcome 0, processing 0⟩
                ⟨tailOutcome j, tailProcessing j⟩ := by
        unfold obligatoryJobsOfFunctions
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      have hOPTRow :
          (List.map
            (obligatoryOPTPairCharge
              ⟨outcome 0, processing 0⟩)
            (obligatoryJobsOfFunctions
              tailOutcome tailProcessing)).sum =
            ∑ j : Fin n,
              obligatoryOPTPairCharge
                ⟨outcome 0, processing 0⟩
                ⟨tailOutcome j, tailProcessing j⟩ := by
        unfold obligatoryJobsOfFunctions
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      rw [hALGRow, hOPTRow]
      change
        obligatorySelfExcessAt (processing 0) +
            (∑ i : Fin n,
              obligatorySelfExcessAt (tailProcessing i)) +
            ((∑ j : Fin n,
              obligatoryPairExcessAt
                (outcome 0) (tailOutcome j)
                (processing 0) (tailProcessing j)) +
              ∑ i : Fin n,
                ∑ j ∈ Finset.univ.filter (fun j => i < j),
                  obligatoryPairExcessAt
                    (tailOutcome i) (tailOutcome j)
                    (tailProcessing i) (tailProcessing j)) =
          1 + processing 0 +
              (∑ j : Fin n,
                obligatoryALGPairCharge
                  ⟨outcome 0, processing 0⟩
                  ⟨tailOutcome j, tailProcessing j⟩) +
              obligatoryALGPairObjective
                (obligatoryJobsOfFunctions tailOutcome tailProcessing) -
            RStar *
              (1 + processing 0 +
                (∑ j : Fin n,
                  obligatoryOPTPairCharge
                    ⟨outcome 0, processing 0⟩
                    ⟨tailOutcome j, tailProcessing j⟩) +
                obligatoryOPTPairObjective
                  (obligatoryJobsOfFunctions
                    tailOutcome tailProcessing))
      have hPairRow :
          (∑ j : Fin n,
              obligatoryPairExcessAt
                (outcome 0) (tailOutcome j)
                (processing 0) (tailProcessing j)) =
            (∑ j : Fin n,
              obligatoryALGPairCharge
                ⟨outcome 0, processing 0⟩
                ⟨tailOutcome j, tailProcessing j⟩) -
              RStar *
                ∑ j : Fin n,
                  obligatoryOPTPairCharge
                    ⟨outcome 0, processing 0⟩
                    ⟨tailOutcome j, tailProcessing j⟩ := by
        simp only [obligatoryPairExcessAt,
          Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hPairRow]
      simp only [obligatorySelfExcessAt,
        obligatoryPairExcessAt] at htailExpanded
      unfold obligatorySelfExcessAt obligatoryPairExcessAt
      linear_combination htailExpanded

end

end SchedulingPaper
