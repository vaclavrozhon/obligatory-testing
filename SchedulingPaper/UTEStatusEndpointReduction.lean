import SchedulingPaper.UTERuntimeEndpoint
import Mathlib.Tactic

/-!
# Endpoint reduction for the frozen UTE status word

For `s ≥ 1`, forced-prefix and suffix-immediate coordinates have the usual
coordinatewise convex endpoint reductions.  Deferred coordinates need the
two-stage argument from the paper: values in `[s,s+1]` are first raised to
the cap, and the remaining values lie in `[1,s]`, where the coefficient of
the concave minimum is `1 - uteRho s < 0`.
-/

namespace SchedulingPaper

noncomputable section

open Set

private theorem convexOn_singleton_any (f : ℝ → ℝ) (x : ℝ) :
    ConvexOn ℝ ({x} : Set ℝ) f := by
  have hconst :
      EqOn f (fun _ : ℝ => f x) ({x} : Set ℝ) := by
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    rfl
  exact
    (convexOn_const (𝕜 := ℝ) (β := ℝ) (f x)
      (convex_singleton x)).congr hconst.symm

theorem uteStatusPairExcess_convex_left_immediate
    {s : ℝ} (hs : 0 < s)
    {leftOutcome : BoundaryOutcome}
    (hleft : leftOutcome ≠ .deferred)
    (rightOutcome : BoundaryOutcome) (q : ℝ) :
    ConvexOn ℝ univ
      (fun p =>
        uteStatusPairExcess s leftOutcome rightOutcome p q) := by
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  have h :=
    convexOn_affine_sub_mul_min
      1 (1 - uteRho s) (uteRho s)
        (uteEffectiveAt s q - 1) hrho
  refine h.congr ?_
  intro p _hp
  change
    1 * p + (1 - uteRho s) -
        uteRho s * min p (uteEffectiveAt s q - 1) =
      uteStatusPairExcess s leftOutcome rightOutcome p q
  unfold uteStatusPairExcess
  rw [uteFixedOPTPairCharge_eq_leftMin]
  cases leftOutcome <;>
    simp [obligatoryALGPairCharge] at hleft ⊢ <;>
    ring

theorem uteStatusPairExcess_convex_right_immediate
    {s : ℝ} (hs : 0 < s)
    (leftOutcome : BoundaryOutcome)
    {rightOutcome : BoundaryOutcome}
    (hright : rightOutcome ≠ .deferred)
    (p : ℝ) :
    ConvexOn ℝ univ
      (fun q =>
        uteStatusPairExcess s leftOutcome rightOutcome p q) := by
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  cases leftOutcome with
  | zero | epsilon | immediate =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - uteRho s) (uteRho s)
            (uteEffectiveAt s p - 1) hrho
      refine h.congr ?_
      intro q _hq
      change
        0 * q + (1 + p - uteRho s) -
            uteRho s * min q (uteEffectiveAt s p - 1) =
          uteStatusPairExcess s _ rightOutcome p q
      unfold uteStatusPairExcess
      rw [uteFixedOPTPairCharge_eq_rightMin]
      simp [obligatoryALGPairCharge]
      ring
  | deferred =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (2 - uteRho s) (uteRho s)
            (uteEffectiveAt s p - 1) hrho
      refine h.congr ?_
      intro q _hq
      change
        1 * q + (2 - uteRho s) -
            uteRho s * min q (uteEffectiveAt s p - 1) =
          uteStatusPairExcess s .deferred rightOutcome p q
      unfold uteStatusPairExcess
      rw [uteFixedOPTPairCharge_eq_rightMin]
      cases rightOutcome <;>
        simp [obligatoryALGPairCharge] at hright ⊢ <;>
        ring

theorem uteStatusPairExcess_convex_left_deferred_right_immediate
    {s : ℝ} (hs : 0 < s)
    {rightOutcome : BoundaryOutcome}
    (hright : rightOutcome ≠ .deferred) (q : ℝ) :
    ConvexOn ℝ univ
      (fun p =>
        uteStatusPairExcess s .deferred rightOutcome p q) := by
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  have h :=
    convexOn_affine_sub_mul_min
      0 (2 + q - uteRho s) (uteRho s)
        (uteEffectiveAt s q - 1) hrho
  refine h.congr ?_
  intro p _hp
  change
    0 * p + (2 + q - uteRho s) -
        uteRho s * min p (uteEffectiveAt s q - 1) =
      uteStatusPairExcess s .deferred rightOutcome p q
  unfold uteStatusPairExcess
  rw [uteFixedOPTPairCharge_eq_leftMin]
  cases rightOutcome <;>
    simp [obligatoryALGPairCharge] at hright ⊢ <;>
    ring

theorem uteStatusPairExcess_convex_right_deferred_left_immediate
    {s : ℝ} (hs : 0 < s)
    {leftOutcome : BoundaryOutcome}
    (hleft : leftOutcome ≠ .deferred) (p : ℝ) :
    ConvexOn ℝ univ
      (fun q =>
        uteStatusPairExcess s leftOutcome .deferred p q) := by
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  have h :=
    convexOn_affine_sub_mul_min
      0 (1 + p - uteRho s) (uteRho s)
        (uteEffectiveAt s p - 1) hrho
  refine h.congr ?_
  intro q _hq
  change
    0 * q + (1 + p - uteRho s) -
        uteRho s * min q (uteEffectiveAt s p - 1) =
      uteStatusPairExcess s leftOutcome .deferred p q
  unfold uteStatusPairExcess
  rw [uteFixedOPTPairCharge_eq_rightMin]
  cases leftOutcome <;>
    simp [obligatoryALGPairCharge] at hleft ⊢ <;>
    ring

private theorem uteStatusPairExcess_deferred_eq_lowMin
    {s p q : ℝ} (hp : p ≤ s) (hq : q ≤ s) :
    uteStatusPairExcess s .deferred .deferred p q =
      (2 - uteRho s) -
        (uteRho s - 1) * min p q := by
  have heffp :
      uteEffectiveAt s p = 1 + p := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_left hp]
  have heffq :
      uteEffectiveAt s q = 1 + q := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_left hq]
  unfold uteStatusPairExcess obligatoryALGPairCharge
    uteFixedOPTPairCharge
  rw [heffp, heffq, min_add_add_left]
  ring

theorem uteStatusPairExcess_convex_left_deferred_low
    {s q : ℝ} (hs : 0 < s) (hq : q ≤ s) :
    ConvexOn ℝ (Icc 1 s)
      (fun p =>
        uteStatusPairExcess s .deferred .deferred p q) := by
  have hc : 0 ≤ uteRho s - 1 := by
    linarith [uteRho_gt_one hs]
  have h :=
    convexOn_affine_sub_mul_min
      0 (2 - uteRho s) (uteRho s - 1) q hc
  have h' :=
    h.subset (subset_univ (Icc (1 : ℝ) s))
      (convex_Icc (1 : ℝ) s)
  refine h'.congr ?_
  intro p hp
  change
    0 * p + (2 - uteRho s) -
        (uteRho s - 1) * min p q =
      uteStatusPairExcess s .deferred .deferred p q
  rw [uteStatusPairExcess_deferred_eq_lowMin hp.2 hq]
  ring

theorem uteStatusPairExcess_convex_right_deferred_low
    {s p : ℝ} (hs : 0 < s) (hp : p ≤ s) :
    ConvexOn ℝ (Icc 1 s)
      (fun q =>
        uteStatusPairExcess s .deferred .deferred p q) := by
  have hc : 0 ≤ uteRho s - 1 := by
    linarith [uteRho_gt_one hs]
  have h :=
    convexOn_affine_sub_mul_min
      0 (2 - uteRho s) (uteRho s - 1) p hc
  have h' :=
    h.subset (subset_univ (Icc (1 : ℝ) s))
      (convex_Icc (1 : ℝ) s)
  refine h'.congr ?_
  intro q hq
  change
    0 * q + (2 - uteRho s) -
        (uteRho s - 1) * min q p =
      uteStatusPairExcess s .deferred .deferred p q
  rw [uteStatusPairExcess_deferred_eq_lowMin hp hq.2,
    min_comm]
  ring

theorem uteStatusPairExcess_convex_left_deferred_cap
    {s : ℝ} (hs1 : 1 ≤ s) :
    ConvexOn ℝ (Icc 1 s)
      (fun p =>
        uteStatusPairExcess s .deferred .deferred p (s + 1)) := by
  have hconv :
      ConvexOn ℝ (Icc 1 s)
        (fun p => (1 - uteRho s) * p + (2 - uteRho s)) := by
    have h :=
      convexOn_affine_sub_mul_min
        (1 - uteRho s) (2 - uteRho s) 0 0
          (le_refl (0 : ℝ))
    have h' :=
      h.subset (subset_univ (Icc (1 : ℝ) s))
        (convex_Icc (1 : ℝ) s)
    simpa using h'
  refine hconv.congr ?_
  intro p hp
  have hpu : p ≤ s + 1 := by
    have hps := hp.2
    linarith
  have heffp :
      uteEffectiveAt s p = 1 + p := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_left hp.2]
  have heffu :
      uteEffectiveAt s (s + 1) = s + 1 := by
    simp [uteEffectiveAt]
  have heffOrder : 1 + p ≤ s + 1 := by
    have hps := hp.2
    linarith
  change
    (1 - uteRho s) * p + (2 - uteRho s) =
      uteStatusPairExcess s .deferred .deferred p (s + 1)
  simp only [uteStatusPairExcess, obligatoryALGPairCharge,
    uteFixedOPTPairCharge]
  rw [min_eq_left hpu, heffp, heffu,
    min_eq_left heffOrder]
  ring

theorem uteStatusPairExcess_convex_right_deferred_cap
    {s : ℝ} (hs1 : 1 ≤ s) :
    ConvexOn ℝ (Icc 1 s)
      (fun q =>
        uteStatusPairExcess s .deferred .deferred (s + 1) q) := by
  have hconv :
      ConvexOn ℝ (Icc 1 s)
        (fun q => (1 - uteRho s) * q + (2 - uteRho s)) := by
    have h :=
      convexOn_affine_sub_mul_min
        (1 - uteRho s) (2 - uteRho s) 0 0
          (le_refl (0 : ℝ))
    have h' :=
      h.subset (subset_univ (Icc (1 : ℝ) s))
        (convex_Icc (1 : ℝ) s)
    simpa using h'
  refine hconv.congr ?_
  intro q hq
  have hqu : q ≤ s + 1 := by
    have hqs := hq.2
    linarith
  have heffq :
      uteEffectiveAt s q = 1 + q := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_left hq.2]
  have heffu :
      uteEffectiveAt s (s + 1) = s + 1 := by
    simp [uteEffectiveAt]
  have heffOrder : 1 + q ≤ s + 1 := by
    have hqs := hq.2
    linarith
  change
    (1 - uteRho s) * q + (2 - uteRho s) =
      uteStatusPairExcess s .deferred .deferred (s + 1) q
  simp only [uteStatusPairExcess, obligatoryALGPairCharge,
    uteFixedOPTPairCharge]
  rw [min_eq_right hqu, heffq, heffu,
    min_eq_right heffOrder]
  ring

/-! ## Raising the flat-offline part of a deferred coordinate -/

theorem uteFixedSelfExcessAt_le_cap_of_high
    {s p : ℝ} (hsp : s ≤ p) (hpu : p ≤ s + 1) :
    uteFixedSelfExcessAt s p ≤
      uteFixedSelfExcessAt s (s + 1) := by
  have hpmin : min p s = s := min_eq_right hsp
  have humin : min (s + 1) s = s := min_eq_right (by linarith)
  unfold uteFixedSelfExcessAt
  rw [uteEffectiveAt_eq_one_add_min,
    uteEffectiveAt_eq_one_add_min, hpmin, humin]
  linarith

theorem uteStatusPairExcess_le_raise_left_deferred
    {s p q : ℝ} (hsp : s ≤ p) (hpu : p ≤ s + 1)
    (rightOutcome : BoundaryOutcome) :
    uteStatusPairExcess s .deferred rightOutcome p q ≤
      uteStatusPairExcess s .deferred rightOutcome (s + 1) q := by
  have heffp :
      uteEffectiveAt s p = s + 1 := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_right hsp]
    ring
  have heffu :
      uteEffectiveAt s (s + 1) = s + 1 := by
    rw [uteEffectiveAt_eq_one_add_min,
      min_eq_right (by linarith)]
    ring
  cases rightOutcome with
  | zero | epsilon | immediate =>
      simp [uteStatusPairExcess, obligatoryALGPairCharge,
        uteFixedOPTPairCharge, heffp, heffu]
  | deferred =>
      have hmin : min p q ≤ min (s + 1) q :=
        min_le_min hpu le_rfl
      simp only [uteStatusPairExcess, obligatoryALGPairCharge,
        uteFixedOPTPairCharge, heffp, heffu]
      linarith

theorem uteStatusPairExcess_le_raise_right_deferred
    {s p q : ℝ} (hsq : s ≤ q) (hqu : q ≤ s + 1)
    (leftOutcome : BoundaryOutcome) :
    uteStatusPairExcess s leftOutcome .deferred p q ≤
      uteStatusPairExcess s leftOutcome .deferred p (s + 1) := by
  have heffq :
      uteEffectiveAt s q = s + 1 := by
    rw [uteEffectiveAt_eq_one_add_min, min_eq_right hsq]
    ring
  have heffu :
      uteEffectiveAt s (s + 1) = s + 1 := by
    rw [uteEffectiveAt_eq_one_add_min,
      min_eq_right (by linarith)]
    ring
  cases leftOutcome with
  | zero | epsilon | immediate =>
      simp [uteStatusPairExcess, obligatoryALGPairCharge,
        uteFixedOPTPairCharge, heffq, heffu]
  | deferred =>
      have hmin : min p q ≤ min p (s + 1) :=
        min_le_min le_rfl hqu
      simp only [uteStatusPairExcess, obligatoryALGPairCharge,
        uteFixedOPTPairCharge, heffq, heffu]
      linarith

/-- Raising one high deferred coordinate to `s+1` cannot decrease the whole
frozen-status excess. -/
theorem uteStatusWordExcess_le_update_high_deferred
    {n : ℕ} {s : ℝ}
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) (coordinate : Fin n)
    (hdeferred : outcome coordinate = .deferred)
    (hhigh : s ≤ processing coordinate)
    (hcap : processing coordinate ≤ s + 1) :
    uteStatusWordExcess s outcome processing ≤
      uteStatusWordExcess s outcome
        (Function.update processing coordinate (s + 1)) := by
  classical
  unfold uteStatusWordExcess
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _hi
    by_cases hi : i = coordinate
    · subst i
      simpa using
        uteFixedSelfExcessAt_le_cap_of_high hhigh hcap
    · simp [Function.update, hi]
  · apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    by_cases hi : i = coordinate
    · subst i
      have hjne : j ≠ coordinate := ne_of_gt hij
      simpa [Function.update, hjne, hdeferred] using
        (uteStatusPairExcess_le_raise_left_deferred
          hhigh hcap (outcome j))
    · by_cases hjc : j = coordinate
      · subst j
        simpa [Function.update, hi, hdeferred] using
          (uteStatusPairExcess_le_raise_right_deferred
            hhigh hcap (outcome i))
      · simp [Function.update, hi, hjc]

def uteRaiseCoordinates {n : ℕ}
    (u : ℝ) (coordinates : Finset (Fin n))
    (processing : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ coordinates then u else processing i

@[simp] theorem uteRaiseCoordinates_empty
    {n : ℕ} (u : ℝ) (processing : Fin n → ℝ) :
    uteRaiseCoordinates u ∅ processing = processing := by
  funext i
  simp [uteRaiseCoordinates]

theorem uteRaiseCoordinates_insert
    {n : ℕ} (u : ℝ) (processing : Fin n → ℝ)
    (coordinates : Finset (Fin n)) (i : Fin n) :
    uteRaiseCoordinates u (insert i coordinates) processing =
      Function.update
        (uteRaiseCoordinates u coordinates processing) i u := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [uteRaiseCoordinates]
  · simp [uteRaiseCoordinates, hji]

theorem uteStatusWordExcess_le_raiseCoordinates
    {n : ℕ} {s : ℝ}
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ)
    (hcap : ∀ i, processing i ≤ s + 1)
    (coordinates : Finset (Fin n))
    (hcoordinates :
      ∀ i ∈ coordinates,
        outcome i = .deferred ∧ s ≤ processing i) :
    uteStatusWordExcess s outcome processing ≤
      uteStatusWordExcess s outcome
        (uteRaiseCoordinates (s + 1) coordinates processing) := by
  classical
  induction coordinates using Finset.induction_on with
  | empty =>
      simp
  | @insert i coordinates hi ih =>
      have htail :
          ∀ j ∈ coordinates,
            outcome j = .deferred ∧ s ≤ processing j := by
        intro j hj
        exact hcoordinates j (Finset.mem_insert_of_mem hj)
      have hhead :=
        hcoordinates i (Finset.mem_insert_self i coordinates)
      have hcurrent :
          uteRaiseCoordinates (s + 1) coordinates processing i =
            processing i := by
        simp [uteRaiseCoordinates, hi]
      have hstep :
          uteStatusWordExcess s outcome
              (uteRaiseCoordinates (s + 1) coordinates processing) ≤
            uteStatusWordExcess s outcome
              (Function.update
                (uteRaiseCoordinates (s + 1) coordinates processing)
                i (s + 1)) := by
        apply uteStatusWordExcess_le_update_high_deferred
        · exact hhead.1
        · simpa [hcurrent] using hhead.2
        · rw [hcurrent]
          exact hcap i
      rw [uteRaiseCoordinates_insert]
      exact (ih htail).trans hstep

/-- Raise every deferred coordinate in the flat-offline interval `[s,s+1]`
to the cap. -/
def uteRaiseHighDeferred {n : ℕ}
    (s : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : Fin n → ℝ :=
  uteRaiseCoordinates (s + 1)
    (Finset.univ.filter fun i =>
      outcome i = .deferred ∧ s ≤ processing i)
    processing

theorem uteStatusWordExcess_le_raiseHighDeferred
    {n : ℕ} {s : ℝ}
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ)
    (hcap : ∀ i, processing i ≤ s + 1) :
    uteStatusWordExcess s outcome processing ≤
      uteStatusWordExcess s outcome
        (uteRaiseHighDeferred s outcome processing) := by
  apply uteStatusWordExcess_le_raiseCoordinates
  · exact hcap
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

theorem uteRaiseHighDeferred_eq_cap_or_original
    {n : ℕ} (s : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) (i : Fin n) :
    uteRaiseHighDeferred s outcome processing i = s + 1 ∨
      uteRaiseHighDeferred s outcome processing i = processing i := by
  unfold uteRaiseHighDeferred uteRaiseCoordinates
  split <;> simp_all

theorem uteRaiseHighDeferred_deferred_low_or_cap
    {n : ℕ} {s : ℝ}
    {outcome : Fin n → BoundaryOutcome}
    {processing : Fin n → ℝ}
    {i : Fin n} (hdeferred : outcome i = .deferred) :
    uteRaiseHighDeferred s outcome processing i = s + 1 ∨
      uteRaiseHighDeferred s outcome processing i < s := by
  unfold uteRaiseHighDeferred uteRaiseCoordinates
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hhigh : s ≤ processing i
  · simp [hdeferred, hhigh]
  · right
    simp [hdeferred, hhigh, lt_of_not_ge hhigh]

/-! ## A status-adapted box -/

/-- Lower endpoint of the box after all high deferred coordinates have
been raised.  A deferred coordinate already at the cap stays fixed. -/
def uteStatusBoxLower {n : ℕ}
    (s : ℝ) (outcome : Fin n → BoundaryOutcome)
    (marker : Fin n → ℝ) (i : Fin n) : ℝ :=
  if outcome i = .deferred then
    if marker i = s + 1 then s + 1 else 1
  else
    0

/-- Upper endpoint of the status-adapted box.  Nondeferred prefix
coordinates range over `[0,s+1]`, nondeferred suffix coordinates over
`[0,1]`, and low deferred coordinates over `[1,s]`. -/
def uteStatusBoxUpper {n : ℕ}
    (s : ℝ) (k : ℕ) (outcome : Fin n → BoundaryOutcome)
    (marker : Fin n → ℝ) (i : Fin n) : ℝ :=
  if outcome i = .deferred then
    if marker i = s + 1 then s + 1 else s
  else if i.val < k then
    s + 1
  else
    1

theorem uteStatusBoxLower_le_upper
    {n : ℕ} {s : ℝ} (hs1 : 1 ≤ s) (k : ℕ)
    (outcome : Fin n → BoundaryOutcome)
    (marker : Fin n → ℝ) :
    ∀ i,
      uteStatusBoxLower s outcome marker i ≤
        uteStatusBoxUpper s k outcome marker i := by
  intro i
  classical
  by_cases hd : outcome i = .deferred
  · by_cases hu : marker i = s + 1
    · simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hu]
    · simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hu, hs1]
  · by_cases hk : i.val < k
    · simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hk]
      linarith
    · simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hk]

private theorem uteStatus_convexOn_finset_sum
    {ι : Type*} {domain : Set ℝ} (hdomain : Convex ℝ domain)
    (indices : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ indices, ConvexOn ℝ domain (f i)) :
    ConvexOn ℝ domain (fun x => ∑ i ∈ indices, f i x) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (convexOn_const (𝕜 := ℝ) (β := ℝ) 0 hdomain)
  | @insert i indices hi ih =>
      have hhead := hf i (Finset.mem_insert_self i indices)
      have htail :
          ∀ j ∈ indices, ConvexOn ℝ domain (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum := hhead.add (ih htail)
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hsum

/-- On the box selected by a frozen status word, the exact competitive
excess is convex in each coordinate separately.  The only non-generic
case is a low deferred coordinate paired with another deferred one; the
second coordinate is then either in `[1,s]` or fixed at `s+1`. -/
theorem uteStatusWordExcess_coordinatewiseConvexOnBox
    {n : ℕ} {s : ℝ} (hs1 : 1 ≤ s) (k : ℕ)
    (outcome : Fin n → BoundaryOutcome)
    (marker : Fin n → ℝ) :
    CoordinatewiseConvexOnBox
      (uteStatusBoxLower s outcome marker)
      (uteStatusBoxUpper s k outcome marker)
      (uteStatusWordExcess s outcome) := by
  classical
  have hs : 0 < s := zero_lt_one.trans_le hs1
  intro processing hbox coordinate
  let interval : Set ℝ :=
    Icc (uteStatusBoxLower s outcome marker coordinate)
      (uteStatusBoxUpper s k outcome marker coordinate)
  have hinterval : Convex ℝ interval :=
    convex_Icc _ _
  have hself (i : Fin n) :
      ConvexOn ℝ interval
        (fun x =>
          uteFixedSelfExcessAt s
            (Function.update processing coordinate x i)) := by
    by_cases hi : i = coordinate
    · subst i
      simpa [interval] using
        (uteFixedSelfExcessAt_convex hs).subset
          (subset_univ _) hinterval
    · have hconst :
          (fun x =>
            uteFixedSelfExcessAt s
              (Function.update processing coordinate x i)) =
            (fun _ : ℝ =>
              uteFixedSelfExcessAt s (processing i)) := by
          funext x
          simp [Function.update, hi]
      rw [hconst]
      exact convexOn_const _ hinterval
  have hpair (i j : Fin n) (hij : i < j) :
      ConvexOn ℝ interval
        (fun x =>
          uteStatusPairExcess s (outcome i) (outcome j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    by_cases hi : i = coordinate
    · subst i
      have hj : j ≠ coordinate := ne_of_gt hij
      by_cases hcoord : outcome coordinate = .deferred
      · by_cases hfixed : marker coordinate = s + 1
        · have hsingle :=
            convexOn_singleton_any
              (fun x =>
                uteStatusPairExcess s (outcome coordinate) (outcome j)
                  x (processing j)) (s + 1)
          simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
            hcoord, hfixed, Function.update, hj] using hsingle
        · by_cases hjout : outcome j = .deferred
          · by_cases hjfixed : marker j = s + 1
            · have hjbox :
                  processing j ∈ Icc (s + 1) (s + 1) := by
                simpa [uteStatusBoxLower, uteStatusBoxUpper,
                  hjout, hjfixed] using hbox j
              have hjvalue : processing j = s + 1 :=
                le_antisymm hjbox.2 hjbox.1
              have hconv :=
                uteStatusPairExcess_convex_left_deferred_cap hs1
              simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
                hcoord, hfixed, hjout, hjvalue, Function.update, hj] using hconv
            · have hjbox :
                  processing j ∈ Icc 1 s := by
                simpa [uteStatusBoxLower, uteStatusBoxUpper,
                  hjout, hjfixed] using hbox j
              have hconv :=
                uteStatusPairExcess_convex_left_deferred_low
                  hs hjbox.2
              simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
                hcoord, hfixed, hjout, Function.update, hj] using hconv
          · have hconv :=
              (uteStatusPairExcess_convex_left_deferred_right_immediate
                hs hjout (processing j)).subset
                (subset_univ _) hinterval
            simpa [Function.update, hj, hcoord] using hconv
      · have hconv :=
          (uteStatusPairExcess_convex_left_immediate
            hs hcoord (outcome j) (processing j)).subset
            (subset_univ _) hinterval
        simpa [Function.update, hj] using hconv
    · by_cases hj : j = coordinate
      · subst j
        by_cases hcoord : outcome coordinate = .deferred
        · by_cases hfixed : marker coordinate = s + 1
          · have hsingle :=
              convexOn_singleton_any
                (fun x =>
                  uteStatusPairExcess s (outcome i) (outcome coordinate)
                    (processing i) x) (s + 1)
            simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
              hcoord, hfixed, Function.update, hi] using hsingle
          · by_cases hiout : outcome i = .deferred
            · by_cases hifixed : marker i = s + 1
              · have hibox :
                    processing i ∈ Icc (s + 1) (s + 1) := by
                  simpa [uteStatusBoxLower, uteStatusBoxUpper,
                    hiout, hifixed] using hbox i
                have hivalue : processing i = s + 1 :=
                  le_antisymm hibox.2 hibox.1
                have hconv :=
                  uteStatusPairExcess_convex_right_deferred_cap hs1
                simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
                  hcoord, hfixed, hiout, hivalue, Function.update, hi] using hconv
              · have hibox :
                    processing i ∈ Icc 1 s := by
                  simpa [uteStatusBoxLower, uteStatusBoxUpper,
                    hiout, hifixed] using hbox i
                have hconv :=
                  uteStatusPairExcess_convex_right_deferred_low
                    hs hibox.2
                simpa [interval, uteStatusBoxLower, uteStatusBoxUpper,
                  hcoord, hfixed, hiout, Function.update, hi] using hconv
            · have hconv :=
                (uteStatusPairExcess_convex_right_deferred_left_immediate
                  hs hiout (processing i)).subset
                  (subset_univ _) hinterval
              simpa [Function.update, hi, hcoord] using hconv
        · have hconv :=
            (uteStatusPairExcess_convex_right_immediate
              hs (outcome i) hcoord (processing i)).subset
              (subset_univ _) hinterval
          simpa [Function.update, hi] using hconv
      · have hconst :
          (fun x =>
            uteStatusPairExcess s (outcome i) (outcome j)
              (Function.update processing coordinate x i)
              (Function.update processing coordinate x j)) =
            (fun _ : ℝ =>
              uteStatusPairExcess s (outcome i) (outcome j)
                (processing i) (processing j)) := by
          funext x
          simp [Function.update, hi, hj]
        rw [hconst]
        exact convexOn_const _ hinterval
  have hselfSum :
      ConvexOn ℝ interval
        (fun x => ∑ i,
          uteFixedSelfExcessAt s
            (Function.update processing coordinate x i)) := by
    simpa using uteStatus_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => uteFixedSelfExcessAt s
        (Function.update processing coordinate x i))
      (fun i _hi => hself i)
  have hpairRow (i : Fin n) :
      ConvexOn ℝ interval
        (fun x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
          uteStatusPairExcess s (outcome i) (outcome j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    apply uteStatus_convexOn_finset_sum hinterval
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hj).2
  have hpairSum :
      ConvexOn ℝ interval
        (fun x => ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            uteStatusPairExcess s (outcome i) (outcome j)
              (Function.update processing coordinate x i)
              (Function.update processing coordinate x j)) := by
    simpa using uteStatus_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
        uteStatusPairExcess s (outcome i) (outcome j)
          (Function.update processing coordinate x i)
          (Function.update processing coordinate x j))
      (fun i _hi => hpairRow i)
  simpa [uteStatusWordExcess, interval, Pi.add_apply] using
    hselfSum.add hpairSum

@[simp] theorem uteRaiseHighDeferred_eq_of_ne_deferred
    {n : ℕ} (s : ℝ) {outcome : Fin n → BoundaryOutcome}
    {processing : Fin n → ℝ} {i : Fin n}
    (hi : outcome i ≠ .deferred) :
    uteRaiseHighDeferred s outcome processing i = processing i := by
  unfold uteRaiseHighDeferred uteRaiseCoordinates
  simp [hi]

theorem uteRaiseHighDeferred_le_cap
    {n : ℕ} {s : ℝ} (outcome : Fin n → BoundaryOutcome)
    {processing : Fin n → ℝ}
    (hcap : ∀ i, processing i ≤ s + 1) :
    ∀ i, uteRaiseHighDeferred s outcome processing i ≤ s + 1 := by
  intro i
  rcases uteRaiseHighDeferred_eq_cap_or_original
      s outcome processing i with hi | hi
  · rw [hi]
  · rw [hi]
    exact hcap i

/-- The processing vector obtained by raising the flat deferred part lies
in the status-adapted box for the concrete UTE outcome. -/
theorem uteRaiseHighDeferred_mem_statusBox
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hnonneg : ∀ i, 0 ≤ processing i)
    (hcap : ∀ i, processing i ≤ s + 1) :
    uteRaiseHighDeferred s (uteRuntimeOutcome k processing) processing ∈
      coordinateBox
        (uteStatusBoxLower s (uteRuntimeOutcome k processing)
          (uteRaiseHighDeferred s
            (uteRuntimeOutcome k processing) processing))
        (uteStatusBoxUpper s k (uteRuntimeOutcome k processing)
          (uteRaiseHighDeferred s
            (uteRuntimeOutcome k processing) processing)) := by
  classical
  intro i
  let outcome := uteRuntimeOutcome k processing
  let raised := uteRaiseHighDeferred s outcome processing
  change
    raised i ∈
      Icc (uteStatusBoxLower s outcome raised i)
        (uteStatusBoxUpper s k outcome raised i)
  by_cases hd : outcome i = .deferred
  · rcases uteRaiseHighDeferred_deferred_low_or_cap
        (s := s) (processing := processing) hd with hcapValue | hlow
    · change raised i = s + 1 at hcapValue
      simp only [mem_Icc, uteStatusBoxLower,
        uteStatusBoxUpper, hd, if_pos]
      simp [hcapValue]
    · have horiginal : raised i = processing i := by
        rcases uteRaiseHighDeferred_eq_cap_or_original
            s outcome processing i with hcap' | horiginal
        · exact False.elim (by linarith)
        · exact horiginal
      have hpOne : 1 < processing i := by
        have hcondition :
            ¬ (i.val < k ∨ processing i ≤ 1) := by
          simpa [outcome] using
            (uteRuntimeOutcome_eq_deferred_iff.mp hd)
        exact lt_of_not_ge (fun hp => hcondition (Or.inr hp))
      change raised i < s at hlow
      have hne : raised i ≠ s + 1 := by
        intro h
        linarith
      have hpne : processing i ≠ s + 1 := by
        intro h
        exact hne (horiginal.trans h)
      have hps : processing i ≤ s := by
        linarith
      simp only [mem_Icc, uteStatusBoxLower,
        uteStatusBoxUpper, hd, if_pos]
      simp [horiginal, hpne, hpOne.le, hps]
  · have horiginal : raised i = processing i :=
      uteRaiseHighDeferred_eq_of_ne_deferred s hd
    by_cases hk : i.val < k
    · have hupper : processing i ≤ s + 1 := hcap i
      simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hk,
        horiginal, hnonneg i, hupper]
    · have hpOne : processing i ≤ 1 := by
        have hcondition :
            i.val < k ∨ processing i ≤ 1 := by
          simpa [outcome] using
            (uteRuntimeOutcome_ne_deferred_iff.mp hd)
        exact hcondition.resolve_left hk
      simp [uteStatusBoxLower, uteStatusBoxUpper, hd, hk,
        horiginal, hnonneg i, hpOne]

/-- First endpoint-reduction milestone: every concrete endpoint-range UTE
execution is dominated by a vertex of its frozen-status box. -/
theorem exists_uteStatusBoxVertex_ge_runtime
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hnonneg : ∀ i, 0 ≤ processing i)
    (hcap : ∀ i, processing i ≤ s + 1) :
    let outcome := uteRuntimeOutcome k processing
    let raised := uteRaiseHighDeferred s outcome processing
    ∃ vertex,
      vertex ∈ coordinateBox
        (uteStatusBoxLower s outcome raised)
        (uteStatusBoxUpper s k outcome raised) ∧
      IsBoxVertex
        (uteStatusBoxLower s outcome raised)
        (uteStatusBoxUpper s k outcome raised) vertex ∧
      uteStatusWordExcess s outcome processing ≤
        uteStatusWordExcess s outcome vertex := by
  dsimp only
  let outcome := uteRuntimeOutcome k processing
  let raised := uteRaiseHighDeferred s outcome processing
  have hraise :
      uteStatusWordExcess s outcome processing ≤
        uteStatusWordExcess s outcome raised := by
    apply uteStatusWordExcess_le_raiseHighDeferred
    exact hcap
  have hraisedBox :
      raised ∈ coordinateBox
        (uteStatusBoxLower s outcome raised)
        (uteStatusBoxUpper s k outcome raised) := by
    exact uteRaiseHighDeferred_mem_statusBox
      hs1 processing hnonneg hcap
  obtain ⟨vertex, hvertexBox, hvertex, hvertexLe⟩ :=
    exists_boxVertex_ge
      (uteStatusBoxLower_le_upper hs1 k outcome raised)
      (uteStatusWordExcess_coordinatewiseConvexOnBox
        hs1 k outcome raised)
      raised hraisedBox
  exact ⟨vertex, hvertexBox, hvertex,
    hraise.trans hvertexLe⟩

theorem uteRaiseHighDeferred_eq_one_or_cap_of_three_values
    {n : ℕ} {s : ℝ} {outcome : Fin n → BoundaryOutcome}
    {processing : Fin n → ℝ} {i : Fin n}
    (hdeferred : outcome i = .deferred)
    (hvalues :
      processing i = 1 ∨ processing i = s ∨
        processing i = s + 1) :
    uteRaiseHighDeferred s outcome processing i = 1 ∨
      uteRaiseHighDeferred s outcome processing i = s + 1 := by
  classical
  by_cases hhigh : s ≤ processing i
  · right
    unfold uteRaiseHighDeferred uteRaiseCoordinates
    simp [hdeferred, hhigh]
  · left
    have hone : processing i = 1 := by
      rcases hvalues with hone | hs | hu
      · exact hone
      · exfalso
        exact hhigh hs.ge
      · exfalso
        apply hhigh
        rw [hu]
        linarith
    have hnotmem :
        i ∉ Finset.univ.filter (fun j =>
          outcome j = .deferred ∧ s ≤ processing j) := by
      simp [hhigh]
    unfold uteRaiseHighDeferred uteRaiseCoordinates
    simp [hnotmem, hone]

/-- After the second (vertex-to-cap) raising step, every coordinate has
exactly one of the processing values represented by the six UTE endpoint
classes. -/
theorem utePromotedStatusVertex_values
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (processing marker vertex : Fin n → ℝ)
    (hvertex :
      IsBoxVertex
        (uteStatusBoxLower s (uteRuntimeOutcome k processing) marker)
        (uteStatusBoxUpper s k
          (uteRuntimeOutcome k processing) marker)
        vertex) :
    let outcome := uteRuntimeOutcome k processing
    let promoted := uteRaiseHighDeferred s outcome vertex
    (∀ i, i.val < k →
      promoted i = 0 ∨ promoted i = s + 1) ∧
    (∀ i, k ≤ i.val → outcome i = .deferred →
      promoted i = 1 ∨ promoted i = s + 1) ∧
    (∀ i, k ≤ i.val → outcome i ≠ .deferred →
      promoted i = 0 ∨ promoted i = 1) := by
  dsimp only
  let outcome := uteRuntimeOutcome k processing
  let promoted := uteRaiseHighDeferred s outcome vertex
  constructor
  · intro i hi
    have hout : outcome i ≠ .deferred := by
      rw [uteRuntimeOutcome_ne_deferred_iff]
      exact Or.inl hi
    have hv := hvertex i
    have hv' : vertex i = 0 ∨ vertex i = s + 1 := by
      simpa [uteStatusBoxLower, uteStatusBoxUpper,
        outcome, hout, hi] using hv
    have hp : promoted i = vertex i := by
      exact uteRaiseHighDeferred_eq_of_ne_deferred s hout
    exact hv'.imp (fun h => hp.trans h) (fun h => hp.trans h)
  · constructor
    · intro i _hi hout
      have hv := hvertex i
      by_cases hmarker : marker i = s + 1
      · have hv' : vertex i = s + 1 := by
          rcases hv with hv | hv
          · simpa [uteStatusBoxLower, hout, hmarker] using hv
          · simpa [uteStatusBoxUpper, hout, hmarker] using hv
        exact
          uteRaiseHighDeferred_eq_one_or_cap_of_three_values
            hout (Or.inr (Or.inr hv'))
      · have hv' : vertex i = 1 ∨ vertex i = s := by
          simpa [uteStatusBoxLower, uteStatusBoxUpper,
            hout, hmarker] using hv
        exact
          uteRaiseHighDeferred_eq_one_or_cap_of_three_values
            hout (hv'.imp_right Or.inl)
    · intro i hi hout
      have hv := hvertex i
      have hnotPrefix : ¬ i.val < k := Nat.not_lt.mpr hi
      have hv' : vertex i = 0 ∨ vertex i = 1 := by
        simpa [uteStatusBoxLower, uteStatusBoxUpper,
          outcome, hout, hnotPrefix] using hv
      have hp : promoted i = vertex i := by
        exact uteRaiseHighDeferred_eq_of_ne_deferred s hout
      exact hv'.imp (fun h => hp.trans h) (fun h => hp.trans h)

theorem uteStatusBoxUpper_le_cap
    {n : ℕ} {s : ℝ} (hs1 : 1 ≤ s) (k : ℕ)
    (outcome : Fin n → BoundaryOutcome)
    (marker : Fin n → ℝ) :
    ∀ i,
      uteStatusBoxUpper s k outcome marker i ≤ s + 1 := by
  intro i
  classical
  by_cases hout : outcome i = .deferred
  · by_cases hmarker : marker i = s + 1
    · simp [uteStatusBoxUpper, hout, hmarker]
    · simp [uteStatusBoxUpper, hout, hmarker]
  · by_cases hi : i.val < k
    · simp [uteStatusBoxUpper, hout, hi]
    · simp [uteStatusBoxUpper, hout, hi]
      linarith

/-- Turn a promoted status-box vertex into its canonical UTE endpoint
class. -/
def uteEndpointOfPromoted {n : ℕ}
    (k : ℕ) (outcome : Fin n → BoundaryOutcome)
    (promoted : Fin n → ℝ) (i : Fin n) : UTEEndpoint :=
  if i.val < k then
    if promoted i = 0 then .forcedZero else .forcedCap
  else if outcome i = .deferred then
    if promoted i = 1 then .boundaryDeferred else .cappedDeferred
  else
    if promoted i = 0 then .suffixZero else .immediateOne

theorem uteEndpointOfPromoted_processing_eq
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (outcome : Fin n → BoundaryOutcome)
    (promoted : Fin n → ℝ)
    (hforced : ∀ i, i.val < k →
      promoted i = 0 ∨ promoted i = s + 1)
    (hdeferred : ∀ i, k ≤ i.val → outcome i = .deferred →
      promoted i = 1 ∨ promoted i = s + 1)
    (himmediate : ∀ i, k ≤ i.val → outcome i ≠ .deferred →
      promoted i = 0 ∨ promoted i = 1) :
    ∀ i,
      uteEndpointProcessing s
          (uteEndpointOfPromoted k outcome promoted i) =
        promoted i := by
  intro i
  by_cases hi : i.val < k
  · rcases hforced i hi with hzero | hcap
    · simp [uteEndpointOfPromoted, hi, hzero,
        uteEndpointProcessing]
    · have hcapZero : s + 1 ≠ 0 := by linarith
      simp [uteEndpointOfPromoted, hi, hcap, hcapZero,
        uteEndpointProcessing]
  · have hki : k ≤ i.val := Nat.le_of_not_gt hi
    by_cases hout : outcome i = .deferred
    · rcases hdeferred i hki hout with hone | hcap
      · simp [uteEndpointOfPromoted, hi, hout, hone,
          uteEndpointProcessing]
      · have hcapOne : s + 1 ≠ 1 := by linarith
        simp [uteEndpointOfPromoted, hi, hout, hcap, hcapOne,
          uteEndpointProcessing]
    · rcases himmediate i hki hout with hzero | hone
      · simp [uteEndpointOfPromoted, hi, hout, hzero,
          uteEndpointProcessing]
      · simp [uteEndpointOfPromoted, hi, hout, hone,
          uteEndpointProcessing]

theorem uteEndpointOfPromoted_outcome_eq_runtime
    {n k : ℕ} (processing promoted : Fin n → ℝ) :
    ∀ i,
      (uteEndpointOfPromoted k
          (uteRuntimeOutcome k processing) promoted i).outcome =
        uteRuntimeOutcome k processing i := by
  intro i
  by_cases hi : i.val < k
  · by_cases hzero : promoted i = 0
    · simp [uteEndpointOfPromoted, hi, hzero,
        uteRuntimeOutcome, UTEEndpoint.outcome]
    · simp [uteEndpointOfPromoted, hi, hzero,
        uteRuntimeOutcome, UTEEndpoint.outcome]
  · by_cases hpOne : processing i ≤ 1
    · by_cases hzero : promoted i = 0
      · simp [uteEndpointOfPromoted, hi, hpOne, hzero,
          uteRuntimeOutcome, UTEEndpoint.outcome]
      · simp [uteEndpointOfPromoted, hi, hpOne, hzero,
          uteRuntimeOutcome, UTEEndpoint.outcome]
    · by_cases hone : promoted i = 1
      · simp [uteEndpointOfPromoted, hi, hpOne, hone,
          uteRuntimeOutcome, UTEEndpoint.outcome]
      · simp [uteEndpointOfPromoted, hi, hpOne, hone,
          uteRuntimeOutcome, UTEEndpoint.outcome]

theorem uteEndpointOfPromoted_isForced
    {n k : ℕ} (outcome : Fin n → BoundaryOutcome)
    (promoted : Fin n → ℝ) :
    (∀ i, i.val < k →
      (uteEndpointOfPromoted k outcome promoted i).IsForced) ∧
    (∀ i, k ≤ i.val →
      ¬ (uteEndpointOfPromoted k outcome promoted i).IsForced) := by
  constructor
  · intro i hi
    by_cases hzero : promoted i = 0
    · simp [uteEndpointOfPromoted, hi, hzero,
        UTEEndpoint.IsForced]
    · simp [uteEndpointOfPromoted, hi, hzero,
        UTEEndpoint.IsForced]
  · intro i hi
    have hnot : ¬ i.val < k := Nat.not_lt.mpr hi
    by_cases hout : outcome i = .deferred
    · by_cases hone : promoted i = 1
      · simp [uteEndpointOfPromoted, hnot, hout, hone,
          UTEEndpoint.IsForced]
      · simp [uteEndpointOfPromoted, hnot, hout, hone,
          UTEEndpoint.IsForced]
    · by_cases hzero : promoted i = 0
      · simp [uteEndpointOfPromoted, hnot, hout, hzero,
          UTEEndpoint.IsForced]
      · simp [uteEndpointOfPromoted, hnot, hout, hzero,
          UTEEndpoint.IsForced]

theorem uteStatusWordExcess_eq_endpointOfPromoted
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (processing promoted : Fin n → ℝ)
    (hforced : ∀ i, i.val < k →
      promoted i = 0 ∨ promoted i = s + 1)
    (hdeferred : ∀ i, k ≤ i.val →
      uteRuntimeOutcome k processing i = .deferred →
      promoted i = 1 ∨ promoted i = s + 1)
    (himmediate : ∀ i, k ≤ i.val →
      uteRuntimeOutcome k processing i ≠ .deferred →
      promoted i = 0 ∨ promoted i = 1) :
    uteStatusWordExcess s
        (uteRuntimeOutcome k processing) promoted =
      uteEndpointWordExcess s
        (uteEndpointOfPromoted k
          (uteRuntimeOutcome k processing) promoted) := by
  unfold uteEndpointWordExcess
  have hout :
      (fun i =>
        (uteEndpointOfPromoted k
          (uteRuntimeOutcome k processing) promoted i).outcome) =
        uteRuntimeOutcome k processing := by
    funext i
    exact uteEndpointOfPromoted_outcome_eq_runtime
      processing promoted i
  have hprocessing :
      (fun i =>
        uteEndpointProcessing s
          (uteEndpointOfPromoted k
            (uteRuntimeOutcome k processing) promoted i)) =
        promoted := by
    funext i
    exact uteEndpointOfPromoted_processing_eq hs1
      (uteRuntimeOutcome k processing) promoted
      hforced hdeferred himmediate i
  rw [hout, hprocessing]

/-- Complete operational endpoint reduction for the endpoint range
`u=s+1`: a concrete UTE status word is dominated by a six-class endpoint
word, preserving the forced-prefix/suffix split. -/
theorem exists_uteEndpoint_ge_runtimeStatus
    {n k : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (processing : Fin n → ℝ)
    (hnonneg : ∀ i, 0 ≤ processing i)
    (hcap : ∀ i, processing i ≤ s + 1) :
    ∃ endpoint : Fin n → UTEEndpoint,
      (∀ i, i.val < k → (endpoint i).IsForced) ∧
      (∀ i, k ≤ i.val → ¬ (endpoint i).IsForced) ∧
      uteStatusWordExcess s
          (uteRuntimeOutcome k processing) processing ≤
        uteEndpointWordExcess s endpoint := by
  let outcome := uteRuntimeOutcome k processing
  let raised := uteRaiseHighDeferred s outcome processing
  obtain ⟨vertex, hvertexBox, hvertex, hprocessingVertex⟩ :=
    exists_uteStatusBoxVertex_ge_runtime
      hs1 processing hnonneg hcap
  let promoted := uteRaiseHighDeferred s outcome vertex
  have hvertexCap : ∀ i, vertex i ≤ s + 1 := by
    intro i
    exact (hvertexBox i).2.trans
      (uteStatusBoxUpper_le_cap hs1 k outcome raised i)
  have hvertexPromoted :
      uteStatusWordExcess s outcome vertex ≤
        uteStatusWordExcess s outcome promoted := by
    exact uteStatusWordExcess_le_raiseHighDeferred
      outcome vertex hvertexCap
  obtain ⟨hforcedValues, hdeferredValues,
      himmediateValues⟩ :=
    utePromotedStatusVertex_values
      hs1 processing raised vertex hvertex
  let endpoint :=
    uteEndpointOfPromoted k outcome promoted
  have hforcedSplit :=
    uteEndpointOfPromoted_isForced (k := k) outcome promoted
  have hendpointEq :
      uteStatusWordExcess s outcome promoted =
        uteEndpointWordExcess s endpoint := by
    exact uteStatusWordExcess_eq_endpointOfPromoted
      hs1 processing promoted
      hforcedValues hdeferredValues himmediateValues
  refine ⟨endpoint, hforcedSplit.1, hforcedSplit.2, ?_⟩
  exact hprocessingVertex.trans
    (hvertexPromoted.trans_eq hendpointEq)

end

end SchedulingPaper
