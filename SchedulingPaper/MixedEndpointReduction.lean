import SchedulingPaper.ParameterizedRuntimeAccounting
import SchedulingPaper.PlateauRuntimeObjective

/-!
# Endpoint reduction for the finite mixed branch

Below the effective-length saturation point the fixed-word excess is
coordinatewise convex.  Coordinates already in the saturated interval can
first be raised to the cap without changing OPT and without decreasing ALG.
-/

namespace SchedulingPaper

noncomputable section

open Set
open Online

def mixedNormalizedSelfExcessAt (c p : ℝ) : ℝ :=
  (1 + p) - (1 + c) * (1 + p)

def mixedNormalizedPairExcessAt
    (c : ℝ) (left right : BoundaryOutcome) (p q : ℝ) : ℝ :=
  obligatoryALGPairCharge ⟨left, p⟩ ⟨right, q⟩ -
    (1 + c) * (1 + min p q)

def mixedNormalizedFixedWordExcess {n : ℕ}
    (c : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, mixedNormalizedSelfExcessAt c (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      mixedNormalizedPairExcessAt c
        (outcome i) (outcome j) (processing i) (processing j)

theorem mixedNormalizedSelfExcessAt_convex
    {c : ℝ} :
    ConvexOn ℝ univ (mixedNormalizedSelfExcessAt c) := by
  have h :=
    convexOn_affine_sub_mul_min
      (-c) (-c) 0 0 (show (0 : ℝ) ≤ 0 by norm_num)
  refine h.congr ?_
  intro p _hp
  unfold mixedNormalizedSelfExcessAt
  simp
  ring

theorem mixedNormalizedPairExcessAt_convex_left
    {c : ℝ} (hc : 0 ≤ c)
    (left right : BoundaryOutcome) (q : ℝ) :
    ConvexOn ℝ univ
      (fun p => mixedNormalizedPairExcessAt c left right p q) := by
  have hratio : 0 ≤ 1 + c := by linarith
  cases left with
  | zero =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (-c) (1 + c) q hratio
      refine h.congr ?_
      intro p _hp
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge]
      ring
  | epsilon =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (-c) (1 + c) q hratio
      refine h.congr ?_
      intro p _hp
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge]
      ring
  | immediate =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (-c) (1 + c) q hratio
      refine h.congr ?_
      intro p _hp
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge]
      ring
  | deferred =>
      cases right with
      | zero =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (1 + q - c) (1 + c) q hratio
          refine h.congr ?_
          intro p _hp
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge]
          ring
      | epsilon =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (1 + q - c) (1 + c) q hratio
          refine h.congr ?_
          intro p _hp
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge]
          ring
      | immediate =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (1 + q - c) (1 + c) q hratio
          refine h.congr ?_
          intro p _hp
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge]
          ring
      | deferred =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (1 - c) c q hc
          refine h.congr ?_
          intro p _hp
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge]
          ring

theorem mixedNormalizedPairExcessAt_convex_right
    {c : ℝ} (hc : 0 ≤ c)
    (left right : BoundaryOutcome) (p : ℝ) :
    ConvexOn ℝ univ
      (fun q => mixedNormalizedPairExcessAt c left right p q) := by
  have hratio : 0 ≤ 1 + c := by linarith
  cases left with
  | zero =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (p - c) (1 + c) p hratio
      refine h.congr ?_
      intro q _hq
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge, min_comm p q]
      ring
  | epsilon =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (p - c) (1 + c) p hratio
      refine h.congr ?_
      intro q _hq
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge, min_comm p q]
      ring
  | immediate =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (p - c) (1 + c) p hratio
      refine h.congr ?_
      intro q _hq
      simp [mixedNormalizedPairExcessAt,
        obligatoryALGPairCharge, min_comm p q]
      ring
  | deferred =>
      cases right with
      | zero =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (1 - c) (1 + c) p hratio
          refine h.congr ?_
          intro q _hq
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge, min_comm p q]
          ring
      | epsilon =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (1 - c) (1 + c) p hratio
          refine h.congr ?_
          intro q _hq
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge, min_comm p q]
          ring
      | immediate =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (1 - c) (1 + c) p hratio
          refine h.congr ?_
          intro q _hq
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge, min_comm p q]
          ring
      | deferred =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (1 - c) c p hc
          refine h.congr ?_
          intro q _hq
          simp [mixedNormalizedPairExcessAt,
            obligatoryALGPairCharge, min_comm p q]
          ring

private theorem convexOn_finset_sum_mixed
    {ι : Type*} {s : Set ℝ} (hs : Convex ℝ s)
    (indices : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ indices, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => ∑ i ∈ indices, f i x) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using (convexOn_const (𝕜 := ℝ) (β := ℝ) 0 hs)
  | @insert i indices hi ih =>
      have hhead := hf i (Finset.mem_insert_self i indices)
      have htail :
          ∀ j ∈ indices, ConvexOn ℝ s (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum := hhead.add (ih htail)
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hsum

theorem mixedNormalizedFixedWordExcess_coordinatewiseConvex
    {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (outcome : Fin n → BoundaryOutcome)
    (lower upper : Fin n → ℝ) :
    CoordinatewiseConvexOnBox lower upper
      (mixedNormalizedFixedWordExcess c outcome) := by
  classical
  intro processing _hbox coordinate
  let interval : Set ℝ := Icc (lower coordinate) (upper coordinate)
  have hinterval : Convex ℝ interval :=
    convex_Icc (lower coordinate) (upper coordinate)
  have hself (i : Fin n) :
      ConvexOn ℝ interval
        (fun t =>
          mixedNormalizedSelfExcessAt c
            (Function.update processing coordinate t i)) := by
    by_cases hi : i = coordinate
    · subst i
      simpa [interval] using
        (mixedNormalizedSelfExcessAt_convex (c := c)).subset
          (subset_univ _) hinterval
    · have hconst :
          (fun t =>
            mixedNormalizedSelfExcessAt c
              (Function.update processing coordinate t i)) =
            (fun _ : ℝ =>
              mixedNormalizedSelfExcessAt c (processing i)) := by
          funext t
          simp [Function.update, hi]
      rw [hconst]
      exact convexOn_const _ hinterval
  have hpair (i j : Fin n) (hij : i < j) :
      ConvexOn ℝ interval
        (fun t =>
          mixedNormalizedPairExcessAt c
            (outcome i) (outcome j)
            (Function.update processing coordinate t i)
            (Function.update processing coordinate t j)) := by
    by_cases hi : i = coordinate
    · subst i
      have hj : j ≠ coordinate := ne_of_gt hij
      have hleft :=
        (mixedNormalizedPairExcessAt_convex_left hc
          (outcome coordinate) (outcome j)
          (processing j)).subset (subset_univ _) hinterval
      simpa [Function.update, hj] using hleft
    · by_cases hj : j = coordinate
      · subst j
        have hright :=
          (mixedNormalizedPairExcessAt_convex_right hc
            (outcome i) (outcome coordinate)
            (processing i)).subset (subset_univ _) hinterval
        simpa [Function.update, hi] using hright
      · have hconst :
            (fun t =>
              mixedNormalizedPairExcessAt c
                (outcome i) (outcome j)
                (Function.update processing coordinate t i)
                (Function.update processing coordinate t j)) =
              (fun _ : ℝ =>
                mixedNormalizedPairExcessAt c
                  (outcome i) (outcome j)
                  (processing i) (processing j)) := by
            funext t
            simp [Function.update, hi, hj]
        rw [hconst]
        exact convexOn_const _ hinterval
  have hselfSum :
      ConvexOn ℝ interval
        (fun t => ∑ i,
          mixedNormalizedSelfExcessAt c
            (Function.update processing coordinate t i)) := by
    simpa using convexOn_finset_sum_mixed hinterval
      Finset.univ
      (fun i t => mixedNormalizedSelfExcessAt c
        (Function.update processing coordinate t i))
      (fun i _hi => hself i)
  have hpairRow (i : Fin n) :
      ConvexOn ℝ interval
        (fun t => ∑ j ∈ Finset.univ.filter (fun j => i < j),
          mixedNormalizedPairExcessAt c
            (outcome i) (outcome j)
            (Function.update processing coordinate t i)
            (Function.update processing coordinate t j)) := by
    apply convexOn_finset_sum_mixed hinterval
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hj).2
  have hpairSum :
      ConvexOn ℝ interval
        (fun t => ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            mixedNormalizedPairExcessAt c
              (outcome i) (outcome j)
              (Function.update processing coordinate t i)
              (Function.update processing coordinate t j)) := by
    simpa using convexOn_finset_sum_mixed hinterval
      Finset.univ
      (fun i t => ∑ j ∈ Finset.univ.filter (fun j => i < j),
        mixedNormalizedPairExcessAt c
          (outcome i) (outcome j)
          (Function.update processing coordinate t i)
          (Function.update processing coordinate t j))
      (fun i _hi => hpairRow i)
  simpa [mixedNormalizedFixedWordExcess, interval, Pi.add_apply] using
    hselfSum.add hpairSum

theorem exists_mixedNormalizedFixedWord_endpoint_ge
    {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (outcome : Fin n → BoundaryOutcome)
    (lower upper processing : Fin n → ℝ)
    (horder : ∀ i, lower i ≤ upper i)
    (hprocessing : processing ∈ coordinateBox lower upper) :
    ∃ vertex,
      vertex ∈ coordinateBox lower upper ∧
      IsBoxVertex lower upper vertex ∧
      mixedNormalizedFixedWordExcess c outcome processing ≤
        mixedNormalizedFixedWordExcess c outcome vertex :=
  exists_boxVertex_ge horder
    (mixedNormalizedFixedWordExcess_coordinatewiseConvex
      hc outcome lower upper)
    processing hprocessing

def mixedFiniteSelfExcessAt (c u p : ℝ) : ℝ :=
  (1 + p) - (1 + c) *
    (1 + plateauClippedProcessing u p)

def mixedFinitePairExcessAt
    (c u : ℝ) (left right : BoundaryOutcome) (p q : ℝ) : ℝ :=
  obligatoryALGPairCharge ⟨left, p⟩ ⟨right, q⟩ -
    (1 + c) *
      (1 + min (plateauClippedProcessing u p)
        (plateauClippedProcessing u q))

def mixedFiniteFixedWordExcess {n : ℕ}
    (c u : ℝ) (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, mixedFiniteSelfExcessAt c u (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      mixedFinitePairExcessAt c u
        (outcome i) (outcome j) (processing i) (processing j)

end

end SchedulingPaper
