import SchedulingPaper.UTEPairAccounting
import SchedulingPaper.ListPairPermutation
import Mathlib.Tactic

/-!
# Finite endpoint accounting for ForcedPrefixUTE

The scalar UTE game is homogeneous and uses normalized endpoint masses.
An actual execution contains integral class counts and an arbitrary order
inside the forced prefix and the suffix.  This file proves that sorting those
classes can only increase the online pair objective, leaves the offline pair
objective unchanged, and evaluates the resulting finite count exactly.
-/

namespace SchedulingPaper

noncomputable section

def UTEEndpoint.rank : UTEEndpoint → ℕ
  | .forcedCap => 0
  | .forcedZero => 1
  | .cappedDeferred => 2
  | .boundaryDeferred => 3
  | .immediateOne => 4
  | .suffixZero => 5

def UTEEndpoint.IsForced : UTEEndpoint → Prop
  | .forcedCap | .forcedZero => True
  | .cappedDeferred | .boundaryDeferred
  | .immediateOne | .suffixZero => False

/-- The charge after putting the two endpoint classes in the canonical
order from the paper.  Unlike `uteALGPairCharge`, this is symmetric. -/
def uteCanonicalALGPairCharge
    (s : ℝ) (left right : UTEEndpoint) : ℝ :=
  if left.rank ≤ right.rank then
    uteALGPairCharge s left right
  else
    uteALGPairCharge s right left

theorem uteCanonicalALGPairCharge_comm
    (s : ℝ) (left right : UTEEndpoint) :
    uteCanonicalALGPairCharge s left right =
      uteCanonicalALGPairCharge s right left := by
  cases left <;> cases right <;>
    simp [uteCanonicalALGPairCharge, UTEEndpoint.rank,
      uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate, min_comm]

theorem uteOPTPairCharge_comm
    (s : ℝ) (left right : UTEEndpoint) :
    uteOPTPairCharge s left right =
      uteOPTPairCharge s right left := by
  simp [uteOPTPairCharge, min_comm]

theorem uteALGPairCharge_nonneg
    {s : ℝ} (hs : 0 ≤ s)
    (left right : UTEEndpoint) :
    0 ≤ uteALGPairCharge s left right := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  cases left <;> cases right <;>
    simp [uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate, min_eq_left hone,
      min_eq_right hone] <;> linarith

theorem uteOPTPairCharge_nonneg
    {s : ℝ} (hs : 0 ≤ s)
    (left right : UTEEndpoint) :
    0 ≤ uteOPTPairCharge s left right := by
  cases left <;> cases right <;>
    simp [uteOPTPairCharge, uteEndpointEffective,
      uteEndpointProcessing] <;> linarith

theorem uteALGPairCharge_le_canonical_forced_left
    {s : ℝ} (hs : 0 ≤ s)
    {left right : UTEEndpoint} (hleft : left.IsForced) :
    uteALGPairCharge s left right ≤
      uteCanonicalALGPairCharge s left right := by
  cases left <;> cases right <;>
    simp [UTEEndpoint.IsForced, uteCanonicalALGPairCharge,
      UTEEndpoint.rank, uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate, min_eq_left, min_eq_right] at hleft ⊢ <;>
    linarith

theorem uteALGPairCharge_le_canonical_suffix
    {s : ℝ} (hs : 0 ≤ s)
    {left right : UTEEndpoint}
    (hleft : ¬ left.IsForced) (hright : ¬ right.IsForced) :
    uteALGPairCharge s left right ≤
      uteCanonicalALGPairCharge s left right := by
  cases left <;> cases right <;>
    simp [UTEEndpoint.IsForced, uteCanonicalALGPairCharge,
      UTEEndpoint.rank, uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate, min_eq_left, min_eq_right] at hleft hright ⊢ <;>
    linarith

private theorem pairwise_of_mem_property
    {α : Type*} {property : α → Prop} {relation : α → α → Prop}
    (hrelation :
      ∀ left right, property left → property right →
        relation left right) :
    ∀ {values : List α},
      (∀ value ∈ values, property value) →
        values.Pairwise relation := by
  intro values hall
  induction values with
  | nil =>
      simp
  | cons value values ih =>
      rw [List.pairwise_cons]
      constructor
      · intro tail htail
        exact hrelation value tail
          (hall value (by simp))
          (hall tail (by simp [htail]))
      · apply ih
        intro tail htail
        exact hall tail (by simp [htail])

/-- On a word consisting of a forced block followed by a suffix block,
canonical class ordering dominates every actual ordered pair charge. -/
theorem ute_listPairObjective_le_canonical
    {s : ℝ} (hs : 0 ≤ s)
    (forcedBlock suffixBlock : List UTEEndpoint)
    (hforced : ∀ endpoint ∈ forcedBlock, endpoint.IsForced)
    (hsuffix : ∀ endpoint ∈ suffixBlock, ¬ endpoint.IsForced) :
    listPairObjective (fun _ => 0) (uteALGPairCharge s)
        (forcedBlock ++ suffixBlock) ≤
      listPairObjective (fun _ => 0)
        (uteCanonicalALGPairCharge s)
        (forcedBlock ++ suffixBlock) := by
  apply listPairObjective_mono_of_pairwise
  · simp
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact pairwise_of_mem_property
        (values := forcedBlock)
        (property := fun endpoint : UTEEndpoint =>
          endpoint.IsForced)
        (relation := fun left right =>
          uteALGPairCharge s left right ≤
            uteCanonicalALGPairCharge s left right)
        (fun left right hleft _hright =>
          uteALGPairCharge_le_canonical_forced_left hs hleft)
        hforced
    · exact pairwise_of_mem_property
        (values := suffixBlock)
        (property := fun endpoint : UTEEndpoint =>
          ¬ endpoint.IsForced)
        (relation := fun left right =>
          uteALGPairCharge s left right ≤
            uteCanonicalALGPairCharge s left right)
        (fun left right hleft hright =>
          uteALGPairCharge_le_canonical_suffix hs hleft hright)
        hsuffix
    · intro left hleft right _hright
      exact uteALGPairCharge_le_canonical_forced_left hs
        (hforced left hleft)

def uteCanonicalEndpointList
    (af zf d t m zs : ℕ) : List UTEEndpoint :=
  List.replicate af .forcedCap ++
    List.replicate zf .forcedZero ++
    List.replicate d .cappedDeferred ++
    List.replicate t .boundaryDeferred ++
    List.replicate m .immediateOne ++
    List.replicate zs .suffixZero

theorem uteEndpointList_perm_canonical
    (values : List UTEEndpoint) :
    values.Perm
      (uteCanonicalEndpointList
        (values.count .forcedCap)
        (values.count .forcedZero)
        (values.count .cappedDeferred)
        (values.count .boundaryDeferred)
        (values.count .immediateOne)
        (values.count .suffixZero)) := by
  apply List.perm_iff_count.mpr
  intro endpoint
  cases endpoint <;>
    simp [uteCanonicalEndpointList, List.count_replicate]

def uteFiniteALGCore
    (s : ℝ) (af zf d t m zs : ℕ) : ℝ :=
  (af : ℝ) * (af - 1) / 2 *
      uteALGPairCharge s .forcedCap .forcedCap +
    (zf : ℝ) * (zf - 1) / 2 *
      uteALGPairCharge s .forcedZero .forcedZero +
    (d : ℝ) * (d - 1) / 2 *
      uteALGPairCharge s .cappedDeferred .cappedDeferred +
    (t : ℝ) * (t - 1) / 2 *
      uteALGPairCharge s .boundaryDeferred .boundaryDeferred +
    (m : ℝ) * (m - 1) / 2 *
      uteALGPairCharge s .immediateOne .immediateOne +
    (zs : ℝ) * (zs - 1) / 2 *
      uteALGPairCharge s .suffixZero .suffixZero +
    af * zf * uteALGPairCharge s .forcedCap .forcedZero +
    af * d * uteALGPairCharge s .forcedCap .cappedDeferred +
    af * t * uteALGPairCharge s .forcedCap .boundaryDeferred +
    af * m * uteALGPairCharge s .forcedCap .immediateOne +
    af * zs * uteALGPairCharge s .forcedCap .suffixZero +
    zf * d * uteALGPairCharge s .forcedZero .cappedDeferred +
    zf * t * uteALGPairCharge s .forcedZero .boundaryDeferred +
    zf * m * uteALGPairCharge s .forcedZero .immediateOne +
    zf * zs * uteALGPairCharge s .forcedZero .suffixZero +
    d * t * uteALGPairCharge s .cappedDeferred .boundaryDeferred +
    d * m * uteALGPairCharge s .cappedDeferred .immediateOne +
    d * zs * uteALGPairCharge s .cappedDeferred .suffixZero +
    t * m * uteALGPairCharge s .boundaryDeferred .immediateOne +
    t * zs * uteALGPairCharge s .boundaryDeferred .suffixZero +
    m * zs * uteALGPairCharge s .immediateOne .suffixZero

def uteFiniteOPTCore
    (s : ℝ) (af zf d t m zs : ℕ) : ℝ :=
  (af : ℝ) * (af - 1) / 2 *
      uteOPTPairCharge s .forcedCap .forcedCap +
    (zf : ℝ) * (zf - 1) / 2 *
      uteOPTPairCharge s .forcedZero .forcedZero +
    (d : ℝ) * (d - 1) / 2 *
      uteOPTPairCharge s .cappedDeferred .cappedDeferred +
    (t : ℝ) * (t - 1) / 2 *
      uteOPTPairCharge s .boundaryDeferred .boundaryDeferred +
    (m : ℝ) * (m - 1) / 2 *
      uteOPTPairCharge s .immediateOne .immediateOne +
    (zs : ℝ) * (zs - 1) / 2 *
      uteOPTPairCharge s .suffixZero .suffixZero +
    af * zf * uteOPTPairCharge s .forcedCap .forcedZero +
    af * d * uteOPTPairCharge s .forcedCap .cappedDeferred +
    af * t * uteOPTPairCharge s .forcedCap .boundaryDeferred +
    af * m * uteOPTPairCharge s .forcedCap .immediateOne +
    af * zs * uteOPTPairCharge s .forcedCap .suffixZero +
    zf * d * uteOPTPairCharge s .forcedZero .cappedDeferred +
    zf * t * uteOPTPairCharge s .forcedZero .boundaryDeferred +
    zf * m * uteOPTPairCharge s .forcedZero .immediateOne +
    zf * zs * uteOPTPairCharge s .forcedZero .suffixZero +
    d * t * uteOPTPairCharge s .cappedDeferred .boundaryDeferred +
    d * m * uteOPTPairCharge s .cappedDeferred .immediateOne +
    d * zs * uteOPTPairCharge s .cappedDeferred .suffixZero +
    t * m * uteOPTPairCharge s .boundaryDeferred .immediateOne +
    t * zs * uteOPTPairCharge s .boundaryDeferred .suffixZero +
    m * zs * uteOPTPairCharge s .immediateOne .suffixZero

theorem uteFiniteALGCore_eq_literal_sub_diagonal
    (s : ℝ) (af zf d t m zs : ℕ) :
    uteFiniteALGCore s af zf d t m zs =
      uteLiteralALGCore s af zf d t m zs -
        ((af : ℝ) / 2 *
            uteALGPairCharge s .forcedCap .forcedCap +
          (zf : ℝ) / 2 *
            uteALGPairCharge s .forcedZero .forcedZero +
          (d : ℝ) / 2 *
            uteALGPairCharge s .cappedDeferred .cappedDeferred +
          (t : ℝ) / 2 *
            uteALGPairCharge s .boundaryDeferred .boundaryDeferred +
          (m : ℝ) / 2 *
            uteALGPairCharge s .immediateOne .immediateOne +
          (zs : ℝ) / 2 *
            uteALGPairCharge s .suffixZero .suffixZero) := by
  unfold uteFiniteALGCore uteLiteralALGCore
  ring

theorem uteFiniteOPTCore_eq_literal_sub_diagonal
    (s : ℝ) (af zf d t m zs : ℕ) :
    uteFiniteOPTCore s af zf d t m zs =
      uteLiteralOPTCore s af zf d t m zs -
        ((af : ℝ) / 2 *
            uteOPTPairCharge s .forcedCap .forcedCap +
          (zf : ℝ) / 2 *
            uteOPTPairCharge s .forcedZero .forcedZero +
          (d : ℝ) / 2 *
            uteOPTPairCharge s .cappedDeferred .cappedDeferred +
          (t : ℝ) / 2 *
            uteOPTPairCharge s .boundaryDeferred .boundaryDeferred +
          (m : ℝ) / 2 *
            uteOPTPairCharge s .immediateOne .immediateOne +
          (zs : ℝ) / 2 *
            uteOPTPairCharge s .suffixZero .suffixZero) := by
  unfold uteFiniteOPTCore uteLiteralOPTCore
  ring

theorem uteLiteralALGCore_scale
    (s scale af zf d t m zs : ℝ) :
    uteLiteralALGCore s
        (scale * af) (scale * zf) (scale * d)
        (scale * t) (scale * m) (scale * zs) =
      scale ^ 2 * uteLiteralALGCore s af zf d t m zs := by
  unfold uteLiteralALGCore
  ring

theorem uteLiteralOPTCore_scale
    (s scale af zf d t m zs : ℝ) :
    uteLiteralOPTCore s
        (scale * af) (scale * zf) (scale * d)
        (scale * t) (scale * m) (scale * zs) =
      scale ^ 2 * uteLiteralOPTCore s af zf d t m zs := by
  unfold uteLiteralOPTCore
  ring

theorem uteLiteralALGCore_mono_forcedZero
    {s af zf zf' d t m zs : ℝ}
    (hs : 0 ≤ s)
    (haf : 0 ≤ af) (hzf : 0 ≤ zf) (hzz : zf ≤ zf')
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m) (hzs : 0 ≤ zs) :
    uteLiteralALGCore s af zf d t m zs ≤
      uteLiteralALGCore s af zf' d t m zs := by
  have hsum : 0 ≤ zf' + zf := by linarith
  have hfactor :
      0 ≤
        (zf' + zf) / 2 *
            uteALGPairCharge s .forcedZero .forcedZero +
          af * uteALGPairCharge s .forcedCap .forcedZero +
          d * uteALGPairCharge s .forcedZero .cappedDeferred +
          t * uteALGPairCharge s .forcedZero .boundaryDeferred +
          m * uteALGPairCharge s .forcedZero .immediateOne +
          zs * uteALGPairCharge s .forcedZero .suffixZero := by
    simp [uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate]
    positivity
  have hid :
      uteLiteralALGCore s af zf' d t m zs -
          uteLiteralALGCore s af zf d t m zs =
        (zf' - zf) *
          ((zf' + zf) / 2 *
              uteALGPairCharge s .forcedZero .forcedZero +
            af * uteALGPairCharge s .forcedCap .forcedZero +
            d * uteALGPairCharge s .forcedZero .cappedDeferred +
            t * uteALGPairCharge s .forcedZero .boundaryDeferred +
            m * uteALGPairCharge s .forcedZero .immediateOne +
            zs * uteALGPairCharge s .forcedZero .suffixZero) := by
    unfold uteLiteralALGCore
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hzz) hfactor

theorem uteLiteralALGCore_mono_suffixZero
    {s af zf d t m zs zs' : ℝ}
    (hs : 0 ≤ s)
    (haf : 0 ≤ af) (hzf : 0 ≤ zf)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hzs : 0 ≤ zs) (hzz : zs ≤ zs') :
    uteLiteralALGCore s af zf d t m zs ≤
      uteLiteralALGCore s af zf d t m zs' := by
  have hsum : 0 ≤ zs' + zs := by linarith
  have hfactor :
      0 ≤
        (zs' + zs) / 2 *
            uteALGPairCharge s .suffixZero .suffixZero +
          af * uteALGPairCharge s .forcedCap .suffixZero +
          zf * uteALGPairCharge s .forcedZero .suffixZero +
          d * uteALGPairCharge s .cappedDeferred .suffixZero +
          t * uteALGPairCharge s .boundaryDeferred .suffixZero +
          m * uteALGPairCharge s .immediateOne .suffixZero := by
    simp [uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate]
    positivity
  have hid :
      uteLiteralALGCore s af zf d t m zs' -
          uteLiteralALGCore s af zf d t m zs =
        (zs' - zs) *
          ((zs' + zs) / 2 *
              uteALGPairCharge s .suffixZero .suffixZero +
            af * uteALGPairCharge s .forcedCap .suffixZero +
            zf * uteALGPairCharge s .forcedZero .suffixZero +
            d * uteALGPairCharge s .cappedDeferred .suffixZero +
            t * uteALGPairCharge s .boundaryDeferred .suffixZero +
            m * uteALGPairCharge s .immediateOne .suffixZero) := by
    unfold uteLiteralALGCore
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hzz) hfactor

theorem uteFiniteALGCore_le_literal
    {s : ℝ} (hs : 0 ≤ s)
    (af zf d t m zs : ℕ) :
    uteFiniteALGCore s af zf d t m zs ≤
      uteLiteralALGCore s af zf d t m zs := by
  rw [uteFiniteALGCore_eq_literal_sub_diagonal]
  have hdiag :
      0 ≤
        ((af : ℝ) / 2 *
            uteALGPairCharge s .forcedCap .forcedCap +
          (zf : ℝ) / 2 *
            uteALGPairCharge s .forcedZero .forcedZero +
          (d : ℝ) / 2 *
            uteALGPairCharge s .cappedDeferred .cappedDeferred +
          (t : ℝ) / 2 *
            uteALGPairCharge s .boundaryDeferred .boundaryDeferred +
          (m : ℝ) / 2 *
            uteALGPairCharge s .immediateOne .immediateOne +
          (zs : ℝ) / 2 *
            uteALGPairCharge s .suffixZero .suffixZero) := by
    simp [uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate]
    positivity
  linarith

theorem uteLiteralOPTCore_add_zero_mass
    {s af zf d t m zs theta eta : ℝ}
    (hs : 1 ≤ s) :
    uteLiteralOPTCore s af (zf + theta) d t m (zs + eta) =
      uteLiteralOPTCore s af zf d t m zs +
        (theta + eta) * (af + zf + d + t + m + zs) +
        (theta + eta) ^ 2 / 2 := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  have htwo : (2 : ℝ) ≤ s + 1 := by linarith
  have hminTwo :
      min ((1 : ℝ) + 1) (s + 1) = 2 := by
    convert min_eq_left htwo using 1 <;> norm_num
  have hminOneLeft :
      min (1 : ℝ) (min (1 + 1) (s + 1)) = 1 := by
    rw [hminTwo]
    norm_num
  have hminOneRight :
      min (min ((1 : ℝ) + 1) (s + 1)) 1 = 1 := by
    rw [hminTwo]
    norm_num
  simp [uteLiteralOPTCore, uteOPTPairCharge,
    uteEndpointEffective, uteEndpointProcessing,
    min_eq_left hone, min_eq_right hone,
    min_eq_left htwo, min_eq_right htwo]
  rw [hminOneLeft, hminOneRight, hminTwo]
  ring

theorem uteFiniteOPT_diagonal_le
    {s : ℝ} (hs : 1 ≤ s)
    (af zf d t m zs : ℕ) :
    uteLiteralOPTCore s af zf d t m zs -
        uteFiniteOPTCore s af zf d t m zs ≤
      (s + 1) / 2 * (af + zf + d + t + m + zs) := by
  rw [uteFiniteOPTCore_eq_literal_sub_diagonal]
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  have htwo : (2 : ℝ) ≤ s + 1 := by linarith
  simp [uteOPTPairCharge, uteEndpointEffective,
    uteEndpointProcessing, min_eq_left hone,
    min_eq_right hone, min_eq_left htwo,
    min_eq_right htwo]
  push_cast
  have haf : (0 : ℝ) ≤ af := by positivity
  have hzf : (0 : ℝ) ≤ zf := by positivity
  have hd : (0 : ℝ) ≤ d := by positivity
  have ht : (0 : ℝ) ≤ t := by positivity
  have hm : (0 : ℝ) ≤ m := by positivity
  have hzs : (0 : ℝ) ≤ zs := by positivity
  have hminBound :
      min ((1 : ℝ) + 1) (s + 1) ≤ s + 1 :=
    min_le_right _ _
  have hzfTerm :
      (zf : ℝ) / 2 ≤ (zf : ℝ) / 2 * (s + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hzf]
  have hzsTerm :
      (zs : ℝ) / 2 ≤ (zs : ℝ) / 2 * (s + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hzs]
  have htTerm :
      (t : ℝ) / 2 * min (1 + 1) (s + 1) ≤
        (t : ℝ) / 2 * (s + 1) :=
    mul_le_mul_of_nonneg_left hminBound (by positivity)
  have hmTerm :
      (m : ℝ) / 2 * min (1 + 1) (s + 1) ≤
        (m : ℝ) / 2 * (s + 1) :=
    mul_le_mul_of_nonneg_left hminBound (by positivity)
  nlinarith

theorem uteLiteralALGWithPrefix_normalized
    {n : ℕ} (hn : n ≠ 0)
    (s b af d t m : ℝ) :
    (n : ℝ) ^ 2 *
        uteLiteralALGWithPrefix s b
          (af / n) (d / n) (t / n) (m / n) =
      uteLiteralALGCore s af ((n : ℝ) * b - af) d t m
        ((n : ℝ) * (1 - b) - d - t - m) := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold uteLiteralALGWithPrefix
  rw [← uteLiteralALGCore_scale s (n : ℝ)
    (af / n) (b - af / n) (d / n) (t / n) (m / n)
    (1 - b - d / n - t / n - m / n)]
  field_simp [hnreal]

theorem uteLiteralOPTWithPrefix_normalized
    {n : ℕ} (hn : n ≠ 0)
    (s b af d t m : ℝ) :
    (n : ℝ) ^ 2 *
        uteLiteralOPTWithPrefix s b
          (af / n) (d / n) (t / n) (m / n) =
      uteLiteralOPTCore s af ((n : ℝ) * b - af) d t m
        ((n : ℝ) * (1 - b) - d - t - m) := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold uteLiteralOPTWithPrefix
  rw [← uteLiteralOPTCore_scale s (n : ℝ)
    (af / n) (b - af / n) (d / n) (t / n) (m / n)
    (1 - b - d / n - t / n - m / n)]
  field_simp [hnreal]

set_option maxHeartbeats 800000 in
/-- Removing one suffix job absorbs the `floor (bn)` discrepancy.  The
remaining integral endpoint counts fit the exact scalar mass constraints;
the missing job contributes only the displayed linear offline allowance. -/
theorem uteFinite_pairExcess_le_normalized
    {n k af zf d t m zs : ℕ} {s b rho : ℝ}
    (hn : n ≠ 0) (hs : 1 ≤ s)
    (hkLower : (k : ℝ) ≤ b * n)
    (hkUpper : b * n < k + 1)
    (hforced : af + zf = k)
    (htotal : af + zf + d + t + m + zs + 1 = n)
    (hrho : 0 ≤ rho) :
    uteFiniteALGCore s af zf d t m zs -
        rho * uteFiniteOPTCore s af zf d t m zs ≤
      (n : ℝ) ^ 2 *
        (uteLiteralALGWithPrefix s b
            (af / n) (d / n) (t / n) (m / n) -
          rho * uteLiteralOPTWithPrefix s b
            (af / n) (d / n) (t / n) (m / n)) +
        rho * (s + 3) * n := by
  let theta : ℝ := b * n - k
  let eta : ℝ := k + 1 - b * n
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact sub_nonneg.mpr hkLower
  have heta : 0 ≤ eta := by
    dsimp [eta]
    linarith
  have hthetaEta : theta + eta = 1 := by
    dsimp [theta, eta]
    ring
  have hforcedR :
      (af : ℝ) + zf = k := by
    exact_mod_cast hforced
  have htotalR :
      (af : ℝ) + zf + d + t + m + zs + 1 = n := by
    exact_mod_cast htotal
  have hzTarget :
      (n : ℝ) * b - af = zf + theta := by
    dsimp [theta]
    nlinarith
  have hzsTarget :
      (n : ℝ) * (1 - b) - d - t - m = zs + eta := by
    dsimp [eta]
    nlinarith
  have holdSum :
      (af : ℝ) + zf + d + t + m + zs = n - 1 := by
    linarith
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have haf0 : (0 : ℝ) ≤ af := by positivity
  have hzf0 : (0 : ℝ) ≤ zf := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hzs0 : (0 : ℝ) ≤ zs := by positivity
  have hzfTheta : 0 ≤ (zf : ℝ) + theta := by positivity
  have halgOld :
      uteFiniteALGCore s af zf d t m zs ≤
        uteLiteralALGCore s af zf d t m zs :=
    uteFiniteALGCore_le_literal hs0 af zf d t m zs
  have halgTheta :
      uteLiteralALGCore s af zf d t m zs ≤
        uteLiteralALGCore s af (zf + theta) d t m zs :=
    uteLiteralALGCore_mono_forcedZero hs0
      haf0 hzf0 (by linarith) hd0 ht0 hm0 hzs0
  have halgEta :
      uteLiteralALGCore s af (zf + theta) d t m zs ≤
        uteLiteralALGCore s af (zf + theta) d t m (zs + eta) :=
    uteLiteralALGCore_mono_suffixZero hs0
      haf0 hzfTheta hd0 ht0 hm0 hzs0 (by linarith)
  have halg :
      uteFiniteALGCore s af zf d t m zs ≤
        uteLiteralALGCore s af ((n : ℝ) * b - af) d t m
          ((n : ℝ) * (1 - b) - d - t - m) := by
    rw [hzTarget, hzsTarget]
    exact halgOld.trans (halgTheta.trans halgEta)
  have hdiag :=
    uteFiniteOPT_diagonal_le hs af zf d t m zs
  have hoptAdd :=
    uteLiteralOPTCore_add_zero_mass
      (s := s) (af := (af : ℝ)) (zf := (zf : ℝ))
      (d := (d : ℝ)) (t := (t : ℝ)) (m := (m : ℝ))
      (zs := (zs : ℝ)) (theta := theta) (eta := eta) hs
  have hopt :
      uteLiteralOPTCore s af ((n : ℝ) * b - af) d t m
            ((n : ℝ) * (1 - b) - d - t - m) -
          uteFiniteOPTCore s af zf d t m zs ≤
        (s + 3) * n := by
    rw [hzTarget, hzsTarget, hoptAdd]
    have hsn :
        0 ≤ (s + 1) * ((n : ℝ) - 1) := by positivity
    nlinarith
  have hoptScaled :
      rho *
          (uteLiteralOPTCore s af ((n : ℝ) * b - af) d t m
              ((n : ℝ) * (1 - b) - d - t - m) -
            uteFiniteOPTCore s af zf d t m zs) ≤
        rho * ((s + 3) * n) :=
    mul_le_mul_of_nonneg_left hopt hrho
  have halgNorm :=
    uteLiteralALGWithPrefix_normalized hn
      s b (af : ℝ) (d : ℝ) (t : ℝ) (m : ℝ)
  have hoptNorm :=
    uteLiteralOPTWithPrefix_normalized hn
      s b (af : ℝ) (d : ℝ) (t : ℝ) (m : ℝ)
  have hgapNorm :
      (n : ℝ) ^ 2 *
          (uteLiteralALGWithPrefix s b
              (af / n) (d / n) (t / n) (m / n) -
            rho * uteLiteralOPTWithPrefix s b
              (af / n) (d / n) (t / n) (m / n)) =
        uteLiteralALGCore s af ((n : ℝ) * b - af) d t m
            ((n : ℝ) * (1 - b) - d - t - m) -
          rho *
            uteLiteralOPTCore s af ((n : ℝ) * b - af) d t m
              ((n : ℝ) * (1 - b) - d - t - m) := by
    calc
      (n : ℝ) ^ 2 *
          (uteLiteralALGWithPrefix s b
              (af / n) (d / n) (t / n) (m / n) -
            rho * uteLiteralOPTWithPrefix s b
              (af / n) (d / n) (t / n) (m / n)) =
        (n : ℝ) ^ 2 *
            uteLiteralALGWithPrefix s b
              (af / n) (d / n) (t / n) (m / n) -
          rho * ((n : ℝ) ^ 2 *
            uteLiteralOPTWithPrefix s b
              (af / n) (d / n) (t / n) (m / n)) := by ring
      _ =
        uteLiteralALGCore s af ((n : ℝ) * b - af) d t m
            ((n : ℝ) * (1 - b) - d - t - m) -
          rho *
            uteLiteralOPTCore s af ((n : ℝ) * b - af) d t m
              ((n : ℝ) * (1 - b) - d - t - m) := by
        rw [halgNorm, hoptNorm]
  rw [hgapNorm]
  nlinarith

theorem canonicalEndpointList_alg_eq_finiteCore
    (s : ℝ) (af zf d t m zs : ℕ) :
    listPairObjective (fun _ => 0)
        (uteCanonicalALGPairCharge s)
        (uteCanonicalEndpointList af zf d t m zs) =
      uteFiniteALGCore s af zf d t m zs := by
  simp only [uteCanonicalEndpointList]
  simp only [List.append_assoc]
  rw [listPairObjective_replicate_append
      (uteCanonicalALGPairCharge s) .forcedCap af,
    listPairObjective_replicate_append
      (uteCanonicalALGPairCharge s) .forcedZero zf,
    listPairObjective_replicate_append
      (uteCanonicalALGPairCharge s) .cappedDeferred d,
    listPairObjective_replicate_append
      (uteCanonicalALGPairCharge s) .boundaryDeferred t,
    listPairObjective_replicate_append
      (uteCanonicalALGPairCharge s) .immediateOne m,
    listPairObjective_replicate
      (uteCanonicalALGPairCharge s) .suffixZero zs]
  simp [uteCanonicalALGPairCharge, UTEEndpoint.rank,
    uteFiniteALGCore]
  ring

theorem canonicalEndpointList_opt_eq_finiteCore
    (s : ℝ) (af zf d t m zs : ℕ) :
    listPairObjective (fun _ => 0)
        (uteOPTPairCharge s)
        (uteCanonicalEndpointList af zf d t m zs) =
      uteFiniteOPTCore s af zf d t m zs := by
  simp only [uteCanonicalEndpointList]
  simp only [List.append_assoc]
  rw [listPairObjective_replicate_append
      (uteOPTPairCharge s) .forcedCap af,
    listPairObjective_replicate_append
      (uteOPTPairCharge s) .forcedZero zf,
    listPairObjective_replicate_append
      (uteOPTPairCharge s) .cappedDeferred d,
    listPairObjective_replicate_append
      (uteOPTPairCharge s) .boundaryDeferred t,
    listPairObjective_replicate_append
      (uteOPTPairCharge s) .immediateOne m,
    listPairObjective_replicate
      (uteOPTPairCharge s) .suffixZero zs]
  simp [uteFiniteOPTCore]
  ring

theorem listPairObjective_canonicalALG_eq_finiteCore
    (s : ℝ) (values : List UTEEndpoint) :
    listPairObjective (fun _ => 0)
        (uteCanonicalALGPairCharge s) values =
      uteFiniteALGCore s
        (values.count .forcedCap)
        (values.count .forcedZero)
        (values.count .cappedDeferred)
        (values.count .boundaryDeferred)
        (values.count .immediateOne)
        (values.count .suffixZero) := by
  rw [listPairObjective_perm (fun _ => 0)
      (uteCanonicalALGPairCharge s)
      (uteCanonicalALGPairCharge_comm s)
      (uteEndpointList_perm_canonical values)]
  exact canonicalEndpointList_alg_eq_finiteCore s _ _ _ _ _ _

theorem listPairObjective_opt_eq_finiteCore
    (s : ℝ) (values : List UTEEndpoint) :
    listPairObjective (fun _ => 0)
        (uteOPTPairCharge s) values =
      uteFiniteOPTCore s
        (values.count .forcedCap)
        (values.count .forcedZero)
        (values.count .cappedDeferred)
        (values.count .boundaryDeferred)
        (values.count .immediateOne)
        (values.count .suffixZero) := by
  rw [listPairObjective_perm (fun _ => 0)
      (uteOPTPairCharge s)
      (uteOPTPairCharge_comm s)
      (uteEndpointList_perm_canonical values)]
  exact canonicalEndpointList_opt_eq_finiteCore s _ _ _ _ _ _

end

end SchedulingPaper
