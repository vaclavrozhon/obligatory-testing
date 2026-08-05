import SchedulingPaper.ForcedPrefixUTE
import SchedulingPaper.UTEEndpointReduction
import SchedulingPaper.EndpointReduction
import Mathlib.Tactic

/-!
# Literal pair accounting for ForcedPrefixUTE

This module supplies the literal pairwise layer immediately before the
four-mass objectives `uteA` and `uteO`.  For a forced-prefix fraction `b`,
the canonical endpoint order is

`forced-cap, forced-zero, capped-deferred, boundary-deferred,
 immediate-one, suffix-zero`.

The corresponding masses are

`a, b-a, d, t, m, 1-b-d-t-m`.

The online pair charge follows the actual test order and the immediate versus
deferred decision.  The offline charge is the finite-cap shortest-first pair
charge.  At `b = uteB s`, their fluid sums are exactly `uteA` and `uteO`.
-/

namespace SchedulingPaper

noncomputable section

open Set

/-- Canonical endpoint classes for a ForcedPrefixUTE word. -/
inductive UTEEndpoint where
  | forcedCap
  | forcedZero
  | cappedDeferred
  | boundaryDeferred
  | immediateOne
  | suffixZero
  deriving DecidableEq

/-- Endpoint processing value when the finite upper cap is `s+1`. -/
def uteEndpointProcessing (s : ℝ) : UTEEndpoint → ℝ
  | .forcedCap | .cappedDeferred => s + 1
  | .boundaryDeferred | .immediateOne => 1
  | .forcedZero | .suffixZero => 0

/-- Whether the endpoint is completed immediately during the test phase. -/
def UTEEndpoint.IsImmediate : UTEEndpoint → Bool
  | .forcedCap | .forcedZero | .immediateOne | .suffixZero => true
  | .cappedDeferred | .boundaryDeferred => false

/-- Literal online contribution of a pair in canonical test order. -/
def uteALGPairCharge
    (s : ℝ) (left right : UTEEndpoint) : ℝ :=
  let p := uteEndpointProcessing s left
  let q := uteEndpointProcessing s right
  if left.IsImmediate then
    1 + p
  else if right.IsImmediate then
    2 + q
  else
    2 + min p q

/-- Effective finite-cap length represented by a UTE endpoint. -/
def uteEndpointEffective (s : ℝ) (endpoint : UTEEndpoint) : ℝ :=
  min (1 + uteEndpointProcessing s endpoint) (s + 1)

/-- Literal shortest-first offline contribution of an unordered pair. -/
def uteOPTPairCharge
    (s : ℝ) (left right : UTEEndpoint) : ℝ :=
  min (uteEndpointEffective s left)
    (uteEndpointEffective s right)

/-- Six-class online pair sum.  Its arguments are the masses in canonical
endpoint order. -/
def uteLiteralALGCore
    (s af zf d t m zs : ℝ) : ℝ :=
  af ^ 2 / 2 * uteALGPairCharge s .forcedCap .forcedCap +
    zf ^ 2 / 2 * uteALGPairCharge s .forcedZero .forcedZero +
    d ^ 2 / 2 *
      uteALGPairCharge s .cappedDeferred .cappedDeferred +
    t ^ 2 / 2 *
      uteALGPairCharge s .boundaryDeferred .boundaryDeferred +
    m ^ 2 / 2 * uteALGPairCharge s .immediateOne .immediateOne +
    zs ^ 2 / 2 * uteALGPairCharge s .suffixZero .suffixZero +
    af * zf * uteALGPairCharge s .forcedCap .forcedZero +
    af * d * uteALGPairCharge s .forcedCap .cappedDeferred +
    af * t * uteALGPairCharge s .forcedCap .boundaryDeferred +
    af * m * uteALGPairCharge s .forcedCap .immediateOne +
    af * zs * uteALGPairCharge s .forcedCap .suffixZero +
    zf * d * uteALGPairCharge s .forcedZero .cappedDeferred +
    zf * t * uteALGPairCharge s .forcedZero .boundaryDeferred +
    zf * m * uteALGPairCharge s .forcedZero .immediateOne +
    zf * zs * uteALGPairCharge s .forcedZero .suffixZero +
    d * t *
      uteALGPairCharge s .cappedDeferred .boundaryDeferred +
    d * m * uteALGPairCharge s .cappedDeferred .immediateOne +
    d * zs * uteALGPairCharge s .cappedDeferred .suffixZero +
    t * m * uteALGPairCharge s .boundaryDeferred .immediateOne +
    t * zs * uteALGPairCharge s .boundaryDeferred .suffixZero +
    m * zs * uteALGPairCharge s .immediateOne .suffixZero

/-- Six-class finite-cap offline pair sum. -/
def uteLiteralOPTCore
    (s af zf d t m zs : ℝ) : ℝ :=
  af ^ 2 / 2 * uteOPTPairCharge s .forcedCap .forcedCap +
    zf ^ 2 / 2 * uteOPTPairCharge s .forcedZero .forcedZero +
    d ^ 2 / 2 *
      uteOPTPairCharge s .cappedDeferred .cappedDeferred +
    t ^ 2 / 2 *
      uteOPTPairCharge s .boundaryDeferred .boundaryDeferred +
    m ^ 2 / 2 * uteOPTPairCharge s .immediateOne .immediateOne +
    zs ^ 2 / 2 * uteOPTPairCharge s .suffixZero .suffixZero +
    af * zf * uteOPTPairCharge s .forcedCap .forcedZero +
    af * d * uteOPTPairCharge s .forcedCap .cappedDeferred +
    af * t * uteOPTPairCharge s .forcedCap .boundaryDeferred +
    af * m * uteOPTPairCharge s .forcedCap .immediateOne +
    af * zs * uteOPTPairCharge s .forcedCap .suffixZero +
    zf * d * uteOPTPairCharge s .forcedZero .cappedDeferred +
    zf * t * uteOPTPairCharge s .forcedZero .boundaryDeferred +
    zf * m * uteOPTPairCharge s .forcedZero .immediateOne +
    zf * zs * uteOPTPairCharge s .forcedZero .suffixZero +
    d * t *
      uteOPTPairCharge s .cappedDeferred .boundaryDeferred +
    d * m * uteOPTPairCharge s .cappedDeferred .immediateOne +
    d * zs * uteOPTPairCharge s .cappedDeferred .suffixZero +
    t * m * uteOPTPairCharge s .boundaryDeferred .immediateOne +
    t * zs * uteOPTPairCharge s .boundaryDeferred .suffixZero +
    m * zs * uteOPTPairCharge s .immediateOne .suffixZero

/-- Literal online objective with forced-prefix fraction `b`. -/
def uteLiteralALGWithPrefix
    (s b a d t m : ℝ) : ℝ :=
  uteLiteralALGCore s a (b - a) d t m
    (1 - b - d - t - m)

/-- Literal offline objective with the same six endpoint masses. -/
def uteLiteralOPTWithPrefix
    (s b a d t m : ℝ) : ℝ :=
  uteLiteralOPTCore s a (b - a) d t m
    (1 - b - d - t - m)

/-- The actual ForcedPrefixUTE online endpoint objective uses
`b = uteB s`. -/
def uteLiteralALG (s a d t m : ℝ) : ℝ :=
  uteLiteralALGWithPrefix s (uteB s) a d t m

/-- The actual finite-cap offline endpoint objective. -/
def uteLiteralOPT (s a d t m : ℝ) : ℝ :=
  uteLiteralOPTWithPrefix s (uteB s) a d t m

/-- Expansion of the literal online pair table for an arbitrary forced-prefix
fraction `b`. -/
theorem uteLiteralALGWithPrefix_eq_polynomial
    {s b a d t m : ℝ} (hs : 0 ≤ s) :
    uteLiteralALGWithPrefix s b a d t m =
      1 / 2 + (s + 1) * (a - a ^ 2 / 2) +
        (1 - b) * (d + t + m) - m ^ 2 / 2 +
        s * d ^ 2 / 2 := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  simp [uteLiteralALGWithPrefix, uteLiteralALGCore,
    uteALGPairCharge, uteEndpointProcessing,
    UTEEndpoint.IsImmediate, min_eq_right hone]
  ring

/-- Expansion of the literal finite-cap shortest-first table. -/
theorem uteLiteralOPTWithPrefix_eq_polynomial
    {s b a d t m : ℝ} (hs : 1 ≤ s) :
    uteLiteralOPTWithPrefix s b a d t m =
      1 / 2 + (a + d + t + m) ^ 2 / 2 +
        (s - 1) * (a + d) ^ 2 / 2 := by
  have htwo : (2 : ℝ) ≤ s + 1 := by linarith
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  simp [uteLiteralOPTWithPrefix, uteLiteralOPTCore,
    uteOPTPairCharge, uteEndpointEffective,
    uteEndpointProcessing, min_eq_left hone,
    min_eq_right hone]
  norm_num only
  rw [min_eq_left htwo]
  norm_num
  ring

/-- Exact identification of the literal online pair objective with `uteA`. -/
theorem uteLiteralALG_eq_uteA
    {s a d t m : ℝ} (hs : 0 ≤ s) :
    uteLiteralALG s a d t m = uteA s a d t m := by
  unfold uteLiteralALG
  rw [uteLiteralALGWithPrefix_eq_polynomial hs]
  rfl

/-- Exact identification of the literal offline pair objective with `uteO`. -/
theorem uteLiteralOPT_eq_uteO
    {s a d t m : ℝ} (hs : 1 ≤ s) :
    uteLiteralOPT s a d t m = uteO s a d t m := by
  unfold uteLiteralOPT
  rw [uteLiteralOPTWithPrefix_eq_polynomial hs]
  rfl

/-- The literal pair excess is exactly the four-mass scalar gap. -/
theorem uteLiteralPairExcess_eq_uteGap
    {s a d t m : ℝ} (hs : 1 ≤ s) :
    uteLiteralALG s a d t m -
        uteRho s * uteLiteralOPT s a d t m =
      uteGap s a d t m := by
  rw [uteLiteralALG_eq_uteA (zero_le_one.trans hs),
    uteLiteralOPT_eq_uteO hs]
  rfl

/-- Literal-pair form of the complete feasible UTE endpoint certificate. -/
theorem uteLiteralALG_le_rho_mul_OPT
    {s a d t m : ℝ}
    (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (ha : 0 ≤ a) (had : a ≤ uteB s)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hmass : d + t + m ≤ 1 - uteB s) :
    uteLiteralALG s a d t m ≤
      uteRho s * uteLiteralOPT s a d t m := by
  rw [uteLiteralALG_eq_uteA (zero_le_one.trans hs1),
    uteLiteralOPT_eq_uteO hs1]
  exact sub_nonpos.mp
    (uteGap_nonpos_of_feasible
      hs1 hs0 ha had hd ht hm hmass)

/-! ## Coordinatewise endpoint reduction on a fixed symbolic word -/

/-- Effective finite-cap length of an arbitrary processing value. -/
def uteEffectiveAt (s p : ℝ) : ℝ :=
  min (1 + p) (s + 1)

/-- The three pair-completion patterns that can occur in a fixed
ForcedPrefixUTE symbolic word. -/
inductive UTEPairSymbol where
  /-- The left job completes immediately after its own test. -/
  | leftAfterOneTest
  /-- Both tests occur before the left job completes. -/
  | leftAfterTwoTests
  /-- Both tests occur before the right job completes. -/
  | rightAfterTwoTests
  deriving DecidableEq

/-- Literal online charge selected by a fixed pair-completion symbol. -/
def uteFixedALGPairCharge :
    UTEPairSymbol → ℝ → ℝ → ℝ
  | .leftAfterOneTest, p, _ => 1 + p
  | .leftAfterTwoTests, p, _ => 2 + p
  | .rightAfterTwoTests, _, q => 2 + q

/-- Literal shortest-first finite-cap pair charge at arbitrary values. -/
def uteFixedOPTPairCharge (s p q : ℝ) : ℝ :=
  min (uteEffectiveAt s p) (uteEffectiveAt s q)

def uteFixedSelfExcessAt (s p : ℝ) : ℝ :=
  (1 + p) - uteRho s * uteEffectiveAt s p

def uteFixedPairExcessAt
    (s : ℝ) (symbol : UTEPairSymbol) (p q : ℝ) : ℝ :=
  uteFixedALGPairCharge symbol p q -
    uteRho s * uteFixedOPTPairCharge s p q

/-- With the right processing value fixed, the capped offline pair charge
is a translated one-variable minimum. -/
theorem uteFixedOPTPairCharge_eq_leftMin
    (s p q : ℝ) :
    uteFixedOPTPairCharge s p q =
      1 + min p (uteEffectiveAt s q - 1) := by
  have hqCap :
      min (1 + q) (s + 1) ≤ s + 1 :=
    min_le_right _ _
  unfold uteFixedOPTPairCharge uteEffectiveAt
  rw [min_assoc, min_eq_right hqCap]
  by_cases hp : p ≤ min (1 + q) (s + 1) - 1
  · rw [min_eq_left hp, min_eq_left (by linarith)]
  · have hp' :
        min (1 + q) (s + 1) - 1 ≤ p :=
      le_of_not_ge hp
    rw [min_eq_right hp', min_eq_right (by linarith)]
    ring

/-- Symmetric translated-min formula with the left value fixed. -/
theorem uteFixedOPTPairCharge_eq_rightMin
    (s p q : ℝ) :
    uteFixedOPTPairCharge s p q =
      1 + min q (uteEffectiveAt s p - 1) := by
  rw [uteFixedOPTPairCharge, min_comm]
  exact uteFixedOPTPairCharge_eq_leftMin s q p

theorem uteEffectiveAt_eq_one_add_min (s p : ℝ) :
    uteEffectiveAt s p = 1 + min p s := by
  unfold uteEffectiveAt
  simpa [add_comm] using min_add_add_left 1 p s

theorem uteFixedSelfExcessAt_convex
    {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ univ (uteFixedSelfExcessAt s) := by
  have h :=
    convexOn_affine_sub_mul_min
      1 (1 - uteRho s) (uteRho s) s (uteRho_pos hs).le
  refine h.congr ?_
  intro p _hp
  rw [uteFixedSelfExcessAt, uteEffectiveAt_eq_one_add_min]
  ring

theorem uteFixedPairExcessAt_convex_left
    {s : ℝ} (hs : 0 < s)
    (symbol : UTEPairSymbol) (q : ℝ) :
    ConvexOn ℝ univ
      (fun p => uteFixedPairExcessAt s symbol p q) := by
  have hρ : 0 ≤ uteRho s := (uteRho_pos hs).le
  cases symbol with
  | leftAfterOneTest =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (1 - uteRho s) (uteRho s)
            (uteEffectiveAt s q - 1) hρ
      refine h.congr ?_
      intro p _hp
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring
  | leftAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (2 - uteRho s) (uteRho s)
            (uteEffectiveAt s q - 1) hρ
      refine h.congr ?_
      intro p _hp
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring
  | rightAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (2 + q - uteRho s) (uteRho s)
            (uteEffectiveAt s q - 1) hρ
      refine h.congr ?_
      intro p _hp
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_leftMin]
      ring

theorem uteFixedPairExcessAt_convex_right
    {s : ℝ} (hs : 0 < s)
    (symbol : UTEPairSymbol) (p : ℝ) :
    ConvexOn ℝ univ
      (fun q => uteFixedPairExcessAt s symbol p q) := by
  have hρ : 0 ≤ uteRho s := (uteRho_pos hs).le
  cases symbol with
  | leftAfterOneTest =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - uteRho s) (uteRho s)
            (uteEffectiveAt s p - 1) hρ
      refine h.congr ?_
      intro q _hq
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring
  | leftAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (2 + p - uteRho s) (uteRho s)
            (uteEffectiveAt s p - 1) hρ
      refine h.congr ?_
      intro q _hq
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring
  | rightAfterTwoTests =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (2 - uteRho s) (uteRho s)
            (uteEffectiveAt s p - 1) hρ
      refine h.congr ?_
      intro q _hq
      simp only [uteFixedPairExcessAt, uteFixedALGPairCharge]
      rw [uteFixedOPTPairCharge_eq_rightMin]
      ring

/-- A symbolic word fixes, for each test-ordered pair, which of the three
possible completion patterns supplies its online pair charge. -/
structure UTEFixedSymbolicWord (n : ℕ) where
  pairSymbol : Fin n → Fin n → UTEPairSymbol

/-- Exact self-plus-unordered-pair excess associated with a fixed symbolic
completion word. -/
def uteFixedWordExcess {n : ℕ}
    (s : ℝ) (word : UTEFixedSymbolicWord n)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, uteFixedSelfExcessAt s (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      uteFixedPairExcessAt s
        (word.pairSymbol i j) (processing i) (processing j)

private theorem ute_convexOn_finset_sum
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

/-- On every finite box, the exact excess of a fixed UTE symbolic word is
convex in each processing coordinate separately. -/
theorem uteFixedWordExcess_coordinatewiseConvex
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (word : UTEFixedSymbolicWord n)
    (lower upper : Fin n → ℝ) :
    CoordinatewiseConvexOnBox lower upper
      (uteFixedWordExcess s word) := by
  classical
  intro processing _hbox coordinate
  let interval : Set ℝ :=
    Icc (lower coordinate) (upper coordinate)
  have hinterval : Convex ℝ interval :=
    convex_Icc (lower coordinate) (upper coordinate)
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
          uteFixedPairExcessAt s (word.pairSymbol i j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    by_cases hi : i = coordinate
    · subst i
      have hj : j ≠ coordinate := ne_of_gt hij
      have hleft :=
        (uteFixedPairExcessAt_convex_left hs
          (word.pairSymbol coordinate j)
          (processing j)).subset (subset_univ _) hinterval
      simpa [Function.update, hj] using hleft
    · by_cases hj : j = coordinate
      · subst j
        have hright :=
          (uteFixedPairExcessAt_convex_right hs
            (word.pairSymbol i coordinate)
            (processing i)).subset (subset_univ _) hinterval
        simpa [Function.update, hi] using hright
      · have hconst :
            (fun x =>
              uteFixedPairExcessAt s (word.pairSymbol i j)
                (Function.update processing coordinate x i)
                (Function.update processing coordinate x j)) =
              (fun _ : ℝ =>
                uteFixedPairExcessAt s (word.pairSymbol i j)
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
    simpa using ute_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => uteFixedSelfExcessAt s
        (Function.update processing coordinate x i))
      (fun i _hi => hself i)
  have hpairRow (i : Fin n) :
      ConvexOn ℝ interval
        (fun x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
          uteFixedPairExcessAt s (word.pairSymbol i j)
            (Function.update processing coordinate x i)
            (Function.update processing coordinate x j)) := by
    apply ute_convexOn_finset_sum hinterval
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hj).2
  have hpairSum :
      ConvexOn ℝ interval
        (fun x => ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            uteFixedPairExcessAt s (word.pairSymbol i j)
              (Function.update processing coordinate x i)
              (Function.update processing coordinate x j)) := by
    simpa using ute_convexOn_finset_sum hinterval
      Finset.univ
      (fun i x => ∑ j ∈ Finset.univ.filter (fun j => i < j),
        uteFixedPairExcessAt s (word.pairSymbol i j)
          (Function.update processing coordinate x i)
          (Function.update processing coordinate x j))
      (fun i _hi => hpairRow i)
  simpa [uteFixedWordExcess, interval, Pi.add_apply] using
    hselfSum.add hpairSum

/-- Iterated coordinatewise endpoint reduction for a fixed UTE symbolic
word. -/
theorem exists_uteFixedWord_endpoint_ge
    {n : ℕ} {s : ℝ} (hs : 0 < s)
    (word : UTEFixedSymbolicWord n)
    (lower upper processing : Fin n → ℝ)
    (horder : ∀ i, lower i ≤ upper i)
    (hprocessing : processing ∈ coordinateBox lower upper) :
    ∃ vertex,
      vertex ∈ coordinateBox lower upper ∧
      IsBoxVertex lower upper vertex ∧
      uteFixedWordExcess s word processing ≤
        uteFixedWordExcess s word vertex :=
  exists_boxVertex_ge horder
    (uteFixedWordExcess_coordinatewiseConvex
      hs word lower upper)
    processing hprocessing

end

end SchedulingPaper
