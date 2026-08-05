import SchedulingPaper.MixedQuotaLower
import Mathlib.Tactic

/-!
# Cap deferral across the finite harmonic tail

This module isolates the list algebra used by the mixed-quota lower
construction.  A tested cap job has a remaining processing block of length
`u`; a tail job of processing time `p` occupies the complete block
`1 + p`.  Interchanging these adjacent blocks changes total completion time
by exactly `u - 1 - p`.  The block versions below sum this identity over a
tail and over any number of pending cap jobs.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-- Complete test/process lengths of the harmonic tail. -/
def mixedTailCompletionBlocks (processing : List ℝ) : List ℝ :=
  processing.map (fun p => 1 + p)

@[simp] theorem mixedTailCompletionBlocks_length
    (processing : List ℝ) :
    (mixedTailCompletionBlocks processing).length = processing.length := by
  simp [mixedTailCompletionBlocks]

theorem mixedTailCompletionBlocks_sum
    (processing : List ℝ) :
    (mixedTailCompletionBlocks processing).sum =
      processing.length + processing.sum := by
  induction processing with
  | nil =>
      simp [mixedTailCompletionBlocks]
  | cons p processing ih =>
      change
        1 + p + (mixedTailCompletionBlocks processing).sum =
          ((processing.length + 1 : ℕ) : ℝ) +
            (p + processing.sum)
      rw [ih]
      push_cast
      ring

/-- Exact adjacent exchange: putting a cap-processing block immediately
before one complete tail block adds `u - 1 - p` to total completion time. -/
theorem mixedCap_tail_adjacent_exchange
    (left right : List ℝ) (u p : ℝ) :
    prefixCost (left ++ u :: (1 + p) :: right) =
      prefixCost (left ++ (1 + p) :: u :: right) +
        (u - 1 - p) := by
  have hswap :=
    prefixCost_adjacent_swap_eq left right u (1 + p)
  linarith

/-- Exact contextual exchange of two whole blocks. -/
theorem prefixCost_swap_blocks_sub_eq
    (left caps tail right : List ℝ) :
    prefixCost (left ++ caps ++ tail ++ right) -
        prefixCost (left ++ tail ++ caps ++ right) =
      (tail.length : ℝ) * caps.sum -
        (caps.length : ℝ) * tail.sum := by
  rw [prefixCost_append, prefixCost_append]
  simp only [List.length_append, List.sum_append]
  rw [prefixCost_append, prefixCost_append]
  simp only [List.length_append, List.sum_append]
  rw [prefixCost_append, prefixCost_append]
  simp only [List.sum_append]
  push_cast
  ring

/-- Iterating the adjacent exchange across an arbitrary tail gives the sum
of the individual gaps `u - 1 - p`. -/
theorem mixedCap_tail_exchange
    (left right processing : List ℝ) (u : ℝ) :
    prefixCost
          (left ++ [u] ++
            mixedTailCompletionBlocks processing ++ right) -
        prefixCost
          (left ++ mixedTailCompletionBlocks processing ++
            [u] ++ right) =
      (processing.length : ℝ) * (u - 1) - processing.sum := by
  rw [prefixCost_swap_blocks_sub_eq]
  simp [mixedTailCompletionBlocks_length,
    mixedTailCompletionBlocks_sum]
  push_cast
  ring

/-- Moving all `q` pending cap-processing blocks behind the tail accumulates
`q` copies of the one-cap exchange gain. -/
theorem mixedCaps_tail_exchange
    (left right processing : List ℝ) (u : ℝ) (q : ℕ) :
    prefixCost
          (left ++ List.replicate q u ++
            mixedTailCompletionBlocks processing ++ right) -
        prefixCost
          (left ++ mixedTailCompletionBlocks processing ++
            List.replicate q u ++ right) =
      (q : ℝ) *
        ((processing.length : ℝ) * (u - 1) - processing.sum) := by
  rw [prefixCost_swap_blocks_sub_eq]
  simp [mixedTailCompletionBlocks_length,
    mixedTailCompletionBlocks_sum, List.sum_replicate]
  push_cast
  ring

/-- The concrete finite harmonic tail: `K` positive levels and `Z` zero
levels.  Its order is immaterial for the cap exchange, but this order agrees
with `harmonicFutureLevels`. -/
def mixedHarmonicTailProcessing (K Z : ℕ) : List ℝ :=
  harmonicFutureLevels (Z : ℝ) 0 K ++ List.replicate Z 0

@[simp] theorem mixedHarmonicTailProcessing_length
    (K Z : ℕ) :
    (mixedHarmonicTailProcessing K Z).length = K + Z := by
  simp [mixedHarmonicTailProcessing]

@[simp] theorem mixedHarmonicTailProcessing_sum
    (K Z : ℕ) :
    (mixedHarmonicTailProcessing K Z).sum =
      (harmonicFutureLevels (Z : ℝ) 0 K).sum := by
  simp [mixedHarmonicTailProcessing]

/-- Exact exchange gain for `q` pending cap processings and the finite
`K + Z` harmonic tail. -/
theorem mixedCaps_harmonicTail_exchange
    (left right : List ℝ) (u : ℝ) (q K Z : ℕ) :
    prefixCost
          (left ++ List.replicate q u ++
            mixedTailCompletionBlocks
              (mixedHarmonicTailProcessing K Z) ++ right) -
        prefixCost
          (left ++
            mixedTailCompletionBlocks
              (mixedHarmonicTailProcessing K Z) ++
            List.replicate q u ++ right) =
      (q : ℝ) *
        (((K + Z : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum) := by
  simpa using
    mixedCaps_tail_exchange left right
      (mixedHarmonicTailProcessing K Z) u q

/-- The scalar deferral margin pays the largest possible cap-cap saving
from `q ≤ C` early cap completions.  Algebraically the difference of the
two sides is
`q * (H*(u-1) - L - C) + triangular q`. -/
theorem earlyCapSavings_le_tailExchangeGain
    {C q H : ℕ} {u L : ℝ}
    (_hq : q ≤ C)
    (hmargin :
      0 ≤ (H : ℝ) * (u - 1) - L - (C : ℝ)) :
    (q : ℝ) * (C : ℝ) - triangular q ≤
      (q : ℝ) * ((H : ℝ) * (u - 1) - L) := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hscaled :
      0 ≤ (q : ℝ) *
        ((H : ℝ) * (u - 1) - L - (C : ℝ)) :=
    mul_nonneg hq0 hmargin
  have htriangular : 0 ≤ triangular q := by
    unfold triangular
    positivity
  linarith

/-- Specialization of the scalar exchange inequality to the finite
harmonic tail used by `mixedFiniteOnline`. -/
theorem earlyCapSavings_le_harmonicTailExchangeGain
    {C q K Z : ℕ} {u : ℝ}
    (hq : q ≤ C)
    (hmargin :
      0 ≤
        (((K + Z : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum -
          (C : ℝ))) :
    (q : ℝ) * (C : ℝ) - triangular q ≤
      (q : ℝ) *
        (((K + Z : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum) := by
  exact earlyCapSavings_le_tailExchangeGain hq hmargin

/-- Competitive-gap form of the completed exchange.  The offline objective
is unchanged by the schedule permutation, so it cancels literally.  The
tail exchange pays both the normalized after-tail schedule and the maximal
cap-cap saving caused by `q` early completions. -/
theorem mixedCaps_harmonicTail_competitiveGap_exchange
    (left right : List ℝ) (u c opt : ℝ)
    {C q K Z : ℕ}
    (hq : q ≤ C)
    (hmargin :
      0 ≤
        (((K + Z : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum -
          (C : ℝ))) :
    prefixCost
          (left ++
            mixedTailCompletionBlocks
              (mixedHarmonicTailProcessing K Z) ++
            List.replicate q u ++ right) -
          c * opt +
          ((q : ℝ) * (C : ℝ) - triangular q) ≤
      prefixCost
          (left ++ List.replicate q u ++
            mixedTailCompletionBlocks
              (mixedHarmonicTailProcessing K Z) ++ right) -
          c * opt := by
  have hexchange :=
    mixedCaps_harmonicTail_exchange left right u q K Z
  have hsavings :=
    earlyCapSavings_le_harmonicTailExchangeGain hq hmargin
  linarith

end LowerBound

end

end SchedulingPaper
