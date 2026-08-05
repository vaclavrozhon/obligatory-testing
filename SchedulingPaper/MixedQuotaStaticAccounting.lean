import SchedulingPaper.MixedQuotaLower
import Mathlib.Tactic

/-!
# Static accounting for the finite mixed benchmark

The mixed lower construction freezes to `C` capped jobs together with a
finite harmonic tail.  This file identifies the exact sorted effective-length
list and evaluates its offline prefix cost as `mixedFiniteOffline`.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-- Sorted effective lengths of the finite harmonic tail. -/
def mixedHarmonicEffectiveCandidate (K Z : ℕ) : List ℝ :=
  List.replicate Z 1 ++
    (harmonicFutureLevels (Z : ℝ) 0 K).map (fun p => 1 + p)

/-- Sorted effective lengths of the harmonic tail followed by `C` caps. -/
def mixedEffectiveCandidate (u : ℝ) (C K Z : ℕ) : List ℝ :=
  mixedHarmonicEffectiveCandidate K Z ++ List.replicate C u

@[simp] theorem mixedHarmonicEffectiveCandidate_length (K Z : ℕ) :
    (mixedHarmonicEffectiveCandidate K Z).length = K + Z := by
  simp [mixedHarmonicEffectiveCandidate, Nat.add_comm]

theorem mixedHarmonicEffectiveCandidate_sum (K Z : ℕ) :
    (mixedHarmonicEffectiveCandidate K Z).sum =
      (K + Z : ℕ) +
        (harmonicFutureLevels (Z : ℝ) 0 K).sum := by
  have hmap (xs : List ℝ) :
      (xs.map (fun p => 1 + p)).sum =
        (xs.length : ℝ) + xs.sum := by
    induction xs with
    | nil => simp
    | cons p xs ih =>
        simp [ih]
        ring
  simp [mixedHarmonicEffectiveCandidate, hmap]
  push_cast
  ring

@[simp] theorem mixedEffectiveCandidate_length
    (u : ℝ) (C K Z : ℕ) :
    (mixedEffectiveCandidate u C K Z).length = C + K + Z := by
  simp [mixedEffectiveCandidate]
  omega

/-- The list expression for the mixed frozen instance is exactly the finite
offline benchmark used by the analytic ratio calculation. -/
theorem prefixCost_mixedEffectiveCandidate
    {Z : ℕ} (hZ : 0 < Z) (u : ℝ) (C K : ℕ) :
    prefixCost (mixedEffectiveCandidate u C K Z) =
      mixedFiniteOffline u C K Z := by
  unfold mixedEffectiveCandidate mixedFiniteOffline
  rw [prefixCost_append, prefixCost_replicate,
    mixedHarmonicEffectiveCandidate_sum]
  simp only [List.length_replicate, Nat.cast_ofNat]
  have htail :=
    harmonicEffectiveCandidate_cost
      (ξ := (Z : ℝ)) (γ := 0)
      (by exact_mod_cast hZ) K Z
  change
    prefixCost (mixedHarmonicEffectiveCandidate K Z) +
          (C : ℝ) *
            ((K + Z : ℕ) +
              (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
        u * triangular C =
      harmonicFiniteOffline K Z 0 +
        (C : ℝ) *
          ((K + Z : ℕ) +
            (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
        u * triangular C
  have hcandidate :
      prefixCost (mixedHarmonicEffectiveCandidate K Z) =
        harmonicFiniteOffline K Z 0 := by
    simpa [mixedHarmonicEffectiveCandidate,
      harmonicFiniteOffline] using htail
  rw [hcandidate]

/-- If every harmonic effective length fits below the cap, the displayed
mixed candidate is already in shortest-first order. -/
theorem mixedEffectiveCandidate_pairwise
    {u : ℝ} {C K Z : ℕ} (hZ : 0 < Z)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u) :
    (mixedEffectiveCandidate u C K Z).Pairwise (· ≤ ·) := by
  unfold mixedEffectiveCandidate
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · exact harmonicEffectiveCandidate_pairwise
      (by exact_mod_cast hZ) (le_refl 0) K Z
  · intro a ha b hb
    have hbEq : b = u := (List.mem_replicate.mp hb).2
    subst b
    rcases List.mem_append.mp ha with ha | ha
    · have haEq : a = 1 := (List.mem_replicate.mp ha).2
      subst a
      have hzero := hsafe 0 (Nat.zero_le K)
      rw [harmonicLevel_zero] at hzero
      norm_num at hzero
      linarith
    · rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨L, hL, rfl⟩
      exact hsafe L (Nat.le_of_lt (Finset.mem_range.mp hL))

/-- A frozen vector whose effective lengths are a permutation of the mixed
candidate has exactly `mixedFiniteOffline` as its clairvoyant optimum. -/
theorem vectorOfflineCost_eq_mixedFiniteOffline_of_perm
    {n C K Z : ℕ} {u : ℝ} (hZ : 0 < Z)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u)
    (processingTime : Online.Label n → ℝ)
    (hperm :
      (mixedEffectiveCandidate u C K Z).Perm
        (vectorEffectiveLengths (.finite u) processingTime)) :
    vectorOfflineCost (.finite u) processingTime =
      mixedFiniteOffline u C K Z := by
  unfold vectorOfflineCost
  rw [shortestFirst_pair_formula]
  rw [← pairCost_perm hperm]
  rw [← prefixCost_eq_pairCost_of_pairwise
    (mixedEffectiveCandidate_pairwise hZ hsafe)]
  exact prefixCost_mixedEffectiveCandidate hZ u C K

end LowerBound

end

end SchedulingPaper
