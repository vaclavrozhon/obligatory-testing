import SchedulingPaper.MixedQuotaStaticAccounting
import Mathlib.Tactic

/-!
# Static accounting with the raw-zero prefix

At a mixed crossing, `v` prefix jobs may already have completed raw with
hidden value zero.  Their effective lengths are `v` additional ones before
the harmonic/cap candidate.  This file gives the exact offline objective of
that full vector.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

def mixedExtendedEffectiveCandidate
    (u : ℝ) (v C K Z : ℕ) : List ℝ :=
  List.replicate v 1 ++ mixedEffectiveCandidate u C K Z

def mixedPrefixZeroOffline (v tailSize : ℕ) : ℝ :=
  triangular v + (v : ℝ) * tailSize

def mixedExtendedFiniteOffline
    (u : ℝ) (v C K Z : ℕ) : ℝ :=
  mixedPrefixZeroOffline v (C + K + Z) +
    mixedFiniteOffline u C K Z

@[simp] theorem mixedExtendedEffectiveCandidate_length
    (u : ℝ) (v C K Z : ℕ) :
    (mixedExtendedEffectiveCandidate u v C K Z).length =
      v + C + K + Z := by
  simp [mixedExtendedEffectiveCandidate]
  omega

theorem prefixCost_mixedExtendedEffectiveCandidate
    {Z : ℕ} (hZ : 0 < Z)
    (u : ℝ) (v C K : ℕ) :
    prefixCost
        (mixedExtendedEffectiveCandidate u v C K Z) =
      mixedExtendedFiniteOffline u v C K Z := by
  unfold mixedExtendedEffectiveCandidate
    mixedExtendedFiniteOffline mixedPrefixZeroOffline
  rw [prefixCost_append, prefixCost_replicate,
    prefixCost_mixedEffectiveCandidate hZ]
  simp [List.sum_replicate]
  push_cast
  ring

theorem one_le_of_mem_mixedEffectiveCandidate
    {u : ℝ} {C K Z : ℕ} (hZ : 0 < Z)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u)
    {x : ℝ} (hx : x ∈ mixedEffectiveCandidate u C K Z) :
    1 ≤ x := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · have hxEq : x = 1 := (List.mem_replicate.mp hx).2
      linarith
    · rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨L, hL, rfl⟩
      have hZreal : (0 : ℝ) < Z := by exact_mod_cast hZ
      have hone :=
        harmonicLevel_one_le hZreal (le_refl 0) L
      linarith
  · have hxEq : x = u := (List.mem_replicate.mp hx).2
    subst x
    have htwo := hsafe 0 (Nat.zero_le K)
    rw [harmonicLevel_zero] at htwo
    norm_num at htwo
    linarith

theorem mixedExtendedEffectiveCandidate_pairwise
    {u : ℝ} {v C K Z : ℕ} (hZ : 0 < Z)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u) :
    List.Pairwise (· ≤ ·)
      (mixedExtendedEffectiveCandidate u v C K Z) := by
  unfold mixedExtendedEffectiveCandidate
  rw [List.pairwise_append]
  refine ⟨by simp, mixedEffectiveCandidate_pairwise hZ hsafe, ?_⟩
  intro a ha b hb
  have haEq : a = 1 := (List.mem_replicate.mp ha).2
  subst a
  exact one_le_of_mem_mixedEffectiveCandidate hZ hsafe hb

theorem vectorOfflineCost_eq_mixedExtendedFiniteOffline_of_perm
    {n v C K Z : ℕ} {u : ℝ} (hZ : 0 < Z)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u)
    (processingTime : Online.Label n → ℝ)
    (hperm :
      (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u) processingTime)) :
    vectorOfflineCost (.finite u) processingTime =
      mixedExtendedFiniteOffline u v C K Z := by
  unfold vectorOfflineCost
  rw [shortestFirst_pair_formula]
  rw [← pairCost_perm hperm]
  rw [← prefixCost_eq_pairCost_of_pairwise
    (mixedExtendedEffectiveCandidate_pairwise hZ hsafe)]
  exact prefixCost_mixedExtendedEffectiveCandidate hZ u v C K

end LowerBound

end

end SchedulingPaper
