import SchedulingPaper.HarmonicCore
import SchedulingPaper.OfflineOptimal
import Mathlib.Tactic

/-!
# Dynamic accounting for the obligatory harmonic adversary

The state records the numbers of still-untested positive and zero jobs and
the processing times of tested but unfinished positive jobs.  The potential
is the cost of testing everything that remains and then processing the
positive jobs shortest first.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open Finset

def harmonicFutureLevels (ξ γ : ℝ) (L : ℕ) : List ℝ :=
  (List.range L).map (harmonicLevel ξ γ)

@[simp] theorem harmonicFutureLevels_zero (ξ γ : ℝ) :
    harmonicFutureLevels ξ γ 0 = [] := rfl

theorem harmonicFutureLevels_succ (ξ γ : ℝ) (L : ℕ) :
    harmonicFutureLevels ξ γ (L + 1) =
      harmonicFutureLevels ξ γ L ++ [harmonicLevel ξ γ L] := by
  simp [harmonicFutureLevels, List.range_succ, List.map_append]

@[simp] theorem harmonicFutureLevels_length (ξ γ : ℝ) (L : ℕ) :
    (harmonicFutureLevels ξ γ L).length = L := by
  simp [harmonicFutureLevels]

theorem sum_harmonicLevel_gap_eq_weightedGap
    (ξ γ : ℝ) (L : ℕ) :
    ∑ m ∈ Finset.range L,
        (harmonicLevel ξ γ L - harmonicLevel ξ γ m) =
      harmonicWeightedGap ξ L := by
  induction L with
  | zero =>
      simp [harmonicWeightedGap]
  | succ L ih =>
      rw [Finset.sum_range_succ]
      have hshift :
          ∑ m ∈ Finset.range L,
              (harmonicLevel ξ γ (L + 1) -
                harmonicLevel ξ γ m) =
            ∑ m ∈ Finset.range L,
                (harmonicLevel ξ γ L -
                  harmonicLevel ξ γ m) +
              L * (1 / (ξ + (L + 1 : ℕ))) := by
        calc
          (∑ m ∈ Finset.range L,
              (harmonicLevel ξ γ (L + 1) -
                harmonicLevel ξ γ m)) =
              ∑ m ∈ Finset.range L,
                ((harmonicLevel ξ γ L -
                    harmonicLevel ξ γ m) +
                  1 / (ξ + (L + 1 : ℕ))) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    rw [harmonicLevel_succ]
                    ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
      rw [hshift, ih, harmonicLevel_succ]
      unfold harmonicWeightedGap
      rw [Finset.sum_range_succ]
      push_cast
      ring

theorem harmonicFutureLevels_sum (ξ γ : ℝ) (L : ℕ) :
    (harmonicFutureLevels ξ γ L).sum =
      ∑ m ∈ Finset.range L, harmonicLevel ξ γ m := by
  induction L with
  | zero => simp [harmonicFutureLevels]
  | succ L ih =>
      rw [harmonicFutureLevels_succ, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

theorem harmonic_level_tail_identity
    {ξ γ : ℝ} (hξ : 0 < ξ) (L : ℕ) :
    (ξ + L) * (harmonicLevel ξ γ L - 1) -
        (harmonicFutureLevels ξ γ L).sum = γ := by
  have hgap := sum_harmonicLevel_gap_eq_weightedGap ξ γ L
  have hfuture := harmonicFutureLevels_sum ξ γ L
  have hrewrite :
      ∑ m ∈ Finset.range L,
          (harmonicLevel ξ γ L - harmonicLevel ξ γ m) =
        L * harmonicLevel ξ γ L -
          ∑ m ∈ Finset.range L, harmonicLevel ξ γ m := by
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [hrewrite] at hgap
  rw [hfuture]
  have ht := harmonic_telescope (γ := γ) hξ L
  linarith

theorem harmonicLevel_one_le
    {ξ γ : ℝ} (hξ : 0 < ξ) (hγ : 0 ≤ γ) (L : ℕ) :
    1 ≤ harmonicLevel ξ γ L := by
  unfold harmonicLevel
  have hbase : 0 ≤ γ / ξ := div_nonneg hγ hξ.le
  have hsum :
      0 ≤ ∑ r ∈ Finset.range L, 1 / (ξ + (r + 1 : ℕ)) := by
    positivity
  linarith

theorem harmonicFutureLevels_le_level
    {ξ γ : ℝ} (hξ : 0 < ξ) {L : ℕ} :
    ∀ q ∈ harmonicFutureLevels ξ γ L,
      q ≤ harmonicLevel ξ γ L := by
  intro q hq
  simp only [harmonicFutureLevels, List.mem_map] at hq
  obtain ⟨m, hm, rfl⟩ := hq
  have hmL : m < L := by simpa using hm
  exact (harmonicLevel_strictMono (γ := γ) hξ hmL).le

def harmonicDynamicPotential
    (ξ γ : ℝ) (L z : ℕ) (pending : List ℝ) : ℝ :=
  let U : ℕ := L + z + pending.length
  L * U + triangular z + z * (pending.length + L) +
    pairCost (pending ++ harmonicFutureLevels ξ γ L)

theorem harmonicDynamicPotential_terminal (ξ γ : ℝ) :
    harmonicDynamicPotential ξ γ 0 0 [] = 0 := by
  simp [harmonicDynamicPotential, triangular, pairCost]

theorem harmonicDynamicPotential_test_positive
    (ξ γ : ℝ) {L z : ℕ} (pending : List ℝ)
    (hL : 0 < L) :
    harmonicDynamicPotential ξ γ L z pending =
      (L + z + pending.length) +
        harmonicDynamicPotential ξ γ (L - 1) z
          (pending ++ [harmonicLevel ξ γ (L - 1)]) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  simp only [Nat.succ_sub_one]
  unfold harmonicDynamicPotential
  dsimp only
  rw [harmonicFutureLevels_succ]
  have hperm :
      (pending ++ harmonicFutureLevels ξ γ L ++
          [harmonicLevel ξ γ L]).Perm
        ((pending ++ [harmonicLevel ξ γ L]) ++
          harmonicFutureLevels ξ γ L) := by
    have hmove :
        (harmonicFutureLevels ξ γ L ++
            [harmonicLevel ξ γ L]).Perm
          (harmonicLevel ξ γ L ::
            harmonicFutureLevels ξ γ L) :=
      by
        simpa using
          (List.perm_middle
            (a := harmonicLevel ξ γ L)
            (l₁ := harmonicFutureLevels ξ γ L)
            (l₂ := []))
    simpa only [List.append_assoc] using
      List.Perm.append_left pending hmove
  have hpceq :
      pairCost
          (pending ++
            (harmonicFutureLevels ξ γ L ++
              [harmonicLevel ξ γ L])) =
        pairCost
          ((pending ++ [harmonicLevel ξ γ L]) ++
            harmonicFutureLevels ξ γ L) := by
    apply pairCost_perm
    simpa only [List.append_assoc] using hperm
  rw [hpceq]
  simp only [List.length_append, List.length_singleton,
    harmonicFutureLevels_length]
  push_cast
  ring

theorem triangular_succ_real (z : ℕ) :
    triangular (z + 1) = (z + 1 : ℕ) + triangular z := by
  unfold triangular
  push_cast
  ring

theorem harmonicDynamicPotential_test_zero
    (ξ γ : ℝ) {z : ℕ} (pending : List ℝ)
    (hz : 0 < z) :
    harmonicDynamicPotential ξ γ 0 z pending =
      (z + pending.length) +
        harmonicDynamicPotential ξ γ 0 (z - 1) pending := by
  obtain ⟨z, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hz)
  simp only [Nat.succ_sub_one]
  unfold harmonicDynamicPotential
  dsimp only
  rw [triangular_succ_real]
  push_cast
  ring

theorem pairCost_remove_upper
    {ξ γ p : ℝ} {L : ℕ}
    {before after : List ℝ}
    (hpFuture :
      ∀ q ∈ harmonicFutureLevels ξ γ L, q ≤ p) :
    pairCost
        ((before ++ p :: after) ++ harmonicFutureLevels ξ γ L) -
      pairCost
        ((before ++ after) ++ harmonicFutureLevels ξ γ L) ≤
      (before.length + after.length + 1) * p +
        (harmonicFutureLevels ξ γ L).sum := by
  let rest :=
    (before ++ after) ++ harmonicFutureLevels ξ γ L
  have hperm :
      ((before ++ p :: after) ++
          harmonicFutureLevels ξ γ L).Perm (p :: rest) := by
    dsimp [rest]
    change
      ((before ++ p :: after) ++
          harmonicFutureLevels ξ γ L).Perm
        (p :: ((before ++ after) ++
          harmonicFutureLevels ξ γ L))
    exact List.Perm.append_right
      (harmonicFutureLevels ξ γ L)
      (List.perm_middle :
        (before ++ p :: after).Perm (p :: before ++ after))
  rw [pairCost_perm hperm]
  simp only [pairCost, pairMinCost_cons, List.sum_cons]
  have hsplit :
      (rest.map (min p)).sum =
        ((before ++ after).map (min p)).sum +
          ((harmonicFutureLevels ξ γ L).map (min p)).sum := by
    simp [rest, List.sum_append]
    ring
  rw [hsplit]
  have hpending :
      ((before ++ after).map (min p)).sum ≤
        (before.length + after.length) * p := by
    calc
      ((before ++ after).map (min p)).sum ≤
          ((before ++ after).map fun _ => p).sum := by
        exact List.sum_le_sum fun q hq => min_le_left p q
      _ = (before.length + after.length) * p := by
        simp
  have hfuture :
      ((harmonicFutureLevels ξ γ L).map (min p)).sum =
        (harmonicFutureLevels ξ γ L).sum := by
    let future := harmonicFutureLevels ξ γ L
    have hall : ∀ q ∈ future, q ≤ p := by
      simpa [future] using hpFuture
    have hmap :
        future.map (min p) = future.map (fun q => q) := by
      apply List.map_congr_left
      intro q hq
      exact min_eq_right (hall q hq)
    simpa [future] using congrArg List.sum hmap
  rw [hfuture]
  dsimp [rest]
  simp only [List.sum_append]
  linarith

theorem harmonicDynamicPotential_process
    {ξ γ : ℝ} (hξ : 0 < ξ) (hγ : 0 ≤ γ)
    {L z : ℕ} {before after : List ℝ} {p : ℝ}
    (hphase : L = 0 ∨ z = ξ)
    (hp :
      harmonicLevel ξ γ L ≤ p) :
    harmonicDynamicPotential ξ γ L z (before ++ p :: after) ≤
      p * (L + z + (before ++ p :: after).length) +
        harmonicDynamicPotential ξ γ L z (before ++ after) := by
  have hp1 : 1 ≤ p :=
    (harmonicLevel_one_le hξ hγ L).trans hp
  have hpFuture :
      ∀ q ∈ harmonicFutureLevels ξ γ L, q ≤ p := by
    intro q hq
    exact (harmonicFutureLevels_le_level hξ q hq).trans hp
  have hpair :=
    pairCost_remove_upper
      (before := before) (after := after) hpFuture
  unfold harmonicDynamicPotential
  dsimp only
  simp only [List.length_append, List.length_cons,
    List.length_nil, Nat.add_zero]
  push_cast at hpair ⊢
  by_cases hL : L = 0
  · subst L
    simp [harmonicFutureLevels] at hpair ⊢
    simp only [Nat.cast_zero, zero_add, zero_mul] at *
    have hnonneg :
        0 ≤ (z : ℝ) * (p - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp1)
    nlinarith
  · have hz : (z : ℝ) = ξ := by
      rcases hphase with hzero | heq
      · exact (hL hzero).elim
      · exact_mod_cast heq
    have hid :=
      harmonic_level_tail_identity (γ := γ) hξ L
    have hscale :
        (ξ + L) *
            (harmonicLevel ξ γ L - 1) ≤
          (ξ + L) * (p - 1) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_right hp 1)
        (add_nonneg hξ.le (Nat.cast_nonneg _))
    rw [hz]
    have htail :
        (harmonicFutureLevels ξ γ L).sum ≤
          (ξ + L) * (p - 1) := by
      linarith
    nlinarith

end

end SchedulingPaper
