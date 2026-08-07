import SchedulingPaper.RandomizedOperationalAnalytic
import Mathlib.Tactic

/-!
# Expected cost of the literal sampled obligatory-testing policy

This module transports the deterministic learned/fallback bounds through the
outer random relabelling and applies the finite histogram concentration
theorem.  The resulting statement is about the actual terminating online run.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

theorem categoryClass_card_comp_perm
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (c : α → β) (σ : Equiv.Perm α) (b : β) :
    (categoryClass (c ∘ σ) b).card = (categoryClass c b).card := by
  apply Nat.cast_injective (R := ℝ)
  have hleft : ((categoryClass (c ∘ σ) b).card : ℝ) =
      ∑ i : α, if c (σ i) = b then 1 else 0 := by
    simp [categoryClass, Function.comp_apply]
  have hright : ((categoryClass c b).card : ℝ) =
      ∑ i : α, if c i = b then 1 else 0 := by
    simp [categoryClass]
  rw [hleft, hright]
  exact Equiv.sum_comp σ (fun i : α => if c i = b then (1 : ℝ) else 0)

theorem sampleCategoryFraction_comp_perm_refl
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (c : α → β) (σ : Equiv.Perm α) (b : β) :
    sampleCategoryFraction S (categoryClass (c ∘ σ) b) (Equiv.refl _) =
      sampleCategoryFraction S (categoryClass c b) σ := by
  unfold sampleCategoryFraction permutationSampleSum categoryIndicator
  apply congrArg (fun x : ℝ => x / S.card)
  apply Finset.sum_congr rfl
  intro i _
  simp [categoryClass, Function.comp_apply]

theorem histogramL1Error_comp_perm_refl
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (c : α → β) (σ : Equiv.Perm α) :
    histogramL1Error S (c ∘ σ) (Equiv.refl _) =
      histogramL1Error S c σ := by
  unfold histogramL1Error
  apply Finset.sum_congr rfl
  intro b _
  rw [sampleCategoryFraction_comp_perm_refl,
    categoryClass_card_comp_perm]

theorem finiteObligatoryOPT_comp_perm
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    finiteObligatoryOPT (p ∘ σ) = finiteObligatoryOPT p := by
  rw [finiteObligatoryOPT_eq_pairCost hn,
    finiteObligatoryOPT_eq_pairCost hn]
  apply pairCost_perm
  exact Equiv.Perm.ofFn_comp_perm σ (fun i : Fin n => 1 + p i)

/-- Concentration applied to the exact conditional sample-first scalar cost.
All branch choices are those made by the transcript learner itself. -/
theorem uniformAverage_learnedSampleFirstScalarCost_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hnCard : 1 < k + r)
    (η : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hηUpper : η ≤ 32 / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage (fun σ : Equiv.Perm (Fin (k + r)) =>
        learnedSampleFirstScalarCost k r d η hη (p ∘ σ)) ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (9472 * Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) + 22 * η) +
        17 * (k + r : ℝ) * k / 2 := by
  have hn : 0 < k + r := Nat.add_pos_left hk r
  letI : Nonempty (Fin (k + r)) := ⟨⟨0, hn⟩⟩
  let sample := firstBlockPositions k r
  let c := fun i : Fin (k + r) => quantizedCategory d η (p i) hη
  let cost := fun σ : Equiv.Perm (Fin (k + r)) =>
    learnedSampleFirstScalarCost k r d η hη (p ∘ σ)
  have hSample : sample.Nonempty := by
    exact firstBlockPositions_nonempty (r := r) hk
  have hopt0 : 0 ≤ finiteObligatoryOPT p := by
    have hlower := finiteObligatoryOPT_lower p hp
    simp only [Nat.cast_add] at hlower
    exact (show 0 ≤ (k + r : ℝ) * ((k + r : ℝ) + 1) / 2 by
      positivity).trans hlower
  have hgood : ∀ σ : Equiv.Perm (Fin (k + r)),
      ¬(1 / 1056 < histogramL1Error sample c σ) →
      cost σ ≤ 4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (1024 * histogramL1Error sample c σ + 22 * η) +
        17 * (k + r : ℝ) * k / 2 := by
    intro σ hgoodσ
    have hgoodσ' :
        histogramL1Error (firstBlockPositions k r)
          (fun i => quantizedCategory d η ((p ∘ σ) i) hη)
          (Equiv.refl _) ≤ 1 / (32 * 33) := by
      rw [show (fun i => quantizedCategory d η ((p ∘ σ) i) hη) =
          c ∘ σ by rfl,
        histogramL1Error_comp_perm_refl]
      dsimp [sample, c] at hgoodσ ⊢
      norm_num at hgoodσ ⊢
      exact hgoodσ
    cases hlearn : Online.learnedThresholdFromResults? d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) with
    | none =>
        have hfb := fallback_good_sampleFirstCost_bound
          k r d hk hr η hη hcutoff hηUpper (p ∘ σ)
          (fun i => hp (σ i)) hlearn hgoodσ'
        have hΔ0 : 0 ≤ histogramL1Error sample c σ := by
          dsimp [sample]
          unfold histogramL1Error
          positivity
        have hn2 : 0 ≤ (k + r : ℝ) ^ 2 := sq_nonneg _
        have hbracket : 0 ≤
            1024 * histogramL1Error sample c σ + 22 * η := by
          exact add_nonneg
            (mul_nonneg (by norm_num) hΔ0)
            (mul_nonneg (by norm_num) hη.le)
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hfb
        nlinarith [mul_nonneg hn2 hbracket]
    | some θHat =>
        have hlearned := learned_good_sampleFirstCost_bound
          k r d hk hr η hη hcutoff (p ∘ σ) (fun i => hp (σ i))
          hlearn hgoodσ'
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hlearned
        rw [show histogramL1Error (firstBlockPositions k r)
            (fun i => quantizedCategory d η ((p ∘ σ) i) hη)
            (Equiv.refl _) = histogramL1Error sample c σ by
          rw [show (fun i => quantizedCategory d η ((p ∘ σ) i) hη) =
              c ∘ σ by rfl,
            histogramL1Error_comp_perm_refl]
          ] at hlearned
        exact hlearned
  have hbad : ∀ σ : Equiv.Perm (Fin (k + r)),
      1 / 1056 < histogramL1Error sample c σ →
      cost σ ≤ 4 / 3 * finiteObligatoryOPT p +
        8 * (k + r : ℝ) ^ 2 + 17 * (k + r : ℝ) * k / 2 := by
    intro σ _hbadσ
    cases hlearn : Online.learnedThresholdFromResults? d η hη
        ((Online.fixedTestResults (p ∘ σ)).take k) with
    | none =>
        have hfb := fallback_sampleFirstCost_bound
          k r d hk hr η hη (p ∘ σ) (fun i => hp (σ i)) hlearn
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hfb
        nlinarith [hopt0, sq_nonneg (k + r : ℝ)]
    | some θHat =>
        have hlearned := learned_crude_sampleFirstCost_bound
          k r d hk hr η hη hcutoff (p ∘ σ) (fun i => hp (σ i)) hlearn
        dsimp [cost]
        rw [finiteObligatoryOPT_comp_perm hn p σ] at hlearned
        nlinarith [hopt0]
  have hcard : 1 < Fintype.card (Fin (k + r)) := by
    simpa only [Fintype.card_fin] using hnCard
  have havg := expectedCost_le_histogram_B32 sample c hSample hcard cost
    (n := (k + r : ℝ)) (opt := finiteObligatoryOPT p)
    (rounding := 22 * η) (overhead := 17 * (k + r : ℝ) * k / 2)
    (by positivity) (mul_nonneg (by norm_num) hη.le) (by positivity)
    hgood hbad
  simpa [sample, c, cost, firstBlockPositions_card, Fintype.card_fin,
    Nat.cast_add, Nat.cast_ofNat] using havg

/-- The expected completion cost of the literal terminating online run. -/
theorem uniformAverage_physicalSampledRunCost_analytic_le
    (k r d : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hnCard : 1 < k + r)
    (η : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hηUpper : η ≤ 32 / 12)
    (p : Fin (k + r) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage (physicalSampledRunCost (k + r) k d η hη p) ≤
      4 / 3 * finiteObligatoryOPT p +
        (k + r : ℝ) ^ 2 *
          (9472 * Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) + 22 * η) +
        17 * ((k + r : ℝ) * k / 2 + (k : ℝ) ^ 2) := by
  have hop := uniformAverage_physicalSampledRunCost_le
    k r d hk hr η hη p hp
  have han := uniformAverage_learnedSampleFirstScalarCost_le
    k r d hk hr hnCard η hη hcutoff hηUpper p hp
  linarith

/-- Explicit large-instance form.  The hypotheses isolate the elementary
floor/fourth-root arithmetic from the scheduling and probability proof. -/
theorem uniformAverage_physicalSampledRunCost_le_20378
    (k rest d : ℕ) (hk : 0 < k) (hrest : 0 < rest)
    (hnCard : 1 < k + rest)
    (η R : ℝ) (hη : 0 < η) (hcutoff : (d : ℝ) * η = 32)
    (hηUpper : η ≤ 32 / 12) (hR : 12 ≤ R)
    (hsize : (k + rest : ℝ) ≤ R ^ 4)
    (hsampleSize : (k : ℝ) ≤ R ^ 3)
    (herror : Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) ≤ 2 / R)
    (hrounding : η ≤ 64 / R)
    (p : Fin (k + rest) → ℝ) (hp : ∀ i, 0 ≤ p i) :
    uniformAverage
        (physicalSampledRunCost (k + rest) k d η hη p) ≤
      4 / 3 * finiteObligatoryOPT p + 20378 * R ^ 7 := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have han := uniformAverage_physicalSampledRunCost_analytic_le
    k rest d hk hrest hnCard η hη hcutoff hηUpper p hp
  have hn0 : 0 ≤ (k + rest : ℝ) := by positivity
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hnSq : (k + rest : ℝ) ^ 2 ≤ R ^ 8 := by
    have hsquare := mul_self_le_mul_self hn0 hsize
    nlinarith
  have hbracket :
      9472 * Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) + 22 * η ≤
        9472 * (2 / R) + 704 * (2 / R) := by
    have hsqrt := mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 9472)
    have heta := mul_le_mul_of_nonneg_left hrounding (by norm_num : (0 : ℝ) ≤ 22)
    have hetaNorm : 22 * (64 / R) = 704 * (2 / R) := by ring
    rw [hetaNorm] at heta
    nlinarith
  have hbracket0 : 0 ≤ 9472 * (2 / R) + 704 * (2 / R) := by
    positivity
  have hmain :
      (k + rest : ℝ) ^ 2 *
          (9472 * Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) + 22 * η) ≤
        R ^ 8 * (9472 * (2 / R) + 704 * (2 / R)) := by
    calc
      _ ≤ (k + rest : ℝ) ^ 2 *
          (9472 * (2 / R) + 704 * (2 / R)) :=
        mul_le_mul_of_nonneg_left hbracket (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hnSq hbracket0
  have hoverhead :
      17 * ((k + rest : ℝ) * k / 2 + (k : ℝ) ^ 2) ≤
        17 * (R ^ 4 * R ^ 3 / 2 + (R ^ 3) ^ 2) := by
    have hprod := mul_le_mul hsize hsampleSize (by positivity) (by positivity)
    have hsqK := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ k) hsampleSize
    nlinarith
  have hupper :
      uniformAverage
          (physicalSampledRunCost (k + rest) k d η hη p) ≤
        4 / 3 * finiteObligatoryOPT p +
          R ^ 8 * (9472 * (2 / R) + 704 * (2 / R)) +
          17 * (R ^ 4 * R ^ 3 / 2 + (R ^ 3) ^ 2) := by
    nlinarith
  exact explicit_20378_bound hR hupper

end

end RandomizedObligatory
end SchedulingPaper
