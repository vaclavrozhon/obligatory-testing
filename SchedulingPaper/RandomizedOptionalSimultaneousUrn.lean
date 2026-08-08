import SchedulingPaper.RandomizedOptionalRates
import Mathlib.Tactic

/-!
# Optional testing: simultaneous touch-prefix urn control

The fixed-horizon predictable-urn theorem is not by itself enough for the
optional lower bound: the realized number of tests is adaptive, and the
completion envelope is applied at every physical prefix.  This file upgrades
the checked centered-increment estimate to one event controlling every
first-touch prefix.  It uses coarse touch checkpoints and deterministic
interpolation; no stopping time is conditioned upon.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

/-- Keep a selector only through one deterministic first-touch cutoff. -/
def selectorThrough {n : ℕ} (cutoff : Fin n)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ) :
    Fin n → Equiv.Perm (Fin n) → ℝ :=
  fun j σ => if j ∈ positionsThrough cutoff then select j σ else 0

theorem selectorThrough_predictable {n : ℕ} {cutoff : Fin n}
    {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hselect : PredictableSelector select) :
    PredictableSelector (selectorThrough cutoff select) := by
  intro j σ τ hpref
  unfold selectorThrough
  split
  · rw [hselect j σ τ hpref]
  · rfl

theorem selectorThrough_nonneg {n : ℕ} {cutoff : Fin n}
    {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hselect : ∀ j σ, 0 ≤ select j σ) :
    ∀ j σ, 0 ≤ selectorThrough cutoff select j σ := by
  intro j σ
  unfold selectorThrough
  split
  · exact hselect j σ
  · norm_num

theorem selectorThrough_le_one {n : ℕ} {cutoff : Fin n}
    {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hselect : ∀ j σ, select j σ ≤ 1) :
    ∀ j σ, selectorThrough cutoff select j σ ≤ 1 := by
  intro j σ
  unfold selectorThrough
  split
  · exact hselect j σ
  · norm_num

theorem centeredUrnSum_selectorThrough {n : ℕ}
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) (σ : Equiv.Perm (Fin n)) :
    (∑ j, centeredUrnIncrement value
        (selectorThrough cutoff select) j σ) =
      ∑ j ∈ positionsThrough cutoff,
        centeredUrnIncrement value select j σ := by
  classical
  calc
    (∑ j, centeredUrnIncrement value
        (selectorThrough cutoff select) j σ) =
        ∑ j, if j ∈ positionsThrough cutoff then
          centeredUrnIncrement value select j σ else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold centeredUrnIncrement selectorThrough
      by_cases hmem : j ∈ positionsThrough cutoff <;> simp [hmem]
    _ = ∑ j ∈ positionsThrough cutoff,
        centeredUrnIncrement value select j σ := by
      unfold positionsThrough
      rw [Finset.sum_filter]
      simp

/-- A union bound for centered predictable sums at a finite collection of
touch cutoffs. -/
theorem predictable_centeredUrn_checkpoint_probability_le
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (checkpoints : Finset (Fin n))
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e : ℝ} (he : 0 < e) :
    uniformProbability (fun σ => ∃ c ∈ checkpoints,
      e < |∑ j ∈ positionsThrough c,
        centeredUrnIncrement value select j σ|) ≤
      checkpoints.card * (n / e ^ 2) := by
  let P : ↥checkpoints → Equiv.Perm (Fin n) → Prop := fun c σ =>
    e < |∑ j ∈ positionsThrough c.val,
      centeredUrnIncrement value select j σ|
  have hpoint : ∀ c : ↥checkpoints,
      uniformProbability (P c) ≤ n / e ^ 2 := by
    intro c
    have hfixed := predictable_centeredUrnSum_probability_le
      value (selectorThrough c.val select)
      (selectorThrough_predictable hPredictable)
      hvalue0 hvalue1
      (selectorThrough_nonneg hselect0)
      (selectorThrough_le_one hselect1) he
    simpa [P, centeredUrnSum_selectorThrough] using hfixed
  have hunion := uniformProbability_exists_le_card_mul P hpoint
  simpa [P] using hunion

@[simp] theorem positionsThrough_card {n : ℕ} (cutoff : Fin n) :
    (positionsThrough cutoff).card = cutoff.val + 1 := by
  have hset : positionsThrough cutoff = Finset.Iic cutoff := by
    ext j
    simp [positionsThrough]
  rw [hset]
  simp

theorem positionsThrough_mono {n : ℕ} {i j : Fin n}
    (hij : i.val ≤ j.val) :
    positionsThrough i ⊆ positionsThrough j := by
  intro k hk
  rw [mem_positionsThrough] at hk ⊢
  omega

theorem positionsThrough_sdiff_card_le {n step : ℕ} {i j : Fin n}
    (hij : i.val ≤ j.val) (hdist : j.val ≤ i.val + step) :
    (positionsThrough j \ positionsThrough i).card ≤ step := by
  have hsubset := positionsThrough_mono hij
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset,
    positionsThrough_card, positionsThrough_card]
  omega

theorem abs_centeredUrnIncrement_le_one {n : ℕ}
    {value : Fin n → ℝ}
    {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hvalue0 : ∀ i, 0 ≤ value i) (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) :
    |centeredUrnIncrement value select j σ| ≤ 1 := by
  obtain ⟨hmean0, hmean1⟩ :=
    permutationSuffixMean_mem_Icc value σ j hvalue0 hvalue1
  have hdiff : |value (σ j) - permutationSuffixMean value σ j| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hvalue0 (σ j), hvalue1 (σ j)]
  have hsel : |select j σ| ≤ 1 := by
    rw [abs_of_nonneg (hselect0 j σ)]
    exact hselect1 j σ
  unfold centeredUrnIncrement
  rw [abs_mul]
  nlinarith [mul_le_mul hsel hdiff (abs_nonneg _)
    (show 0 ≤ (1 : ℝ) by norm_num)]

/-- Deterministic interpolation from controlled coarse checkpoints to every
touch prefix. -/
theorem centeredUrn_all_prefix_abs_le_of_checkpoints
    {n step : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) (checkpoints : Finset (Fin n))
    (hcover : ∀ j ∈ positionsThrough cutoff, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧ c.val ≤ j.val + step)
    (hvalue0 : ∀ i, 0 ≤ value i) (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e : ℝ} {σ : Equiv.Perm (Fin n)}
    (hcheckpoint : ∀ c ∈ checkpoints,
      |∑ j ∈ positionsThrough c,
        centeredUrnIncrement value select j σ| ≤ e) :
    ∀ j ∈ positionsThrough cutoff,
      |∑ k ∈ positionsThrough j,
        centeredUrnIncrement value select k σ| ≤ e + step := by
  intro j hj
  obtain ⟨c, hc, hjc, hdist⟩ := hcover j hj
  let small := positionsThrough j
  let large := positionsThrough c
  let extra := large \ small
  have hsubset : small ⊆ large := positionsThrough_mono hjc
  have hsum := Finset.sum_sdiff hsubset
    (f := fun k => centeredUrnIncrement value select k σ)
  have hextraAbs :
      |∑ k ∈ extra, centeredUrnIncrement value select k σ| ≤ extra.card := by
    calc
      |∑ k ∈ extra, centeredUrnIncrement value select k σ| ≤
          ∑ k ∈ extra, |centeredUrnIncrement value select k σ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ extra, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          abs_centeredUrnIncrement_le_one hvalue0 hvalue1
            hselect0 hselect1 k σ
      _ = extra.card := by simp
  have hextraCard : (extra.card : ℝ) ≤ step := by
    exact_mod_cast positionsThrough_sdiff_card_le hjc hdist
  have hlarge := hcheckpoint c hc
  have hrewrite :
      (∑ k ∈ small, centeredUrnIncrement value select k σ) =
        (∑ k ∈ large, centeredUrnIncrement value select k σ) -
          ∑ k ∈ extra, centeredUrnIncrement value select k σ := by
    dsimp [small, large, extra] at hsum ⊢
    linarith
  rw [hrewrite]
  calc
    |(∑ k ∈ large, centeredUrnIncrement value select k σ) -
        ∑ k ∈ extra, centeredUrnIncrement value select k σ| ≤
      |∑ k ∈ large, centeredUrnIncrement value select k σ| +
        |∑ k ∈ extra, centeredUrnIncrement value select k σ| :=
      abs_sub _ _
    _ ≤ e + step := add_le_add hlarge (hextraAbs.trans hextraCard)

theorem sum_selectorThrough {n : ℕ} (cutoff : Fin n)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    (∑ j, selectorThrough cutoff select j σ) =
      ∑ j ∈ positionsThrough cutoff, select j σ := by
  classical
  calc
    (∑ j, selectorThrough cutoff select j σ) =
        ∑ j, if j ∈ positionsThrough cutoff then select j σ else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [selectorThrough]
    _ = ∑ j ∈ positionsThrough cutoff, select j σ := by
      unfold positionsThrough
      rw [Finset.sum_filter]
      simp

theorem sum_selectorThrough_mul {n : ℕ} (cutoff : Fin n)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (value : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ j, selectorThrough cutoff select j σ * value (σ j)) =
      ∑ j ∈ positionsThrough cutoff, select j σ * value (σ j) := by
  classical
  calc
    (∑ j, selectorThrough cutoff select j σ * value (σ j)) =
        ∑ j, if j ∈ positionsThrough cutoff then
          select j σ * value (σ j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [selectorThrough]
    _ = ∑ j ∈ positionsThrough cutoff,
        select j σ * value (σ j) := by
      unfold positionsThrough
      rw [Finset.sum_filter]
      simp

/-- Pathwise conversion of simultaneous centered-increment and remaining-urn
mean control into the population-discrepancy inequality used by the grid
repair. -/
theorem selected_prefix_discrepancy_abs_le
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (cutoff : Fin n) (σ : Equiv.Perm (Fin n))
    {martingaleError driftError : ℝ}
    (hmartingale :
      |∑ j ∈ positionsThrough cutoff,
        centeredUrnIncrement value select j σ| ≤ martingaleError)
    (hsuffix : ∀ j ∈ positionsThrough cutoff,
      |permutationSuffixMean value σ j - populationMean value| ≤ driftError) :
    |(∑ j ∈ positionsThrough cutoff, select j σ * value (σ j)) -
        populationMean value *
          ∑ j ∈ positionsThrough cutoff, select j σ| ≤
      martingaleError + driftError * n := by
  let selected := selectorThrough cutoff select
  let remaining : Fin n → ℝ := fun j =>
    if j ∈ positionsThrough cutoff then
      permutationSuffixMean value σ j else populationMean value
  have hselected0 : ∀ j, 0 ≤ selected j σ := fun j =>
    selectorThrough_nonneg (cutoff := cutoff) hselect0 j σ
  have hdrift0 : 0 ≤ driftError := by
    have hmem : cutoff ∈ positionsThrough cutoff := by simp
    have h := hsuffix cutoff hmem
    exact le_trans (abs_nonneg _) h
  have hremaining : ∀ j,
      |remaining j - populationMean value| ≤ driftError := by
    intro j
    by_cases hj : j ∈ positionsThrough cutoff
    · dsimp [remaining]
      rw [if_pos hj]
      exact hsuffix j hj
    · dsimp [remaining]
      rw [if_neg hj]
      simpa using hdrift0
  have hcentered :
      (∑ j, selected j σ *
        (value (σ j) - remaining j)) =
      ∑ j ∈ positionsThrough cutoff,
        centeredUrnIncrement value select j σ := by
    calc
      (∑ j, selected j σ * (value (σ j) - remaining j)) =
          ∑ j, centeredUrnIncrement value
            (selectorThrough cutoff select) j σ := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold centeredUrnIncrement selected selectorThrough
        by_cases hmem : j ∈ positionsThrough cutoff
        · dsimp [remaining]
          rw [if_pos hmem, if_pos hmem]
        · dsimp [remaining]
          rw [if_neg hmem, if_neg hmem]
          simp
      _ = _ := centeredUrnSum_selectorThrough value select cutoff σ
  have hmartingale' :
      |∑ j, selected j σ * (value (σ j) - remaining j)| ≤
        martingaleError := by
    rw [hcentered]
    exact hmartingale
  have hraw := predictable_selection_discrepancy_abs_le
    hselected0 hmartingale' hremaining
  have hsumSelected : (∑ j, selected j σ) ≤ n := by
    calc
      (∑ j, selected j σ) ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => selectorThrough_le_one hselect1 j σ
      _ = n := by simp
  have hdrift : driftError * (∑ j, selected j σ) ≤ driftError * n :=
    mul_le_mul_of_nonneg_left hsumSelected hdrift0
  rw [sum_selectorThrough] at hdrift
  rw [sum_selectorThrough_mul, sum_selectorThrough] at hraw
  exact hraw.trans (by linarith)

/-- One event controls the adaptively selected discrepancy at every relevant
first-touch prefix.  The first checkpoint family controls centered sums; the
second controls all remaining-urn means. -/
theorem predictable_selected_all_prefix_probability_le
    {n step : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n)
    (martingaleCheckpoints suffixCheckpoints : Finset (Fin n))
    (hMartingaleCover : ∀ j ∈ positionsThrough cutoff,
      ∃ c ∈ martingaleCheckpoints,
        j.val ≤ c.val ∧ c.val ≤ j.val + step)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e K r D : ℝ}
    (he : 0 < e) (hK : 0 < K) (hr : 0 < r)
    (hSuffixCard : ∀ c ∈ suffixCheckpoints,
      K ≤ (suffixPositions c).card)
    (hSuffixCover : ∀ j ∈ positionsThrough cutoff,
      ∃ c ∈ suffixCheckpoints,
        j.val ≤ c.val ∧
        ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ D ∧
        K ≤ (suffixPositions c).card) :
    uniformProbability (fun σ => ∃ j ∈ positionsThrough cutoff,
      e + step + (r + 2 * D / K) * n <
        |(∑ k ∈ positionsThrough j, select k σ * value (σ k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j, select k σ|) ≤
      martingaleCheckpoints.card * (n / e ^ 2) +
        suffixCheckpoints.card * ((2 / K) / r ^ 2) := by
  classical
  let martingaleBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∃ c ∈ martingaleCheckpoints,
      e < |∑ j ∈ positionsThrough c,
        centeredUrnIncrement value select j σ|
  let suffixBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∃ j ∈ positionsThrough cutoff,
      r + 2 * D / K <
        |permutationSuffixMean value σ j - populationMean value|
  have hmartingale : uniformProbability martingaleBad ≤
      martingaleCheckpoints.card * (n / e ^ 2) := by
    exact predictable_centeredUrn_checkpoint_probability_le
      value select martingaleCheckpoints hPredictable hvalue0 hvalue1
        hselect0 hselect1 he
  have hsuffix : uniformProbability suffixBad ≤
      suffixCheckpoints.card * ((2 / K) / r ^ 2) := by
    exact uniformProbability_relevant_suffixMean_abs_gt_le
      hn value (positionsThrough cutoff) suffixCheckpoints
        hvalue0 hvalue1 hK hr hSuffixCard hSuffixCover
  have hcontain : ∀ σ,
      (∃ j ∈ positionsThrough cutoff,
        e + step + (r + 2 * D / K) * n <
          |(∑ k ∈ positionsThrough j, select k σ * value (σ k)) -
            populationMean value *
              ∑ k ∈ positionsThrough j, select k σ|) →
      martingaleBad σ ∨ suffixBad σ := by
    intro σ hbad
    by_contra hnot
    have hnotMartingale : ¬ martingaleBad σ := fun h => hnot (Or.inl h)
    have hnotSuffix : ¬ suffixBad σ := fun h => hnot (Or.inr h)
    have hcheckpoint : ∀ c ∈ martingaleCheckpoints,
        |∑ j ∈ positionsThrough c,
          centeredUrnIncrement value select j σ| ≤ e := by
      intro c hc
      exact le_of_not_gt fun hlarge =>
        hnotMartingale ⟨c, hc, hlarge⟩
    have hallCentered := centeredUrn_all_prefix_abs_le_of_checkpoints
      value select cutoff martingaleCheckpoints hMartingaleCover
        hvalue0 hvalue1 hselect0 hselect1 hcheckpoint
    have hallSuffix : ∀ j ∈ positionsThrough cutoff,
        |permutationSuffixMean value σ j - populationMean value| ≤
          r + 2 * D / K := by
      intro j hj
      exact le_of_not_gt fun hlarge => hnotSuffix ⟨j, hj, hlarge⟩
    obtain ⟨j, hj, hjbad⟩ := hbad
    have hjle : j.val ≤ cutoff.val := by
      simpa only [mem_positionsThrough] using hj
    have hjsubset : positionsThrough j ⊆ positionsThrough cutoff :=
      positionsThrough_mono hjle
    have hgood := selected_prefix_discrepancy_abs_le
      value select hselect0 hselect1 j σ
        (hallCentered j hj) (fun k hk => hallSuffix k (hjsubset hk))
    exact (not_lt_of_ge hgood) hjbad
  calc
    uniformProbability (fun σ => ∃ j ∈ positionsThrough cutoff,
        e + step + (r + 2 * D / K) * n <
          |(∑ k ∈ positionsThrough j, select k σ * value (σ k)) -
            populationMean value *
              ∑ k ∈ positionsThrough j, select k σ|) ≤
        uniformProbability (fun σ => martingaleBad σ ∨ suffixBad σ) :=
      uniformProbability_mono hcontain
    _ ≤ uniformProbability martingaleBad + uniformProbability suffixBad :=
      uniformProbability_or_le martingaleBad suffixBad
    _ ≤ martingaleCheckpoints.card * (n / e ^ 2) +
        suffixCheckpoints.card * ((2 / K) / r ^ 2) :=
      add_le_add hmartingale hsuffix

/-- Regular-checkpoint specialization of the simultaneous-prefix theorem. -/
theorem predictable_selected_all_prefix_regular_probability_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ => ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j, select k σ * value (σ k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j, select k σ|) ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
  let martingaleCheckpoints := backwardCheckpoints martingaleStep cutoff
  let suffixCheckpoints := backwardCheckpoints suffixStep cutoff
  let K : ℝ := (suffixPositions cutoff).card
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (suffixPositions_nonempty cutoff).card_pos
  have hMartingaleCover : ∀ j ∈ positionsThrough cutoff,
      ∃ c ∈ martingaleCheckpoints,
        j.val ≤ c.val ∧ c.val ≤ j.val + martingaleStep := by
    intro j hj
    obtain ⟨c, hc, hjc, hdist⟩ :=
      backwardCheckpoints_cover hMartingaleStep hj
    exact ⟨c, by simpa [martingaleCheckpoints] using hc, hjc, by omega⟩
  have hSuffixCard : ∀ c ∈ suffixCheckpoints,
      K ≤ (suffixPositions c).card := by
    intro c hc
    have hcle := backwardCheckpoints_mem_le_cutoff
      (by simpa [suffixCheckpoints] using hc)
    dsimp [K]
    simp only [suffixPositions_card]
    exact_mod_cast (by omega : n - cutoff.val ≤ n - c.val)
  have hSuffixCover : ∀ j ∈ positionsThrough cutoff,
      ∃ c ∈ suffixCheckpoints,
        j.val ≤ c.val ∧
        ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ suffixStep ∧
        K ≤ (suffixPositions c).card := by
    intro j hj
    obtain ⟨c, hc, hjc, hdist⟩ :=
      backwardCheckpoints_cover hSuffixStep hj
    refine ⟨c, by simpa [suffixCheckpoints] using hc, hjc, ?_,
      hSuffixCard c (by simpa [suffixCheckpoints] using hc)⟩
    simp only [suffixPositions_card]
    norm_num at *
    exact_mod_cast (by omega : c.val ≤ suffixStep + j.val)
  simpa [martingaleCheckpoints, suffixCheckpoints, K] using
    predictable_selected_all_prefix_probability_le hn value select cutoff
      martingaleCheckpoints suffixCheckpoints hMartingaleCover hPredictable
      hvalue0 hvalue1 hselect0 hselect1 he hK hr hSuffixCard hSuffixCover

/-- Union of the simultaneous-prefix estimate over every class of a finite
grid. -/
theorem predictable_selected_all_categories_prefix_regular_probability_le
    {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 1 < n) (value : κ → Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ c i, 0 ≤ value c i)
    (hvalue1 : ∀ c i, value c i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ => ∃ c, ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            select k σ * value c (σ k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j, select k σ|) ≤
      Fintype.card κ *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) := by
  let P : κ → Equiv.Perm (Fin n) → Prop := fun c σ =>
    ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            select k σ * value c (σ k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j, select k σ|
  have hpoint : ∀ c, uniformProbability (P c) ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
    intro c
    exact predictable_selected_all_prefix_regular_probability_le
      hn (value c) select cutoff hMartingaleStep hSuffixStep hPredictable
        (hvalue0 c) (hvalue1 c) hselect0 hselect1 he hr
  have hunion := uniformProbability_exists_le_card_mul P hpoint
  simpa [P] using hunion

end

end RandomizedOptional
end SchedulingPaper
