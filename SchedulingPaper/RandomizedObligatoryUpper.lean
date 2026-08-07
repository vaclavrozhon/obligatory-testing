import SchedulingPaper.RandomizedHistogramConcentration
import SchedulingPaper.RandomizedHistogramTransfer
import SchedulingPaper.RandomizedSampleAlgebra
import Mathlib.Tactic

/-!
# Randomized obligatory testing: finite upper-bound assembly

This module formalizes the analytic upper-bound steps that sit between the
already checked histogram concentration theorem and the operational sampled
strategy.  In particular it contains the finite weighted robust `4/3`
certificate, the learned-threshold transfer at the fixed cutoff `B = 32`, the
fallback arithmetic, and the exact good/bad-event aggregation constants.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open RandomizedAnnounced
open Randomized

noncomputable section

/-- The early pair-minimum moment is at most early mass times early work. -/
theorem weightedMinPair_le_mass_mul_moment
    {ι : Type*} [Fintype ι]
    {μ p : ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hp : ∀ i, 0 ≤ p i) :
    weightedMinPair μ p ≤ weightedMass μ * weightedMoment μ p := by
  have hpoint : ∀ i j,
      μ i * μ j * min (p i) (p j) ≤ μ i * μ j * p i := by
    intro i j
    exact mul_le_mul_of_nonneg_left (min_le_left (p i) (p j))
      (mul_nonneg (hμ i) (hμ j))
  have hsum :
      (∑ i, ∑ j, μ i * μ j * min (p i) (p j)) ≤
        ∑ i, ∑ j, μ i * μ j * p i :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  unfold weightedMinPair weightedMass weightedMoment
  calc
    (∑ i, ∑ j, μ i * μ j * min (p i) (p j)) ≤
        ∑ i, ∑ j, μ i * μ j * p i := hsum
    _ = ∑ j, ∑ i, μ i * μ j * p i := by
      rw [Finset.sum_comm]
    _ = (∑ i, μ i * p i) * ∑ j, μ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, μ i) * ∑ i, μ i * p i := by ring

/-- Support-aware finite early-pair inequality.  Values carried by zero
weight need not satisfy the threshold. -/
theorem weightedMoment_sq_le_threshold_mul_minPair_on_support
    {ι : Type*} [Fintype ι]
    {θ : ℝ} {μ p : ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpθ : ∀ i, μ i ≠ 0 → p i ≤ θ) :
    weightedMoment μ p ^ 2 ≤ θ * weightedMinPair μ p := by
  have hpoint : ∀ i j,
      (μ i * p i) * (μ j * p j) ≤
        θ * (μ i * μ j * min (p i) (p j)) := by
    intro i j
    by_cases hμi : μ i = 0
    · simp [hμi]
    by_cases hμj : μ j = 0
    · simp [hμj]
    have hmin := early_min_pair_mul_le
      (hp0 i) (hp0 j) (hpθ i hμi) (hpθ j hμj)
    have hweight : 0 ≤ μ i * μ j := mul_nonneg (hμ i) (hμ j)
    have := mul_le_mul_of_nonneg_left hmin hweight
    nlinarith
  have hdouble :
      (∑ i, ∑ j, (μ i * p i) * (μ j * p j)) ≤
        ∑ i, ∑ j, θ * (μ i * μ j * min (p i) (p j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hleft :
      weightedMoment μ p ^ 2 =
        ∑ i, ∑ j, (μ i * p i) * (μ j * p j) := by
    unfold weightedMoment
    rw [pow_two, Fintype.sum_mul_sum]
  have hright :
      (∑ i, ∑ j, θ * (μ i * μ j * min (p i) (p j))) =
        θ * weightedMinPair μ p := by
    unfold weightedMinPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hleft, ← hright]
  exact hdouble

/-- Support-aware late-pair inequality. -/
theorem threshold_mul_weightedMass_sq_le_minPair_on_support
    {ι : Type*} [Fintype ι]
    {θ : ℝ} {μ p : ι → ℝ}
    (hμ : ∀ i, 0 ≤ μ i)
    (hpθ : ∀ i, μ i ≠ 0 → θ ≤ p i) :
    θ * weightedMass μ ^ 2 ≤ weightedMinPair μ p := by
  have hpoint : ∀ i j,
      θ * (μ i * μ j) ≤ μ i * μ j * min (p i) (p j) := by
    intro i j
    by_cases hμi : μ i = 0
    · simp [hμi]
    by_cases hμj : μ j = 0
    · simp [hμj]
    have hmin := threshold_le_late_min (hpθ i hμi) (hpθ j hμj)
    have := mul_le_mul_of_nonneg_left hmin (mul_nonneg (hμ i) (hμ j))
    nlinarith
  have hdouble :
      (∑ i, ∑ j, θ * (μ i * μ j)) ≤
        ∑ i, ∑ j, μ i * μ j * min (p i) (p j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hleft :
      θ * weightedMass μ ^ 2 = ∑ i, ∑ j, θ * (μ i * μ j) := by
    unfold weightedMass
    rw [pow_two, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
  unfold weightedMinPair
  rw [hleft]
  exact hdouble

/-- Finite weighted robust certificate for an approximately separated split.

The early and late classes are allowed to use unrelated finite index types.
Their masses sum to one, the chosen early block has inverse density `θ`, and
the pointwise separation may lose `s` on either side. -/
theorem finiteSplit_stationaryFluidCost_le_four_thirds_add_slack
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {θ s : ℝ} {μEarly pEarly : ι → ℝ} {μLate pLate : κ → ℝ}
    (hθ : 0 < θ)
    (hs : 0 ≤ s)
    (hμEarly : ∀ i, 0 ≤ μEarly i)
    (hμLate : ∀ i, 0 ≤ μLate i)
    (hpEarly0 : ∀ i, 0 ≤ pEarly i)
    (hpEarly : ∀ i, pEarly i ≤ θ + s)
    (hpLate : ∀ i, θ - s ≤ pLate i)
    (hmass : weightedMass μLate = 1 - weightedMass μEarly)
    (hdensity :
      weightedMoment μEarly pEarly = weightedMass μEarly * θ - 1) :
    stationaryFluidCost θ (weightedMass μEarly)
        (weightedMinPair μLate pLate) ≤
      4 / 3 * offlineFluidCost
        (weightedMoment μEarly pEarly)
        (weightedMass μLate)
        (weightedMinPair μEarly pEarly)
        (weightedMinPair μLate pLate) + 2 / 3 * s := by
  have ha0 : 0 ≤ weightedMass μEarly :=
    Finset.sum_nonneg fun i _ => hμEarly i
  have hh0 : 0 ≤ weightedMass μLate :=
    Finset.sum_nonneg fun i _ => hμLate i
  have ha1 : weightedMass μEarly ≤ 1 := by linarith
  apply stationaryFluidCost_le_four_thirds_add_slack
      hθ ha0 ha1 hs hmass hdensity
  · exact weightedMoment_sq_le_threshold_mul_minPair
      hμEarly hpEarly0 hpEarly
  · exact weightedMinPair_le_mass_mul_moment hμEarly hpEarly0
  · exact threshold_mul_weightedMass_sq_le_minPair hμLate hpLate

/-- On the fixed good event, learned early mass is at least `1/32`. -/
theorem learned_mass_lower_B32
    {a aHat Δ : ℝ}
    (hHat : 1 / 16 ≤ aHat)
    (hΔ : Δ ≤ 1 / (32 * 33))
    (herror : |a - aHat| ≤ Δ) :
    1 / 32 ≤ a := by
  have hlower : aHat - a ≤ Δ := by
    have herr : |aHat - a| ≤ Δ := by
      simpa [abs_sub_comm] using herror
    exact le_trans (le_abs_self (aHat - a)) herr
  norm_num at hHat hΔ ⊢
  linarith

/-- The scalar threshold-transfer estimate used in the learned branch.

At `B = 32`, histogram mass error `Δ` and rounded moment error
`32 Δ + η` move the inverse density by at most `1536 Δ + 32 η`.-/
theorem learned_threshold_distance_B32
    {a aHat m mHat θ θHat Δ η : ℝ}
    (ha : 1 / 32 ≤ a)
    (hθHat0 : 0 ≤ θHat)
    (hθHat16 : θHat ≤ 16)
    (hMass : |a - aHat| ≤ Δ)
    (hMoment : |m - mHat| ≤ 32 * Δ + η)
    (hθ : θ = (1 + m) / a)
    (hθHat : 1 + mHat = aHat * θHat) :
    |θ - θHat| ≤ 1536 * Δ + 32 * η := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hMass' : |aHat - a| ≤ Δ := by simpa [abs_sub_comm] using hMass
  have hnum :
      |(m - mHat) + θHat * (aHat - a)| ≤ 48 * Δ + η := by
    calc
      |(m - mHat) + θHat * (aHat - a)| ≤
          |m - mHat| + |θHat * (aHat - a)| := abs_add_le _ _
      _ = |m - mHat| + θHat * |aHat - a| := by
        rw [abs_mul, abs_of_nonneg hθHat0]
      _ ≤ (32 * Δ + η) + 16 * Δ := by
        gcongr
      _ = 48 * Δ + η := by ring
  have hid :
      θ - θHat = ((m - mHat) + θHat * (aHat - a)) / a := by
    rw [hθ]
    field_simp [ha0.ne']
    nlinarith [hθHat]
  rw [hid, abs_div, abs_of_pos ha0]
  apply (div_le_iff₀ ha0).2
  have haScale : (48 * Δ + η) ≤ a * (1536 * Δ + 32 * η) := by
    have hnonneg : 0 ≤ 48 * Δ + η :=
      (abs_nonneg ((m - mHat) + θHat * (aHat - a))).trans hnum
    have hmul := mul_le_mul_of_nonneg_right ha hnonneg
    nlinarith
  exact hnum.trans (by simpa [mul_comm] using haScale)

/-- Exact fallback arithmetic at the cutoff `B = 32`. -/
theorem fallback_le_four_thirds
    {n O opt alg : ℝ}
    (hn : 0 ≤ n)
    (hO : 57 / 16 ≤ O)
    (hopt : n ^ 2 * O ≤ opt)
    (halg : alg ≤ opt + n ^ 2 / 2) :
    alg ≤ 4 / 3 * opt := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hlarge : 3 / 2 * n ^ 2 ≤ opt := by
    nlinarith [mul_nonneg hn2 (sub_nonneg.mpr hO)]
  nlinarith

/-- The grid-density test in fallback mode forces the true maximum-density
threshold to be at least eight.  This is Section 9's two-case argument with
`B=32` and `η≤B/12`. -/
theorem fallback_threshold_ge_eight_B32
    {θ η ρGrid : ℝ}
    (hθ : 0 < θ)
    (hη0 : 0 ≤ η) (hη : η ≤ 32 / 12)
    (hρ : ρGrid < 3 / 32)
    (hgrid : θ + η ≤ 32 → 1 / (θ + η) ≤ ρGrid) :
    8 ≤ θ := by
  by_cases hwithin : θ + η ≤ 32
  · have hsum : 0 < θ + η := add_pos_of_pos_of_nonneg hθ hη0
    have hrecip : 1 / (θ + η) < 3 / 32 := (hgrid hwithin).trans_lt hρ
    have hmul := (div_lt_iff₀ hsum).mp hrecip
    norm_num at hη hmul ⊢
    nlinarith
  · have hout : 32 < θ + η := lt_of_not_ge hwithin
    norm_num at hη ⊢
    nlinarith

/-- A true threshold at least eight implies the normalized offline fluid
value `O ≥ 57/16`. -/
theorem fallback_offlineFluid_lower_B32
    {θ a m h Kearly Klate : ℝ}
    (hθ : 8 ≤ θ)
    (hh : h = 1 - a)
    (hm : m = a * θ - 1)
    (hEarly : m ^ 2 ≤ θ * Kearly)
    (hLate : θ * h ^ 2 ≤ Klate) :
    57 / 16 ≤ offlineFluidCost m h Kearly Klate := by
  have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
  have hlower := offlineFluidCost_lower_of_thresholdSplit
    hθpos hh hm hEarly hLate
  have hpoly : 0 ≤ (θ - 8) * (8 * θ - 1) := by
    exact mul_nonneg (sub_nonneg.mpr hθ) (by nlinarith)
  have hscalar : 57 / 16 ≤ (θ - 1 + 1 / θ) / 2 := by
    rw [← sub_nonneg]
    have hid :
        (θ - 1 + 1 / θ) / 2 - 57 / 16 =
          ((θ - 8) * (8 * θ - 1)) / (16 * θ) := by
      field_simp [hθpos.ne']
      ring
    rw [hid]
    exact div_nonneg hpoly (mul_nonneg (by norm_num) hθpos.le)
  exact hscalar.trans hlower

/-- Uniform averaging of an affine function plus an event indicator. -/
theorem uniformAverage_affine_event
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (c A E : ℝ) (f : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    uniformAverage (fun ω => c + A * f ω + E * (if P ω then 1 else 0)) =
      c + A * uniformAverage f + E * uniformProbability P := by
  rw [show (fun ω => c + A * f ω + E * (if P ω then 1 else 0)) =
      (fun ω => (fun _ : Ω => c) ω +
        ((fun ω => A * f ω) ω +
          (fun ω => E * (if P ω then 1 else 0)) ω)) by
            funext ω
            ring]
  rw [uniformAverage_add, uniformAverage_const, uniformAverage_add,
    uniformAverage_smul, uniformAverage_smul]
  unfold uniformProbability
  ring

/-- Exact good/bad-event aggregation for `B = 32`.

`rounding` denotes the deterministic normalized rounding loss
`(2/3)(B+1)η`.  A good learned seed pays `1024 Δ + rounding`, a good fallback
seed has nonpositive target excess, and either bad branch pays at most
`8 n²`.  Markov contributes `8 * 32 * 33 = 8448`, giving the coefficient
`1024 + 8448 = 9472`. -/
theorem expectedCost_le_of_good_bad_B32
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {cost error : Ω → ℝ} {bad : Ω → Prop} [DecidablePred bad]
    {n opt rounding overhead : ℝ}
    (hn : 0 ≤ n)
    (herror : ∀ ω, 0 ≤ error ω)
    (hrounding : 0 ≤ rounding)
    (hoverhead : 0 ≤ overhead)
    (hgood : ∀ ω, ¬ bad ω →
      cost ω ≤ 4 / 3 * opt +
        n ^ 2 * (1024 * error ω + rounding) + overhead)
    (hbad : ∀ ω, bad ω →
      cost ω ≤ 4 / 3 * opt + 8 * n ^ 2 + overhead)
    (hprob : uniformProbability bad ≤ 1056 * uniformAverage error) :
    uniformAverage cost ≤
      4 / 3 * opt +
        n ^ 2 * (9472 * uniformAverage error + rounding) + overhead := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hpoint : ∀ ω,
      cost ω ≤
        4 / 3 * opt +
          (1024 * n ^ 2) * error ω + n ^ 2 * rounding + overhead +
          (8 * n ^ 2) * (if bad ω then 1 else 0) := by
    intro ω
    by_cases hb : bad ω
    · have := hbad ω hb
      simp only [if_pos hb]
      have herr0 : 0 ≤ (1024 * n ^ 2) * error ω :=
        mul_nonneg (mul_nonneg (by norm_num) hn2) (herror ω)
      have hr0 : 0 ≤ n ^ 2 * rounding := mul_nonneg hn2 hrounding
      linarith
    · have := hgood ω hb
      simp only [if_neg hb]
      nlinarith
  have havg := uniformAverage_mono hpoint
  have haffine := uniformAverage_affine_event
    (Ω := Ω)
    (4 / 3 * opt + n ^ 2 * rounding + overhead)
    (1024 * n ^ 2) (8 * n ^ 2) error bad
  have hrewrite :
      uniformAverage (fun ω =>
        4 / 3 * opt +
          (1024 * n ^ 2) * error ω + n ^ 2 * rounding + overhead +
          (8 * n ^ 2) * (if bad ω then 1 else 0)) =
        4 / 3 * opt + n ^ 2 * rounding + overhead +
          (1024 * n ^ 2) * uniformAverage error +
          (8 * n ^ 2) * uniformProbability bad := by
    calc
      uniformAverage (fun ω =>
          4 / 3 * opt +
            (1024 * n ^ 2) * error ω + n ^ 2 * rounding + overhead +
            (8 * n ^ 2) * (if bad ω then 1 else 0)) =
          uniformAverage (fun ω =>
            (4 / 3 * opt + n ^ 2 * rounding + overhead) +
              (1024 * n ^ 2) * error ω +
              (8 * n ^ 2) * (if bad ω then 1 else 0)) := by
        congr 1
        funext ω
        ring
      _ = _ := haffine
  rw [hrewrite] at havg
  have hprobScaled :
      (8 * n ^ 2) * uniformProbability bad ≤
        (8 * n ^ 2) * (1056 * uniformAverage error) :=
    mul_le_mul_of_nonneg_left hprob (mul_nonneg (by norm_num) hn2)
  nlinarith

/-- Complete concentration/event aggregation for an actual fixed-size
permutation sample.  This theorem discharges both Markov's inequality and
the expected `L¹` histogram error; its only remaining hypotheses are the
deterministic good- and bad-sample schedule bounds. -/
theorem expectedCost_le_histogram_B32
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (S : Finset α) (c : α → β)
    (hS : S.Nonempty) (hcard : 1 < Fintype.card α)
    (cost : Equiv.Perm α → ℝ)
    {n opt rounding overhead : ℝ}
    (hn : 0 ≤ n)
    (hrounding : 0 ≤ rounding)
    (hoverhead : 0 ≤ overhead)
    (hgood : ∀ σ,
      ¬(1 / 1056 < histogramL1Error S c σ) →
      cost σ ≤ 4 / 3 * opt +
        n ^ 2 * (1024 * histogramL1Error S c σ + rounding) + overhead)
    (hbad : ∀ σ,
      1 / 1056 < histogramL1Error S c σ →
      cost σ ≤ 4 / 3 * opt + 8 * n ^ 2 + overhead) :
    uniformAverage cost ≤
      4 / 3 * opt +
        n ^ 2 *
          (9472 * Real.sqrt ((Fintype.card β : ℝ) / S.card) + rounding) +
        overhead := by
  let error : Equiv.Perm α → ℝ := histogramL1Error S c
  have herror0 : ∀ σ, 0 ≤ error σ := fun σ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hprob :
      uniformProbability (fun σ : Equiv.Perm α => 1 / 1056 < error σ) ≤
        1056 * uniformAverage error := by
    have hmarkov := uniformProbability_lt_le_average_div
      error herror0 (show 0 < (1 / 1056 : ℝ) by norm_num)
    convert hmarkov using 1 <;> norm_num <;> ring
  have haggregate := expectedCost_le_of_good_bad_B32
    (cost := cost) (error := error)
    (bad := fun σ => 1 / 1056 < error σ)
    hn herror0 hrounding hoverhead hgood hbad hprob
  have herrAvg := uniformAverage_histogramL1Error_le_sqrt S c hS hcard
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hscaled :
      n ^ 2 * (9472 * uniformAverage error + rounding) ≤
        n ^ 2 *
          (9472 * Real.sqrt ((Fintype.card β : ℝ) / S.card) + rounding) := by
    apply mul_le_mul_of_nonneg_left _ hn2
    dsimp [error]
    nlinarith
  exact haggregate.trans (by nlinarith)

/-- The final explicit coefficient calculation for the large-`n` regime.

Writing `r = n^(1/4)`, the proof uses `r ≥ 12`, histogram and rounding
errors at most `2/r`, and sample size at most `r^3`. -/
theorem explicit_20378_bound
    {r alg opt : ℝ}
    (hr : 12 ≤ r)
    (hupper :
      alg ≤ 4 / 3 * opt +
        r ^ 8 * (9472 * (2 / r) + 704 * (2 / r)) +
        17 * (r ^ 4 * r ^ 3 / 2 + (r ^ 3) ^ 2)) :
    alg ≤ 4 / 3 * opt + 20378 * r ^ 7 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrInv : 1 / r ≤ 1 / 12 := by
    exact one_div_le_one_div_of_le (by norm_num) hr
  have hr6 : 0 ≤ r ^ 6 := by positivity
  have hr7 : 0 ≤ r ^ 7 := by positivity
  have hsample : 17 * (r ^ 4 * r ^ 3 / 2 + (r ^ 3) ^ 2) ≤
      10 * r ^ 7 := by
    have hpow : r ^ 6 ≤ r ^ 7 / 12 := by
      have := mul_le_mul_of_nonneg_left hrInv hr7
      field_simp [hr0.ne'] at this ⊢
      nlinarith
    nlinarith
  have hmain :
      r ^ 8 * (9472 * (2 / r) + 704 * (2 / r)) = 20352 * r ^ 7 := by
    field_simp [hr0.ne']
    ring
  rw [hmain] at hupper
  linarith

/-- Lift the normalized robust certificate to the exact finite objective.

The two correction terms are the diagonal terms in Lemmas 1 and 2 of the
paper.  For nonnegative processing times, `earlyCorrection ≤ 4 D / 3`, so
only the quadratic fluid term pays the threshold slack. -/
theorem finiteCost_le_four_thirds_add_slack
    {n P O s alg opt earlyCorrection offlineCorrection : ℝ}
    (hn : 0 ≤ n)
    (hs : 0 ≤ s)
    (hfluid : P ≤ 4 / 3 * O + 2 / 3 * s)
    (halg : alg ≤ n ^ 2 * P + earlyCorrection)
    (hopt : opt = n ^ 2 * O + offlineCorrection)
    (hcorrection : earlyCorrection ≤ 4 / 3 * offlineCorrection) :
    alg ≤ 4 / 3 * opt + 2 / 3 * n ^ 2 * s := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left hfluid hn2
  rw [hopt]
  nlinarith

/-- Learned-mode deterministic bound after substituting the threshold
transfer `s ≤ 1536 Δ + 33 η`.  This is exactly the coefficient calculation
behind equation (10.3). -/
theorem learned_good_cost_B32
    {n P O s Δ η alg opt earlyCorrection offlineCorrection overhead : ℝ}
    (hn : 0 ≤ n) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) (hη : 0 ≤ η)
    (hfluid : P ≤ 4 / 3 * O + 2 / 3 * s)
    (hslack : s ≤ 1536 * Δ + 33 * η)
    (halg : alg ≤ n ^ 2 * P + earlyCorrection + overhead)
    (hopt : opt = n ^ 2 * O + offlineCorrection)
    (hcorrection : earlyCorrection ≤ 4 / 3 * offlineCorrection) :
    alg ≤ 4 / 3 * opt +
      n ^ 2 * (1024 * Δ + 22 * η) + overhead := by
  have hbase := finiteCost_le_four_thirds_add_slack
    hn hs hfluid
    (show alg - overhead ≤ n ^ 2 * P + earlyCorrection by linarith)
    hopt hcorrection
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left hslack
    (show 0 ≤ 2 / 3 * n ^ 2 by positivity)
  nlinarith

/-- Crude learned-mode bound on a bad histogram.  Early processing times are
at most sixteen, hence the normalized stationary loss is at most eight. -/
theorem learned_bad_cost_B32
    {n alg opt overhead : ℝ}
    (hopt0 : 0 ≤ opt)
    (halg : alg ≤ opt + 8 * n ^ 2 + overhead) :
    alg ≤ 4 / 3 * opt + 8 * n ^ 2 + overhead := by
  nlinarith

/-- A good fallback branch, already below `4OPT/3`, also satisfies the
nonnegative learned-branch envelope. -/
theorem good_fallback_satisfies_envelope
    {n Δ rounding overhead alg opt : ℝ}
    (hn : 0 ≤ n) (hΔ : 0 ≤ Δ) (hrounding : 0 ≤ rounding)
    (hoverhead : 0 ≤ overhead)
    (hfallback : alg ≤ 4 / 3 * opt) :
    alg ≤ 4 / 3 * opt +
      n ^ 2 * (1024 * Δ + rounding) + overhead := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hterm : 0 ≤ n ^ 2 * (1024 * Δ + rounding) := by positivity
  linarith

/-- The sample-first and delayed-sample implementation overhead from
Section 8, specialized to `B=32` and a sample of size at most `k`.

The first term is the antisymmetric sample/rest cross term; the second is
the delay of the sampled early batch. -/
theorem sampleFirst_overhead_B32
    {n k crossCost batchDelay : ℝ}
    (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hcross : crossCost ≤ n * k * 17 / 2)
    (hbatch : batchDelay ≤ 17 * k ^ 2) :
    crossCost + batchDelay ≤ 17 * (n * k / 2 + k ^ 2) := by
  nlinarith

/-- Converting the explicit additive estimate to the displayed
multiplicative estimate using `OPT ≥ n²/2`. -/
theorem additive_20378_to_multiplicative
    {n alg opt nQuarter : ℝ}
    (hn : 0 ≤ n)
    (hquarter : 0 < nQuarter)
    (hpower : n = nQuarter ^ 4)
    (hopt : n ^ 2 / 2 ≤ opt)
    (hadd : alg ≤ 4 / 3 * opt + 20378 * nQuarter ^ 7) :
    alg ≤ (4 / 3 + 40756 / nQuarter) * opt := by
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hscale : 20378 * nQuarter ^ 7 ≤
      (40756 / nQuarter) * opt := by
    have hmul := mul_le_mul_of_nonneg_left hopt
      (show 0 ≤ 40756 / nQuarter by positivity)
    calc
      20378 * nQuarter ^ 7 =
          (40756 / nQuarter) * (n ^ 2 / 2) := by
        rw [hpower]
        field_simp [hquarter.ne']
        ring
      _ ≤ (40756 / nQuarter) * opt := hmul
  nlinarith

end

end RandomizedObligatory
end SchedulingPaper
