import SchedulingPaper.RevealingOptimizationReduction
import SchedulingPaper.FinPairObjective
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Survival-function inequalities for revealing optimization

This file supplies the real-analysis bridge which precedes the scalar
endpoint reduction.  It proves directly that the average of an antitone
survival function on every initial interval dominates its full-prefix
average, together with the resulting quadratic-energy and adjacent-tail
bounds used in the paper.
-/

namespace SchedulingPaper
namespace RevealingOptimization

noncomputable section

open Set
open MeasureTheory
open intervalIntegral

def intervalEnergy (S : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, S t ^ 2

/-- Right-continuous empirical survival function of a labelled finite input.
The value at atoms is immaterial for all interval integrals below. -/
def empiricalSurvival {n : ℕ} (p : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun job ↦ t < p job).card : ℝ) / n

/-- Finite maximum-density threshold equation, before setting it equal to
the number of jobs. -/
def thresholdDeficit {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∑ job, max (τ - p job) 0

/-- Every nonempty finite nonnegative input has a maximum-density threshold
in the exact sum form used below. -/
theorem exists_thresholdDeficit_eq_card
    {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) :
    ∃ τ, 1 ≤ τ ∧ thresholdDeficit p τ = n := by
  let upper : ℝ := 1 + ∑ job, p job
  have hsum0 : 0 ≤ ∑ job, p job := Finset.sum_nonneg fun job _ ↦ hp job
  have honeUpper : (1 : ℝ) ≤ upper := by dsimp [upper]; linarith
  have hcontinuous : Continuous (thresholdDeficit p) := by
    unfold thresholdDeficit
    fun_prop
  have hatOne : thresholdDeficit p 1 ≤ n := by
    unfold thresholdDeficit
    calc
      (∑ job, max (1 - p job) 0) ≤ ∑ _job : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro job _hjob
        exact max_le (by linarith [hp job]) zero_le_one
      _ = n := by simp
  have hatUpper : (n : ℝ) ≤ thresholdDeficit p upper := by
    unfold thresholdDeficit
    calc
      (n : ℝ) = ∑ _job : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ job, max (upper - p job) 0 := by
        apply Finset.sum_le_sum
        intro job _hjob
        have hjobSum : p job ≤ ∑ other, p other := by
          exact Finset.single_le_sum (fun other _ ↦ hp other)
            (Finset.mem_univ job)
        exact le_max_of_le_left (by dsimp [upper]; linarith)
  have htarget : (n : ℝ) ∈
      Set.Icc (thresholdDeficit p 1) (thresholdDeficit p upper) :=
    ⟨hatOne, hatUpper⟩
  obtain ⟨τ, hτ, hvalue⟩ :=
    (intermediate_value_Icc honeUpper hcontinuous.continuousOn) htarget
  exact ⟨τ, hτ.1, hvalue⟩

theorem empiricalSurvival_antitone {n : ℕ} (p : Fin n → ℝ) :
    Antitone (empiricalSurvival p) := by
  intro a b hab
  unfold empiricalSurvival
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro job hjob
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjob ⊢
      exact lt_of_le_of_lt hab hjob)
  · positivity

theorem empiricalSurvival_nonneg {n : ℕ} (p : Fin n → ℝ) :
    ∀ t, 0 ≤ empiricalSurvival p t := by
  intro t
  unfold empiricalSurvival
  positivity

theorem empiricalSurvival_eq_zero_above
    {n : ℕ} {p : Fin n → ℝ} {u : ℝ}
    (hp : ∀ job, p job ≤ u) :
    ∀ t, u ≤ t → empiricalSurvival p t = 0 := by
  intro t hut
  unfold empiricalSurvival
  have hempty : (Finset.univ.filter fun job ↦ t < p job) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro job _hjob hlt
    exact (not_lt_of_ge ((hp job).trans hut)) hlt
  rw [hempty]
  simp

theorem empiricalSurvival_eq_sum {n : ℕ} (p : Fin n → ℝ) (t : ℝ) :
    empiricalSurvival p t =
      (∑ job, if t < p job then (1 : ℝ) else 0) / n := by
  unfold empiricalSurvival
  congr 1
  calc
    ((Finset.univ.filter fun job ↦ t < p job).card : ℝ) =
        ∑ job ∈ Finset.univ.filter (fun job ↦ t < p job), (1 : ℝ) := by
      simp
    _ = ∑ job, if t < p job then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]

theorem integral_lt_indicator_eq_min
    {p τ : ℝ} (hp : 0 ≤ p) (hτ : 0 ≤ τ) :
    (∫ t in (0 : ℝ)..τ, if t < p then (1 : ℝ) else 0) = min τ p := by
  by_cases hpτ : p ≤ τ
  · calc
      (∫ t in (0 : ℝ)..τ, if t < p then (1 : ℝ) else 0) =
          ∫ t in (0 : ℝ)..τ,
            (Set.Iic p).indicator (fun _ : ℝ ↦ (1 : ℝ)) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [Measure.ae_ne volume p] with t htp
        intro _ht
        by_cases hle : t ≤ p
        · have hlt : t < p := lt_of_le_of_ne hle htp
          simp [hle, hlt]
        · have hnlt : ¬t < p := fun hlt ↦ hle hlt.le
          simp [hle, hnlt]
      _ = ∫ _t in (0 : ℝ)..p, (1 : ℝ) := by
        exact intervalIntegral.integral_indicator ⟨hp, hpτ⟩
      _ = p := by simp
      _ = min τ p := (min_eq_right hpτ).symm
  · have hτp : τ < p := lt_of_not_ge hpτ
    calc
      (∫ t in (0 : ℝ)..τ, if t < p then (1 : ℝ) else 0) =
          ∫ _t in (0 : ℝ)..τ, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) τ := by
          simpa [Set.uIcc_of_le hτ] using ht
        simp [lt_of_le_of_lt htIcc.2 hτp]
      _ = τ := by simp
      _ = min τ p := (min_eq_left hτp.le).symm

theorem integral_empiricalSurvival_eq_average_min
    {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) { τ : ℝ} (hτ : 0 ≤ τ) :
    (∫ t in (0 : ℝ)..τ, empiricalSurvival p t) =
      (∑ job, min τ (p job)) / n := by
  simp_rw [empiricalSurvival_eq_sum]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_lt_indicator_eq_min (hp _) hτ]
  · intro job _hjob
    have hanti : Antitone (fun t : ℝ ↦
        if t < p job then (1 : ℝ) else 0) := by
      intro a b hab
      by_cases hb : b < p job
      · have ha : a < p job := lt_of_le_of_lt hab hb
        simp [ha, hb]
      · by_cases ha : a < p job <;> simp [ha, hb]
    exact hanti.intervalIntegrable

/-- The empirical maximum-density threshold equation in sum form implies
the integral threshold equation used by the survival reduction. -/
theorem empiricalSurvival_threshold_integral
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) {τ : ℝ} (hτ : 0 ≤ τ)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    (∫ t in (0 : ℝ)..τ, empiricalSurvival p t) = τ - 1 := by
  rw [integral_empiricalSurvival_eq_average_min p hp hτ]
  have hpoint : ∀ job, min τ (p job) = τ - max (τ - p job) 0 := by
    intro job
    by_cases hjob : p job ≤ τ
    · rw [min_eq_right hjob, max_eq_left (sub_nonneg.mpr hjob)]
      ring
    · have hτp : τ ≤ p job := le_of_not_ge hjob
      rw [min_eq_left hτp, max_eq_right (sub_nonpos.mpr hτp)]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hthreshold]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  simp [Fintype.card_fin]
  ring

/-- Pointwise finite-product expansion of the squared empirical survival
function.  The two coordinates represent two independent draws from the
empirical input. -/
theorem empiricalSurvival_sq_eq_pairIndicators
    {n : ℕ} (p : Fin n → ℝ) (t : ℝ) :
    empiricalSurvival p t ^ 2 =
      (∑ jobs : Fin n × Fin n,
        if t < min (p jobs.1) (p jobs.2) then (1 : ℝ) else 0) /
        (n : ℝ) ^ 2 := by
  rw [empiricalSurvival_eq_sum, div_pow]
  congr 1
  rw [pow_two, Fintype.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _hleft
  apply Finset.sum_congr rfl
  intro right _hright
  by_cases hl : t < p left <;> by_cases hr : t < p right <;>
    simp [hl, hr]

/-- Exact empirical layer-cake identity for the offline minimum kernel. -/
theorem intervalEnergy_empiricalSurvival_eq_pairMin
    {n : ℕ} (p : Fin n → ℝ) (hp : ∀ job, 0 ≤ p job)
    {a : ℝ} (ha : 0 ≤ a) :
    intervalEnergy (empiricalSurvival p) 0 a =
      (∑ jobs : Fin n × Fin n,
        min a (min (p jobs.1) (p jobs.2))) / (n : ℝ) ^ 2 := by
  unfold intervalEnergy
  simp_rw [empiricalSurvival_sq_eq_pairIndicators]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_finsetSum]
  · apply congrArg (fun value : ℝ ↦ value / (n : ℝ) ^ 2)
    apply Finset.sum_congr rfl
    intro jobs _hjobs
    exact integral_lt_indicator_eq_min
      (le_min (hp jobs.1) (hp jobs.2)) ha
  · intro jobs _hjobs
    have hanti : Antitone (fun t : ℝ ↦
        if t < min (p jobs.1) (p jobs.2) then (1 : ℝ) else 0) := by
      intro x y hxy
      by_cases hy : y < min (p jobs.1) (p jobs.2)
      · have hx : x < min (p jobs.1) (p jobs.2) := lt_of_le_of_lt hxy hy
        simp [hx, hy]
      · by_cases hx : x < min (p jobs.1) (p jobs.2) <;> simp [hx, hy]
    exact hanti.intervalIntegrable

/-- Ordered-pair leading term of the clairvoyant revealing-optimization
benchmark on a labelled finite input. -/
def empiricalRevealingOfflinePair {n : ℕ}
    (u : ℝ) (p : Fin n → ℝ) : ℝ :=
  (∑ jobs : Fin n × Fin n,
      min (effectiveLength (.finite u) (p jobs.1))
        (effectiveLength (.finite u) (p jobs.2))) / (n : ℝ) ^ 2

/-- Literal finite clairvoyant completion cost for the same vector. -/
def empiricalRevealingOfflineCost {n : ℕ}
    (u : ℝ) (p : Fin n → ℝ) : ℝ :=
  prefixCost (shortestFirst (List.ofFn fun job ↦
    effectiveLength (.finite u) (p job)))

theorem min_effectiveLengths_finite_eq
    {u p q : ℝ} :
    min (effectiveLength (.finite u) p)
        (effectiveLength (.finite u) q) =
      1 + min (u - 1) (min p q) := by
  simp only [effectiveLength_finite]
  have hsingle (x : ℝ) : min u (1 + x) = 1 + min (u - 1) x := by
    calc
      min u (1 + x) = min (1 + (u - 1)) (1 + x) := by ring_nf
      _ = 1 + min (u - 1) x := min_add_add_left 1 (u - 1) x
  rw [hsingle p, hsingle q, min_add_add_left]
  congr 1
  simp only [min_assoc, min_left_comm, min_comm, min_self]

/-- Exact finite counterpart of the paper's offline survival formula:
the ordered-pair leading coefficient is `1 + ∫ S²`. -/
theorem empiricalRevealingOfflinePair_eq_one_add_intervalEnergy
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) {u : ℝ} (hu : 1 ≤ u) :
    empiricalRevealingOfflinePair u p =
      1 + intervalEnergy (empiricalSurvival p) 0 (u - 1) := by
  rw [intervalEnergy_empiricalSurvival_eq_pairMin p hp (by linarith)]
  unfold empiricalRevealingOfflinePair
  simp_rw [min_effectiveLengths_finite_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  norm_cast
  ring_nf

/-- Exact diagonal correction relating the normalized ordered-pair term to
the literal finite shortest-first optimum. -/
theorem two_mul_empiricalRevealingOfflineCost
    {n : ℕ} (hn : 0 < n) (u : ℝ) (p : Fin n → ℝ) :
    2 * empiricalRevealingOfflineCost u p =
      (n : ℝ) ^ 2 * empiricalRevealingOfflinePair u p +
        ∑ job, effectiveLength (.finite u) (p job) := by
  unfold empiricalRevealingOfflineCost
  rw [shortestFirst_pair_formula]
  rw [two_mul_pairCost_ofFn]
  unfold empiricalRevealingOfflinePair
  rw [Fintype.sum_prod_type]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

/-- The ordered-pair leading term is a lower bound on the literal finite
offline cost; the difference is exactly half of the nonnegative diagonal. -/
theorem empiricalRevealingOfflinePair_le_offlineCost
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) {u : ℝ} (hu : 1 ≤ u) :
    (n : ℝ) ^ 2 / 2 * empiricalRevealingOfflinePair u p ≤
      empiricalRevealingOfflineCost u p := by
  have hdiag : 0 ≤ ∑ job, effectiveLength (.finite u) (p job) := by
    apply Finset.sum_nonneg
    intro job _hjob
    exact le_min (by linarith) (by linarith [hp job])
  have hexact := two_mul_empiricalRevealingOfflineCost hn u p
  nlinarith

/-- The average of an antitone function on an initial subinterval is at
least its average on the whole interval.  This is the deterministic
monotonicity fact behind the flat-prefix reduction. -/
theorem antitone_initial_integral_ge_average
    (S : ℝ → ℝ) (hS : Antitone S)
    {a τ y : ℝ} (hτ : 0 < τ) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ * y) :
    a * y ≤ ∫ t in (0 : ℝ)..a, S t := by
  have hS0a : IntervalIntegrable S volume 0 a := hS.intervalIntegrable
  have hSaτ : IntervalIntegrable S volume a τ := hS.intervalIntegrable
  have hconst0a : IntervalIntegrable (fun _ : ℝ => S a) volume 0 a :=
    intervalIntegrable_const
  have hconstaτ : IntervalIntegrable (fun _ : ℝ => S a) volume a τ :=
    intervalIntegrable_const
  have hleft : a * S a ≤ ∫ t in (0 : ℝ)..a, S t := by
    have hmono := intervalIntegral.integral_mono_on ha0 hconst0a hS0a
      (fun t ht => hS ht.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hright : (∫ t in a..τ, S t) ≤ (τ - a) * S a := by
    have hmono := intervalIntegral.integral_mono_on haτ hSaτ hconstaτ
      (fun t ht => hS ht.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hsplit :
      (∫ t in (0 : ℝ)..τ, S t) =
        (∫ t in (0 : ℝ)..a, S t) + ∫ t in a..τ, S t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hS0a hSaτ).symm
  have hτa : 0 ≤ τ - a := sub_nonneg.mpr haτ
  have hscaledLeft : (τ - a) * (a * S a) ≤
      (τ - a) * (∫ t in (0 : ℝ)..a, S t) :=
    mul_le_mul_of_nonneg_left hleft hτa
  have ha : 0 ≤ a := ha0
  have hscaledRight :
      a * (∫ t in a..τ, S t) ≤ a * ((τ - a) * S a) :=
    mul_le_mul_of_nonneg_left hright ha
  rw [hmean] at hsplit
  nlinarith

/-- Values after the averaging interval cannot exceed the initial-interval
average of an antitone function. -/
theorem antitone_tail_le_average
    (S : ℝ → ℝ) (hS : Antitone S)
    {τ y : ℝ} (hτ : 0 < τ)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ * y) :
    ∀ t, τ ≤ t → S t ≤ y := by
  have hSint : IntervalIntegrable S volume 0 τ := hS.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => S τ) volume 0 τ :=
    intervalIntegrable_const
  have hτvalue : S τ ≤ y := by
    have hlower := intervalIntegral.integral_mono_on hτ.le hconst hSint
      (fun x hx => hS hx.2)
    have hlower' : τ * S τ ≤ ∫ t in (0 : ℝ)..τ, S t := by
      simpa [intervalIntegral.integral_const, smul_eq_mul] using hlower
    rw [hmean] at hlower'
    nlinarith
  intro t hτt
  exact (hS hτt).trans hτvalue

/-- Cauchy--Schwarz on an interval, in the exact scalar form needed below.
The proof expands the nonnegative integral of `(S-y)^2`. -/
theorem intervalEnergy_ge_of_integral
    (S : ℝ → ℝ) {a y : ℝ} (ha : 0 ≤ a)
    (hS : IntervalIntegrable S volume 0 a)
    (hSsq : IntervalIntegrable (fun t => S t ^ 2) volume 0 a)
    (hmean : (∫ t in (0 : ℝ)..a, S t) = a * y) :
    a * y ^ 2 ≤ intervalEnergy S 0 a := by
  have hconst : IntervalIntegrable (fun _ : ℝ => y) volume 0 a :=
    intervalIntegrable_const
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..a, (S t - y) ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun _ _ => sq_nonneg _)
  have hexpand :
      (∫ t in (0 : ℝ)..a, (S t - y) ^ 2) =
        intervalEnergy S 0 a - 2 * y * (∫ t in (0 : ℝ)..a, S t) +
          a * y ^ 2 := by
    have hlinear : IntervalIntegrable (fun t => 2 * y * S t) volume 0 a :=
      (hS.const_mul (2 * y))
    have hconstSq : IntervalIntegrable (fun _ : ℝ => y ^ 2) volume 0 a :=
      intervalIntegrable_const
    have hpoint : (fun t => (S t - y) ^ 2) =
        (fun t => S t ^ 2 - 2 * y * S t + y ^ 2) := by
      funext t
      ring
    rw [hpoint]
    rw [intervalIntegral.integral_add (hSsq.sub hlinear) hconstSq,
      intervalIntegral.integral_sub hSsq hlinear]
    simp only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    unfold intervalEnergy
    ring
  rw [hexpand, hmean] at hnonneg
  nlinarith

/-- Initial-prefix energy bound used in
`eq:rcu-initial-cs`: monotonicity supplies the mean inequality and the
preceding interval Cauchy--Schwarz lemma supplies the square. -/
theorem antitone_initial_energy_ge
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {a τ y : ℝ} (hτ : 0 < τ) (ha0 : 0 ≤ a) (haτ : a ≤ τ)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ * y) :
    a * y ^ 2 ≤ intervalEnergy S 0 a := by
  have hS0a : IntervalIntegrable S volume 0 a := hS.intervalIntegrable
  have hSsq0a : IntervalIntegrable (fun t => S t ^ 2) volume 0 a := by
    have hsqAnti : Antitone (fun t => S t ^ 2) := by
      intro x z hxz
      have hxzS := hS hxz
      nlinarith [hS0 x, hS0 z]
    exact hsqAnti.intervalIntegrable
  have hprefix := antitone_initial_integral_ge_average
    S hS hτ ha0 haτ hmean
  let z := (∫ t in (0 : ℝ)..a, S t) / a
  by_cases haZero : a = 0
  · subst a
    simp [intervalEnergy]
  · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
    have hz : (∫ t in (0 : ℝ)..a, S t) = a * z := by
      dsimp [z]
      field_simp
    have henergy := intervalEnergy_ge_of_integral S ha0 hS0a hSsq0a hz
    have hyz : y ≤ z := by
      dsimp [z]
      rw [le_div_iff₀ haPos]
      simpa [mul_comm] using hprefix
    have hySq : y ^ 2 ≤ z ^ 2 := by
      have hy0 : 0 ≤ y := by
        have hfullNonneg : 0 ≤ ∫ t in (0 : ℝ)..τ, S t :=
          intervalIntegral.integral_nonneg hτ.le (fun t _ => hS0 t)
        rw [hmean] at hfullNonneg
        nlinarith
      nlinarith
    exact (mul_le_mul_of_nonneg_left hySq ha0).trans henergy

/-- A pointwise upper bound on a nonnegative function gives the expected
interval-energy upper bound. -/
theorem intervalEnergy_le_const
    (S : ℝ → ℝ) {a b y : ℝ} (hab : a ≤ b)
    (hS : IntervalIntegrable (fun t => S t ^ 2) volume a b)
    (hS0 : ∀ t ∈ Set.Icc a b, 0 ≤ S t)
    (hSy : ∀ t ∈ Set.Icc a b, S t ≤ y) :
    intervalEnergy S a b ≤ (b - a) * y ^ 2 := by
  have hconst : IntervalIntegrable (fun _ : ℝ => y ^ 2) volume a b :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hS hconst (fun t ht => by
    nlinarith [hS0 t ht, hSy t ht])
  simpa [intervalEnergy, intervalIntegral.integral_const, smul_eq_mul] using hmono

/-- Adjacent-tail averaging for a nonnegative antitone survival function.
The later unit interval has no more quadratic energy than `1/L` times the
preceding interval of length `L`. -/
theorem antitone_adjacent_tail_energy
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {a b : ℝ} (hab : a < b) :
    intervalEnergy S b (b + 1) ≤
      intervalEnergy S a b / (b - a) := by
  have hsqAnti : Antitone (fun t => S t ^ 2) := by
    intro x y hxy
    have hxyS := hS hxy
    nlinarith [hS0 x, hS0 y]
  have hsqab : IntervalIntegrable (fun t => S t ^ 2) volume a b :=
    hsqAnti.intervalIntegrable
  have hsqTail : IntervalIntegrable (fun t => S t ^ 2) volume b (b + 1) :=
    hsqAnti.intervalIntegrable
  have hconstAB : IntervalIntegrable (fun _ : ℝ => S b ^ 2) volume a b :=
    intervalIntegrable_const
  have hconstTail : IntervalIntegrable (fun _ : ℝ => S b ^ 2) volume b (b + 1) :=
    intervalIntegrable_const
  have hlower : (b - a) * S b ^ 2 ≤ intervalEnergy S a b := by
    have hmono := intervalIntegral.integral_mono_on hab.le hconstAB hsqab
      (fun t ht => by
        have hle := hS ht.2
        nlinarith [hS0 t, hS0 b])
    simpa [intervalEnergy, intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hupper : intervalEnergy S b (b + 1) ≤ S b ^ 2 := by
    have hmono := intervalIntegral.integral_mono_on (by linarith) hsqTail hconstTail
      (fun t ht => by
        have hle := hS ht.1
        nlinarith [hS0 t, hS0 b])
    simpa [intervalEnergy, intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [le_div_iff₀ hba]
  exact (mul_le_mul_of_nonneg_right hupper hba.le).trans (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower)

/-- All monotone-tail constraints used in the middle case, derived from the
literal survival-function hypotheses rather than assumed as scalar facts. -/
theorem survival_middle_tail_constraints
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ y : ℝ} (hτ : 0 < τ) (hcase : τ < u - 1)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ * y) :
    let E := intervalEnergy S τ (u - 1)
    let G := intervalEnergy S (u - 1) u
    0 ≤ E ∧ E ≤ (u - 1 - τ) * y ^ 2 ∧
      G ≤ E / (u - 1 - τ) := by
  dsimp
  have hsqAnti : Antitone (fun t => S t ^ 2) := by
    intro x z hxz
    have hxzS := hS hxz
    nlinarith [hS0 x, hS0 z]
  have hEint : IntervalIntegrable (fun t => S t ^ 2) volume τ (u - 1) :=
    hsqAnti.intervalIntegrable
  have hE0 : 0 ≤ intervalEnergy S τ (u - 1) := by
    unfold intervalEnergy
    exact intervalIntegral.integral_nonneg hcase.le
      (fun t _ => sq_nonneg (S t))
  have htail : ∀ t ∈ Set.Icc τ (u - 1), S t ≤ y := by
    intro t ht
    exact antitone_tail_le_average S hS hτ hmean t ht.1
  have hEmax : intervalEnergy S τ (u - 1) ≤
      (u - 1 - τ) * y ^ 2 := by
    exact intervalEnergy_le_const S hcase.le hEint
      (fun t _ => hS0 t) htail
  have hG := antitone_adjacent_tail_energy S hS hS0 hcase
  have hendpoint : u - 1 + 1 = u := by ring
  rw [hendpoint] at hG
  exact ⟨hE0, hEmax, hG⟩

/-- The complete middle-case survival reduction.  Unlike
`middleTail_reduction_le_binary_families`, this theorem starts with an
actual nonnegative antitone survival function and derives both its prefix
and tail energy inequalities internally. -/
theorem survival_middle_case_le_binary_families
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ : ℝ} (hτ : 1 ≤ τ) (hcase : τ < u - 1)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ - 1) :
    let E := intervalEnergy S τ (u - 1)
    let G := intervalEnergy S (u - 1) u
    (τ + E + G) / (1 + intervalEnergy S 0 (u - 1)) ≤
      max (familyA τ) (familyB u τ) := by
  dsimp
  let y := survivalMass τ
  let E := intervalEnergy S τ (u - 1)
  let G := intervalEnergy S (u - 1) u
  let L := u - 1 - τ
  have hτ0 : 0 < τ := by linarith
  have hmeanY : (∫ t in (0 : ℝ)..τ, S t) = τ * y := by
    rw [hmean]
    dsimp [y, survivalMass]
    field_simp [hτ0.ne']
  obtain ⟨hE0, hEmax, hG⟩ :=
    survival_middle_tail_constraints S hS hS0 hτ0 hcase hmeanY
  have hL : 0 < L := by dsimp [L]; linarith
  have hsqAnti : Antitone (fun t => S t ^ 2) := by
    intro x z hxz
    have hxzS := hS hxz
    nlinarith [hS0 x, hS0 z]
  have hsq0τ : IntervalIntegrable (fun t => S t ^ 2) volume 0 τ :=
    hsqAnti.intervalIntegrable
  have hsqτs : IntervalIntegrable (fun t => S t ^ 2) volume τ (u - 1) :=
    hsqAnti.intervalIntegrable
  have hprefix : τ * y ^ 2 ≤ intervalEnergy S 0 τ := by
    exact antitone_initial_energy_ge S hS hS0 hτ0 hτ0.le le_rfl hmeanY
  have hsplit : intervalEnergy S 0 (u - 1) =
      intervalEnergy S 0 τ + E := by
    unfold intervalEnergy E
    exact (intervalIntegral.integral_add_adjacent_intervals hsq0τ hsqτs).symm
  have hden : 1 + τ * y ^ 2 + E ≤
      1 + intervalEnergy S 0 (u - 1) := by
    rw [hsplit]
    linarith
  have hden0 : 0 < 1 + τ * y ^ 2 + E := by
    positivity
  have hnum0 : 0 ≤ τ + E + G := by
    have hG0 : 0 ≤ G := by
      unfold G intervalEnergy
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun t _ => sq_nonneg (S t))
    linarith
  have hnum : τ + E + G ≤ τ + (u - τ) / L * E := by
    have hGE : G ≤ E / L := by simpa [E, G, L] using hG
    have huτ : u - τ = L + 1 := by
      dsimp [L]
      ring
    have hfactor : (u - τ) / L * E = E + E / L := by
      rw [huτ, add_div, div_self hL.ne']
      ring
    rw [hfactor]
    linarith
  have hratio : (τ + E + G) /
        (1 + intervalEnergy S 0 (u - 1)) ≤
      (τ + (u - τ) / L * E) / (1 + τ * y ^ 2 + E) := by
    calc
      (τ + E + G) / (1 + intervalEnergy S 0 (u - 1)) ≤
          (τ + E + G) / (1 + τ * y ^ 2 + E) := by
        exact div_le_div_of_nonneg_left hnum0 hden0 hden
      _ ≤ (τ + (u - τ) / L * E) / (1 + τ * y ^ 2 + E) := by
        exact div_le_div_of_nonneg_right hnum hden0.le
  exact hratio.trans (by
    simpa [E, L, y] using
      middleTail_reduction_le_binary_families hτ hcase hE0 (by
        simpa [E, L, y] using hEmax))

/-- The complete near-cap case `u-1 ≤ τ ≤ u`, starting from the survival
function.  Prefix energy controls the denominator and tail monotonicity
controls the numerator. -/
theorem survival_near_cap_le_familyB
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ : ℝ} (hu : 1 ≤ u) (hτ : 1 ≤ τ)
    (hlower : u - 1 ≤ τ) (hupper : τ ≤ u)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ - 1) :
    (τ + intervalEnergy S τ u) /
        (1 + intervalEnergy S 0 (u - 1)) ≤ familyB u τ := by
  let y := survivalMass τ
  have hτ0 : 0 < τ := by linarith
  have hmeanY : (∫ t in (0 : ℝ)..τ, S t) = τ * y := by
    rw [hmean]
    dsimp [y, survivalMass]
    field_simp [hτ0.ne']
  have hsqAnti : Antitone (fun t => S t ^ 2) := by
    intro x z hxz
    have hxzS := hS hxz
    nlinarith [hS0 x, hS0 z]
  have htailInt : IntervalIntegrable (fun t => S t ^ 2) volume τ u :=
    hsqAnti.intervalIntegrable
  have htailBound : intervalEnergy S τ u ≤ (u - τ) * y ^ 2 := by
    exact intervalEnergy_le_const S hupper htailInt
      (fun t _ => hS0 t)
      (fun t ht => antitone_tail_le_average S hS hτ0 hmeanY t ht.1)
  have hprefix : (u - 1) * y ^ 2 ≤ intervalEnergy S 0 (u - 1) := by
    exact antitone_initial_energy_ge S hS hS0 hτ0
      (by linarith) hlower hmeanY
  have henergy0 : 0 ≤ intervalEnergy S 0 (u - 1) := by
    unfold intervalEnergy
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t _ => sq_nonneg (S t))
  have hden : 0 < 1 + intervalEnergy S 0 (u - 1) := by linarith
  apply nearCap_reduction_le_familyB hu hτ hupper hden
  · simpa [y] using add_le_add_left htailBound τ
  · simpa [y] using add_le_add_left hprefix 1

/-- The `τ>u` survival case.  The zero extension identifies the average on
`[0,u]`; the initial-energy lemma then gives exactly the denominator bound
for the cap endpoint `B_u(u)`. -/
theorem survival_beyond_cap_le_familyB
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ : ℝ} (hu : 1 < u) (hτ : u < τ)
    (hzero : ∀ t, u ≤ t → S t = 0)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ - 1) :
    u / (1 + intervalEnergy S 0 (u - 1)) ≤ familyB u u := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hτ0 : 0 < τ := hu0.trans hτ
  have hS0u : IntervalIntegrable S volume 0 u := hS.intervalIntegrable
  have hSuτ : IntervalIntegrable S volume u τ := hS.intervalIntegrable
  have htailZero : (∫ t in u..τ, S t) = 0 := by
    have heq : Set.EqOn S (fun _ : ℝ => 0) (Set.uIcc u τ) := by
      intro t ht
      have ht' : t ∈ Set.Icc u τ := by
        simpa [Set.uIcc_of_le hτ.le] using ht
      exact hzero t ht'.1
    simpa using intervalIntegral.integral_congr heq
  have hsplit : (∫ t in (0 : ℝ)..τ, S t) =
      (∫ t in (0 : ℝ)..u, S t) + ∫ t in u..τ, S t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hS0u hSuτ).symm
  have hmeanCap : (∫ t in (0 : ℝ)..u, S t) =
      u * ((τ - 1) / u) := by
    have hmean' := hmean
    rw [hsplit, htailZero, add_zero] at hmean'
    calc
      (∫ t in (0 : ℝ)..u, S t) = τ - 1 := hmean'
      _ = u * ((τ - 1) / u) := by field_simp [hu0.ne']
  have hprefix : (u - 1) * ((τ - 1) / u) ^ 2 ≤
      intervalEnergy S 0 (u - 1) := by
    exact antitone_initial_energy_ge S hS hS0 hu0
      (by linarith) (by linarith) hmeanCap
  have hyCompare : survivalMass u ≤ (τ - 1) / u := by
    unfold survivalMass
    rw [div_le_div_iff₀ hu0 hu0]
    nlinarith
  have hy0 : 0 ≤ survivalMass u := by
    unfold survivalMass
    positivity
  have htarget : (u - 1) * survivalMass u ^ 2 ≤
      intervalEnergy S 0 (u - 1) := by
    have hsquare : survivalMass u ^ 2 ≤ ((τ - 1) / u) ^ 2 := by
      nlinarith
    exact (mul_le_mul_of_nonneg_left hsquare (by linarith)).trans hprefix
  have henergy0 : 0 ≤ intervalEnergy S 0 (u - 1) := by
    unfold intervalEnergy
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t _ => sq_nonneg (S t))
  apply nearCap_reduction_le_familyB hu.le hu.le le_rfl (by linarith)
  · simp
  · simpa using add_le_add_left htarget 1

/-- The three survival regimes assembled into the exact endpoint reduction
used by the curve proof.  The branch `τ≤u` uses the stationary numerator;
the branch `u<τ` uses raw execution. -/
theorem survival_case_reduction
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ)
    (hzero : ∀ t, u ≤ t → S t = 0)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ - 1) :
    if τ ≤ u then
      (τ + intervalEnergy S τ u) /
          (1 + intervalEnergy S 0 (u - 1)) ≤
        max (familyA τ) (familyB u τ)
    else
      u / (1 + intervalEnergy S 0 (u - 1)) ≤ familyB u u := by
  split_ifs with hτu
  · by_cases hmiddle : τ < u - 1
    · have hsqAnti : Antitone (fun t => S t ^ 2) := by
        intro x z hxz
        have hxzS := hS hxz
        nlinarith [hS0 x, hS0 z]
      have hleft : IntervalIntegrable (fun t => S t ^ 2) volume τ (u - 1) :=
        hsqAnti.intervalIntegrable
      have hright : IntervalIntegrable (fun t => S t ^ 2) volume (u - 1) u :=
        hsqAnti.intervalIntegrable
      have htailSplit : intervalEnergy S τ u =
          intervalEnergy S τ (u - 1) + intervalEnergy S (u - 1) u := by
        unfold intervalEnergy
        exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
      rw [htailSplit]
      simpa [add_assoc] using
        survival_middle_case_le_binary_families S hS hS0 hτ hmiddle hmean
    · have hnear : u - 1 ≤ τ := by linarith
      exact (survival_near_cap_le_familyB S hS hS0 hu.le hτ
        hnear hτu hmean).trans (le_max_right _ _)
  · exact survival_beyond_cap_le_familyB S hS hS0 hu
      (lt_of_not_ge hτu) hzero hmean

/-- End product of the survival calculation: every literal nonnegative
antitone survival function satisfying the maximum-density threshold equation
lies below the advertised four-piece randomized curve. -/
theorem survival_ratio_le_randomizedCurve
    (S : ℝ → ℝ) (hS : Antitone S) (hS0 : ∀ t, 0 ≤ S t)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ)
    (hzero : ∀ t, u ≤ t → S t = 0)
    (hmean : (∫ t in (0 : ℝ)..τ, S t) = τ - 1) :
    if τ ≤ u then
      (τ + intervalEnergy S τ u) /
          (1 + intervalEnergy S 0 (u - 1)) ≤ randomizedCurve u
    else
      u / (1 + intervalEnergy S 0 (u - 1)) ≤ randomizedCurve u := by
  have hfamilies := binaryFamilies_le_curve hu
  split_ifs with hτu
  · by_cases hmiddle : τ < u - 1
    · have hreduction := survival_case_reduction
        S hS hS0 hu hτ hzero hmean
      rw [if_pos hτu] at hreduction
      exact hreduction.trans (max_le
        (hfamilies.2 τ hτ hmiddle.le)
        (hfamilies.1 τ hτ hτu))
    · have hnear : u - 1 ≤ τ := le_of_not_gt hmiddle
      exact (survival_near_cap_le_familyB S hS hS0 hu.le hτ
        hnear hτu hmean).trans (hfamilies.1 τ hτ hτu)
  · exact (survival_beyond_cap_le_familyB S hS hS0 hu
      (lt_of_not_ge hτu) hzero hmean).trans
        (hfamilies.1 u hu.le le_rfl)

/-- Empirical-input specialization of `survival_ratio_le_randomizedCurve`.
No abstract survival-function hypotheses remain: monotonicity, nonnegativity,
and the cap support are derived from the concrete labelled vector. -/
theorem empiricalSurvival_ratio_le_randomizedCurve
    {n : ℕ} (p : Fin n → ℝ)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ)
    (hp : ∀ job, p job ≤ u)
    (hmean : (∫ t in (0 : ℝ)..τ, empiricalSurvival p t) = τ - 1) :
    if τ ≤ u then
      (τ + intervalEnergy (empiricalSurvival p) τ u) /
          (1 + intervalEnergy (empiricalSurvival p) 0 (u - 1)) ≤
        randomizedCurve u
    else
      u / (1 + intervalEnergy (empiricalSurvival p) 0 (u - 1)) ≤
        randomizedCurve u := by
  exact survival_ratio_le_randomizedCurve (empiricalSurvival p)
    (empiricalSurvival_antitone p) (empiricalSurvival_nonneg p)
    hu hτ (empiricalSurvival_eq_zero_above hp) hmean

/-- Fully discrete specialization: the maximum-density threshold is supplied
in the finite sum form used by the scheduling policy, and all survival
hypotheses are discharged from the labelled processing-time vector. -/
theorem empiricalSurvival_ratio_le_randomizedCurve_of_threshold
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    if τ ≤ u then
      (τ + intervalEnergy (empiricalSurvival p) τ u) /
          (1 + intervalEnergy (empiricalSurvival p) 0 (u - 1)) ≤
        randomizedCurve u
    else
      u / (1 + intervalEnergy (empiricalSurvival p) 0 (u - 1)) ≤
        randomizedCurve u := by
  apply empiricalSurvival_ratio_le_randomizedCurve p hu hτ hpu
  exact empiricalSurvival_threshold_integral hn p hp0 (by linarith) hthreshold

/-- The same discrete theorem with the denominator rewritten as the actual
ordered-pair leading term of the finite clairvoyant benchmark. -/
theorem empiricalStationaryRatio_le_randomizedCurve_of_threshold
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    if τ ≤ u then
      (τ + intervalEnergy (empiricalSurvival p) τ u) /
          empiricalRevealingOfflinePair u p ≤ randomizedCurve u
    else
      u / empiricalRevealingOfflinePair u p ≤ randomizedCurve u := by
  rw [empiricalRevealingOfflinePair_eq_one_add_intervalEnergy
    hn p hp0 hu.le]
  exact empiricalSurvival_ratio_le_randomizedCurve_of_threshold
    hn p hu hτ hp0 hpu hthreshold

/-- Unconditional empirical announced-policy bound.  For every nonempty
finite input the theorem constructs a valid maximum-density threshold and
bounds the resulting stationary-or-raw leading ratio by the exact curve. -/
theorem exists_empiricalStationaryRatio_le_randomizedCurve
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u : ℝ} (hu : 1 < u)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u) :
    ∃ τ, 1 ≤ τ ∧
      (∑ job, max (τ - p job) 0 = n) ∧
      (if τ ≤ u then
        (τ + intervalEnergy (empiricalSurvival p) τ u) /
            empiricalRevealingOfflinePair u p ≤ randomizedCurve u
      else
        u / empiricalRevealingOfflinePair u p ≤ randomizedCurve u) := by
  obtain ⟨τ, hτ, hthreshold⟩ := exists_thresholdDeficit_eq_card p hp0
  have hthreshold' : ∑ job, max (τ - p job) 0 = n := by
    simpa [thresholdDeficit] using hthreshold
  exact ⟨τ, hτ, hthreshold',
    empiricalStationaryRatio_le_randomizedCurve_of_threshold
      hn p hu hτ hp0 hpu hthreshold'⟩

/-- Finite leading-cost form of the announced upper bound.  The only
omitted part of an operational stationary schedule is its linear diagonal
and implementation remainder; the comparator on the right is the literal
finite clairvoyant SPT cost. -/
theorem exists_empiricalAnnouncedLeadingCost_le_curve_mul_offline
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u : ℝ} (hu : 1 < u)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u) :
    ∃ τ, 1 ≤ τ ∧
      (∑ job, max (τ - p job) 0 = n) ∧
      (n : ℝ) ^ 2 / 2 *
          (if τ ≤ u then
            τ + intervalEnergy (empiricalSurvival p) τ u
          else u) ≤
        randomizedCurve u * empiricalRevealingOfflineCost u p := by
  obtain ⟨τ, hτ, hthreshold, hratio⟩ :=
    exists_empiricalStationaryRatio_le_randomizedCurve hn p hu hp0 hpu
  let D := empiricalRevealingOfflinePair u p
  have henergy0 : 0 ≤ intervalEnergy (empiricalSurvival p) 0 (u - 1) := by
    unfold intervalEnergy
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t _ ↦ sq_nonneg (empiricalSurvival p t))
  have hDform : D =
      1 + intervalEnergy (empiricalSurvival p) 0 (u - 1) := by
    dsimp [D]
    exact empiricalRevealingOfflinePair_eq_one_add_intervalEnergy
      hn p hp0 hu.le
  have hDpos : 0 < D := by rw [hDform]; linarith
  have hoffline : (n : ℝ) ^ 2 / 2 * D ≤
      empiricalRevealingOfflineCost u p := by
    exact empiricalRevealingOfflinePair_le_offlineCost hn p hp0 hu.le
  have hscale0 : 0 ≤ (n : ℝ) ^ 2 / 2 := by positivity
  refine ⟨τ, hτ, hthreshold, ?_⟩
  by_cases hτu : τ ≤ u
  · rw [if_pos hτu] at hratio ⊢
    let numerator := τ + intervalEnergy (empiricalSurvival p) τ u
    have htail0 : 0 ≤ intervalEnergy (empiricalSurvival p) τ u := by
      unfold intervalEnergy
      exact intervalIntegral.integral_nonneg hτu
        (fun t _ ↦ sq_nonneg (empiricalSurvival p t))
    have hnum0 : 0 ≤ numerator := by dsimp [numerator]; linarith
    have hratio' : numerator / D ≤ randomizedCurve u := by
      simpa [numerator, D] using hratio
    have hnumLe : numerator ≤ randomizedCurve u * D :=
      (div_le_iff₀ hDpos).mp hratio'
    have hcurve0 : 0 ≤ randomizedCurve u :=
      (div_nonneg hnum0 hDpos.le).trans hratio'
    calc
      (n : ℝ) ^ 2 / 2 * numerator ≤
          (n : ℝ) ^ 2 / 2 * (randomizedCurve u * D) :=
        mul_le_mul_of_nonneg_left hnumLe hscale0
      _ = randomizedCurve u * ((n : ℝ) ^ 2 / 2 * D) := by ring
      _ ≤ randomizedCurve u * empiricalRevealingOfflineCost u p :=
        mul_le_mul_of_nonneg_left hoffline hcurve0
  · rw [if_neg hτu] at hratio ⊢
    have hratio' : u / D ≤ randomizedCurve u := by
      simpa [D] using hratio
    have hu0 : 0 ≤ u := by linarith
    have hnumLe : u ≤ randomizedCurve u * D :=
      (div_le_iff₀ hDpos).mp hratio'
    have hcurve0 : 0 ≤ randomizedCurve u :=
      (div_nonneg hu0 hDpos.le).trans hratio'
    calc
      (n : ℝ) ^ 2 / 2 * u ≤
          (n : ℝ) ^ 2 / 2 * (randomizedCurve u * D) :=
        mul_le_mul_of_nonneg_left hnumLe hscale0
      _ = randomizedCurve u * ((n : ℝ) ^ 2 / 2 * D) := by ring
      _ ≤ randomizedCurve u * empiricalRevealingOfflineCost u p :=
        mul_le_mul_of_nonneg_left hoffline hcurve0

/-! ## Exact finite stationary endpoint -/

/-- Number of occurrences strictly below a maximum-density threshold. -/
def thresholdEarlyCount {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∑ job, if p job < τ then 1 else 0

/-- Processing work of the occurrences strictly below the threshold. -/
def thresholdEarlyWork {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∑ job, if p job < τ then p job else 0

/-- Indicator of the deferred threshold tail.  Equality is put in the tail;
this convention is immaterial for the density equation. -/
def thresholdLateIndicator {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) (job : Fin n) : ℝ :=
  if τ ≤ p job then 1 else 0

/-- Ordered minimum-pair work of the deferred threshold tail. -/
def thresholdLateOrderedMin {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∑ jobs : Fin n × Fin n,
    thresholdLateIndicator p τ jobs.1 *
      thresholdLateIndicator p τ jobs.2 *
        min (p jobs.1) (p jobs.2)

/-- The threshold deficit is exactly `τ e-m`, where `e` and `m` are the
early count and early processing work. -/
theorem thresholdDeficit_eq_threshold_mul_earlyCount_sub_earlyWork
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    thresholdDeficit p τ =
      τ * thresholdEarlyCount p τ - thresholdEarlyWork p τ := by
  unfold thresholdDeficit thresholdEarlyCount thresholdEarlyWork
  calc
    (∑ job, max (τ - p job) 0) =
        ∑ job, if p job < τ then τ - p job else 0 := by
      apply Finset.sum_congr rfl
      intro job _hjob
      by_cases h : p job < τ
      · rw [if_pos h, max_eq_left (sub_nonneg.mpr h.le)]
      · rw [if_neg h, max_eq_right]
        exact sub_nonpos.mpr (le_of_not_gt h)
    _ = τ * (∑ job, if p job < τ then 1 else 0) -
          ∑ job, if p job < τ then p job else 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro job _hjob
      by_cases h : p job < τ <;> simp [h]

/-- Early and late threshold indicators partition every occurrence. -/
theorem thresholdEarlyCount_add_lateCount
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    thresholdEarlyCount p τ +
        ∑ job, thresholdLateIndicator p τ job = n := by
  unfold thresholdEarlyCount thresholdLateIndicator
  rw [← Finset.sum_add_distrib]
  calc
    (∑ job : Fin n, ((if p job < τ then (1 : ℝ) else 0) +
        (if τ ≤ p job then 1 else 0))) =
        ∑ _job : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro job _hjob
      by_cases h : p job < τ
      · simp [h, not_le.mpr h]
      · simp [h, le_of_not_gt h]
    _ = n := by simp

/-- The deferred ordered minimum moment splits into a rectangle of height
`τ` plus the excess of the full pair minimum above `τ`. -/
theorem thresholdLateOrderedMin_eq_rectangle_add_excess
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    thresholdLateOrderedMin p τ =
      τ * ((n : ℝ) - thresholdEarlyCount p τ) ^ 2 +
        ∑ jobs : Fin n × Fin n,
          max (min (p jobs.1) (p jobs.2) - τ) 0 := by
  have hpoint : ∀ jobs : Fin n × Fin n,
      thresholdLateIndicator p τ jobs.1 *
          thresholdLateIndicator p τ jobs.2 *
            min (p jobs.1) (p jobs.2) =
        τ * (thresholdLateIndicator p τ jobs.1 *
          thresholdLateIndicator p τ jobs.2) +
            max (min (p jobs.1) (p jobs.2) - τ) 0 := by
    intro jobs
    by_cases hleft : τ ≤ p jobs.1
    · by_cases hright : τ ≤ p jobs.2
      · have hmin : τ ≤ min (p jobs.1) (p jobs.2) :=
          le_min hleft hright
        simp [thresholdLateIndicator, hleft, hright]
      · have hright' : p jobs.2 < τ := lt_of_not_ge hright
        have hmin : min (p jobs.1) (p jobs.2) ≤ τ :=
          (min_le_right _ _).trans hright'.le
        simp [thresholdLateIndicator, hleft, hright,
          max_eq_right (sub_nonpos.mpr hmin)]
    · have hleft' : p jobs.1 < τ := lt_of_not_ge hleft
      have hmin : min (p jobs.1) (p jobs.2) ≤ τ :=
        (min_le_left _ _).trans hleft'.le
      simp [thresholdLateIndicator, hleft,
        max_eq_right (sub_nonpos.mpr hmin)]
  unfold thresholdLateOrderedMin
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  have hproduct :
      (∑ jobs : Fin n × Fin n,
          thresholdLateIndicator p τ jobs.1 *
            thresholdLateIndicator p τ jobs.2) =
        (∑ job, thresholdLateIndicator p τ job) ^ 2 := by
    rw [Fintype.sum_prod_type, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro left _hleft
    rw [Finset.mul_sum]
  rw [hproduct]
  have hpartition := thresholdEarlyCount_add_lateCount p τ
  have hlate : (∑ job, thresholdLateIndicator p τ job) =
      (n : ℝ) - thresholdEarlyCount p τ := by linarith
  rw [hlate]

/-- Exact empirical layer-cake formula for the survival energy above a
threshold. -/
theorem intervalEnergy_empiricalSurvival_tail_eq_pairExcess
    {n : ℕ} (p : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) {τ u : ℝ}
    (hτ0 : 0 ≤ τ) (hτu : τ ≤ u) (hpu : ∀ job, p job ≤ u) :
    intervalEnergy (empiricalSurvival p) τ u =
      (∑ jobs : Fin n × Fin n,
        max (min (p jobs.1) (p jobs.2) - τ) 0) / (n : ℝ) ^ 2 := by
  have hsqAnti : Antitone (fun t ↦ empiricalSurvival p t ^ 2) := by
    intro a b hab
    have hanti := empiricalSurvival_antitone p hab
    nlinarith [empiricalSurvival_nonneg p a,
      empiricalSurvival_nonneg p b]
  have hleft : IntervalIntegrable
      (fun t ↦ empiricalSurvival p t ^ 2) volume 0 τ :=
    hsqAnti.intervalIntegrable
  have hright : IntervalIntegrable
      (fun t ↦ empiricalSurvival p t ^ 2) volume τ u :=
    hsqAnti.intervalIntegrable
  have hsplit :
      intervalEnergy (empiricalSurvival p) 0 u =
        intervalEnergy (empiricalSurvival p) 0 τ +
          intervalEnergy (empiricalSurvival p) τ u := by
    unfold intervalEnergy
    exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
  rw [intervalEnergy_empiricalSurvival_eq_pairMin p hp0 hτ0,
    intervalEnergy_empiricalSurvival_eq_pairMin p hp0
      (hτ0.trans hτu)] at hsplit
  calc
    intervalEnergy (empiricalSurvival p) τ u =
        (∑ jobs : Fin n × Fin n,
            min u (min (p jobs.1) (p jobs.2))) / (n : ℝ) ^ 2 -
          (∑ jobs : Fin n × Fin n,
            min τ (min (p jobs.1) (p jobs.2))) / (n : ℝ) ^ 2 := by
      linarith [hsplit]
    _ = (∑ jobs : Fin n × Fin n,
          (min u (min (p jobs.1) (p jobs.2)) -
            min τ (min (p jobs.1) (p jobs.2)))) / (n : ℝ) ^ 2 := by
      rw [← sub_div, ← Finset.sum_sub_distrib]
    _ = (∑ jobs : Fin n × Fin n,
          max (min (p jobs.1) (p jobs.2) - τ) 0) /
            (n : ℝ) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro jobs _hjobs
      let pair := min (p jobs.1) (p jobs.2)
      have hpairU : pair ≤ u :=
        (min_le_left _ _).trans (hpu jobs.1)
      rw [min_eq_right hpairU]
      by_cases hpairτ : pair ≤ τ
      · rw [min_eq_right hpairτ, max_eq_right (sub_nonpos.mpr hpairτ)]
        ring
      · have hτpair : τ ≤ pair := le_of_not_ge hpairτ
        rw [min_eq_left hτpair, max_eq_left (sub_nonneg.mpr hτpair)]

/-- Normalized ordered minimum moment of the deferred tail, in the exact
survival form used by the stationary policy. -/
theorem thresholdLateOrderedMin_div_eq_rectangle_add_tailEnergy
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) {τ u : ℝ}
    (hτ0 : 0 ≤ τ) (hτu : τ ≤ u) (hpu : ∀ job, p job ≤ u) :
    thresholdLateOrderedMin p τ / (n : ℝ) ^ 2 =
      τ * (1 - thresholdEarlyCount p τ / n) ^ 2 +
        intervalEnergy (empiricalSurvival p) τ u := by
  rw [thresholdLateOrderedMin_eq_rectangle_add_excess]
  rw [intervalEnergy_empiricalSurvival_tail_eq_pairExcess
    p hp0 hτ0 hτu hpu]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

/-- Exact finite completion-cost formula for the stationary threshold
template, written in normalized early/tail aggregates.  The final summand is
the diagonal correction from the stationary pair identity. -/
def empiricalStationaryFiniteCost {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  let e := thresholdEarlyCount p τ
  let m := thresholdEarlyWork p τ
  let K := thresholdLateOrderedMin p τ
  (n : ℝ) ^ 2 *
      ((1 + m / n) * (1 - (e / n) / 2) +
        (K / (n : ℝ) ^ 2) / 2) +
    (e + ∑ job, p job) / 2

/-- Under the maximum-density equation, the exact finite stationary cost is
its survival leading term plus the precise diagonal correction. -/
theorem empiricalStationaryFiniteCost_eq_survival
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) {τ u : ℝ}
    (hτ : 1 ≤ τ) (hτu : τ ≤ u) (hpu : ∀ job, p job ≤ u)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    empiricalStationaryFiniteCost p τ =
      (n : ℝ) ^ 2 / 2 *
          (τ + intervalEnergy (empiricalSurvival p) τ u) +
        (thresholdEarlyCount p τ + ∑ job, p job) / 2 := by
  have hdeficit : thresholdDeficit p τ = n := by
    simpa [thresholdDeficit] using hthreshold
  rw [thresholdDeficit_eq_threshold_mul_earlyCount_sub_earlyWork]
      at hdeficit
  have hm : thresholdEarlyWork p τ =
      τ * thresholdEarlyCount p τ - n := by linarith
  have htail :=
    thresholdLateOrderedMin_div_eq_rectangle_add_tailEnergy
      hn p hp0 (by linarith) hτu hpu
  unfold empiricalStationaryFiniteCost
  dsimp only
  rw [hm, htail]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring

/-- Literal all-raw completion cost on `n` equal raw blocks. -/
def empiricalRawCost (n : ℕ) (u : ℝ) : ℝ :=
  u * n * (n + 1) / 2

/-- At a cap at most one, every effective length equals the raw duration, so
the literal all-raw cost is exactly the finite clairvoyant optimum. -/
theorem empiricalRawCost_eq_revealingOfflineCost_of_cap_le_one
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hp0 : ∀ job, 0 ≤ p job) :
    empiricalRawCost n u = empiricalRevealingOfflineCost u p := by
  have heffective : ∀ job,
      effectiveLength (.finite u) (p job) = u := by
    intro job
    simp only [effectiveLength_finite]
    exact min_eq_left (by linarith [hp0 job])
  have hpair : empiricalRevealingOfflinePair u p = u := by
    unfold empiricalRevealingOfflinePair
    simp_rw [heffective, min_self]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Fintype.card_fin]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnR]
    norm_cast
    ring
  have hdiag : (∑ job, effectiveLength (.finite u) (p job)) = n * u := by
    simp_rw [heffective]
    simp
  have hexact := two_mul_empiricalRevealingOfflineCost hn u p
  rw [hpair, hdiag] at hexact
  unfold empiricalRawCost
  nlinarith

/-- The finite upper half of the randomized revealing curve in the trivial
low-cap regime. -/
theorem empiricalRawCost_le_curve_mul_offline_of_cap_le_one
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hp0 : ∀ job, 0 ≤ p job) :
    empiricalRawCost n u ≤
      randomizedCurve u * empiricalRevealingOfflineCost u p := by
  rw [empiricalRawCost_eq_revealingOfflineCost_of_cap_le_one
    hn p hu0 hu1 hp0]
  unfold randomizedCurve
  rw [if_pos hu1]
  simp

/-- Exact finite announced endpoint guarantee.  The chosen maximum-density
threshold uses the stationary template when it lies below the cap and the
literal all-raw template otherwise.  Unlike the preceding leading-term
theorem, this statement retains an explicit linear finite-size remainder. -/
theorem exists_empiricalAnnouncedCost_le_curve_mul_offline_add_linear
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {u : ℝ} (hu : 1 < u)
    (hp0 : ∀ job, 0 ≤ p job) (hpu : ∀ job, p job ≤ u) :
    ∃ τ, 1 ≤ τ ∧
      (∑ job, max (τ - p job) 0 = n) ∧
      (if τ ≤ u then empiricalStationaryFiniteCost p τ
       else empiricalRawCost n u) ≤
        randomizedCurve u * empiricalRevealingOfflineCost u p +
          (n : ℝ) * (1 + u) / 2 := by
  obtain ⟨τ, hτ, hthreshold, hleading⟩ :=
    exists_empiricalAnnouncedLeadingCost_le_curve_mul_offline
      hn p hu hp0 hpu
  refine ⟨τ, hτ, hthreshold, ?_⟩
  by_cases hτu : τ ≤ u
  · rw [if_pos hτu]
    rw [empiricalStationaryFiniteCost_eq_survival
      hn p hp0 hτ hτu hpu hthreshold]
    rw [if_pos hτu] at hleading
    have he : thresholdEarlyCount p τ ≤ n := by
      unfold thresholdEarlyCount
      calc
        (∑ job, if p job < τ then (1 : ℝ) else 0) ≤
            ∑ _job : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro job _hjob
          split <;> norm_num
        _ = n := by simp
    have hpSum : (∑ job, p job) ≤ n * u := by
      calc
        (∑ job, p job) ≤ ∑ _job : Fin n, u :=
          Finset.sum_le_sum fun job _hjob ↦ hpu job
        _ = n * u := by simp
    have hdiag :
        (thresholdEarlyCount p τ + ∑ job, p job) / 2 ≤
          (n : ℝ) * (1 + u) / 2 := by
      nlinarith
    linarith
  · rw [if_neg hτu]
    rw [if_neg hτu] at hleading
    unfold empiricalRawCost
    have hrawIdentity :
        u * (n : ℝ) * (n + 1) / 2 =
          (n : ℝ) ^ 2 / 2 * u + (n : ℝ) * u / 2 := by ring
    rw [hrawIdentity]
    have hlinear : (n : ℝ) * u / 2 ≤
        (n : ℝ) * (1 + u) / 2 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    linarith

end

end RevealingOptimization
end SchedulingPaper
