import SchedulingPaper.RevealingOptimizationReduction
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
    if hτu : τ ≤ u then
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

end

end RevealingOptimization
end SchedulingPaper
