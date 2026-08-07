import SchedulingPaper.RandomizedOperationalExpected
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Concrete fourth-root parameters for the sampled `4/3` algorithm
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

def fourthRoot (N : ℕ) : ℝ := Real.sqrt (Real.sqrt N)

def concreteBins (N : ℕ) : ℕ := ⌊fourthRoot N⌋₊

def concreteSampleSize (N : ℕ) : ℕ := ⌊(fourthRoot N) ^ 3⌋₊

def concreteEta (N : ℕ) : ℝ := 32 / concreteBins N

theorem fourthRoot_nonneg (N : ℕ) : 0 ≤ fourthRoot N := by
  unfold fourthRoot
  positivity

theorem fourthRoot_pow_four (N : ℕ) : (fourthRoot N) ^ 4 = N := by
  have houter : (fourthRoot N) ^ 2 = Real.sqrt N := by
    unfold fourthRoot
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hinner : (Real.sqrt (N : ℝ)) ^ 2 = N :=
    Real.sq_sqrt (by positivity)
  calc
    (fourthRoot N) ^ 4 = ((fourthRoot N) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt (N : ℝ)) ^ 2 := by rw [houter]
    _ = N := hinner

theorem concrete_parameter_bounds
    (N : ℕ) (hR : 12 ≤ fourthRoot N) :
    let R := fourthRoot N
    let d := concreteBins N
    let k := concreteSampleSize N
    let η := concreteEta N
    0 < d ∧ 0 < k ∧ k < N ∧
      (d : ℝ) * η = 32 ∧
      0 < η ∧ η ≤ 32 / 12 ∧ η ≤ 64 / R ∧
      (N : ℝ) = R ^ 4 ∧
      (k : ℝ) ≤ R ^ 3 ∧
      Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) ≤ 2 / R := by
  dsimp only
  let R := fourthRoot N
  let d := concreteBins N
  let k := concreteSampleSize N
  let η := concreteEta N
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRnonneg : 0 ≤ R := hR0.le
  have hdCastLe : (d : ℝ) ≤ R := by
    dsimp [d, concreteBins]
    exact Nat.floor_le hRnonneg
  have hRltD : R < (d : ℝ) + 1 := by
    dsimp [d, concreteBins]
    exact Nat.lt_floor_add_one R
  have hdLower : R - 1 ≤ (d : ℝ) := by linarith
  have hdTwelve : 12 ≤ d := by
    dsimp [d, concreteBins]
    exact Nat.le_floor hR
  have hdPos : 0 < d := lt_of_lt_of_le (by omega) hdTwelve
  have hdCastPos : 0 < (d : ℝ) := by exact_mod_cast hdPos
  have hR3nonneg : 0 ≤ R ^ 3 := by positivity
  have hkCastLe : (k : ℝ) ≤ R ^ 3 := by
    dsimp [k, concreteSampleSize]
    exact Nat.floor_le hR3nonneg
  have hR3ltK : R ^ 3 < (k : ℝ) + 1 := by
    dsimp [k, concreteSampleSize]
    exact Nat.lt_floor_add_one (R ^ 3)
  have hkLower : R ^ 3 - 1 ≤ (k : ℝ) := by linarith
  have hkOne : 1 ≤ k := by
    dsimp [k, concreteSampleSize]
    apply Nat.le_floor
    have hpow : (1 : ℝ) ^ 3 ≤ R ^ 3 := by
      gcongr
      norm_num
      exact hR.trans' (by norm_num)
    norm_num at hpow ⊢
    exact hpow
  have hkPos : 0 < k := by omega
  have hRN : (N : ℝ) = R ^ 4 := by
    dsimp [R]
    exact (fourthRoot_pow_four N).symm
  have hR3ltR4 : R ^ 3 < R ^ 4 := by
    have hRone : 1 < R := lt_of_lt_of_le (by norm_num) hR
    nlinarith [mul_pos (pow_pos hR0 3) (sub_pos.mpr hRone)]
  have hkNcast : (k : ℝ) < N := by
    rw [hRN]
    exact lt_of_le_of_lt hkCastLe hR3ltR4
  have hkN : k < N := by exact_mod_cast hkNcast
  have hηDef : η = 32 / (d : ℝ) := rfl
  have hcutoff : (d : ℝ) * η = 32 := by
    rw [hηDef]
    field_simp [hdCastPos.ne']
  have hηPos : 0 < η := by
    rw [hηDef]
    positivity
  have hηTwelve : η ≤ 32 / 12 := by
    rw [hηDef]
    apply (div_le_div_iff₀ hdCastPos (by norm_num : (0 : ℝ) < 12)).2
    have hdTwelveR : (12 : ℝ) ≤ d := by exact_mod_cast hdTwelve
    nlinarith
  have hdHalf : R / 2 ≤ (d : ℝ) := by
    have hRtwo : 2 ≤ R := by
      dsimp [R]
      linarith
    linarith
  have hηR : η ≤ 64 / R := by
    rw [hηDef]
    apply (div_le_div_iff₀ hdCastPos hR0).2
    nlinarith
  have hpoly : R ^ 3 + 2 * R ^ 2 ≤ 4 * (R ^ 3 - 1) := by
    nlinarith [sq_nonneg (R - 12),
      mul_nonneg (sq_nonneg R) (show 0 ≤ 3 * R - 2 by nlinarith)]
  have hleft : ((d : ℝ) + 2) * R ^ 2 ≤ R ^ 3 + 2 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right (add_le_add_right hdCastLe 2)
      (sq_nonneg R)
    nlinarith
  have hright : 4 * (R ^ 3 - 1) ≤ 4 * (k : ℝ) := by nlinarith
  have hratio : ((d : ℝ) + 2) / (k : ℝ) ≤ (2 / R) ^ 2 := by
    have hkCastPos : 0 < (k : ℝ) := by exact_mod_cast hkPos
    have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hR0
    apply (div_le_iff₀ hkCastPos).2
    have hcross : ((d : ℝ) + 2) * R ^ 2 ≤ 4 * (k : ℝ) :=
      hleft.trans (hpoly.trans hright)
    field_simp [hR0.ne'] at hcross ⊢
    nlinarith
  have hsqrt : Real.sqrt ((d + 2 : ℕ) / (k : ℝ)) ≤ 2 / R := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using hratio
  exact ⟨hdPos, hkPos, hkN, hcutoff, hηPos, hηTwelve, hηR,
    hRN, hkCastLe, hsqrt⟩

theorem concreteSampleSize_lt
    (N : ℕ) (hR : 12 ≤ fourthRoot N) : concreteSampleSize N < N := by
  exact (concrete_parameter_bounds N hR).2.2.1

def concreteRest (N : ℕ) : ℕ := N - concreteSampleSize N

theorem concrete_size_eq
    (N : ℕ) (hR : 12 ≤ fourthRoot N) :
    concreteSampleSize N + concreteRest N = N := by
  unfold concreteRest
  exact Nat.add_sub_of_le (concreteSampleSize_lt N hR).le

def concreteProcessing
    (N : ℕ) (hR : 12 ≤ fourthRoot N) (p : Fin N → ℝ) :
    Fin (concreteSampleSize N + concreteRest N) → ℝ :=
  fun i => p (Fin.cast (concrete_size_eq N hR) i)

/-- Fully instantiated large-`N` algorithm.  `concreteProcessing` is only
the canonical cast along `k + (N-k) = N`; it does not reorder jobs. -/
theorem concrete_unknownMultiset_operational_bound
    (N : ℕ) (hR : 12 ≤ fourthRoot N)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    let k := concreteSampleSize N
    let rest := concreteRest N
    let d := concreteBins N
    let η := concreteEta N
    let hη : 0 < η := (concrete_parameter_bounds N hR).2.2.2.2.1
    let p' := concreteProcessing N hR p
    uniformAverage
        (physicalSampledRunCost (k + rest) k d η hη p') ≤
      4 / 3 * finiteObligatoryOPT p' +
        20378 * (fourthRoot N) ^ 7 := by
  dsimp only
  let k := concreteSampleSize N
  let rest := concreteRest N
  let d := concreteBins N
  let η := concreteEta N
  let R := fourthRoot N
  let p' := concreteProcessing N hR p
  obtain ⟨hdPos, hkPos, hkN, hcutoff, hηPos, hηTwelve,
      hηR, hRN, hkUpper, herror⟩ := concrete_parameter_bounds N hR
  have hrestPos : 0 < rest := by
    dsimp [rest, concreteRest, k]
    exact Nat.sub_pos_iff_lt.mpr hkN
  have hcard : 1 < k + rest := by
    rw [show k + rest = N by
      simpa [k, rest] using concrete_size_eq N hR]
    have hkOne : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkPos.ne'
    omega
  have hsize : (k + rest : ℝ) ≤ R ^ 4 := by
    have hsum : k + rest = N := by
      simpa [k, rest] using concrete_size_eq N hR
    rw [show (k + rest : ℝ) = (N : ℝ) by exact_mod_cast hsum]
    simpa [R] using hRN.le
  apply uniformAverage_physicalSampledRunCost_le_20378
    k rest d hkPos hrestPos hcard η R hηPos
  · simpa [d, η] using hcutoff
  · simpa [η] using hηTwelve
  · simpa [R] using hR
  · exact hsize
  · simpa [k, R] using hkUpper
  · simpa [d, k, R] using herror
  · simpa [η, R] using hηR
  · intro i
    exact hp (Fin.cast (concrete_size_eq N hR) i)

/-- Multiplicative version of the fully instantiated upper bound. -/
theorem concrete_unknownMultiset_operational_multiplicative
    (N : ℕ) (hR : 12 ≤ fourthRoot N)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) :
    let k := concreteSampleSize N
    let rest := concreteRest N
    let d := concreteBins N
    let η := concreteEta N
    let hη : 0 < η := (concrete_parameter_bounds N hR).2.2.2.2.1
    let p' := concreteProcessing N hR p
    uniformAverage
        (physicalSampledRunCost (k + rest) k d η hη p') ≤
      (4 / 3 + 40756 / fourthRoot N) * finiteObligatoryOPT p' := by
  dsimp only
  let k := concreteSampleSize N
  let rest := concreteRest N
  let d := concreteBins N
  let η := concreteEta N
  let R := fourthRoot N
  let p' := concreteProcessing N hR p
  have hadd := concrete_unknownMultiset_operational_bound N hR p hp
  dsimp only at hadd
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hsum : k + rest = N := by
    simpa [k, rest] using concrete_size_eq N hR
  have hp' : ∀ i, 0 ≤ p' i := by
    intro i
    exact hp (Fin.cast (concrete_size_eq N hR) i)
  have hoptBase := finiteObligatoryOPT_lower p' hp'
  have hNpow : (N : ℝ) = R ^ 4 := by
    simpa [R] using (concrete_parameter_bounds N hR).2.2.2.2.2.2.2.1
  have hopt : R ^ 8 / 2 ≤ finiteObligatoryOPT p' := by
    have hcast : (k + rest : ℝ) = (N : ℝ) := by exact_mod_cast hsum
    have hnonneg : 0 ≤ (k + rest : ℝ) := by positivity
    calc
      R ^ 8 / 2 = (N : ℝ) ^ 2 / 2 := by rw [hNpow]; ring
      _ ≤ (k + rest : ℝ) * ((k + rest : ℝ) + 1) / 2 := by
        rw [hcast]
        nlinarith
      _ ≤ finiteObligatoryOPT p' := by
        simpa only [Nat.cast_add] using hoptBase
  have hmult := additive_20378_to_multiplicative
    (n := R ^ 4) (alg := uniformAverage
    (physicalSampledRunCost (k + rest) k d η
        ((concrete_parameter_bounds N hR).2.2.2.2.1) p'))
    (opt := finiteObligatoryOPT p') (nQuarter := R)
    (by positivity) hR0 rfl
    (by simpa only [show (R ^ 4) ^ 2 = R ^ 8 by ring] using hopt)
    (by simpa [k, rest, d, η, R, p'] using hadd)
  simpa [k, rest, d, η, R, p'] using hmult

end

end RandomizedObligatory
end SchedulingPaper
