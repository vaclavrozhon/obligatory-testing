import SchedulingPaper.RandomizedOptionalUnknownInstanceOptimal
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# A literal vanishing parameter family for the unknown-multiset theorem

For an accuracy parameter `m`, and every `n >= m^16`, use `m` grid cells,
`n/m^2` blind pilot jobs and unregulated suffix jobs, checkpoint spacing
`n/m^4`, martingale allowance `n/m^2`, and suffix allowance `1/m^2`.
All seven scalar errors of the finite theorem are `O_L(1/m)`.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedOnline
open ObservedEnvelope
open ObservedTrace
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

def inverseSquareSize (n m : ℕ) : ℕ := n / m ^ 2

def inverseFourthStep (n m : ℕ) : ℕ := n / m ^ 4

def inverseSquareCutoff (n m : ℕ)
    (hsize : 0 < inverseSquareSize n m) : Fin n :=
  ⟨n - inverseSquareSize n m,
    Nat.sub_lt (by
      exact lt_of_lt_of_le hsize (Nat.div_le_self n (m ^ 2))) hsize⟩

def inverseSquarePilotPositions (n m : ℕ)
    (hsmall : inverseSquareSize n m < n) : Finset (Fin n) :=
  Finset.Iio ⟨inverseSquareSize n m, hsmall⟩

/-- The concrete, input-size-only accuracy scale.  Four nested square roots
give the sixteenth root, matching the slack in `n >= m^16`. -/
def sixteenthRoot (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt n)))

def concreteUnknownParameter (n : ℕ) : ℕ := ⌊sixteenthRoot n⌋₊

theorem sixteenthRoot_nonneg (n : ℕ) : 0 ≤ sixteenthRoot n := by
  unfold sixteenthRoot
  positivity

theorem sixteenthRoot_pow_sixteen (n : ℕ) :
    (sixteenthRoot n) ^ 16 = n := by
  let a : ℝ := Real.sqrt n
  let b : ℝ := Real.sqrt a
  let c : ℝ := Real.sqrt b
  let d : ℝ := Real.sqrt c
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = c := Real.sq_sqrt hc0
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb0
  have hb2 : b ^ 2 = a := Real.sq_sqrt ha0
  have ha2 : a ^ 2 = n := Real.sq_sqrt (by positivity)
  change d ^ 16 = n
  calc
    d ^ 16 = (d ^ 2) ^ 8 := by ring
    _ = c ^ 8 := by rw [hd2]
    _ = (c ^ 2) ^ 4 := by ring
    _ = b ^ 4 := by rw [hc2]
    _ = (b ^ 2) ^ 2 := by ring
    _ = a ^ 2 := by rw [hb2]
    _ = n := ha2

theorem concreteUnknownParameter_bounds
    (n : ℕ) (hroot : 2 ≤ sixteenthRoot n) :
    2 ≤ concreteUnknownParameter n ∧
      (concreteUnknownParameter n) ^ 16 ≤ n := by
  have hm : 2 ≤ concreteUnknownParameter n := by
    unfold concreteUnknownParameter
    exact Nat.le_floor hroot
  have hfloor : (concreteUnknownParameter n : ℝ) ≤ sixteenthRoot n := by
    unfold concreteUnknownParameter
    exact Nat.floor_le (sixteenthRoot_nonneg n)
  have hpow : (concreteUnknownParameter n : ℝ) ^ 16 ≤
      (sixteenthRoot n) ^ 16 := by
    gcongr
  rw [sixteenthRoot_pow_sixteen] at hpow
  exact ⟨hm, by exact_mod_cast hpow⟩

theorem concreteUnknownParameter_tendsto_atTop :
    Filter.Tendsto concreteUnknownParameter Filter.atTop Filter.atTop := by
  unfold concreteUnknownParameter sixteenthRoot
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp
        (Real.tendsto_sqrt_atTop.comp
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))))

def concreteUnknownError (L : ℝ) (n : ℕ) : ℝ :=
  7830 * (L + 1) ^ 2 / concreteUnknownParameter n

theorem concreteUnknownError_tendsto_zero (L : ℝ) :
    Filter.Tendsto (concreteUnknownError L) Filter.atTop (nhds 0) := by
  unfold concreteUnknownError
  exact Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp
      concreteUnknownParameter_tendsto_atTop) (7830 * (L + 1) ^ 2)

theorem processing_eq_zero_of_populationMean_eq_zero
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hmean : populationMean p = 0) :
    ∀ job, p job = 0 := by
  have hcard : (Fintype.card (Fin n) : ℝ) ≠ 0 := by simp [hn.ne']
  have hsum : ∑ job, p job = 0 := by
    unfold populationMean at hmean
    exact (div_eq_zero_iff.mp hmean).resolve_right hcard
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg hp0).mp hsum
  intro job
  have hj := congrFun hall job
  simpa using hj

theorem populationHistogram_roundedGridCell_eq_zeroAtom
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hp : ∀ job, p job = 0) :
    populationHistogram (roundedGridCell G) =
      fun cell => if cell = none then 1 else 0 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  funext cell
  cases cell with
  | none =>
      simp [populationHistogram, categoryClass,
        (roundedGridCell_eq_none_iff G _).2 (hp _), hn.ne']
  | some i =>
      have hcell : ∀ job, roundedGridCell G job = none := fun job =>
        (roundedGridCell_eq_none_iff G job).2 (hp job)
      simp [populationHistogram, categoryClass, hcell]

theorem zeroQuota_positiveGridTemplateValue_eq_zero
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} (G : RoundedPositiveGrid ι p)
    (hp : ∀ job, p job = 0) :
    positiveGridTemplateValue
        (populationHistogram (roundedGridCell G)) G.price
        (zeroQuotaGridTemplate (β := ι) n) = 0 := by
  rw [populationHistogram_roundedGridCell_eq_zeroAtom hn G hp]
  simp [positiveGridTemplateValue, canonicalFluidCost, testLowArea,
    mediumArea, blindArea, highArea, templateMoments, finiteExpectation,
    finiteProductExpectation, positiveGridPrice]

@[simp] theorem inverseSquarePilotPositions_card
    (n m : ℕ) (hsmall : inverseSquareSize n m < n) :
    (inverseSquarePilotPositions n m hsmall).card = inverseSquareSize n m := by
  simp [inverseSquarePilotPositions]

theorem inverseSquarePilotPositions_nonempty
    (n m : ℕ) (hsmall : inverseSquareSize n m < n)
    (hpos : 0 < inverseSquareSize n m) :
    (inverseSquarePilotPositions n m hsmall).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hcard := congrArg Finset.card hempty
  simp [inverseSquarePilotPositions, hpos.ne'] at hcard

@[simp] theorem inverseSquareCutoff_suffix_card
    (n m : ℕ) (hsize : 0 < inverseSquareSize n m) :
    (suffixPositions (inverseSquareCutoff n m hsize)).card =
      inverseSquareSize n m := by
  rw [suffixPositions_card]
  dsimp [inverseSquareCutoff]
  have hle : inverseSquareSize n m ≤ n := Nat.div_le_self _ _
  omega

theorem parameter_scales
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n) :
    let k := inverseSquareSize n m
    let d := inverseFourthStep n m
    0 < k ∧ k < n ∧ 0 < d ∧
      (n : ℝ) ≤ 2 * k * (m : ℝ) ^ 2 ∧
      (k : ℝ) * (m : ℝ) ^ 2 ≤ n ∧
      (n : ℝ) ≤ 2 * d * (m : ℝ) ^ 4 ∧
      (d : ℝ) * (m : ℝ) ^ 4 ≤ n := by
  dsimp [inverseSquareSize, inverseFourthStep]
  have hm0 : 0 < m := by omega
  have hm2 : 0 < m ^ 2 := pow_pos hm0 _
  have hm4 : 0 < m ^ 4 := pow_pos hm0 _
  have hm2le : m ^ 2 ≤ n := by
    have hp : m ^ 2 ≤ m ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    exact hp.trans hn
  have hm4le : m ^ 4 ≤ n := by
    have hp : m ^ 4 ≤ m ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
    exact hp.trans hn
  have hkpos : 0 < n / m ^ 2 := Nat.div_pos hm2le hm2
  have hdpos : 0 < n / m ^ 4 := Nat.div_pos hm4le hm4
  have hklt : n / m ^ 2 < n := by
    apply Nat.div_lt_self (lt_of_lt_of_le (pow_pos hm0 16) hn)
    nlinarith
  have hkUpperNat := Nat.div_mul_le_self n (m ^ 2)
  have hdUpperNat := Nat.div_mul_le_self n (m ^ 4)
  have hkRemainder := Nat.lt_div_mul_add (a := n) hm2
  have hdRemainder := Nat.lt_div_mul_add (a := n) hm4
  have hkLowerNat : n ≤ 2 * (n / m ^ 2) * m ^ 2 := by
    have hdenom : m ^ 2 ≤ (n / m ^ 2) * m ^ 2 := by
      nlinarith
    nlinarith
  have hdLowerNat : n ≤ 2 * (n / m ^ 4) * m ^ 4 := by
    have hdenom : m ^ 4 ≤ (n / m ^ 4) * m ^ 4 := by
      nlinarith
    nlinarith
  refine ⟨hkpos, hklt, hdpos, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hkLowerNat
  · exact_mod_cast hkUpperNat
  · exact_mod_cast hdLowerNat
  · exact_mod_cast hdUpperNat

theorem checkpoint_card_le_three_m4
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n) (cutoff : Fin n) :
    (backwardCheckpoints (inverseFourthStep n m) cutoff).card ≤
      3 * m ^ 4 := by
  obtain ⟨_hkpos, _hklt, hdpos, _hkLower, _hkUpper,
      hdLower, _hdUpper⟩ := parameter_scales hm hn
  have hbase := backwardCheckpoints_card_le (inverseFourthStep n m) cutoff
  have hnNat : n ≤ 2 * inverseFourthStep n m * m ^ 4 := by
    exact_mod_cast hdLower
  have hdiv : n / inverseFourthStep n m ≤ 2 * m ^ 4 := by
    apply Nat.div_le_of_le_mul
    nlinarith
  have hcut : cutoff.val / inverseFourthStep n m ≤
      n / inverseFourthStep n m :=
    Nat.div_le_div_right cutoff.isLt.le
  have hm4pos : 0 < m ^ 4 := pow_pos (by omega) _
  omega

set_option maxHeartbeats 1000000 in
theorem inverse_parameter_error_bounds
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) :
    let k := inverseSquareSize n m
    let d := inverseFourthStep n m
    let cutoff := inverseSquareCutoff n m (parameter_scales hm hn).1
    let δ := 30 * (L + 1) / m
    (L + L / m) *
          (((n : ℝ) / (m : ℝ) ^ 2 + d +
            (1 / (m : ℝ) ^ 2 +
              2 * d / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) + L / m ≤ δ ∧
    (m + 1) *
        (((n : ℝ) / (m : ℝ) ^ 2 + d +
          (1 / (m : ℝ) ^ 2 +
            2 * d / (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card) / n) ≤ δ ∧
    (m + 2) *
        ((backwardCheckpoints d cutoff).card *
            (n / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
          (backwardCheckpoints d cutoff).card *
            ((2 / (suffixPositions cutoff).card) /
              (1 / (m : ℝ) ^ 2) ^ 2)) ≤ δ ∧
    Real.sqrt ((m + 1 : ℝ) / k) ≤ δ ∧
    1 / (n : ℝ) ≤ δ ∧ L / (m : ℝ) ≤ δ ∧
    k * L / (n : ℝ) ≤ δ := by
  dsimp
  obtain ⟨hkpos, hklt, hdpos, hkLower, hkUpper, hdLower, hdUpper⟩ :=
    parameter_scales hm hn
  let k := inverseSquareSize n m
  let d := inverseFourthStep n m
  let cutoff := inverseSquareCutoff n m hkpos
  let δ : ℝ := 30 * (L + 1) / m
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by omega) 16) hn)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsuffix : (suffixPositions cutoff).card = k := by
    exact inverseSquareCutoff_suffix_card n m hkpos
  have hcheckpoint := checkpoint_card_le_three_m4 hm hn cutoff
  have hcheckpointR :
      ((backwardCheckpoints d cutoff).card : ℝ) ≤ 3 * (m : ℝ) ^ 4 := by
    exact_mod_cast hcheckpoint
  have hnPower : (m : ℝ) ^ 16 ≤ n := by exact_mod_cast hn
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hkOverN : (k : ℝ) / n ≤ 1 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hnR (sq_pos_of_pos hmR)]
    nlinarith [hkUpper]
  have hdOverN : (d : ℝ) / n ≤ 1 / (m : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hnR (pow_pos hmR 4)]
    nlinarith [hdUpper]
  have hdOverK : (d : ℝ) / k ≤ 2 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hkR (sq_pos_of_pos hmR)]
    nlinarith [hkLower, hdUpper]
  let γ : ℝ := ((n : ℝ) / (m : ℝ) ^ 2 + d +
      (1 / (m : ℝ) ^ 2 + 2 * d / k) * n + k) / n
  have hgamma : γ ≤ 8 / (m : ℝ) ^ 2 := by
    dsimp [γ]
    rw [add_div, add_div, add_div]
    have hfirst : ((n : ℝ) / (m : ℝ) ^ 2) / n =
        1 / (m : ℝ) ^ 2 := by field_simp [hnR.ne', hmR.ne']
    have hthird :
        (1 / (m : ℝ) ^ 2 + 2 * (d : ℝ) / k) * n / n =
          1 / (m : ℝ) ^ 2 + 2 * (d : ℝ) / k := by
      field_simp [hnR.ne']
    rw [hfirst, hthird]
    have hm4 : 1 / (m : ℝ) ^ 4 ≤ 1 / (m : ℝ) ^ 2 := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hmR) (by
        nlinarith [sq_nonneg ((m : ℝ) - 1)])
    have htwod : 2 * (d : ℝ) / k ≤ 4 / (m : ℝ) ^ 2 := by
      calc
        2 * (d : ℝ) / k = 2 * ((d : ℝ) / k) := by ring
        _ ≤ 2 * (2 / (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hdOverK (by norm_num)
        _ = 4 / (m : ℝ) ^ 2 := by ring
    calc
      1 / (m : ℝ) ^ 2 + (d : ℝ) / n +
            (1 / (m : ℝ) ^ 2 + 2 * (d : ℝ) / k) +
            (k : ℝ) / n ≤
          1 / (m : ℝ) ^ 2 + 1 / (m : ℝ) ^ 4 +
            (1 / (m : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2) +
            1 / (m : ℝ) ^ 2 := by
        gcongr
      _ ≤ 1 / (m : ℝ) ^ 2 + 1 / (m : ℝ) ^ 2 +
            (1 / (m : ℝ) ^ 2 + 4 / (m : ℝ) ^ 2) +
            1 / (m : ℝ) ^ 2 := by
        exact add_le_add
          (add_le_add
            (add_le_add (le_refl _) hm4)
            (add_le_add (le_refl _) (le_refl _)))
          (le_refl _)
      _ = 8 / (m : ℝ) ^ 2 := by ring
  have hrounded : L + L / (m : ℝ) ≤ 2 * L := by
    have hdiv : L / (m : ℝ) ≤ L := by
      rw [div_le_iff₀ hmR]
      nlinarith
    linarith
  have hdelta0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hdiscovery : (L + L / (m : ℝ)) * γ + L / m ≤ δ := by
    have hmul := mul_le_mul hrounded hgamma (by positivity)
      (by positivity)
    dsimp [δ]
    have hmInv : 1 / (m : ℝ) ^ 2 ≤ 1 / m := by
      exact one_div_le_one_div_of_le hmR (by nlinarith)
    have hLm : L / (m : ℝ) ≤ L := by
      rw [div_le_iff₀ hmR]
      nlinarith
    calc
      (L + L / (m : ℝ)) * γ + L / m ≤
          16 * L / (m : ℝ) ^ 2 + L / m := by
        have hrewrite :
            (2 * L) * (8 / (m : ℝ) ^ 2) =
              16 * L / (m : ℝ) ^ 2 := by ring
        rw [← hrewrite]
        exact add_le_add hmul (le_refl _)
      _ ≤ 17 * L / m := by
        have hmulInv :=
          mul_le_mul_of_nonneg_left hmInv (by positivity : 0 ≤ 16 * L)
        have hsixteen : 16 * L / (m : ℝ) ^ 2 ≤ 16 * L / m := by
          calc
            16 * L / (m : ℝ) ^ 2 =
                (16 * L) * (1 / (m : ℝ) ^ 2) := by ring
            _ ≤ (16 * L) * (1 / m) := hmulInv
            _ = 16 * L / m := by ring
        calc
          16 * L / (m : ℝ) ^ 2 + L / m ≤
              16 * L / m + L / m := add_le_add hsixteen (le_refl _)
          _ = 17 * L / m := by ring
      _ ≤ δ := by
        dsimp [δ]
        rw [div_le_div_iff₀ hmR hmR]
        nlinarith
  have hcounts : ((m : ℝ) + 1) * γ ≤ δ := by
    have hmplus : (m : ℝ) + 1 ≤ 2 * m := by nlinarith
    have hmul := mul_le_mul hmplus hgamma (by positivity) (by positivity)
    calc
      ((m : ℝ) + 1) * γ ≤
          2 * (m : ℝ) * (8 / (m : ℝ) ^ 2) := hmul
      _ = 16 / m := by field_simp [hmR.ne']; ring
      _ ≤ δ := by
        dsimp [δ]
        rw [div_le_div_iff₀ hmR hmR]
        nlinarith
  have hbadBase :
      ((backwardCheckpoints d cutoff).card : ℝ) *
            ((n : ℝ) / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
          (backwardCheckpoints d cutoff).card *
            ((2 / (k : ℝ)) / (1 / (m : ℝ) ^ 2) ^ 2) ≤
        15 / (m : ℝ) ^ 6 := by
    have hfirstFactor :
        (n : ℝ) / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2 =
          (m : ℝ) ^ 4 / n := by field_simp [hnR.ne', hmR.ne']
    have hsecondFactor :
        (2 / (k : ℝ)) / (1 / (m : ℝ) ^ 2) ^ 2 =
          2 * (m : ℝ) ^ 4 / k := by field_simp [hkR.ne', hmR.ne']
    rw [hfirstFactor, hsecondFactor]
    have hfirst : 3 * (m : ℝ) ^ 4 * ((m : ℝ) ^ 4 / n) ≤
        3 / (m : ℝ) ^ 8 := by
      field_simp [hnR.ne', hmR.ne']
      nlinarith
    have hsecond : 3 * (m : ℝ) ^ 4 *
          (2 * (m : ℝ) ^ 4 / k) ≤ 12 / (m : ℝ) ^ 6 := by
      field_simp [hkR.ne', hmR.ne']
      nlinarith [hkLower, hnPower]
    have hfirstMul := mul_le_mul_of_nonneg_right hcheckpointR
      (by positivity : 0 ≤ (m : ℝ) ^ 4 / n)
    have hsecondMul := mul_le_mul_of_nonneg_right hcheckpointR
      (by positivity : 0 ≤ 2 * (m : ℝ) ^ 4 / k)
    have hmSq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hmPow : (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 8 := by
      calc
        (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 * (m : ℝ) ^ 2 := by
          simpa using (mul_le_mul_of_nonneg_left hmSq
            (by positivity : 0 ≤ (m : ℝ) ^ 6))
        _ = (m : ℝ) ^ 8 := by ring
    have hpowInv : 1 / (m : ℝ) ^ 8 ≤ 1 / (m : ℝ) ^ 6 :=
      one_div_le_one_div_of_le (pow_pos hmR 6) hmPow
    have hpow : 3 / (m : ℝ) ^ 8 ≤ 3 / (m : ℝ) ^ 6 := by
      calc
        3 / (m : ℝ) ^ 8 = 3 * (1 / (m : ℝ) ^ 8) := by ring
        _ ≤ 3 * (1 / (m : ℝ) ^ 6) :=
          mul_le_mul_of_nonneg_left hpowInv (by norm_num)
        _ = 3 / (m : ℝ) ^ 6 := by ring
    calc
      ((backwardCheckpoints d cutoff).card : ℝ) *
              ((m : ℝ) ^ 4 / n) +
            (backwardCheckpoints d cutoff).card *
              (2 * (m : ℝ) ^ 4 / k) ≤
          3 / (m : ℝ) ^ 8 + 12 / (m : ℝ) ^ 6 :=
        add_le_add (hfirstMul.trans hfirst) (hsecondMul.trans hsecond)
      _ ≤ 3 / (m : ℝ) ^ 6 + 12 / (m : ℝ) ^ 6 :=
        add_le_add hpow (le_refl _)
      _ = 15 / (m : ℝ) ^ 6 := by ring
  have hbad : ((m : ℝ) + 2) *
      (((backwardCheckpoints d cutoff).card : ℝ) *
            ((n : ℝ) / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
        (backwardCheckpoints d cutoff).card *
          ((2 / (k : ℝ)) / (1 / (m : ℝ) ^ 2) ^ 2)) ≤ δ := by
    have hmTwo : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hmplus : (m : ℝ) + 2 ≤ 2 * m := by linarith
    have hmul := mul_le_mul hmplus hbadBase (by positivity) (by positivity)
    have hmPow5Nat : m ≤ m ^ 5 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < m) (by omega : 1 ≤ 5)
    have hmPow5 : (m : ℝ) ≤ (m : ℝ) ^ 5 := by
      exact_mod_cast hmPow5Nat
    have hpow : 1 / (m : ℝ) ^ 5 ≤ 1 / m := by
      exact one_div_le_one_div_of_le hmR hmPow5
    have hthirty : 30 / (m : ℝ) ^ 5 ≤ 30 / m := by
      have hmul30 := mul_le_mul_of_nonneg_left hpow
        (by norm_num : (0 : ℝ) ≤ 30)
      simpa [div_eq_mul_inv] using hmul30
    calc
      ((m : ℝ) + 2) *
          (((backwardCheckpoints d cutoff).card : ℝ) *
                ((n : ℝ) / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
            (backwardCheckpoints d cutoff).card *
              ((2 / (k : ℝ)) / (1 / (m : ℝ) ^ 2) ^ 2)) ≤
          2 * (m : ℝ) * (15 / (m : ℝ) ^ 6) := hmul
      _ = 30 / (m : ℝ) ^ 5 := by field_simp [hmR.ne']; ring
      _ ≤ 30 / m := hthirty
      _ ≤ δ := by
        dsimp [δ]
        exact div_le_div_of_nonneg_right (by nlinarith) hmR.le
  have hlearningRatio : ((m : ℝ) + 1) / k ≤ 4 / (m : ℝ) ^ 2 := by
    have hkStrongNat : m ^ 14 ≤ k := by
      dsimp [k, inverseSquareSize]
      apply (Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < m) 2)).2
      calc
        m ^ 14 * m ^ 2 = m ^ 16 := by ring
        _ ≤ n := hn
    have hkStrong : (m : ℝ) ^ 14 ≤ k := by exact_mod_cast hkStrongNat
    have hm3Nat : m ^ 3 ≤ m ^ 14 :=
      Nat.pow_le_pow_right (by omega : 0 < m) (by omega)
    have hm3 : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 14 := by
      exact_mod_cast hm3Nat
    have hmplus : (m : ℝ) + 1 ≤ 2 * m := by nlinarith
    rw [div_le_div_iff₀ hkR (sq_pos_of_pos hmR)]
    nlinarith [mul_le_mul_of_nonneg_right hmplus
      (sq_nonneg (m : ℝ))]
  have hlearning : Real.sqrt (((m : ℝ) + 1) / k) ≤ δ := by
    have hratio0 : 0 ≤ ((m : ℝ) + 1) / k := by positivity
    have hsqrt : Real.sqrt (((m : ℝ) + 1) / k) ≤ 2 / m := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hsquare : (2 / (m : ℝ)) ^ 2 = 4 / (m : ℝ) ^ 2 := by ring
        rw [hsquare]
        exact hlearningRatio
    dsimp [δ]
    exact hsqrt.trans (div_le_div_of_nonneg_right (by nlinarith) hmR.le)
  have hinverse : 1 / (n : ℝ) ≤ δ := by
    have hnm : (m : ℝ) ≤ n := by
      have hmPow16 : m ≤ m ^ 16 := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < m) (by omega : 1 ≤ 16)
      exact_mod_cast hmPow16.trans hn
    have hfrac : 1 / (n : ℝ) ≤ 1 / m := by
      exact one_div_le_one_div_of_le hmR hnm
    dsimp [δ]
    exact hfrac.trans (div_le_div_of_nonneg_right (by nlinarith) hmR.le)
  have hmesh : L / (m : ℝ) ≤ δ := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (by nlinarith) hmR.le
  have hpilot : (k : ℝ) * L / n ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_right hkOverN hL.le
    dsimp [δ]
    have hmInv : 1 / (m : ℝ) ^ 2 ≤ 1 / m := by
      exact one_div_le_one_div_of_le hmR (by nlinarith)
    have hpilotBase : (k : ℝ) * L / n ≤ L / (m : ℝ) ^ 2 := by
      calc
        (k : ℝ) * L / n = ((k : ℝ) / n) * L := by ring
        _ ≤ (1 / (m : ℝ) ^ 2) * L := hmul
        _ = L / (m : ℝ) ^ 2 := by ring
    have hpilotMesh : L / (m : ℝ) ^ 2 ≤ L / m := by
      calc
        L / (m : ℝ) ^ 2 = L * (1 / (m : ℝ) ^ 2) := by ring
        _ ≤ L * (1 / m) := mul_le_mul_of_nonneg_left hmInv hL.le
        _ = L / m := by ring
    exact (hpilotBase.trans hpilotMesh).trans
      (div_le_div_of_nonneg_right (by nlinarith) hmR.le)
  rw [hsuffix]
  exact ⟨hdiscovery, hcounts, hbad, hlearning, hinverse, hmesh, hpilot⟩

/-- The same learned blind-pilot algorithm on the degenerate zero-mean
population.  Nonnegativity forces every processing time to be zero, and the
pure-YOLO template has fluid value zero. -/
theorem boundedUniform_blindPilot_zero_parameter_rate
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : populationMean p = 0)
    (policy : ObservedTrace.CompletePolicy p) :
    let k := inverseSquareSize n m
    let hscales := parameter_scales hm hn
    let pilot := inverseSquarePilotPositions n m hscales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      uniformAverage (normalizedCost p policy) +
        7830 * (L + 1) ^ 2 / m := by
  dsimp
  obtain ⟨hkpos, hklt, _hdpos, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hm hn
  let k := inverseSquareSize n m
  let pilot := inverseSquarePilotPositions n m hklt
  let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
  let scale : ℝ := max 1 (L + L / m)
  let δ : ℝ := 30 * (L + 1) / m
  have hnPos : 0 < n := lt_of_lt_of_le (pow_pos (by omega) 16) hn
  have hnTwo : 1 < n := lt_of_lt_of_le
    (Nat.one_lt_pow (by omega) (by omega)) hn
  have hpzero := processing_eq_zero_of_populationMean_eq_zero hnPos p hp0 hmean
  have hpilotNonempty : pilot.Nonempty :=
    inverseSquarePilotPositions_nonempty n m hklt hkpos
  have hKR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : 0 < L / (m : ℝ) := div_pos hL hKR
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  have hprice0 : ∀ i, 0 < G.price i := by
    intro i
    exact uniformGridPrice_pos hmesh i
  have hprice : Function.Injective G.price := by
    intro i j hij
    apply Fin.ext
    dsimp [G, boundedUniformRoundedGrid, uniformRoundedGrid,
      uniformGridPrice] at hij
    have hcast : (i.val : ℝ) = j.val := by nlinarith
    exact_mod_cast hcast
  have hscaleOne : 1 ≤ scale := le_max_left _ _
  have hroundedLeScale : L + L / (m : ℝ) ≤ scale := le_max_right _ _
  have hpScale : ∀ job, p job ≤ scale := by
    intro job
    rw [hpzero job]
    exact le_trans (by norm_num) hscaleOne
  have hroundedScale : ∀ job, G.roundedProcessing job ≤ scale := by
    intro job
    rw [G.roundedProcessing_eq_zero_of_eq_zero (hpzero job)]
    exact le_trans (by norm_num) hscaleOne
  have hpriceScale : ∀ i, G.price i ≤ scale := by
    intro i
    have hiNat : i.val + 1 ≤ m := by omega
    have hiReal : (i.val + 1 : ℝ) ≤ m := by exact_mod_cast hiNat
    have hendpoint : G.price i ≤ L := by
      rw [boundedUniformRoundedGrid_price]
      unfold uniformGridPrice
      have hmul := mul_le_mul_of_nonneg_right hiReal hmesh.le
      rw [mul_div_cancel₀ L hKR.ne'] at hmul
      exact hmul
    exact hendpoint.trans (by
      have : L ≤ L + L / (m : ℝ) :=
        le_add_of_nonneg_right (div_nonneg hL.le hKR.le)
      exact this.trans hroundedLeScale)
  have hupper := blindPilotLearnedCost_le_target hnTwo G hprice0 hprice
    pilot hpilotNonempty (zeroQuotaGridTemplate (β := Fin m) n)
    hscaleOne hpScale hroundedScale hpriceScale hpL
  rw [zeroQuota_positiveGridTemplateValue_eq_zero hnPos G hpzero,
    zero_add] at hupper
  obtain ⟨_hDiscovery, _hCounts, _hBad, hLearning, hInverse, hMesh, hPilot⟩ :=
    inverse_parameter_error_bounds hm hn hL
  have hlearning' :
      Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤ δ := by
    simpa [pilot, inverseSquarePilotPositions_card] using hLearning
  have hpilot' : pilot.card * L / (n : ℝ) ≤ δ := by
    simpa [pilot, inverseSquarePilotPositions_card] using hPilot
  have hscale : scale ≤ 2 * (L + 1) := by
    apply max_le
    · linarith
    · have hdiv : L / (m : ℝ) ≤ L := by
        rw [div_le_iff₀ hKR]
        have hmOne : (1 : ℝ) ≤ m := by
          exact_mod_cast (by omega : 1 ≤ m)
        nlinarith [mul_le_mul_of_nonneg_left hmOne hL.le]
      linarith
  have hlearnTerm :
      24 * (scale + 1) * Real.sqrt ((m + 1 : ℝ) / pilot.card) ≤
        24 * (scale + 1) * δ :=
    mul_le_mul_of_nonneg_left hlearning' (by positivity)
  have hinverseTerm : (5 + 18 * scale) / (n : ℝ) ≤
      (5 + 18 * scale) * δ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hInverse)
      (by linarith)
  have hmeshTerm : 12 * (scale + 1) * (L / (m : ℝ)) ≤
      12 * (scale + 1) * δ :=
    mul_le_mul_of_nonneg_left hMesh (by positivity)
  have hpilotTerm : 2 * pilot.card * L / (n : ℝ) ≤ 2 * δ := by
    calc
      2 * pilot.card * L / (n : ℝ) =
          2 * (pilot.card * L / n) := by ring
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hpilot' (by norm_num)
  have herror :
      24 * (scale + 1) * δ + (5 + 18 * scale) * δ +
          12 * (scale + 1) * δ + 2 * δ ≤
        7830 * (L + 1) ^ 2 / m := by
    dsimp [δ]
    have hLone : 0 ≤ L + 1 := by linarith
    have hscaleMul := mul_le_mul_of_nonneg_right hscale hLone
    have hnumerator :
        (1620 * scale + 1290) * (L + 1) ≤
          7830 * (L + 1) ^ 2 := by
      nlinarith
    calc
      24 * (scale + 1) * (30 * (L + 1) / m) +
            (5 + 18 * scale) * (30 * (L + 1) / m) +
            12 * (scale + 1) * (30 * (L + 1) / m) +
            2 * (30 * (L + 1) / m) =
          ((1620 * scale + 1290) * (L + 1)) / m := by ring
      _ ≤ (7830 * (L + 1) ^ 2) / m :=
        div_le_div_of_nonneg_right hnumerator hKR.le
  have hpolicyPoint : ∀ σ, 0 ≤ normalizedCost p policy σ := by
    intro σ
    unfold normalizedCost
    apply div_nonneg
    · apply completionCost_nonneg_of_revealsMatch
        (fun job => hp0 (σ job))
      dsimp [settledRun]
      exact (run_historyInvariant (placedProcessing p σ) policy.strategy
        (2 * n + 1)).revealsMatch
    · positivity
  have hpolicy : 0 ≤ uniformAverage (normalizedCost p policy) :=
    uniformAverage_nonneg hpolicyPoint
  have hupper' :
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
          (n : ℝ) ^ 2 ≤
        24 * (scale + 1) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
          (5 + 18 * scale) / (n : ℝ) +
          12 * (scale + 1) * (L / (m : ℝ)) +
          2 * pilot.card * L / (n : ℝ) := by
    simpa [G, scale, boundedUniformRoundedGrid_mesh] using hupper
  calc
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
          (n : ℝ) ^ 2 ≤
        24 * (scale + 1) * Real.sqrt ((m + 1 : ℝ) / pilot.card) +
          (5 + 18 * scale) / (n : ℝ) +
          12 * (scale + 1) * (L / (m : ℝ)) +
          2 * pilot.card * L / (n : ℝ) := hupper'
    _ ≤ 24 * (scale + 1) * δ + (5 + 18 * scale) * δ +
          12 * (scale + 1) * δ + 2 * δ :=
      add_le_add (add_le_add (add_le_add hlearnTerm hinverseTerm)
        hmeshTerm) hpilotTerm
    _ ≤ 7830 * (L + 1) ^ 2 / m := herror
    _ ≤ uniformAverage (normalizedCost p policy) +
          7830 * (L + 1) ^ 2 / m := le_add_of_nonneg_left hpolicy

/-- Fully instantiated finite theorem, valid for every `n >= m^16`.
Letting `m` tend to infinity gives the unknown-multiset `o(n^2)` result for
all sufficiently large `n`, not merely a perfect-power subsequence. -/
theorem boundedUniform_blindPilot_inverse_parameter_rate
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : ObservedTrace.CompletePolicy p) :
    let k := inverseSquareSize n m
    let hscales := parameter_scales hm hn
    let pilot := inverseSquarePilotPositions n m hscales.2.1
    let cutoff := inverseSquareCutoff n m hscales.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      uniformAverage (normalizedCost p policy) +
        7830 * (L + 1) ^ 2 / m := by
  dsimp
  obtain ⟨hkpos, hklt, hdpos, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hm hn
  let k := inverseSquareSize n m
  let d := inverseFourthStep n m
  let pilot := inverseSquarePilotPositions n m hklt
  let cutoff := inverseSquareCutoff n m hkpos
  let δ : ℝ := 30 * (L + 1) / m
  let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
  obtain ⟨hDiscovery, hCounts, hBad, hLearning, hInverse, hMesh, hPilot⟩ :=
    inverse_parameter_error_bounds hm hn hL
  have hpilotNonempty : pilot.Nonempty :=
    inverseSquarePilotPositions_nonempty n m hklt hkpos
  have hrate :=
    boundedUniform_blindPilot_le_every_policy_of_error_bounds
      (show 1 < n by
        exact lt_of_lt_of_le (by
          have : 1 < m ^ 16 := Nat.one_lt_pow (by omega) (by omega)
          exact this) hn)
      (show 0 < m by omega) hL p hp0 hpL hmean pilot hpilotNonempty policy
      cutoff (show 0 < d by exact hdpos) (show 0 < d by exact hdpos)
      (e := (n : ℝ) / (m : ℝ) ^ 2) (r := 1 / (m : ℝ) ^ 2)
      (div_pos (by exact_mod_cast (lt_of_lt_of_le
        (pow_pos (by omega) 16) hn)) (sq_pos_of_pos (by positivity)))
      (by positivity) (δ := δ) (by dsimp [δ]; positivity)
      hDiscovery hCounts hBad
      (by simpa [pilot, inverseSquarePilotPositions_card] using hLearning)
      hInverse hMesh
      (by simpa [pilot, inverseSquarePilotPositions_card] using hPilot)
  have hscale : max 1 (L + L / (m : ℝ)) ≤ 2 * (L + 1) := by
    apply max_le
    · linarith
    · have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hdiv : L / (m : ℝ) ≤ L := by
        rw [div_le_iff₀ hmR]
        have hmOne : (1 : ℝ) ≤ m := by
          exact_mod_cast (by omega : 1 ≤ m)
        nlinarith [mul_le_mul_of_nonneg_left hmOne hL.le]
      linarith
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hconstant :
      (59 + 101 * max 1 (L + L / (m : ℝ))) * δ ≤
        7830 * (L + 1) ^ 2 / m := by
    dsimp [δ]
    have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    calc
      (59 + 101 * max 1 (L + L / (m : ℝ))) *
            (30 * (L + 1) / m) =
          ((59 + 101 * max 1 (L + L / (m : ℝ))) *
            30 * (L + 1)) / m := by ring
      _ ≤ (7830 * (L + 1) ^ 2) / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        nlinarith
  linarith

/-- The finite unknown-multiset comparison with no mean assumption.  The
positive and zero-mean branches use the same pilot/template compiler; only
their analyses differ. -/
theorem boundedUniform_blindPilot_all_means_parameter_rate
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (policy : ObservedTrace.CompletePolicy p) :
    let k := inverseSquareSize n m
    let hscales := parameter_scales hm hn
    let pilot := inverseSquarePilotPositions n m hscales.2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      uniformAverage (normalizedCost p policy) +
        7830 * (L + 1) ^ 2 / m := by
  have hnPos : 0 < n := lt_of_lt_of_le (pow_pos (by omega) 16) hn
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun job _ => hp0 job) (by positivity)
  by_cases hzero : populationMean p = 0
  · exact boundedUniform_blindPilot_zero_parameter_rate
      hm hn hL p hp0 hpL hzero policy
  · have hmean : 0 < populationMean p := lt_of_le_of_ne hmean0 (Ne.symm hzero)
    exact boundedUniform_blindPilot_inverse_parameter_rate
      hm hn hL p hp0 hpL hmean policy

/-- A single input-size-only family.  The algorithm uses the floored
sixteenth root of `n`; no accuracy parameter is supplied by the theorem user.
Its displayed additive coefficient therefore tends to zero with `n`. -/
theorem boundedUniform_blindPilot_concrete_rate
    {n : ℕ} (hroot : 2 ≤ sixteenthRoot n)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (policy : ObservedTrace.CompletePolicy p) :
    let m := concreteUnknownParameter n
    let k := inverseSquareSize n m
    let hscales := concreteUnknownParameter_bounds n hroot
    let pilot := inverseSquarePilotPositions n m
      (parameter_scales hscales.1 hscales.2).2.1
    let G := boundedUniformRoundedGrid (show 0 < m by omega) hL p hp0 hpL
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (blindPilotLearnedCost G pilot pilotOrder)) /
        (n : ℝ) ^ 2 ≤
      uniformAverage (normalizedCost p policy) +
        7830 * (L + 1) ^ 2 / m := by
  dsimp
  let m := concreteUnknownParameter n
  obtain ⟨hm, hn⟩ := concreteUnknownParameter_bounds n hroot
  simpa [m] using
    (boundedUniform_blindPilot_all_means_parameter_rate
      (m := m) hm hn hL p hp0 hpL policy)

end

end RandomizedOptional
end SchedulingPaper
