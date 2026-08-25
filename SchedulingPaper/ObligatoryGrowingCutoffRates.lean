import SchedulingPaper.ObligatoryGrowingCutoffBenchmark
import SchedulingPaper.RandomizedOptionalUnknownRates
import SchedulingPaper.BlindOptionalUnboundedOperational
import Mathlib.Tactic

/-!
# A literal vanishing parameter family for obligatory testing

For an accuracy parameter `m` and every `n >= m^16`, the growing policy uses
`n / m^2` pilot jobs, `m - 1` positive grid intervals, mesh
`(L + 2) / (m - 1)`, and the checkpoint scales already used by the finite
random-permutation lower bound.  Both sides of the common benchmark then
lose at most `400 (L + 3)^2 / m` after normalization by `n^2`.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Randomized
open RandomizedAnnounced
open RandomizedObligatory
open RandomizedOptional
open RandomizedOptional.AnnouncedRoundedLower
open RandomizedOptional.ObservedOnline
open RandomizedOptional.ObservedTrace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The common normalized error coefficient for the explicit parameter
family. -/
def growingInverseParameterError (L : ℝ) (m : ℕ) : ℝ :=
  400 * (L + 3) ^ 2 / m

theorem growingInverseParameterError_nonneg
    {L : ℝ} (hL : 0 < L) (m : ℕ) :
    0 ≤ growingInverseParameterError L m := by
  unfold growingInverseParameterError
  positivity

/-- On the degenerate all-zero population, the all-early template has the
exact obligatory fluid value `1/2`. -/
theorem minimumGrowingTemplateValue_le_half_of_eq_zero
    {n d : ℕ} (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (p : Fin n → ℝ) (hpzero : ∀ job, p job = 0) :
    minimumObligatoryTemplateValue
        (populationHistogram (fun job =>
          quantizedCategory d η (p job) hη))
        (Online.growingQuantizedRepresentative d η) ≤ 1 / 2 := by
  let category := fun job : Fin n => quantizedCategory d η (p job) hη
  let price := Online.growingQuantizedRepresentative d η
  let early : QuantizedCategory d → Bool := fun _ => true
  have hmin := minimizingObligatoryTemplate_minimizes
    (populationHistogram category) price early
  have hmass : weightedMass (earlyJobWeight (fun i => early (category i))) = 1 := by
    convert weightedMass_uniformJobWeight hn using 1
  have hcategory : ∀ i, category i = (⟨0, by omega⟩ : QuantizedCategory d) := by
    intro i
    simp [category, hpzero i, quantizedCategory_zero]
  have hpriceZero : price (⟨0, by omega⟩ : QuantizedCategory d) = 0 := by
    exact Online.growingQuantizedRepresentative_zero d η
  have hmoment :
      weightedMoment (earlyJobWeight (fun i => early (category i)))
        (fun i => price (category i)) = 0 := by
    unfold weightedMoment earlyJobWeight
    apply Finset.sum_eq_zero
    intro i _
    change (if early (category i) then 1 / (n : ℝ) else 0) *
      price (category i) = 0
    rw [hcategory i, hpriceZero]
    ring
  have hpair :
      weightedMinPair (lateJobWeight (fun i => early (category i)))
        (fun i => price (category i)) = 0 := by
    unfold weightedMinPair lateJobWeight
    simp [early]
  have htarget :
      obligatoryTemplateValue (populationHistogram category) price early = 1 / 2 := by
    rw [obligatoryTemplateValue,
      ← weightedMass_categoryTemplate_eq hn category early,
      ← weightedMoment_categoryTemplate_eq hn category price early,
      ← weightedMinPair_categoryTemplate_eq hn category price early,
      hmass, hmoment, hpair]
    norm_num
  simpa [minimumObligatoryTemplateValue] using hmin.trans_eq htarget

/-- Every complete test-only competitor has the same normalized cost on an
all-zero population, independently of its adaptive order. -/
theorem normalizedCost_zero_eq
    {n : ℕ} (hn : 0 < n)
    (policy : CompletePolicy
      (RandomizedOptional.UnboundedOperational.zeroProcessing n))
    (htest : FirstTouchesAreTests policy)
    (σ : ObservedTrace.Placement n) :
    normalizedCost
        (RandomizedOptional.UnboundedOperational.zeroProcessing n)
        policy σ = (n + 1 : ℝ) / (2 * n) := by
  let zero := RandomizedOptional.UnboundedOperational.zeroProcessing n
  let transcript := (settledRun zero policy.strategy σ).config.transcript
  have hplaced : placedProcessing zero σ = zero := by
    funext job
    rfl
  have hmatch := (run_historyInvariant (placedProcessing zero σ)
    policy.strategy (2 * n + 1)).revealsMatch
  have hzero : ∀ job value,
      (job, value) ∈ ObservedOnline.Transcript.revealedResults transcript →
        value = 0 := by
    intro job value hmem
    have hvalue := hmatch job value (by simpa [transcript, settledRun] using hmem)
    simpa [hplaced, zero,
      RandomizedOptional.UnboundedOperational.zeroProcessing] using hvalue
  have harea :
      RandomizedOptional.Unbounded.testedArea
          (RandomizedOptional.UnboundedOperational.traceTested
            (touchTrace zero policy σ)) =
        (n : ℝ) * (n + 1) / 2 := by
    calc
      RandomizedOptional.Unbounded.testedArea
          (RandomizedOptional.UnboundedOperational.traceTested
            (touchTrace zero policy σ)) =
          ∑ rank : Fin n, RandomizedOptional.Unbounded.rankWeight n rank := by
        unfold RandomizedOptional.Unbounded.testedArea
          RandomizedOptional.UnboundedOperational.traceTested
        apply Finset.sum_congr rfl
        intro rank _
        have hkind : (touchTrace zero policy σ).kind rank = .test := htest σ rank
        simp [hkind]
      _ = (n : ℝ) * (n + 1) / 2 :=
        RandomizedOptional.Unbounded.sum_rankWeight n
  unfold normalizedCost
  rw [hplaced]
  change completionCost zero transcript / (n : ℝ) ^ 2 = _
  rw [RandomizedOptional.UnboundedOperational.zero_completionCost_eq_choiceTestArea
      transcript hzero,
    RandomizedOptional.UnboundedOperational.choiceTestArea_touchTrace
      zero policy σ,
    harea]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp [hnR.ne']

set_option maxHeartbeats 3000000 in
/-- The upper and lower error expressions simultaneously satisfy the
explicit inverse-parameter rate. -/
theorem growing_inverse_parameter_error_bounds
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m) :
    let k := inverseSquareSize n m
    let d := m - 1
    let η := (L + 2) / (m - 1 : ℕ)
    let Bcut := L + 2
    let cutoff := inverseSquareCutoff n m (parameter_scales hm hn).1
    let step := inverseFourthStep n m
    let e := (n : ℝ) / (m : ℝ) ^ 2
    let s := 1 / (m : ℝ) ^ 2
    let threshold := e + step +
      (s + 2 * step / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card
    let γ := threshold / n
    let base :=
      (backwardCheckpoints step cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints step cutoff).card *
          ((2 / (suffixPositions cutoff).card) / s ^ 2)
    growingUpperRawError n k d Bcut η L ≤
        (n : ℝ) ^ 2 * growingInverseParameterError L m ∧
      growingLowerUniformError d η L γ base ≤
        growingInverseParameterError L m := by
  dsimp
  obtain ⟨hkpos, _hklt, _hdpos, hkLower, hkUpper,
      _hdLower, _hdUpper⟩ := parameter_scales hm hn
  let k := inverseSquareSize n m
  let step := inverseFourthStep n m
  let cutoff := inverseSquareCutoff n m hkpos
  let η : ℝ := (L + 2) / (m - 1 : ℕ)
  let δ₀ : ℝ := 30 * (L + 1) / m
  let δ : ℝ := growingInverseParameterError L m
  obtain ⟨_hDiscovery, hCounts, hBad, hLearning, hInverse,
      _hMesh, _hPilot⟩ := inverse_parameter_error_bounds hm hn hL
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmSubR : (0 : ℝ) < (m - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by omega) 16) hn)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hmSubR]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    linarith only [hcover]
  have hηRate : η ≤ 2 * (L + 2) / m := by
    dsimp [η]
    rw [div_le_div_iff₀ hmSubR hmR]
    have hmDouble : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
    have hmul := mul_le_mul_of_nonneg_left hmDouble
      (show 0 ≤ L + 2 by linarith only [hL])
    convert hmul using 1 <;> ring
  have hspan : (m : ℝ) * η + 2 ≤ 2 * (L + 3) := by
    dsimp [η]
    rw [div_eq_mul_inv]
    have hmRatio : (m : ℝ) * ((m - 1 : ℕ) : ℝ)⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hmSubR]
      exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
    have hL20 : 0 ≤ L + 2 := by linarith only [hL]
    nlinarith only [mul_le_mul_of_nonneg_right hmRatio hL20]
  have hkOverN : (k : ℝ) / n ≤ 1 / (m : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hnR (sq_pos_of_pos hmR)]
    nlinarith only [hkUpper]
  have hmInv : 1 / (m : ℝ) ^ 2 ≤ 1 / m := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hmR) hmR]
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith only [hmOne]
  have hkOverNRate : (k : ℝ) / n ≤ 1 / m := hkOverN.trans hmInv
  have hkOverN0 : 0 ≤ (k : ℝ) / n := by positivity
  have hδ₀0 : 0 ≤ δ₀ := by dsimp [δ₀]; positivity
  have hlearn : Real.sqrt ((m + 1 : ℝ) / k) ≤ δ₀ := by
    simpa [k, δ₀] using hLearning
  have hlearn0 : 0 ≤ Real.sqrt ((m + 1 : ℝ) / k) := Real.sqrt_nonneg _
  have hstat :
      6 * ((m : ℝ) * η + 2) *
          Real.sqrt ((m + 1 : ℝ) / k) ≤
        360 * (L + 3) ^ 2 / m := by
    have hmul := mul_le_mul hspan hlearn hlearn0
      (by linarith only [hL] : 0 ≤ 2 * (L + 3))
    dsimp [δ₀] at hmul
    have hL13 : L + 1 ≤ L + 3 := by linarith only
    have hL30 : 0 ≤ L + 3 := by linarith only [hL]
    have hsq : (L + 3) * (L + 1) ≤ (L + 3) ^ 2 := by
      nlinarith only [hL]
    calc
      6 * ((m : ℝ) * η + 2) *
            Real.sqrt ((m + 1 : ℝ) / k) ≤
          6 * (2 * (L + 3) * (30 * (L + 1) / m)) := by
            nlinarith only [hmul]
      _ = 360 * ((L + 3) * (L + 1)) / m := by ring
      _ ≤ 360 * (L + 3) ^ 2 / m := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) hmR.le
  have hcross :
      (L + 3) * (k : ℝ) / (2 * n) ≤
        (L + 3) ^ 2 / m := by
    have hkn := mul_le_mul_of_nonneg_left hkOverNRate
      (by linarith only [hL] : 0 ≤ L + 3)
    calc
      (L + 3) * (k : ℝ) / (2 * n) =
          ((L + 3) * ((k : ℝ) / n)) / 2 := by field_simp
      _ ≤ ((L + 3) * (1 / m)) / 2 :=
        div_le_div_of_nonneg_right hkn (by norm_num)
      _ = ((L + 3) / 2) / m := by ring
      _ ≤ (L + 3) ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        nlinarith only [hL]
  have hdiag :
      (1 + L) / (2 * n) ≤ (L + 3) ^ 2 / m := by
    have hmnNat : m ≤ n := by
      have hmPow : m ≤ m ^ 16 := by
        exact Nat.le_pow (by omega : 0 < 16)
      exact hmPow.trans hn
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hmnNat
    have hinv : 1 / (n : ℝ) ≤ 1 / m :=
      one_div_le_one_div_of_le hmR hmn
    have hleft0 : 0 ≤ 1 + L := by linarith only [hL]
    have hmul := mul_le_mul_of_nonneg_left hinv hleft0
    calc
      (1 + L) / (2 * n) = ((1 + L) * (1 / n)) / 2 := by
        field_simp
      _ ≤ ((1 + L) * (1 / m)) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((1 + L) / 2) / m := by ring
      _ ≤ (L + 3) ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        nlinarith only [hL]
  have hpilot :
      (L + 3) * ((k : ℝ) / n) ^ 2 ≤ (L + 3) ^ 2 / m := by
    have hratioSq : ((k : ℝ) / n) ^ 2 ≤ (1 / (m : ℝ)) ^ 2 := by
      have hinv0 : 0 ≤ 1 / (m : ℝ) := by positivity
      nlinarith only [hkOverNRate, hkOverN0, hinv0]
    have hinvOne : (1 / (m : ℝ)) ^ 2 ≤ 1 / m := by
      have hinv0 : 0 ≤ 1 / (m : ℝ) := by positivity
      have hinvLe : 1 / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmR]
        exact_mod_cast (by omega : 1 ≤ m)
      nlinarith only [hinv0, hinvLe]
    have hratioRate := hratioSq.trans hinvOne
    have hmul := mul_le_mul_of_nonneg_left hratioRate
      (by linarith only [hL] : 0 ≤ L + 3)
    have hcoef : (L + 3) / m ≤ (L + 3) ^ 2 / m := by
      apply div_le_div_of_nonneg_right _ hmR.le
      nlinarith only [hL]
    have hcoef' : (L + 3) * (1 / m) ≤ (L + 3) ^ 2 / m := by
      simpa [div_eq_mul_inv] using hcoef
    exact hmul.trans hcoef'
  let upperNorm : ℝ :=
    6 * ((m : ℝ) * η + 2) *
        Real.sqrt ((m + 1 : ℝ) / k) +
      (L + 3) * k / (2 * n) +
      (1 + L) / (2 * n) +
      (L + 3) * ((k : ℝ) / n) ^ 2
  have hupperNorm : upperNorm ≤ δ := by
    let q : ℝ := (L + 3) ^ 2 / m
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hstatQ :
        6 * ((m : ℝ) * η + 2) *
            Real.sqrt ((m + 1 : ℝ) / k) ≤ 360 * q := by
      dsimp [q]
      convert hstat using 1 <;> ring
    have hcrossQ : (L + 3) * (k : ℝ) / (2 * n) ≤ q := by
      exact hcross
    have hdiagQ : (1 + L) / (2 * n) ≤ q := by exact hdiag
    have hpilotQ : (L + 3) * ((k : ℝ) / n) ^ 2 ≤ q := by exact hpilot
    calc
      upperNorm ≤ 360 * q + q + q + q := by
        dsimp only [upperNorm]
        exact add_le_add (add_le_add (add_le_add hstatQ hcrossQ) hdiagQ) hpilotQ
      _ ≤ 400 * q := by linarith only [hq0]
      _ = δ := by dsimp [q, δ, growingInverseParameterError]; ring
  have hupperEq :
      growingUpperRawError n k (m - 1) (L + 2) η L =
        (n : ℝ) ^ 2 * upperNorm := by
    unfold growingUpperRawError
    dsimp [upperNorm]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    field_simp [hnR.ne']
    ring
  have hUpper :
      growingUpperRawError n k (m - 1) (L + 2) η L ≤
        (n : ℝ) ^ 2 * δ := by
    rw [hupperEq]
    exact mul_le_mul_of_nonneg_left hupperNorm (sq_nonneg _)
  have hcount :
      (m + 1 : ℝ) *
          (((n : ℝ) / (m : ℝ) ^ 2 + step +
            (1 / (m : ℝ) ^ 2 +
              2 * step / (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card) / n) ≤ δ₀ := by
    simpa [step, cutoff, δ₀] using hCounts
  have hbad :
      (m + 2 : ℝ) *
          ((backwardCheckpoints step cutoff).card *
              (n / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
            (backwardCheckpoints step cutoff).card *
              ((2 / (suffixPositions cutoff).card) /
                (1 / (m : ℝ) ^ 2) ^ 2)) ≤ δ₀ := by
    simpa [step, cutoff, δ₀] using hBad
  let γ : ℝ :=
    ((n : ℝ) / (m : ℝ) ^ 2 + step +
      (1 / (m : ℝ) ^ 2 +
        2 * step / (suffixPositions cutoff).card) * n +
      (suffixPositions cutoff).card) / n
  let base : ℝ :=
    (backwardCheckpoints step cutoff).card *
        (n / ((n : ℝ) / (m : ℝ) ^ 2) ^ 2) +
      (backwardCheckpoints step cutoff).card *
        ((2 / (suffixPositions cutoff).card) /
          (1 / (m : ℝ) ^ 2) ^ 2)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hbase0 : 0 ≤ base := by dsimp [base]; positivity
  have hcount' : (m + 1 : ℝ) * γ ≤ δ₀ := by
    simpa [γ] using hcount
  have hbad' : (m + 1 : ℝ) * base ≤ δ₀ := by
    have hcoeff : (m + 1 : ℝ) ≤ m + 2 := by norm_num
    have hmul := mul_le_mul_of_nonneg_right hcoeff hbase0
    exact hmul.trans (by simpa [base] using hbad)
  have hmeanFactor : 1 + L + η ≤ L + 2 := by linarith only [hη1]
  have hmeanFactor0 : 0 ≤ 1 + L + η := by positivity
  have hcountTerm :
      (m + 1 : ℝ) * γ * (1 + L + η) ≤ (L + 2) * δ₀ := by
    calc
      (m + 1 : ℝ) * γ * (1 + L + η) ≤
          δ₀ * (1 + L + η) :=
        mul_le_mul_of_nonneg_right hcount' hmeanFactor0
      _ ≤ δ₀ * (L + 2) :=
        mul_le_mul_of_nonneg_left hmeanFactor hδ₀0
      _ = (L + 2) * δ₀ := by ring
  have hbadTerm :
      (1 + L + η) * ((m + 1 : ℝ) * base) ≤ (L + 2) * δ₀ := by
    calc
      (1 + L + η) * ((m + 1 : ℝ) * base) ≤
          (1 + L + η) * δ₀ :=
        mul_le_mul_of_nonneg_left hbad' hmeanFactor0
      _ ≤ (L + 2) * δ₀ :=
        mul_le_mul_of_nonneg_right hmeanFactor hδ₀0
  have hlowerRate :
      η + (m + 1 : ℝ) * γ * (1 + L + η) +
          (1 + L + η) * ((m + 1 : ℝ) * base) ≤ δ := by
    dsimp [δ, δ₀, growingInverseParameterError]
    have hsq : (L + 2) * (L + 1) ≤ (L + 3) ^ 2 := by
      nlinarith only [hL]
    have hprodRate :
        30 * ((L + 2) * (L + 1)) / m ≤
          30 * (L + 3) ^ 2 / m := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) hmR.le
    have hηQ : η ≤ 2 * (L + 3) ^ 2 / m := by
      calc
        η ≤ 2 * (L + 2) / m := hηRate
        _ ≤ 2 * (L + 3) ^ 2 / m := by
          apply div_le_div_of_nonneg_right _ hmR.le
          nlinarith only [hL]
    dsimp [δ₀] at hcountTerm hbadTerm
    let q : ℝ := (L + 3) ^ 2 / m
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hcountQ :
        (m + 1 : ℝ) * γ * (1 + L + η) ≤ 30 * q := by
      calc
        (m + 1 : ℝ) * γ * (1 + L + η) ≤
            (L + 2) * (30 * (L + 1) / m) := hcountTerm
        _ = 30 * ((L + 2) * (L + 1)) / m := by ring
        _ ≤ 30 * q := by dsimp [q]; convert hprodRate using 1 <;> ring
    have hbadQ :
        (1 + L + η) * ((m + 1 : ℝ) * base) ≤ 30 * q := by
      calc
        (1 + L + η) * ((m + 1 : ℝ) * base) ≤
            (L + 2) * (30 * (L + 1) / m) := hbadTerm
        _ = 30 * ((L + 2) * (L + 1)) / m := by ring
        _ ≤ 30 * q := by dsimp [q]; convert hprodRate using 1 <;> ring
    calc
      η + (m + 1 : ℝ) * γ * (1 + L + η) +
          (1 + L + η) * ((m + 1 : ℝ) * base) ≤
          2 * q + 30 * q + 30 * q := by
        have hηQ' : η ≤ 2 * q := by
          dsimp [q]
          convert hηQ using 1 <;> ring
        exact add_le_add (add_le_add hηQ' hcountQ) hbadQ
      _ ≤ 400 * q := by linarith only [hq0]
      _ = 400 * (L + 3) ^ 2 / m := by dsimp [q]; ring
  refine ⟨?_, ?_⟩
  · simpa [k, η, δ] using hUpper
  · unfold growingLowerUniformError
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    convert hlowerRate using 1 <;>
      simp [step, cutoff, γ, base, η, δ, Nat.cast_sub (by omega : 1 ≤ m)] <;>
      ring

set_option maxHeartbeats 5000000 in
/-- Fully instantiated finite instance-optimal comparison in the positive-
mean branch.  The policy and every finitely randomized complete test-only
competitor are compared on one oblivious placement selected by the lower
bound. -/
theorem exists_fixedPlacement_growingPolicy_inverse_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (inverseSquareSize n m +
      (n - inverseSquareSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (hmean : 0 < populationMean p)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := inverseSquareSize n m
    let r := n - k
    let d := m - 1
    let η := (L + 2) / (m - 1 : ℕ)
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d (L + 2) η
            (by
              apply div_pos <;>
                first | linarith only [hL] |
                  exact_mod_cast (show 0 < m - 1 by omega)) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  dsimp only
  let k := inverseSquareSize n m
  let r := n - k
  let d := m - 1
  let η : ℝ := (L + 2) / (m - 1 : ℕ)
  obtain ⟨hk, hklt, hstep, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hm hn
  have hkle : k ≤ n := Nat.div_le_self _ _
  have htotal : k + r = n := by dsimp [r]; omega
  have hr : 0 < r := by dsimp [r]; omega
  have hmSubPosNat : 0 < m - 1 := by omega
  have hmSubR : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast hmSubPosNat
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (by linarith only [hL]) hmSubR
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hmSubR]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    linarith only [hcover]
  have hB0 : 0 ≤ L + 2 := by linarith only [hL]
  have hgridEq : (d : ℝ) * η = L + 2 := by
    dsimp [d, η]
    field_simp [hmSubR.ne']
  have hBgrid : L + 2 ≤ (d : ℝ) * η := hgridEq.ge
  have hgrid : L ≤ (d : ℝ) * η := by rw [hgridEq]; linarith
  have hBcover : 1 + L + η ≤ L + 2 := by linarith only [hη1]
  have hnTotal : m ^ 16 ≤ k + r := by simpa [htotal] using hn
  obtain ⟨hkTotal, _hkTotalLt, hstepTotal, _⟩ :=
    parameter_scales hm hnTotal
  let cutoff := inverseSquareCutoff (k + r) m hkTotal
  let step := inverseFourthStep (k + r) m
  let e : ℝ := (k + r : ℝ) / (m : ℝ) ^ 2
  let s : ℝ := 1 / (m : ℝ) ^ 2
  have he : 0 < e := by dsimp [e]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨hUpper, hLower⟩ :=
    growing_inverse_parameter_error_bounds hm hnTotal hL hcover
  have hkEq : inverseSquareSize (k + r) m = k := by
    simp [k, htotal]
  apply exists_fixedPlacement_growingPolicy_le_of_error_bounds
      k r d hk hr (L + 2) η L hη hB0 hBgrid hgrid hBcover
      p hp0 hpL hmean policy htest cutoff hstepTotal hstepTotal he hs
      (growingInverseParameterError_nonneg hL m)
  · simpa [hkEq, d, η] using hUpper
  · simpa [cutoff, step, e, s, d, η] using hLower

set_option maxHeartbeats 5000000 in
/-- The same rate on the degenerate zero-mean population.  Here the lower
comparison is exact: every complete test-only policy pays `n(n+1)/2`. -/
theorem exists_fixedPlacement_growingPolicy_zero_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (inverseSquareSize n m +
      (n - inverseSquareSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (hmean : populationMean p = 0)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := inverseSquareSize n m
    let r := n - k
    let d := m - 1
    let η := (L + 2) / (m - 1 : ℕ)
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d (L + 2) η
            (by
              apply div_pos <;>
                first | linarith only [hL] |
                  exact_mod_cast (show 0 < m - 1 by omega)) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  dsimp only
  let k := inverseSquareSize n m
  let r := n - k
  let d := m - 1
  let η : ℝ := (L + 2) / (m - 1 : ℕ)
  obtain ⟨hk, hklt, _hstep, _hkLower, _hkUpper, _hdLower, _hdUpper⟩ :=
    parameter_scales hm hn
  have htotal : k + r = n := by dsimp [r]; omega
  have hr : 0 < r := by dsimp [r]; omega
  have htotalPos : 0 < k + r := by omega
  have hpzero := processing_eq_zero_of_populationMean_eq_zero
    htotalPos p hp0 hmean
  let zero := RandomizedOptional.UnboundedOperational.zeroProcessing (k + r)
  have hpEq : p = zero := by
    funext job
    simpa [zero, RandomizedOptional.UnboundedOperational.zeroProcessing]
      using hpzero job
  subst p
  have hmSubR : (0 : ℝ) < (m - 1 : ℕ) := by
    exact_mod_cast (show 0 < m - 1 by omega)
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (by linarith only [hL]) hmSubR
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hmSubR]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    linarith only [hcover]
  have hB0 : 0 ≤ L + 2 := by linarith only [hL]
  have hgridEq : (d : ℝ) * η = L + 2 := by
    dsimp [d, η]
    field_simp [hmSubR.ne']
  have hBgrid : L + 2 ≤ (d : ℝ) * η := hgridEq.ge
  have hgrid : L ≤ (d : ℝ) * η := by rw [hgridEq]; linarith
  have hBcover : 1 + L + η ≤ L + 2 := by linarith only [hη1]
  have hrun := uniformAverage_physicalGrowingRunCost_le_minimum
    k r d hk hr (L + 2) η L hη hB0 hBgrid hgrid hBcover
      zero (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing, hL.le])
  have hmin := minimumGrowingTemplateValue_le_half_of_eq_zero
    (d := d) htotalPos η hη zero
      (fun _ => by simp [zero,
        RandomizedOptional.UnboundedOperational.zeroProcessing])
  obtain ⟨hUpper, _hLower⟩ :=
    growing_inverse_parameter_error_bounds (n := k + r) hm
      (by simpa [htotal] using hn) hL hcover
  have hUpper' :
      growingUpperRawError (k + r) k d (L + 2) η L ≤
        (k + r : ℝ) ^ 2 * growingInverseParameterError L m := by
    have hkEq : inverseSquareSize (k + r) m = k := by simp [k, htotal]
    simpa [hkEq, d, η] using hUpper
  let σ : ObservedTrace.Placement (k + r) := Equiv.refl (Fin (k + r))
  have hcompetitor :
      uniformAverage (fun seed => normalizedCost zero (policy seed) σ) =
        (k + r + 1 : ℝ) / (2 * (k + r)) := by
    rw [show (fun seed => normalizedCost zero (policy seed) σ) =
        fun _seed : Seeds => (k + r + 1 : ℝ) / (2 * (k + r)) by
      funext seed
      have hz := normalizedCost_zero_eq htotalPos (policy seed) (htest seed) σ
      convert hz using 1 <;> push_cast <;> ring]
    exact uniformAverage_const _
  have hcompetitorHalf :
      (1 : ℝ) / 2 ≤ uniformAverage
        (fun seed => normalizedCost zero (policy seed) σ) := by
    rw [hcompetitor]
    have htotalR : (0 : ℝ) < k + r := by exact_mod_cast htotalPos
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos (by norm_num) htotalR)]
    push_cast
    linarith
  have hminScaled := mul_le_mul_of_nonneg_left hmin (sq_nonneg (k + r : ℝ))
  have hcompetitorScaled := mul_le_mul_of_nonneg_left hcompetitorHalf
    (sq_nonneg (k + r : ℝ))
  have hδ0 := growingInverseParameterError_nonneg hL m
  refine ⟨σ, ?_⟩
  dsimp only at hrun
  unfold growingUpperRawError at hUpper'
  push_cast at hrun hUpper' hminScaled hcompetitorScaled ⊢
  nlinarith

/-- One finite theorem covering every bounded nonnegative population. -/
theorem exists_fixedPlacement_growingPolicy_all_means_parameter_rate
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    {n m : ℕ} (hm : 2 ≤ m) (hn : m ^ 16 ≤ n)
    {L : ℝ} (hL : 0 < L) (hcover : L + 3 ≤ m)
    (p : Fin (inverseSquareSize n m +
      (n - inverseSquareSize n m)) → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) (hpL : ∀ job, p job ≤ L)
    (policy : Seeds → CompletePolicy p)
    (htest : ∀ seed, FirstTouchesAreTests (policy seed)) :
    let k := inverseSquareSize n m
    let r := n - k
    let d := m - 1
    let η := (L + 2) / (m - 1 : ℕ)
    ∃ σ : ObservedTrace.Placement (k + r),
      uniformAverage
          (physicalGrowingRunCost (k + r) k d (L + 2) η
            (by
              apply div_pos <;>
                first | linarith only [hL] |
                  exact_mod_cast (show 0 < m - 1 by omega)) p) ≤
        (k + r : ℝ) ^ 2 *
          (uniformAverage (fun seed => normalizedCost p (policy seed) σ) +
            2 * growingInverseParameterError L m) := by
  have htotalPos : 0 < inverseSquareSize n m +
      (n - inverseSquareSize n m) := by
    obtain ⟨hk, hklt, _⟩ := parameter_scales hm hn
    omega
  have hmean0 : 0 ≤ populationMean p := by
    unfold populationMean
    exact div_nonneg (Finset.sum_nonneg fun job _ => hp0 job) (by positivity)
  by_cases hzero : populationMean p = 0
  · exact exists_fixedPlacement_growingPolicy_zero_parameter_rate
      hm hn hL hcover p hp0 hpL hzero policy htest
  · have hmean : 0 < populationMean p := lt_of_le_of_ne hmean0 (Ne.symm hzero)
    exact exists_fixedPlacement_growingPolicy_inverse_parameter_rate
      hm hn hL hcover p hp0 hpL hmean policy htest

end

end ObligatoryInstance
end SchedulingPaper
