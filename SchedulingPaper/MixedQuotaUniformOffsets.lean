import SchedulingPaper.MixedQuotaOffsetLimits
import SchedulingPaper.MixedQuotaDynamicNumerics
import Mathlib.Tactic

/-!
# Uniform affine representation of dynamic mixed quotas

The first-crossing window gives a common scale `q`, but the cap, positive,
and zero counts may each differ from their ideal multiples by a bounded
signed amount.  We shift the common scale backwards by one fixed
parameter-dependent amount.  All three signed errors then become
nonnegative offsets in fixed finite ranges, so the bounded-offset limit
theorem applies uniformly.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- The four inequalities supplied by a quota crossing at scale `q`. -/
structure DynamicQuotaWindow
    (M A B q C H : ℕ) : Prop where
  scaleLower :
    (M + A + B) * q ≤ C + H
  scaleUpper :
    C + H < (M + A + B) * (q + 1)
  capLower :
    (M : ℝ) / (M + A + B : ℕ) * (C + H : ℕ) ≤ C
  capUpper :
    (C : ℝ) <
      (M : ℝ) / (M + A + B : ℕ) * (C + H : ℕ) + 1

/-- A coarse common backward shift which makes every dynamic error
nonnegative. -/
def dynamicOffsetShift (M A B : ℕ) : ℕ :=
  M + (M + A + B)

def dynamicCapOffsetMax (M A B : ℕ) : ℕ :=
  M * (dynamicOffsetShift M A B + 1)

def dynamicPositiveOffsetMax (M A B : ℕ) : ℕ :=
  A * dynamicOffsetShift M A B + (M + A + B)

def dynamicZeroOffsetMax (M A B : ℕ) : ℕ :=
  B * dynamicOffsetShift M A B +
    dynamicOffsetShift M A B

/-- The finite cap-deferral margin of a dynamically rounded tail. -/
def dynamicDeferralMargin
    (u : ℝ) (A B C H : ℕ) : ℝ :=
  ((tailPositiveCount A B H +
      tailZeroCount A B H : ℕ) : ℝ) * (u - 1) -
    (harmonicFutureLevels
      (tailZeroCount A B H : ℝ) 0
      (tailPositiveCount A B H)).sum -
    C

/-- A strategy-independent upper bound for the loss caused by cap jobs
processed before the harmonic tail.  The exact number of such jobs is at
most `C`; using `C` itself makes the remainder depend only on the recovered
dynamic quota data. -/
def dynamicCapExchangeRemainder
    (u : ℝ) (A B C H : ℕ) : ℝ :=
  C * max 0 (-dynamicDeferralMargin u A B C H)

/-- A coarse bound used only below a fixed quota-scale threshold. -/
def dynamicCapExchangeRemainderBound
    (M A B Q : ℕ) : ℝ :=
  (((M + A + B) * Q : ℕ) : ℝ) ^ 2

/-- Raw safety bounds the negative part of the cap-deferral margin by the
number of capped jobs. -/
theorem neg_dynamicDeferralMargin_le_cap
    {u : ℝ} {A B C H : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    -dynamicDeferralMargin u A B C H ≤ C := by
  by_cases hH : H = 0
  · subst H
    simp [dynamicDeferralMargin, tailPositiveCount, tailZeroCount]
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    have hZ : 0 < Z := by
      simpa [Z] using tailZeroCount_pos hB hHpos
    have hsafe :
        1 + harmonicLevel (Z : ℝ) 0 K ≤ u := by
      simpa [K, Z] using
        dynamicTail_static_rawSafe hB hHpos hraw K le_rfl
    have hfuture :
        ∀ p ∈ harmonicFutureLevels (Z : ℝ) 0 K,
          p ≤ u - 1 := by
      intro p hp
      have hpLevel :=
        harmonicFutureLevels_le_level
          (by exact_mod_cast hZ) p hp
      linarith
    have hsum :
        (harmonicFutureLevels (Z : ℝ) 0 K).sum ≤
          (K : ℝ) * (u - 1) := by
      calc
        (harmonicFutureLevels (Z : ℝ) 0 K).sum ≤
            (harmonicFutureLevels (Z : ℝ) 0 K).length •
              (u - 1) :=
          List.sum_le_card_nsmul _ _ hfuture
        _ = (K : ℝ) * (u - 1) := by simp [nsmul_eq_mul]
    have hsplit : K + Z = H := by
      simpa [K, Z] using tail_split A B H
    have huOne : 1 ≤ u := by
      have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
      linarith
    have hZterm : 0 ≤ (Z : ℝ) * (u - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr huOne)
    dsimp [dynamicDeferralMargin]
    change
      -(((K + Z : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels (Z : ℝ) 0 K).sum -
          C) ≤ C
    push_cast
    linarith

/-- Consequently the coarse exchange loss is at most `C²`. -/
theorem dynamicCapExchangeRemainder_le_sq
    {u : ℝ} {A B C H : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    dynamicCapExchangeRemainder u A B C H ≤ (C : ℝ) ^ 2 := by
  have hneg :=
    neg_dynamicDeferralMargin_le_cap
      (u := u) (A := A) (B := B) (C := C) (H := H)
      hB hraw
  have hmax :
      max 0 (-dynamicDeferralMargin u A B C H) ≤ (C : ℝ) :=
    max_le (by positivity) hneg
  unfold dynamicCapExchangeRemainder
  calc
    (C : ℝ) * max 0 (-dynamicDeferralMargin u A B C H) ≤
        (C : ℝ) * C :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (C : ℝ) ^ 2 := by ring

/-- After the fixed backward shift, every dynamic quota triple is an
`affineCount` triple with offsets in fixed finite ranges. -/
theorem dynamicQuota_affine_representation
    {M A B q C H : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hq :
      dynamicOffsetShift M A B + 1 ≤ q)
    (hwindow : DynamicQuotaWindow M A B q C H) :
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    ∃ q₀ m a b : ℕ,
      q₀ = q - (dynamicOffsetShift M A B + 1) ∧
      m ≤ dynamicCapOffsetMax M A B ∧
      a ≤ dynamicPositiveOffsetMax M A B ∧
      b ≤ dynamicZeroOffsetMax M A B ∧
      C = affineCount M m q₀ ∧
      K = affineCount A a q₀ ∧
      Z = affineCount B b q₀ := by
  dsimp only
  let D : ℕ := M + A + B
  let E : ℕ := dynamicOffsetShift M A B
  let K : ℕ := tailPositiveCount A B H
  let Z : ℕ := tailZeroCount A B H
  have hD : 0 < D := by
    dsimp [D]
    omega
  have hAB : 0 < A + B := by omega
  have hcap :=
    quota_cap_count_bounds
      hM hD hwindow.scaleLower hwindow.scaleUpper
      hwindow.capLower hwindow.capUpper
  have htail :=
    quota_tail_size_bounds
      (S := C + H) (C := C) (H := H)
      (q := q) (M := M) (A := A) (B := B)
      rfl hwindow.scaleLower hwindow.scaleUpper hcap.1 hcap.2
  have hpositive :=
    quota_tailPositiveCount_bounds
      (M := M) (A := A) (B := B) (H := H) (q := q)
      hAB htail.1 htail.2
  have hsplit : K + Z = H := by
    simpa [K, Z] using tail_split A B H
  have hEleq : E = M + D := by
    rfl
  have hEpos : 0 < E := by
    dsimp [E, dynamicOffsetShift]
    omega
  have hEgeM : M ≤ E := by
    dsimp [E, dynamicOffsetShift]
    omega
  have hEgeD : D ≤ E := by
    dsimp [E, D, dynamicOffsetShift]
    omega
  have hEone : E + 1 ≤ q := by
    simpa [E] using hq
  have hEq : E ≤ q := by omega
  have hqSplit : q - E + E = q :=
    Nat.sub_add_cancel hEq
  have hq₀Succ :
      q - (E + 1) + 1 = q - E := by
    omega
  have hAEm : M ≤ A * E := by
    have hAE : E ≤ A * E :=
      Nat.le_mul_of_pos_left E hA
    exact hEgeM.trans hAE
  have hBE : E ≤ B * E :=
    Nat.le_mul_of_pos_left E hB
  have hKLower : A * (q - E) ≤ K := by
    have hAq :
        A * q = A * (q - E) + A * E := by
      exact
        (congrArg (fun t : ℕ => A * t) hqSplit.symm).trans
          (Nat.mul_add A (q - E) E)
    rw [hAq] at hpositive
    omega
  have hKUpper :
      K ≤ A * (q - E) +
        (A * E + D) := by
    have hAq :
        A * q = A * (q - E) + A * E := by
      exact
        (congrArg (fun t : ℕ => A * t) hqSplit.symm).trans
          (Nat.mul_add A (q - E) E)
    rw [hAq] at hpositive
    simpa [D, Nat.add_assoc] using hpositive.2
  have hZcoarseLower : B * q ≤ Z + E := by
    have hKupper : K ≤ A * q + D := by
      simpa [D] using hpositive.2
    have htailLower : A * q + B * q ≤ K + Z + M := by
      rw [← Nat.add_mul]
      simpa [hsplit, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail.1
    omega
  have hZcoarseUpper : Z ≤ B * q + E := by
    have htailUpper :
        K + Z < A * q + B * q + D := by
      rw [← Nat.add_mul]
      simpa [D, hsplit] using htail.2
    have hKlower : A * q ≤ K + M := by
      simpa [K] using hpositive.1
    omega
  have hZLower : B * (q - E) ≤ Z := by
    have hBq :
        B * q = B * (q - E) + B * E := by
      exact
        (congrArg (fun t : ℕ => B * t) hqSplit.symm).trans
          (Nat.mul_add B (q - E) E)
    rw [hBq] at hZcoarseLower
    omega
  have hZUpper :
      Z ≤ B * (q - E) + (B * E + E) := by
    have hBq :
        B * q = B * (q - E) + B * E := by
      exact
        (congrArg (fun t : ℕ => B * t) hqSplit.symm).trans
          (Nat.mul_add B (q - E) E)
    rw [hBq] at hZcoarseUpper
    simpa [Nat.add_assoc] using hZcoarseUpper
  have hCLower : M * (q - E) ≤ C := by
    have hMq :
        M * q = M * (q - E) + M * E := by
      exact
        (congrArg (fun t : ℕ => M * t) hqSplit.symm).trans
          (Nat.mul_add M (q - E) E)
    rw [hMq] at hcap
    omega
  have hCUpper :
      C ≤ M * (q - E) + M * (E + 1) := by
    have hMsucc :
        M * (q + 1) =
          M * (q - E) + M * (E + 1) := by
      have hsum : q - E + (E + 1) = q + 1 := by omega
      exact
        (congrArg (fun t : ℕ => M * t) hsum.symm).trans
          (Nat.mul_add M (q - E) (E + 1))
    rw [hMsucc] at hcap
    exact hcap.2
  let q₀ : ℕ := q - (E + 1)
  let m : ℕ := C - M * (q - E)
  let a : ℕ := K - A * (q - E)
  let b : ℕ := Z - B * (q - E)
  have hm :
      m ≤ M * (E + 1) := by
    dsimp [m]
    omega
  have ha :
      a ≤ A * E + D := by
    dsimp [a]
    omega
  have hb :
      b ≤ B * E + E := by
    dsimp [b]
    omega
  have hC :
      C = affineCount M m q₀ := by
    unfold affineCount
    rw [show q₀ + 1 = q - E by simpa [q₀] using hq₀Succ]
    dsimp [m]
    omega
  have hK :
      K = affineCount A a q₀ := by
    unfold affineCount
    rw [show q₀ + 1 = q - E by simpa [q₀] using hq₀Succ]
    dsimp [a]
    omega
  have hZ :
      Z = affineCount B b q₀ := by
    unfold affineCount
    rw [show q₀ + 1 = q - E by simpa [q₀] using hq₀Succ]
    dsimp [b]
    omega
  refine ⟨q₀, m, a, b, ?_, ?_, ?_, ?_, hC, hK, hZ⟩
  · simp [q₀, E]
  · simpa [dynamicCapOffsetMax, E] using hm
  · simpa [dynamicPositiveOffsetMax, E, D] using ha
  · simpa [dynamicZeroOffsetMax, E] using hb

/-- A single threshold gives both the competitive core inequality and the
cap-deferral inequality for every dynamic quota window. -/
theorem eventually_dynamicQuota_ratio_and_deferral
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ C H,
      DynamicQuotaWindow M A B q C H →
        target *
            mixedFiniteOffline u C
              (tailPositiveCount A B H)
              (tailZeroCount A B H) ≤
          mixedFiniteOnline u C
            (tailPositiveCount A B H)
            (tailZeroCount A B H) ∧
        0 ≤
          ((tailPositiveCount A B H +
              tailZeroCount A B H : ℕ) : ℝ) * (u - 1) -
            (harmonicFutureLevels
              (tailZeroCount A B H : ℝ) 0
              (tailPositiveCount A B H)).sum -
            C := by
  have hall :=
    eventually_mixedFinite_ratio_and_deferral_bounded_offsets
      hM hA hB htarget hu hgap
      (dynamicCapOffsetMax M A B)
      (dynamicPositiveOffsetMax M A B)
      (dynamicZeroOffsetMax M A B)
  obtain ⟨Q₀, hQ₀⟩ :=
    Filter.eventually_atTop.1 hall
  let E := dynamicOffsetShift M A B
  let Q := Q₀ + E + 1
  refine ⟨Q, ?_⟩
  intro q hq C H hwindow
  have hshift : E + 1 ≤ q := by
    dsimp [Q] at hq
    omega
  obtain ⟨q₀, m, a, b, hq₀, hm, ha, hb,
      hC, hK, hZ⟩ :=
    dynamicQuota_affine_representation
      hM hA hB (by simpa [E] using hshift) hwindow
  have hq₀Large : Q₀ ≤ q₀ := by
    dsimp [Q] at hq
    rw [hq₀]
    omega
  have hresult :=
    hQ₀ q₀ hq₀Large m hm a ha b hb
  simpa [hC, hK, hZ] using hresult

/-- Eventual competitive estimate with the coarse physical-exchange
remainder included.  Above the common threshold the deferral margin is
nonnegative, hence this remainder is exactly zero. -/
theorem eventually_dynamicQuota_ratio_with_exchangeRemainder
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ C H,
      DynamicQuotaWindow M A B q C H →
        target *
              mixedFiniteOffline u C
                (tailPositiveCount A B H)
                (tailZeroCount A B H) +
            dynamicCapExchangeRemainder u A B C H ≤
          mixedFiniteOnline u C
            (tailPositiveCount A B H)
            (tailZeroCount A B H) := by
  obtain ⟨Q, hQ⟩ :=
    eventually_dynamicQuota_ratio_and_deferral
      hM hA hB htarget hu hgap
  refine ⟨Q, ?_⟩
  intro q hq C H hwindow
  have hresult := hQ q hq C H hwindow
  have hmargin :
      0 ≤ dynamicDeferralMargin u A B C H := by
    simpa [dynamicDeferralMargin] using hresult.2
  have hremainder :
      dynamicCapExchangeRemainder u A B C H = 0 := by
    unfold dynamicCapExchangeRemainder
    rw [max_eq_left (neg_nonpos.mpr hmargin)]
    ring
  rw [hremainder, add_zero]
  exact hresult.1

/-- Below a fixed integral scale `Q`, the coarse exchange remainder is
bounded solely in terms of `Q` and the three integral parameters. -/
theorem dynamicCapExchangeRemainder_below_scale_bound
    {u : ℝ} {M A B q C H Q : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (hq : q < Q)
    (hwindow : DynamicQuotaWindow M A B q C H) :
    dynamicCapExchangeRemainder u A B C H ≤
      dynamicCapExchangeRemainderBound M A B Q := by
  have hqSucc : q + 1 ≤ Q := by omega
  have hsize :
      C + H < (M + A + B) * Q :=
    hwindow.scaleUpper.trans_le
      (Nat.mul_le_mul_left (M + A + B) hqSucc)
  have hC : C ≤ (M + A + B) * Q := by omega
  have hrem :=
    dynamicCapExchangeRemainder_le_sq
      (u := u) (A := A) (B := B) (C := C) (H := H)
      hB hraw
  have hcast :
      (C : ℝ) ≤ (((M + A + B) * Q : ℕ) : ℝ) := by
    exact_mod_cast hC
  unfold dynamicCapExchangeRemainderBound
  nlinarith [sq_nonneg
    ((((M + A + B) * Q : ℕ) : ℝ) - (C : ℝ))]

/-- Ratio-only form matching the input expected by
`exists_size_closing_eventual_mixed_core`. -/
theorem eventually_dynamicQuota_ratio
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ C H,
      DynamicQuotaWindow M A B q C H →
        target *
            mixedFiniteOffline u C
              (tailPositiveCount A B H)
              (tailZeroCount A B H) ≤
          mixedFiniteOnline u C
            (tailPositiveCount A B H)
            (tailZeroCount A B H) := by
  obtain ⟨Q, hQ⟩ :=
    eventually_dynamicQuota_ratio_and_deferral
      hM hA hB htarget hu hgap
  exact ⟨Q, fun q hq C H hwindow =>
    (hQ q hq C H hwindow).1⟩

/-- The eventual dynamic-quota estimate closes at one arbitrarily large
ambient size: a bounded-scale mixed core is absorbed by the initial
raw-zero prefix. -/
theorem exists_size_closing_dynamicQuota
    {u c : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hu : 1 ≤ u) (hc : 0 ≤ c) (huc : 0 < u - c)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (htarget :
      c <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hdeferral :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      ∀ v C H q,
        n = v + C + H →
        DynamicQuotaWindow M A B q C H →
        0 ≤
          mixedFiniteOnline u C
              (tailPositiveCount A B H)
              (tailZeroCount A B H) -
            c *
              mixedFiniteOffline u C
                (tailPositiveCount A B H)
                (tailZeroCount A B H) +
            (u - c) * mixedPrefixZeroOffline v (C + H) := by
  apply exists_size_closing_eventual_mixed_core
    hB hu hc huc hraw
    (DynamicQuotaWindow M A B)
  · exact eventually_dynamicQuota_ratio
      hM hA hB htarget (zero_lt_one.trans_le hu) hdeferral
  · intro q C H hwindow
    exact hwindow.scaleUpper

/-- Remainder-aware form used by the physical cap/tail exchange. -/
theorem exists_size_closing_dynamicQuota_with_exchangeRemainder
    {u c : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hu : 1 ≤ u) (hc : 0 ≤ c) (huc : 0 < u - c)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (htarget :
      c <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hdeferral :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ)) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      ∀ v C H q,
        n = v + C + H →
        DynamicQuotaWindow M A B q C H →
        0 ≤
          mixedFiniteOnline u C
              (tailPositiveCount A B H)
              (tailZeroCount A B H) -
            c *
              mixedFiniteOffline u C
                (tailPositiveCount A B H)
                (tailZeroCount A B H) +
            (u - c) * mixedPrefixZeroOffline v (C + H) -
            dynamicCapExchangeRemainder u A B C H := by
  exact
    exists_size_closing_eventual_mixed_core_with_remainder
      (M := M) (A := A) (B := B)
      hB hu hc huc hraw
      (DynamicQuotaWindow M A B)
      (fun _q C H => dynamicCapExchangeRemainder u A B C H)
      (eventually_dynamicQuota_ratio_with_exchangeRemainder
        hM hA hB htarget (zero_lt_one.trans_le hu) hdeferral)
      (dynamicCapExchangeRemainderBound M A B)
      (by
        intro Q q C H hq hwindow
        exact dynamicCapExchangeRemainder_below_scale_bound
          hB hraw hq hwindow)
      (by
        intro q C H hwindow
        exact hwindow.scaleUpper)

/-- Algebraic endpoint used when the first crossing consumes the entire
remaining tail.  The remainder-aware canonical gap implies the literal
raw/cap block inequality supplied by the zero-tail runtime accounting. -/
theorem zeroTail_ratio_le_physical_of_exchange_gap
    {u c : ℝ} {A B v C : ℕ}
    (hgap :
      0 ≤
        mixedFiniteOnline u C 0 0 -
          c * mixedFiniteOffline u C 0 0 +
          (u - c) * mixedPrefixZeroOffline v C -
          dynamicCapExchangeRemainder u A B C 0) :
    c * mixedExtendedFiniteOffline u v C 0 0 ≤
      prefixCost
        (List.replicate v u ++ List.replicate C (1 + u)) := by
  have htri : 0 ≤ triangular C := by
    unfold triangular
    positivity
  simp [dynamicCapExchangeRemainder, dynamicDeferralMargin,
    tailPositiveCount, tailZeroCount, mixedFiniteOnline,
    mixedFiniteOffline, mixedExtendedFiniteOffline,
    harmonicFiniteOnline, harmonicFiniteOffline,
    harmonicDynamicPotential, harmonicUnfinished,
    mixedPrefixZeroOffline, harmonicFutureLevels,
    prefixCost_append, prefixCost_replicate] at hgap ⊢
  push_cast at hgap ⊢
  nlinarith

/-- The completely raw endpoint (`C = H = 0`) needs no quota window. -/
theorem zeroTail_zeroCap_ratio_le_physical
    {u c : ℝ} {v : ℕ} (hcu : c ≤ u) :
    c * mixedExtendedFiniteOffline u v 0 0 0 ≤
      prefixCost (List.replicate v u) := by
  have htri : 0 ≤ triangular v := by
    unfold triangular
    positivity
  simp [mixedExtendedFiniteOffline, mixedPrefixZeroOffline,
    mixedFiniteOffline, harmonicFiniteOffline,
    harmonicFutureLevels, prefixCost_replicate]
  exact mul_le_mul_of_nonneg_right hcu htri

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
