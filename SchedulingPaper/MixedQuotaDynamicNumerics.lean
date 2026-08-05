import SchedulingPaper.MixedQuotaRounding
import SchedulingPaper.MixedQuotaTerminalAccounting
import Mathlib.Tactic

/-!
# Uniform numerical bounds for the dynamic mixed quota

The crossing scale of the operational mixed construction depends on the
strategy.  This file records the coarse estimates needed to separate that
dependence from the asymptotic ratio calculation.

The main elementary point is that every raw-safe mixed effective length is
between zero and the finite cap.  Consequently the whole mixed offline
benchmark is at most the all-cap triangular benchmark.  If the crossing
scale stays bounded, the positive raw-prefix correction can therefore
absorb the complete mixed block.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-- On the strict interior of the mixed branch, the target ratio is
strictly below the physical cap. -/
theorem mixedFiniteCurve_lt_cap_of_strict_lower
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ)) :
    mixedFiniteCurve u < (u : ℝ) := by
  have hparam : mixedUpperLowerEndpoint < u := by
    exact huLower
  have hcurve :=
    mixedFiniteCurve_strictAnti hparam
  rw [mixedFiniteCurve_lowerEndpoint] at hcurve
  linarith

theorem mixedTarget_cap_gap
    (u : MixedUpperDomain)
    (huLower : goldenRatio + 2 < (u : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    0 < (u : ℝ) - (mixedFiniteCurve u - ε) := by
  linarith [mixedFiniteCurve_lt_cap_of_strict_lower u huLower]

/-- Clear the positive denominator in the normalized one-job crossing
window. -/
theorem quota_window_clear_denominator
    {β : ℝ} {C S : ℕ} (hS : 0 < S)
    (hlower : β ≤ (C : ℝ) / (S : ℝ))
    (hupper :
      (C : ℝ) / (S : ℝ) - β < 1 / (S : ℝ)) :
    β * (S : ℝ) ≤ C ∧
      (C : ℝ) < β * (S : ℝ) + 1 := by
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  constructor
  · exact (le_div_iff₀ hSreal).mp hlower
  · have hquot :
        (C : ℝ) / (S : ℝ) <
          β + 1 / (S : ℝ) := by
      linarith
    have hscaled :=
      (div_lt_iff₀ hSreal).mp hquot
    have hinv : (1 / (S : ℝ)) * (S : ℝ) = 1 := by
      field_simp
    nlinarith

/-- A list bounded above by `u` has prefix cost at most the all-`u`
triangular cost. -/
theorem prefixCost_le_constant_triangular
    {u : ℝ} (xs : List ℝ)
    (hupper : ∀ x ∈ xs, x ≤ u) :
    prefixCost xs ≤ u * triangular xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : x ≤ u := hupper x (by simp)
      have htail : ∀ y ∈ xs, y ≤ u := by
        intro y hy
        exact hupper y (by simp [hy])
      have hcoeff : 0 ≤ (xs.length + 1 : ℝ) := by positivity
      calc
        prefixCost (x :: xs) =
            (xs.length + 1 : ℝ) * x + prefixCost xs := rfl
        _ ≤ (xs.length + 1 : ℝ) * u +
            u * triangular xs.length :=
          add_le_add
            (mul_le_mul_of_nonneg_left hx hcoeff)
            (ih htail)
        _ = u * triangular (x :: xs).length := by
          simp only [List.length_cons, triangular_succ]
          push_cast
          ring

/-- Every entry of a raw-safe mixed candidate lies in `[0,u]`. -/
theorem mixedEffectiveCandidate_mem_bounds
    {u : ℝ} {C K Z : ℕ}
    (hZ : 0 < Z)
    (hu : 1 ≤ u)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u) :
    ∀ x ∈ mixedEffectiveCandidate u C K Z,
      0 ≤ x ∧ x ≤ u := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · have hxEq : x = 1 := (List.mem_replicate.mp hx).2
      subst x
      exact ⟨zero_le_one, hu⟩
    · rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨L, hL, rfl⟩
      have hLK : L ≤ K :=
        Nat.le_of_lt (by simpa using hL)
      have hlower : 1 ≤ harmonicLevel (Z : ℝ) 0 L := by
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) L
      exact ⟨by linarith, hsafe L hLK⟩
  · have hxEq : x = u := (List.mem_replicate.mp hx).2
    subst x
    exact ⟨zero_le_one.trans hu, le_rfl⟩

/-- Raw safety bounds the exact mixed offline benchmark by the cost of
making all jobs have effective length `u`. -/
theorem mixedFiniteOffline_nonneg_le_cap
    {u : ℝ} {C K Z : ℕ} (hZ : 0 < Z)
    (hu : 1 ≤ u)
    (hsafe :
      ∀ L ≤ K, 1 + harmonicLevel (Z : ℝ) 0 L ≤ u) :
    0 ≤ mixedFiniteOffline u C K Z ∧
      mixedFiniteOffline u C K Z ≤
        u * triangular (C + K + Z) := by
  have hbounds :=
    mixedEffectiveCandidate_mem_bounds
      (C := C) (K := K) (Z := Z) hZ hu hsafe
  have heq :=
    prefixCost_mixedEffectiveCandidate hZ u C K
  constructor
  · rw [← heq]
    have hnonneg :=
      prefixCost_quadratic_lower
        (mixedEffectiveCandidate u C K Z)
        (fun x hx => (hbounds x hx).1)
    simpa using hnonneg
  · rw [← heq]
    simpa using
      prefixCost_le_constant_triangular
        (mixedEffectiveCandidate u C K Z)
        (fun x hx => (hbounds x hx).2)

/-- The zero-tail mixed benchmark is just the capped triangular block. -/
theorem mixedFiniteOffline_zero_tail
    (u : ℝ) (C : ℕ) :
    mixedFiniteOffline u C 0 0 = u * triangular C := by
  simp [mixedFiniteOffline, harmonicFiniteOffline,
    harmonicFutureLevels, triangular]

/-- The dynamically rounded tail always satisfies the same all-cap upper
bound, including the degenerate `H = 0` case. -/
theorem mixedDynamicFiniteOffline_nonneg_le_cap
    {u : ℝ} {C A B H : ℕ}
    (hB : 0 < B) (hu : 1 ≤ u)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    let K := MixedQuotaOracle.tailPositiveCount A B H
    let Z := MixedQuotaOracle.tailZeroCount A B H
    0 ≤ mixedFiniteOffline u C K Z ∧
      mixedFiniteOffline u C K Z ≤
        u * triangular (C + H) := by
  dsimp only
  by_cases hH : H = 0
  · subst H
    simp only [MixedQuotaOracle.tailPositiveCount,
      MixedQuotaOracle.tailZeroCount, Nat.mul_zero, Nat.zero_div,
      Nat.sub_zero, add_zero]
    rw [mixedFiniteOffline_zero_tail]
    exact
      ⟨mul_nonneg (zero_le_one.trans hu)
        (by unfold triangular; positivity), le_rfl⟩
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    have hZ :
        0 < MixedQuotaOracle.tailZeroCount A B H :=
      MixedQuotaOracle.tailZeroCount_pos hB hHpos
    have hsafe :=
      MixedQuotaOracle.dynamicTail_static_rawSafe
        hB hHpos hraw
    have hbound :=
      mixedFiniteOffline_nonneg_le_cap
        (C := C) hZ hu hsafe
    have hsplit :=
      MixedQuotaOracle.tail_split A B H
    have hsize :
        C + MixedQuotaOracle.tailPositiveCount A B H +
            MixedQuotaOracle.tailZeroCount A B H =
          C + H := by
      omega
    simpa [hsize] using hbound

/-- The exact mixed online benchmark is nonnegative whenever its offline
part is nonnegative. -/
theorem mixedFiniteOnline_nonneg_of_offline
    {u : ℝ} {C K Z : ℕ}
    (hoffline : 0 ≤ mixedFiniteOffline u C K Z) :
    0 ≤ mixedFiniteOnline u C K Z := by
  rw [mixedFiniteOnline_eq_offline_add_advantage]
  have hadvantage : 0 ≤ harmonicFiniteAdvantage K Z := by
    unfold harmonicFiniteAdvantage
    by_cases hK : K = 0
    · simp [hK]
    · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
      have hfactor :
          0 ≤ (K : ℝ) + 2 * (Z : ℝ) - 1 := by
        have hKone : (1 : ℝ) ≤ K := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hK)
        have hZzero : 0 ≤ (Z : ℝ) := by positivity
        linarith
      exact div_nonneg
        (mul_nonneg (by positivity) hfactor) (by norm_num)
  have hcap : 0 ≤ (C : ℝ) * (C + K + Z : ℕ) := by positivity
  linarith

theorem mixedPrefixZeroOffline_nonneg (v S : ℕ) :
    0 ≤ mixedPrefixZeroOffline v S := by
  unfold mixedPrefixZeroOffline triangular
  positivity

theorem triangular_le_mixedPrefixZeroOffline (v S : ℕ) :
    triangular v ≤ mixedPrefixZeroOffline v S := by
  unfold mixedPrefixZeroOffline
  have hcross : 0 ≤ (v : ℝ) * (S : ℝ) := by positivity
  linarith

/-- Any prescribed nonnegative real amount is eventually dominated by a
positive multiple of a triangular number. -/
theorem exists_nat_mul_triangular_ge
    {a R : ℝ} (ha : 0 < a) :
    ∃ T : ℕ, R ≤ a * triangular T := by
  obtain ⟨T, hT⟩ := exists_nat_ge (max 1 (R / a))
  have hTone : (1 : ℝ) ≤ T :=
    le_trans (le_max_left _ _) hT
  have hTR : R / a ≤ (T : ℝ) :=
    le_trans (le_max_right _ _) hT
  have htri : (T : ℝ) ≤ triangular T := by
    unfold triangular
    have hT0 : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  have hdiv : R ≤ a * (T : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ ha).mp hTR
  exact ⟨T, hdiv.trans (mul_le_mul_of_nonneg_left htri ha.le)⟩

/-- If the non-prefix mixed block has bounded size, a sufficiently long
raw-zero prefix absorbs its entire possible competitive deficit. -/
theorem mixedRawPrefix_absorbs_bounded_core
    {u c : ℝ} {C K Z v Smax T : ℕ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hgap : 0 < u - c)
    (hsize : C + K + Z ≤ Smax)
    (hv : T ≤ v)
    (hT :
      c * u * triangular Smax ≤
        (u - c) * triangular T)
    (hofflineUpper :
      mixedFiniteOffline u C K Z ≤
        u * triangular (C + K + Z))
    (honline : 0 ≤ mixedFiniteOnline u C K Z) :
    0 ≤
      mixedFiniteOnline u C K Z -
        c * mixedFiniteOffline u C K Z +
        (u - c) *
          mixedPrefixZeroOffline v (C + K + Z) := by
  have htriSize :
      triangular (C + K + Z) ≤ triangular Smax :=
    triangular_mono hsize
  have hofflineBound :
      c * mixedFiniteOffline u C K Z ≤
        c * u * triangular Smax := by
    calc
      c * mixedFiniteOffline u C K Z ≤
          c * (u * triangular (C + K + Z)) :=
        mul_le_mul_of_nonneg_left hofflineUpper hc
      _ ≤ c * (u * triangular Smax) := by
        have :=
          mul_le_mul_of_nonneg_left htriSize hu
        exact mul_le_mul_of_nonneg_left this hc
      _ = c * u * triangular Smax := by ring
  have hprefix :
      (u - c) * triangular T ≤
        (u - c) *
          mixedPrefixZeroOffline v (C + K + Z) := by
    have htriV : triangular T ≤ triangular v :=
      triangular_mono hv
    have hbase :
        triangular T ≤
          mixedPrefixZeroOffline v (C + K + Z) :=
      htriV.trans (triangular_le_mixedPrefixZeroOffline _ _)
    exact mul_le_mul_of_nonneg_left hbase hgap.le
  linarith

/-- Remainder-aware form of
`mixedRawPrefix_absorbs_bounded_core`.  It is useful when the operational
cap exchange exposes a nonnegative deferral deficit instead of assuming
that the deficit vanishes. -/
theorem mixedRawPrefix_absorbs_bounded_core_with_remainder
    {u c remainder remainderMax : ℝ}
    {C K Z v Smax T : ℕ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hgap : 0 < u - c)
    (hsize : C + K + Z ≤ Smax)
    (hv : T ≤ v)
    (hT :
      c * u * triangular Smax + remainderMax ≤
        (u - c) * triangular T)
    (hremainder : remainder ≤ remainderMax)
    (hofflineUpper :
      mixedFiniteOffline u C K Z ≤
        u * triangular (C + K + Z))
    (honline : 0 ≤ mixedFiniteOnline u C K Z) :
    0 ≤
      mixedFiniteOnline u C K Z -
        c * mixedFiniteOffline u C K Z +
        (u - c) *
          mixedPrefixZeroOffline v (C + K + Z) -
        remainder := by
  have htriSize :
      triangular (C + K + Z) ≤ triangular Smax :=
    triangular_mono hsize
  have hofflineBound :
      c * mixedFiniteOffline u C K Z ≤
        c * u * triangular Smax := by
    calc
      c * mixedFiniteOffline u C K Z ≤
          c * (u * triangular (C + K + Z)) :=
        mul_le_mul_of_nonneg_left hofflineUpper hc
      _ ≤ c * (u * triangular Smax) := by
        have :=
          mul_le_mul_of_nonneg_left htriSize hu
        exact mul_le_mul_of_nonneg_left this hc
      _ = c * u * triangular Smax := by ring
  have hprefix :
      (u - c) * triangular T ≤
        (u - c) *
          mixedPrefixZeroOffline v (C + K + Z) := by
    have htriV : triangular T ≤ triangular v :=
      triangular_mono hv
    have hbase :
        triangular T ≤
          mixedPrefixZeroOffline v (C + K + Z) :=
      htriV.trans (triangular_le_mixedPrefixZeroOffline _ _)
    exact mul_le_mul_of_nonneg_left hbase hgap.le
  linarith

/-- An eventual lower bound for the dynamically rounded mixed core extends
to one arbitrarily large ambient size.  Large crossing scales use the core
bound directly; all smaller scales form a bounded family and are absorbed
by the raw-zero prefix.

`Good q C H` deliberately abstracts the exact quota-window hypotheses.  A
later crossing lemma only has to provide the displayed upper scale bound
and the eventual core inequality. -/
theorem exists_size_closing_eventual_mixed_core
    {u c : ℝ} {M A B : ℕ}
    (hB : 0 < B) (hu : 1 ≤ u) (hc : 0 ≤ c)
    (hgap : 0 < u - c)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (Good : ℕ → ℕ → ℕ → Prop)
    (hcore :
      ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ C H,
        Good q C H →
          c *
              mixedFiniteOffline u C
                (MixedQuotaOracle.tailPositiveCount A B H)
                (MixedQuotaOracle.tailZeroCount A B H) ≤
            mixedFiniteOnline u C
              (MixedQuotaOracle.tailPositiveCount A B H)
              (MixedQuotaOracle.tailZeroCount A B H))
    (hscaleUpper :
      ∀ q C H, Good q C H →
        C + H < (M + A + B) * (q + 1)) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      ∀ v C H q,
        n = v + C + H →
        Good q C H →
        0 ≤
          mixedFiniteOnline u C
              (MixedQuotaOracle.tailPositiveCount A B H)
              (MixedQuotaOracle.tailZeroCount A B H) -
            c *
              mixedFiniteOffline u C
                (MixedQuotaOracle.tailPositiveCount A B H)
                (MixedQuotaOracle.tailZeroCount A B H) +
            (u - c) * mixedPrefixZeroOffline v (C + H) := by
  intro N
  obtain ⟨Q, hQ⟩ := hcore
  let Smax : ℕ := (M + A + B) * Q
  obtain ⟨T, hT⟩ :=
    exists_nat_mul_triangular_ge
      (a := u - c)
      (R := c * u * triangular Smax) hgap
  let n : ℕ := max N (T + Smax)
  refine ⟨n, Nat.le_max_left _ _, ?_⟩
  intro v C H q hn hgood
  let K := MixedQuotaOracle.tailPositiveCount A B H
  let Z := MixedQuotaOracle.tailZeroCount A B H
  have hsplit :
      K + Z = H := by
    simpa [K, Z] using
      MixedQuotaOracle.tail_split A B H
  by_cases hlarge : Q ≤ q
  · have hcoreBound :=
      hQ q hlarge C H hgood
    have hprefixNonneg :
        0 ≤ (u - c) * mixedPrefixZeroOffline v (C + H) :=
      mul_nonneg hgap.le
        (mixedPrefixZeroOffline_nonneg v (C + H))
    linarith
  · have hq : q < Q := Nat.lt_of_not_ge hlarge
    have hqSucc : q + 1 ≤ Q := by omega
    have hscale :
        C + H < Smax := by
      exact (hscaleUpper q C H hgood).trans_le
        (Nat.mul_le_mul_left (M + A + B) hqSucc)
    have hsize : C + H ≤ Smax :=
      Nat.le_of_lt hscale
    have hnLarge : T + Smax ≤ n :=
      Nat.le_max_right _ _
    have hv : T ≤ v := by
      omega
    have hoffline :=
      mixedDynamicFiniteOffline_nonneg_le_cap
        (C := C) (H := H) hB hu hraw
    have honline :=
      mixedFiniteOnline_nonneg_of_offline hoffline.1
    have hcoreEq : C + K + Z = C + H := by
      omega
    have hcoreSize : C + K + Z ≤ Smax := by
      omega
    have hofflineUpper :
        mixedFiniteOffline u C K Z ≤
          u * triangular (C + K + Z) := by
      rw [hcoreEq]
      simpa [K, Z] using hoffline.2
    have habsorb :=
      mixedRawPrefix_absorbs_bounded_core
        (C := C) (K := K) (Z := Z)
        (v := v) (Smax := Smax) (T := T)
        (zero_le_one.trans hu) hc hgap hcoreSize hv hT
        hofflineUpper
        honline
    rw [hcoreEq] at habsorb
    simpa [K, Z] using habsorb

/-- Remainder-aware uniform-size closure.

For large quota scales the supplied eventual estimate absorbs the remainder
already.  Below its threshold, both the mixed-core deficit and any uniformly
bounded operational exchange remainder are absorbed by the initial raw-zero
prefix.  The bound is allowed to depend on the eventual threshold `Q`, since
only scales `q < Q` enter this branch. -/
theorem exists_size_closing_eventual_mixed_core_with_remainder
    {u c : ℝ} {M A B : ℕ}
    (hB : 0 < B) (hu : 1 ≤ u) (hc : 0 ≤ c)
    (hgap : 0 < u - c)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (Good : ℕ → ℕ → ℕ → Prop)
    (remainder : ℕ → ℕ → ℕ → ℝ)
    (hcore :
      ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ C H,
        Good q C H →
          c *
                mixedFiniteOffline u C
                  (MixedQuotaOracle.tailPositiveCount A B H)
                  (MixedQuotaOracle.tailZeroCount A B H) +
              remainder q C H ≤
            mixedFiniteOnline u C
              (MixedQuotaOracle.tailPositiveCount A B H)
              (MixedQuotaOracle.tailZeroCount A B H))
    (remainderBound : ℕ → ℝ)
    (hremBound :
      ∀ Q q C H, q < Q → Good q C H →
        remainder q C H ≤ remainderBound Q)
    (hscaleUpper :
      ∀ q C H, Good q C H →
        C + H < (M + A + B) * (q + 1)) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      ∀ v C H q,
        n = v + C + H →
        Good q C H →
        0 ≤
          mixedFiniteOnline u C
              (MixedQuotaOracle.tailPositiveCount A B H)
              (MixedQuotaOracle.tailZeroCount A B H) -
            c *
              mixedFiniteOffline u C
                (MixedQuotaOracle.tailPositiveCount A B H)
                (MixedQuotaOracle.tailZeroCount A B H) +
            (u - c) * mixedPrefixZeroOffline v (C + H) -
            remainder q C H := by
  intro N
  obtain ⟨Q, hQ⟩ := hcore
  let Smax : ℕ := (M + A + B) * Q
  obtain ⟨T, hT⟩ :=
    exists_nat_mul_triangular_ge
      (a := u - c)
      (R := c * u * triangular Smax + remainderBound Q) hgap
  let n : ℕ := max N (T + Smax)
  refine ⟨n, Nat.le_max_left _ _, ?_⟩
  intro v C H q hn hgood
  let K := MixedQuotaOracle.tailPositiveCount A B H
  let Z := MixedQuotaOracle.tailZeroCount A B H
  have hsplit :
      K + Z = H := by
    simpa [K, Z] using
      MixedQuotaOracle.tail_split A B H
  by_cases hlarge : Q ≤ q
  · have hcoreBound :=
      hQ q hlarge C H hgood
    have hprefixNonneg :
        0 ≤ (u - c) * mixedPrefixZeroOffline v (C + H) :=
      mul_nonneg hgap.le
        (mixedPrefixZeroOffline_nonneg v (C + H))
    linarith
  · have hq : q < Q := Nat.lt_of_not_ge hlarge
    have hqSucc : q + 1 ≤ Q := by omega
    have hscale :
        C + H < Smax := by
      exact (hscaleUpper q C H hgood).trans_le
        (Nat.mul_le_mul_left (M + A + B) hqSucc)
    have hsize : C + H ≤ Smax :=
      Nat.le_of_lt hscale
    have hnLarge : T + Smax ≤ n :=
      Nat.le_max_right _ _
    have hv : T ≤ v := by
      omega
    have hoffline :=
      mixedDynamicFiniteOffline_nonneg_le_cap
        (C := C) (H := H) hB hu hraw
    have honline :=
      mixedFiniteOnline_nonneg_of_offline hoffline.1
    have hcoreEq : C + K + Z = C + H := by
      omega
    have hcoreSize : C + K + Z ≤ Smax := by
      omega
    have hofflineUpper :
        mixedFiniteOffline u C K Z ≤
          u * triangular (C + K + Z) := by
      rw [hcoreEq]
      simpa [K, Z] using hoffline.2
    have habsorb :=
      mixedRawPrefix_absorbs_bounded_core_with_remainder
        (C := C) (K := K) (Z := Z)
        (v := v) (Smax := Smax) (T := T)
        (remainder := remainder q C H)
        (remainderMax := remainderBound Q)
        (zero_le_one.trans hu) hc hgap hcoreSize hv hT
        (hremBound Q q C H hq hgood)
        hofflineUpper honline
    rw [hcoreEq] at habsorb
    simpa [K, Z] using habsorb

end LowerBound

end

end SchedulingPaper
