import SchedulingPaper.UTEStatusEndpointReduction
import SchedulingPaper.UpperBoundAssembly
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Tactic

/-!
# Finite-word bridge for the operational UTE endpoint reduction

This file removes one suffix coordinate to absorb the floor error in the
forced-prefix size, bounds the removed coordinate by a linear term, and
feeds the remaining endpoint counts to `uteFinite_pairExcess_le_normalized`.
-/

namespace SchedulingPaper

noncomputable section

open Set

theorem listPairObjective_remove_suffix_head
    {α : Type*} (pair : α → α → ℝ)
    (front rest : List α) (exception : α) :
    listPairObjective (fun _ => 0) pair
        (front ++ exception :: rest) =
      listPairObjective (fun _ => 0) pair (front ++ rest) +
        (front.map (fun value => pair value exception)).sum +
        (rest.map (pair exception)).sum := by
  induction front with
  | nil =>
      simp [listPairObjective]
      ring
  | cons value tail ih =>
      simp only [List.cons_append, listPairObjective,
        List.map_cons, List.sum_cons, List.map_append,
        List.sum_append]
      rw [ih]
      ring

theorem uteALGPairCharge_le_linearCap
    {s : ℝ} (hs1 : 1 ≤ s) (left right : UTEEndpoint) :
    uteALGPairCharge s left right ≤ s + 3 := by
  have hone : (1 : ℝ) ≤ s + 1 := by linarith
  cases left <;> cases right <;>
    simp [uteALGPairCharge, uteEndpointProcessing,
      UTEEndpoint.IsImmediate, min_eq_left hone,
      min_eq_right hone] <;> linarith

theorem uteFixedSelfExcess_endpoint_le
    {s : ℝ} (hs1 : 1 ≤ s) (endpoint : UTEEndpoint) :
    uteFixedSelfExcessAt s (uteEndpointProcessing s endpoint) ≤
      s + 2 := by
  have hs : 0 < s := zero_lt_one.trans_le hs1
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  have heff :
      0 ≤ uteEffectiveAt s (uteEndpointProcessing s endpoint) := by
    cases endpoint <;>
      simp [uteEffectiveAt, uteEndpointProcessing] <;> linarith
  have hp :
      uteEndpointProcessing s endpoint ≤ s + 1 := by
    cases endpoint <;>
      simp [uteEndpointProcessing] <;> linarith
  unfold uteFixedSelfExcessAt
  nlinarith [mul_nonneg hrho heff]

theorem uteEndpoint_self_sum_le
    {n : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (endpoint : Fin n → UTEEndpoint) :
    (∑ i,
      uteFixedSelfExcessAt s
        (uteEndpointProcessing s (endpoint i))) ≤
      (s + 2) * n := by
  calc
    (∑ i,
      uteFixedSelfExcessAt s
        (uteEndpointProcessing s (endpoint i))) ≤
        ∑ _i : Fin n, (s + 2) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact uteFixedSelfExcess_endpoint_le hs1 (endpoint i)
    _ = (s + 2) * n := by
      simp
      ring

theorem sum_map_uteALGPairCharge_le
    {s : ℝ} (hs1 : 1 ≤ s) (left : UTEEndpoint) :
    ∀ values : List UTEEndpoint,
      (values.map (uteALGPairCharge s left)).sum ≤
        values.length * (s + 3) := by
  intro values
  calc
    (values.map (uteALGPairCharge s left)).sum ≤
        (values.map (fun _ => s + 3)).sum := by
      apply List.sum_le_sum
      intro right _hright
      exact uteALGPairCharge_le_linearCap hs1 left right
    _ = values.length * (s + 3) := by
      simp
      ring

theorem sum_map_uteALGPairCharge_right_le
    {s : ℝ} (hs1 : 1 ≤ s) (right : UTEEndpoint) :
    ∀ values : List UTEEndpoint,
      (values.map (fun left =>
        uteALGPairCharge s left right)).sum ≤
        values.length * (s + 3) := by
  intro values
  calc
    (values.map (fun left =>
        uteALGPairCharge s left right)).sum ≤
        (values.map (fun _ => s + 3)).sum := by
      apply List.sum_le_sum
      intro left _hleft
      exact uteALGPairCharge_le_linearCap hs1 left right
    _ = values.length * (s + 3) := by
      simp
      ring

theorem sum_map_uteOPTPairCharge_nonneg_left
    {s : ℝ} (hs0 : 0 ≤ s) (left : UTEEndpoint) :
    ∀ values : List UTEEndpoint,
      0 ≤ (values.map (uteOPTPairCharge s left)).sum := by
  intro values
  apply List.sum_nonneg
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨right, _hright, rfl⟩
  exact uteOPTPairCharge_nonneg hs0 left right

theorem sum_map_uteOPTPairCharge_nonneg_right
    {s : ℝ} (hs0 : 0 ≤ s) (right : UTEEndpoint) :
    ∀ values : List UTEEndpoint,
      0 ≤ (values.map (fun left =>
        uteOPTPairCharge s left right)).sum := by
  intro values
  apply List.sum_nonneg
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨left, _hleft, rfl⟩
  exact uteOPTPairCharge_nonneg hs0 left right

def uteForcedEndpointBlock {n : ℕ}
    (k : ℕ) (endpoint : Fin n → UTEEndpoint) :
    List UTEEndpoint :=
  (List.ofFn endpoint).take k

def uteSuffixEndpointBlock {n : ℕ}
    (k : ℕ) (endpoint : Fin n → UTEEndpoint) :
    List UTEEndpoint :=
  (List.ofFn endpoint).drop k

theorem uteEndpointBlocks_append
    {n : ℕ} (k : ℕ) (endpoint : Fin n → UTEEndpoint) :
    uteForcedEndpointBlock k endpoint ++
        uteSuffixEndpointBlock k endpoint =
      List.ofFn endpoint := by
  exact List.take_append_drop k (List.ofFn endpoint)

theorem uteForcedEndpointBlock_all_forced
    {n k : ℕ} (hk : k ≤ n)
    (endpoint : Fin n → UTEEndpoint)
    (hforced : ∀ i, i.val < k → (endpoint i).IsForced) :
    ∀ value ∈ uteForcedEndpointBlock k endpoint,
      value.IsForced := by
  intro value hvalue
  have htake :
      List.ofFn (Fin.take k hk endpoint) =
        uteForcedEndpointBlock k endpoint := by
    exact Fin.ofFn_take_eq_take_ofFn hk endpoint
  rw [← htake] at hvalue
  rcases List.mem_ofFn.mp hvalue with ⟨i, hi⟩
  rw [← hi]
  exact hforced (Fin.castLE hk i)
    (by simpa using i.isLt)

theorem uteSuffixEndpointBlock_all_suffix
    {n k : ℕ} (hk : k ≤ n)
    (endpoint : Fin n → UTEEndpoint)
    (hsuffix : ∀ i, k ≤ i.val → ¬ (endpoint i).IsForced) :
    ∀ value ∈ uteSuffixEndpointBlock k endpoint,
      ¬ value.IsForced := by
  intro value hvalue
  change value ∈ (List.ofFn endpoint).drop k at hvalue
  rcases List.mem_iff_get.mp hvalue with ⟨i, hi⟩
  have hilabel : k + i.val < n := by
    have hiBound := i.isLt
    simp only [List.length_drop, List.length_ofFn] at hiBound
    omega
  let label : Fin n := ⟨k + i.val, hilabel⟩
  have hlabel : k ≤ k + i.val := Nat.le_add_right k i.val
  have hget :
      ((List.ofFn endpoint).drop k).get i =
        endpoint label := by
    simp [label]
  have hvalueEq :
      value = endpoint label := by
    rw [← hi, hget]
  rw [hvalueEq]
  exact hsuffix label (by simpa [label] using hlabel)

theorem uteEndpoint_all_counts :
    ∀ values : List UTEEndpoint,
      values.count .forcedCap +
          values.count .forcedZero +
          values.count .cappedDeferred +
          values.count .boundaryDeferred +
          values.count .immediateOne +
          values.count .suffixZero =
        values.length := by
  intro values
  induction values with
  | nil =>
      simp
  | cons endpoint values ih =>
      cases endpoint <;> simp_all <;> omega

theorem uteEndpoint_forced_counts_eq_length
    (values : List UTEEndpoint)
    (hall : ∀ value ∈ values, value.IsForced) :
    values.count .forcedCap + values.count .forcedZero =
      values.length := by
  induction values with
  | nil =>
      simp
  | cons value values ih =>
      have hvalue := hall value (by simp)
      have htail :
          ∀ tail ∈ values, tail.IsForced := by
        intro tail htail
        exact hall tail (by simp [htail])
      have hi := ih htail
      cases value <;>
        simp [UTEEndpoint.IsForced] at hvalue ⊢ <;>
        omega

theorem uteEndpoint_suffix_forcedCap_count_zero
    (values : List UTEEndpoint)
    (hall : ∀ value ∈ values, ¬ value.IsForced) :
    values.count .forcedCap = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  have hnot := hall .forcedCap hmem
  simp [UTEEndpoint.IsForced] at hnot

theorem uteEndpoint_suffix_forcedZero_count_zero
    (values : List UTEEndpoint)
    (hall : ∀ value ∈ values, ¬ value.IsForced) :
    values.count .forcedZero = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  have hnot := hall .forcedZero hmem
  simp [UTEEndpoint.IsForced] at hnot

theorem uteEndpointWordExcess_le_reducedFiniteCore
    {n : ℕ} {s : ℝ} (hs1 : 1 ≤ s)
    (endpoint : Fin n → UTEEndpoint)
    (front rest : List UTEEndpoint) (exception : UTEEndpoint)
    (hword :
      List.ofFn endpoint = front ++ exception :: rest)
    (hfront : ∀ value ∈ front, value.IsForced)
    (hrest : ∀ value ∈ rest, ¬ value.IsForced) :
    let reduced := front ++ rest
    uteEndpointWordExcess s endpoint ≤
      uteFiniteALGCore s
          (reduced.count .forcedCap)
          (reduced.count .forcedZero)
          (reduced.count .cappedDeferred)
          (reduced.count .boundaryDeferred)
          (reduced.count .immediateOne)
          (reduced.count .suffixZero) -
        uteRho s *
          uteFiniteOPTCore s
            (reduced.count .forcedCap)
            (reduced.count .forcedZero)
            (reduced.count .cappedDeferred)
            (reduced.count .boundaryDeferred)
            (reduced.count .immediateOne)
            (reduced.count .suffixZero) +
        ((s + 2) + (s + 3)) * n := by
  dsimp only
  let reduced := front ++ rest
  have hs0 : 0 ≤ s := zero_le_one.trans hs1
  have hrho : 0 ≤ uteRho s :=
    (uteRho_pos (zero_lt_one.trans_le hs1)).le
  have hlengthNat :
      front.length + rest.length + 1 = n := by
    have hlength := congrArg List.length hword
    simp at hlength
    omega
  have hlength :
      (front.length : ℝ) + rest.length + 1 = n := by
    exact_mod_cast hlengthNat
  have hremovedALG :
      (front.map (fun value =>
          uteALGPairCharge s value exception)).sum +
          (rest.map (uteALGPairCharge s exception)).sum ≤
        (s + 3) * n := by
    have hfrontBound :=
      sum_map_uteALGPairCharge_right_le hs1 exception front
    have hrestBound :=
      sum_map_uteALGPairCharge_le hs1 exception rest
    have hcapNonneg : 0 ≤ s + 3 := by linarith
    nlinarith
  have hremovedOPT :
      0 ≤
        (front.map (fun value =>
          uteOPTPairCharge s value exception)).sum +
          (rest.map (uteOPTPairCharge s exception)).sum := by
    exact add_nonneg
      (sum_map_uteOPTPairCharge_nonneg_right hs0 exception front)
      (sum_map_uteOPTPairCharge_nonneg_left hs0 exception rest)
  have halgRemove :=
    listPairObjective_remove_suffix_head
      (uteALGPairCharge s) front rest exception
  have hoptRemove :=
    listPairObjective_remove_suffix_head
      (uteOPTPairCharge s) front rest exception
  have hcanonical :
      listPairObjective (fun _ => 0) (uteALGPairCharge s)
          reduced ≤
        listPairObjective (fun _ => 0)
          (uteCanonicalALGPairCharge s) reduced := by
    exact ute_listPairObjective_le_canonical
      hs0 front rest hfront hrest
  have hpair :
      listPairObjective (fun _ => 0) (uteALGPairCharge s)
          (front ++ exception :: rest) -
          uteRho s *
            listPairObjective (fun _ => 0)
              (uteOPTPairCharge s)
              (front ++ exception :: rest) ≤
        listPairObjective (fun _ => 0)
            (uteCanonicalALGPairCharge s) reduced -
          uteRho s *
            listPairObjective (fun _ => 0)
              (uteOPTPairCharge s) reduced +
          (s + 3) * n := by
    dsimp [reduced] at halgRemove hoptRemove hcanonical ⊢
    rw [halgRemove, hoptRemove]
    nlinarith [mul_nonneg hrho hremovedOPT]
  have hself := uteEndpoint_self_sum_le hs1 endpoint
  rw [uteEndpointWordExcess_eq_self_add_pairLists, hword]
  calc
    (∑ i,
          uteFixedSelfExcessAt s
            (uteEndpointProcessing s (endpoint i))) +
          listPairObjective (fun _ => 0)
              (uteALGPairCharge s)
              (front ++ exception :: rest) -
          uteRho s *
            listPairObjective (fun _ => 0)
              (uteOPTPairCharge s)
              (front ++ exception :: rest) ≤
        (s + 2) * n +
          (listPairObjective (fun _ => 0)
              (uteCanonicalALGPairCharge s) reduced -
            uteRho s *
              listPairObjective (fun _ => 0)
                (uteOPTPairCharge s) reduced +
            (s + 3) * n) := by
      linarith
    _ =
      uteFiniteALGCore s
          (reduced.count .forcedCap)
          (reduced.count .forcedZero)
          (reduced.count .cappedDeferred)
          (reduced.count .boundaryDeferred)
          (reduced.count .immediateOne)
          (reduced.count .suffixZero) -
        uteRho s *
          uteFiniteOPTCore s
            (reduced.count .forcedCap)
            (reduced.count .forcedZero)
            (reduced.count .cappedDeferred)
            (reduced.count .boundaryDeferred)
            (reduced.count .immediateOne)
            (reduced.count .suffixZero) +
        ((s + 2) + (s + 3)) * n := by
      rw [listPairObjective_canonicalALG_eq_finiteCore,
        listPairObjective_opt_eq_finiteCore]
      ring

theorem exists_uteEndpoint_normalized_bound
    {n k : ℕ} {s : ℝ} (hn : n ≠ 0) (hs1 : 1 ≤ s)
    (hk : k < n)
    (hkLower : (k : ℝ) ≤ uteB s * n)
    (hkUpper : uteB s * n < k + 1)
    (endpoint : Fin n → UTEEndpoint)
    (hforced : ∀ i, i.val < k → (endpoint i).IsForced)
    (hsuffix : ∀ i, k ≤ i.val → ¬ (endpoint i).IsForced) :
    ∃ a d t m : ℝ,
      0 ≤ a ∧ a ≤ uteB s ∧
      0 ≤ d ∧ 0 ≤ t ∧ 0 ≤ m ∧
      d + t + m ≤ 1 - uteB s ∧
      uteEndpointWordExcess s endpoint ≤
        (n : ℝ) ^ 2 * uteGap s a d t m +
          (((s + 2) + (s + 3)) +
            uteRho s * (s + 3)) * n := by
  let front := uteForcedEndpointBlock k endpoint
  let suffix := uteSuffixEndpointBlock k endpoint
  have hkLe : k ≤ n := hk.le
  have hfrontAll :
      ∀ value ∈ front, value.IsForced := by
    exact uteForcedEndpointBlock_all_forced
      hkLe endpoint hforced
  have hsuffixAll :
      ∀ value ∈ suffix, ¬ value.IsForced := by
    exact uteSuffixEndpointBlock_all_suffix
      hkLe endpoint hsuffix
  have hsuffixNe : suffix ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp [suffix, uteSuffixEndpointBlock, hkLe] at hlength
    omega
  cases hsuffixEq : suffix with
  | nil =>
      exact False.elim (hsuffixNe hsuffixEq)
  | cons exception rest =>
      let reduced := front ++ rest
      let af : ℕ := reduced.count .forcedCap
      let zf : ℕ := reduced.count .forcedZero
      let dN : ℕ := reduced.count .cappedDeferred
      let tN : ℕ := reduced.count .boundaryDeferred
      let mN : ℕ := reduced.count .immediateOne
      let zs : ℕ := reduced.count .suffixZero
      let a : ℝ := af / n
      let d : ℝ := dN / n
      let t : ℝ := tN / n
      let m : ℝ := mN / n
      have hrestAll :
          ∀ value ∈ rest, ¬ value.IsForced := by
        intro value hvalue
        exact hsuffixAll value (by
          rw [hsuffixEq]
          simp [hvalue])
      have hword :
          List.ofFn endpoint = front ++ exception :: rest := by
        rw [← uteEndpointBlocks_append k endpoint]
        change front ++ suffix = _
        rw [hsuffixEq]
      have hfrontLength : front.length = k := by
        simp [front, uteForcedEndpointBlock, hkLe]
      have hsuffixLength : suffix.length = n - k := by
        simp [suffix, uteSuffixEndpointBlock]
      have hrestLength : rest.length + 1 = n - k := by
        rw [hsuffixEq] at hsuffixLength
        simp only [List.length_cons] at hsuffixLength
        omega
      have hreducedLength : reduced.length + 1 = n := by
        simp only [reduced, List.length_append]
        omega
      have hrestForcedCap :
          rest.count .forcedCap = 0 :=
        uteEndpoint_suffix_forcedCap_count_zero rest hrestAll
      have hrestForcedZero :
          rest.count .forcedZero = 0 :=
        uteEndpoint_suffix_forcedZero_count_zero rest hrestAll
      have hforcedCounts : af + zf = k := by
        have hfrontCounts :=
          uteEndpoint_forced_counts_eq_length front hfrontAll
        dsimp [af, zf, reduced]
        simp only [List.count_append, hrestForcedCap,
          hrestForcedZero, add_zero]
        omega
      have htotal :
          af + zf + dN + tN + mN + zs + 1 = n := by
        have hall := uteEndpoint_all_counts reduced
        dsimp [af, zf, dN, tN, mN, zs]
        omega
      have hfinite :=
        uteFinite_pairExcess_le_normalized
          hn hs1 hkLower hkUpper hforcedCounts htotal
          ((uteRho_pos (zero_lt_one.trans_le hs1)).le)
      have hgap :
          uteLiteralALGWithPrefix s (uteB s) a d t m -
              uteRho s *
                uteLiteralOPTWithPrefix s (uteB s) a d t m =
            uteGap s a d t m := by
        simpa [uteLiteralALG, uteLiteralOPT] using
          (uteLiteralPairExcess_eq_uteGap
            (s := s) (a := a) (d := d) (t := t) (m := m) hs1)
      have hfinite' :
          uteFiniteALGCore s af zf dN tN mN zs -
              uteRho s *
                uteFiniteOPTCore s af zf dN tN mN zs ≤
            (n : ℝ) ^ 2 * uteGap s a d t m +
              uteRho s * (s + 3) * n := by
        simpa [a, d, t, m, hgap] using hfinite
      have hreduced :=
        uteEndpointWordExcess_le_reducedFiniteCore
          hs1 endpoint front rest exception hword
          hfrontAll hrestAll
      have hreduced' :
          uteEndpointWordExcess s endpoint ≤
            uteFiniteALGCore s af zf dN tN mN zs -
              uteRho s *
                uteFiniteOPTCore s af zf dN tN mN zs +
              ((s + 2) + (s + 3)) * n := by
        simpa [reduced, af, zf, dN, tN, mN, zs] using hreduced
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hafLeK : af ≤ k := by
        omega
      have ha0 : 0 ≤ a := by
        dsimp [a]
        positivity
      have haB : a ≤ uteB s := by
        dsimp [a]
        rw [div_le_iff₀ hnpos]
        have hafCast : (af : ℝ) ≤ k := by
          exact_mod_cast hafLeK
        exact hafCast.trans hkLower
      have hd0 : 0 ≤ d := by
        dsimp [d]
        positivity
      have ht0 : 0 ≤ t := by
        dsimp [t]
        positivity
      have hm0 : 0 ≤ m := by
        dsimp [m]
        positivity
      have hmass : d + t + m ≤ 1 - uteB s := by
        have htotalR :
            (af : ℝ) + zf + dN + tN + mN + zs + 1 = n := by
          exact_mod_cast htotal
        have hforcedR : (af : ℝ) + zf = k := by
          exact_mod_cast hforcedCounts
        have hcount :
            (dN : ℝ) + tN + mN ≤
              (1 - uteB s) * n := by
          have hzs0 : (0 : ℝ) ≤ zs := by positivity
          nlinarith
        dsimp [d, t, m]
        rw [← add_div, ← add_div]
        exact (div_le_iff₀ hnpos).2 (by
          nlinarith)
      refine ⟨a, d, t, m, ha0, haB, hd0, ht0, hm0,
        hmass, ?_⟩
      nlinarith

theorem uteRuntimeExcess_zero
    (s : ℝ) (k : ℕ) (processing : Fin 0 → ℝ) :
    uteRuntimeExcess s k processing = 0 := by
  rw [uteRuntimeExcess_eq_statusWordExcess]
  simp [uteStatusWordExcess]

namespace UpperBound

open LowerBound

/-- Fully verified transcript, endpoint, rounding, and diagonal bridge for
the endpoint-range ForcedPrefixUTE strategy. -/
theorem uteEndpointCostBridge_verified
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero) :
    UTEEndpointCostBridge s := by
  let C : ℝ :=
    ((s + 2) + (s + 3)) + uteRho s * (s + 3)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hrho : 0 ≤ uteRho s :=
      (uteRho_pos (zero_lt_one.trans_le hs1)).le
    positivity
  refine ⟨C, hC, ?_⟩
  intro n input
  let k := Online.forcedPrefixCount n (uteB s)
  have hprocessingNonneg :
      ∀ i, 0 ≤ input.processingTime i := by
    intro i
    exact (input.admissible i).1
  have hprocessingCap :
      ∀ i, input.processingTime i ≤ s + 1 := by
    intro i
    exact (input.admissible i).2
  have hoperational :
      strategyCost (.finite (s + 1))
            (uteEndpointStrategy s) n input -
          uteRho s *
            fixedOfflineCost (.finite (s + 1)) n input =
        uteRuntimeExcess s k input.processingTime := by
    simpa [strategyCost, fixedOfflineCost,
      FixedInput.onlineCost, FixedInput.runResult,
      analysisFuel, uteEndpointStrategy, k] using
        (run_forcedPrefixUTE_endpoint_excess_eq
          n (b := uteB s) hs1 input.processingTime)
  by_cases hn : n = 0
  · subst n
    refine ⟨0, 0, 0, 0, by norm_num, ?_, by norm_num,
      by norm_num, by norm_num, ?_, ?_⟩
    · exact uteB_nonneg hs1 hs0
    · have hb1 : uteB s ≤ 1 := by
        exact
          ((ute_parameter_order hs1 hs0).2.1.trans
            ((ute_parameter_order hs1 hs0).2.2.1.trans
              (ute_parameter_order hs1 hs0).2.2.2)).le
      linarith
    · rw [hoperational, uteRuntimeExcess_zero]
      norm_num
  · have hb0 : 0 ≤ uteB s := uteB_nonneg hs1 hs0
    have hb1 : uteB s < 1 := by
      exact (ute_parameter_order hs1 hs0).2.1.trans
        ((ute_parameter_order hs1 hs0).2.2.1.trans
          (ute_parameter_order hs1 hs0).2.2.2)
    have hkLower : (k : ℝ) ≤ uteB s * n := by
      exact Online.forcedPrefixCount_cast_le hb0
    have hkUpper : uteB s * n < k + 1 := by
      exact Online.forcedPrefixCount_lt_add_one n (uteB s)
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hkLt : k < n := by
      have hbProduct : uteB s * (n : ℝ) < n := by
        nlinarith
      have hkCast : (k : ℝ) < n :=
        hkLower.trans_lt hbProduct
      exact_mod_cast hkCast
    obtain ⟨endpoint, hforced, hsuffix, hstatus⟩ :=
      SchedulingPaper.exists_uteEndpoint_ge_runtimeStatus
        hs1 input.processingTime
        hprocessingNonneg hprocessingCap
    obtain ⟨a, d, t, m, ha0, haB, hd0, ht0, hm0,
        hmass, hendpoint⟩ :=
      exists_uteEndpoint_normalized_bound
        hn hs1 hkLt hkLower hkUpper endpoint
        hforced hsuffix
    refine ⟨a, d, t, m, ha0, haB, hd0, ht0, hm0,
      hmass, ?_⟩
    rw [hoperational,
      uteRuntimeExcess_eq_statusWordExcess]
    dsimp [k] at hstatus
    dsimp [C]
    exact hstatus.trans hendpoint

end UpperBound

end

end SchedulingPaper
