import SchedulingPaper.VerifiedUTEBelowTwoBridge
import SchedulingPaper.UTEEndpointFiniteBridge
import Mathlib.Tactic

/-!
# Completed below-two UTE bridge

This module sums the coordinatewise Bernoulli inequalities, derandomizes
them by a finite coordinate induction, and connects the resulting binary
endpoint word to the finite counting inequality.
-/

namespace SchedulingPaper

noncomputable section

open Set

theorem uteBelow_expectedPairExcess_left_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    {coordinate other : Fin n} (horder : coordinate < other) :
    let r := uteBelowRoundWeight k s processing coordinate
    let atZero := Function.update processing coordinate 0
    let atCap :=
      Function.update processing coordinate (s + 1)
    uteStatusPairExcess s
        (uteBelowRuntimeOutcome k s processing coordinate)
        (uteBelowRuntimeOutcome k s processing other)
        (processing coordinate) (processing other) ≤
      (1 - r) *
          uteStatusPairExcess s
            (uteBelowRuntimeOutcome k s atZero coordinate)
            (uteBelowRuntimeOutcome k s atZero other)
            (atZero coordinate) (atZero other) +
        r *
          uteStatusPairExcess s
            (uteBelowRuntimeOutcome k s atCap coordinate)
            (uteBelowRuntimeOutcome k s atCap other)
            (atCap coordinate) (atCap other) := by
  dsimp only
  have hne : other ≠ coordinate := ne_of_gt horder
  have halg :=
    uteBelow_expectedALGPair_left_le (k := k) hs hs1
      processing hprocessing horder
  have hopt :=
    uteBelow_expectedOPT_left_le (k := k) hs hs1
      processing hprocessing coordinate other
  have hscaled :=
    mul_le_mul_of_nonneg_left hopt (uteRho_pos hs).le
  simp only [Function.update_self,
    Function.update_of_ne hne] at halg ⊢
  unfold uteStatusPairExcess
  nlinarith

theorem uteBelow_expectedPairExcess_right_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    {other coordinate : Fin n} (horder : other < coordinate)
    (hprior :
      ∀ i, i < coordinate →
        processing i = 0 ∨ processing i = s + 1) :
    let r := uteBelowRoundWeight k s processing coordinate
    let atZero := Function.update processing coordinate 0
    let atCap :=
      Function.update processing coordinate (s + 1)
    uteStatusPairExcess s
        (uteBelowRuntimeOutcome k s processing other)
        (uteBelowRuntimeOutcome k s processing coordinate)
        (processing other) (processing coordinate) ≤
      (1 - r) *
          uteStatusPairExcess s
            (uteBelowRuntimeOutcome k s atZero other)
            (uteBelowRuntimeOutcome k s atZero coordinate)
            (atZero other) (atZero coordinate) +
        r *
          uteStatusPairExcess s
            (uteBelowRuntimeOutcome k s atCap other)
            (uteBelowRuntimeOutcome k s atCap coordinate)
            (atCap other) (atCap coordinate) := by
  dsimp only
  have hne : other ≠ coordinate := ne_of_lt horder
  have halg :=
    uteBelow_expectedALGPair_right_le (k := k) hs hs1
      processing hprocessing horder hprior
  have hopt :=
    uteBelow_expectedOPT_right_le (k := k) hs hs1
      processing hprocessing other coordinate
  have hscaled :=
    mul_le_mul_of_nonneg_left hopt (uteRho_pos hs).le
  simp only [Function.update_self,
    Function.update_of_ne hne] at halg ⊢
  unfold uteStatusPairExcess
  nlinarith

def uteBelowSelfSum {n : ℕ}
    (s : ℝ) (processing : Fin n → ℝ) : ℝ :=
  ∑ i, uteFixedSelfExcessAt s (processing i)

def uteBelowPairSum {n : ℕ}
    (s : ℝ) (k : ℕ) (processing : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
    uteStatusPairExcess s
      (uteBelowRuntimeOutcome k s processing i)
      (uteBelowRuntimeOutcome k s processing j)
      (processing i) (processing j)

theorem uteBelowStatusExcess_eq_sums
    {n : ℕ} (s : ℝ) (k : ℕ)
    (processing : Fin n → ℝ) :
    uteBelowStatusExcess s k processing =
      uteBelowSelfSum s processing +
        uteBelowPairSum s k processing := by
  rfl

theorem uteBelow_expectedStatusExcess_le
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n)
    (hprior :
      ∀ i, i < coordinate →
        processing i = 0 ∨ processing i = s + 1) :
    let r := uteBelowRoundWeight k s processing coordinate
    let atZero := Function.update processing coordinate 0
    let atCap :=
      Function.update processing coordinate (s + 1)
    uteBelowStatusExcess s k processing ≤
      (1 - r) * uteBelowStatusExcess s k atZero +
        r * uteBelowStatusExcess s k atCap := by
  dsimp only
  let r := uteBelowRoundWeight k s processing coordinate
  let atZero := Function.update processing coordinate 0
  let atCap :=
    Function.update processing coordinate (s + 1)
  have hself :
      uteBelowSelfSum s processing ≤
        (1 - r) * uteBelowSelfSum s atZero +
          r * uteBelowSelfSum s atCap := by
    unfold uteBelowSelfSum
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hic : i = coordinate
    · subst i
      simpa [atZero, atCap] using
        uteBelow_expectedSelfExcess_le (k := k)
          hs hs1 processing hprocessing coordinate
    · simp only [atZero, atCap,
        Function.update_of_ne hic]
      ring_nf
      exact le_refl (uteFixedSelfExcessAt s (processing i))
  have hpair :
      uteBelowPairSum s k processing ≤
        (1 - r) * uteBelowPairSum s k atZero +
          r * uteBelowPairSum s k atCap := by
    have hterm :
        uteBelowPairSum s k processing ≤
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ((1 - r) *
                uteStatusPairExcess s
                  (uteBelowRuntimeOutcome k s atZero i)
                  (uteBelowRuntimeOutcome k s atZero j)
                  (atZero i) (atZero j) +
              r *
                uteStatusPairExcess s
                  (uteBelowRuntimeOutcome k s atCap i)
                  (uteBelowRuntimeOutcome k s atCap j)
                  (atCap i) (atCap j)) := by
      unfold uteBelowPairSum
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j hj
      have hij : i < j := (Finset.mem_filter.mp hj).2
      by_cases hic : i = coordinate
      · subst i
        exact
          uteBelow_expectedPairExcess_left_le
            (k := k) hs hs1 processing hprocessing hij
      · by_cases hjc : j = coordinate
        · subst j
          exact
            uteBelow_expectedPairExcess_right_le
              (k := k) hs hs1 processing hprocessing
                hij hprior
        · have hout0i :=
            uteBelowRuntimeOutcome_update_ne
              (k := k) (s := s) processing
              (value := (0 : ℝ)) hic
          have hout0j :=
            uteBelowRuntimeOutcome_update_ne
              (k := k) (s := s) processing
              (value := (0 : ℝ)) hjc
          have houtUi :=
            uteBelowRuntimeOutcome_update_ne
              (k := k) (s := s) processing
              (value := s + 1) hic
          have houtUj :=
            uteBelowRuntimeOutcome_update_ne
              (k := k) (s := s) processing
              (value := s + 1) hjc
          simp only [atZero, atCap,
            Function.update_of_ne hic,
            Function.update_of_ne hjc,
            hout0i, hout0j, houtUi, houtUj]
          ring_nf
          exact le_refl
            (uteStatusPairExcess s
              (uteBelowRuntimeOutcome k s processing i)
              (uteBelowRuntimeOutcome k s processing j)
              (processing i) (processing j))
    calc
      uteBelowPairSum s k processing ≤
          ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            ((1 - r) *
                uteStatusPairExcess s
                  (uteBelowRuntimeOutcome k s atZero i)
                  (uteBelowRuntimeOutcome k s atZero j)
                  (atZero i) (atZero j) +
              r *
                uteStatusPairExcess s
                  (uteBelowRuntimeOutcome k s atCap i)
                  (uteBelowRuntimeOutcome k s atCap j)
                  (atCap i) (atCap j)) := hterm
      _ = (1 - r) * uteBelowPairSum s k atZero +
          r * uteBelowPairSum s k atCap := by
        unfold uteBelowPairSum
        simp_rw [Finset.sum_add_distrib,
          ← Finset.mul_sum]
  rw [uteBelowStatusExcess_eq_sums,
    uteBelowStatusExcess_eq_sums,
    uteBelowStatusExcess_eq_sums]
  nlinarith

theorem uteBelow_exists_endpoint_update
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1)
    (coordinate : Fin n)
    (hprior :
      ∀ i, i < coordinate →
        processing i = 0 ∨ processing i = s + 1) :
    ∃ value : ℝ,
      (value = 0 ∨ value = s + 1) ∧
        uteBelowStatusExcess s k processing ≤
          uteBelowStatusExcess s k
            (Function.update processing coordinate value) := by
  let r := uteBelowRoundWeight k s processing coordinate
  let atZero := Function.update processing coordinate 0
  let atCap :=
    Function.update processing coordinate (s + 1)
  have hr :=
    uteBelowRoundWeight_mem (k := k)
      hs hs1 processing hprocessing coordinate
  have hexpected :=
    uteBelow_expectedStatusExcess_le (k := k)
      hs hs1 processing hprocessing coordinate hprior
  dsimp only at hexpected
  by_cases hle :
      uteBelowStatusExcess s k atZero ≤
        uteBelowStatusExcess s k atCap
  · refine ⟨s + 1, Or.inr rfl, ?_⟩
    have hproduct :
        0 ≤ (1 - r) *
          (uteBelowStatusExcess s k atCap -
            uteBelowStatusExcess s k atZero) :=
      mul_nonneg (sub_nonneg.mpr hr.2)
        (sub_nonneg.mpr hle)
    exact hexpected.trans (by nlinarith)
  · have hreverse :
        uteBelowStatusExcess s k atCap ≤
          uteBelowStatusExcess s k atZero :=
      le_of_not_ge hle
    refine ⟨0, Or.inl rfl, ?_⟩
    have hproduct :
        0 ≤ r *
          (uteBelowStatusExcess s k atZero -
            uteBelowStatusExcess s k atCap) :=
      mul_nonneg hr.1 (sub_nonneg.mpr hreverse)
    exact hexpected.trans (by nlinarith)

theorem uteBelow_exists_binary_statusExcess_ge
    {n k : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1) :
    ∃ binary : Fin n → ℝ,
      (∀ i, 0 ≤ binary i ∧ binary i ≤ s + 1) ∧
      (∀ i, binary i = 0 ∨ binary i = s + 1) ∧
      uteBelowStatusExcess s k processing ≤
        uteBelowStatusExcess s k binary := by
  have aux :
      ∀ m : ℕ, m ≤ n →
        ∃ current : Fin n → ℝ,
          (∀ i, 0 ≤ current i ∧ current i ≤ s + 1) ∧
          (∀ i, i.val < m →
            current i = 0 ∨ current i = s + 1) ∧
          uteBelowStatusExcess s k processing ≤
            uteBelowStatusExcess s k current := by
    intro m
    induction m with
    | zero =>
        intro _hm
        exact ⟨processing, hprocessing, by simp, le_rfl⟩
    | succ m ih =>
        intro hm
        have hmle : m ≤ n :=
          Nat.le_trans (Nat.le_succ m) hm
        obtain ⟨current, hcurrent, hbinary, hexcess⟩ :=
          ih hmle
        have hmlt : m < n := Nat.lt_of_succ_le hm
        let coordinate : Fin n := ⟨m, hmlt⟩
        have hprior :
            ∀ i, i < coordinate →
              current i = 0 ∨ current i = s + 1 := by
          intro i hi
          exact hbinary i hi
        obtain ⟨value, hvalue, hstep⟩ :=
          uteBelow_exists_endpoint_update (k := k)
            hs hs1 current hcurrent coordinate hprior
        let next :=
          Function.update current coordinate value
        have hvalueBounds :
            0 ≤ value ∧ value ≤ s + 1 := by
          rcases hvalue with hzero | hcap
          · rw [hzero]
            constructor
            · exact le_rfl
            · linarith
          · rw [hcap]
            exact ⟨by linarith, le_rfl⟩
        refine ⟨next, ?_, ?_, hexcess.trans hstep⟩
        · intro i
          by_cases hic : i = coordinate
          · subst i
            simpa [next] using hvalueBounds
          · simpa [next, Function.update_of_ne hic] using
              hcurrent i
        · intro i hi
          by_cases hic : i = coordinate
          · subst i
            simpa [next] using hvalue
          · have hvalne : i.val ≠ m := by
              intro heq
              apply hic
              apply Fin.ext
              exact heq
            have him : i.val < m := by omega
            simpa [next, Function.update_of_ne hic] using
              hbinary i him
  obtain ⟨binary, hbox, hbinary, hexcess⟩ :=
    aux n le_rfl
  exact
    ⟨binary, hbox, fun i => hbinary i i.isLt, hexcess⟩

def uteBelowBinaryEndpoint {n : ℕ}
    (k : ℕ) (binary : Fin n → ℝ) (i : Fin n) :
    UTEEndpoint :=
  if i.val < k then
    if binary i = 0 then .forcedZero else .forcedCap
  else
    if binary i = 0 then .suffixZero else .cappedDeferred

theorem uteBelowBinaryEndpoint_processing
    {n k : ℕ} {s : ℝ} (hs : 0 < s)
    (binary : Fin n → ℝ)
    (hbinary :
      ∀ i, binary i = 0 ∨ binary i = s + 1) :
    ∀ i,
      uteEndpointProcessing s
          (uteBelowBinaryEndpoint k binary i) =
        binary i := by
  intro i
  by_cases hprefix : i.val < k
  · rcases hbinary i with hzero | hcap
    · simp [uteBelowBinaryEndpoint, hprefix, hzero,
        uteEndpointProcessing]
    · have hne : binary i ≠ 0 := by
        rw [hcap]
        linarith
      have hcapne : s + 1 ≠ 0 := by linarith
      simp [uteBelowBinaryEndpoint, hprefix, hcap, hcapne,
        uteEndpointProcessing]
  · rcases hbinary i with hzero | hcap
    · simp [uteBelowBinaryEndpoint, hprefix, hzero,
        uteEndpointProcessing]
    · have hne : binary i ≠ 0 := by
        rw [hcap]
        linarith
      have hcapne : s + 1 ≠ 0 := by linarith
      simp [uteBelowBinaryEndpoint, hprefix, hcap, hcapne,
        uteEndpointProcessing]

theorem uteBelowBinaryEndpoint_outcome
    {n k : ℕ} {s : ℝ} (hs : 0 < s)
    (binary : Fin n → ℝ)
    (hbinary :
      ∀ i, binary i = 0 ∨ binary i = s + 1) :
    ∀ i,
      (uteBelowBinaryEndpoint k binary i).outcome =
        uteBelowRuntimeOutcome k s binary i := by
  intro i
  by_cases hprefix : i.val < k
  · rcases hbinary i with hzero | hcap
    · simp [uteBelowBinaryEndpoint, hprefix, hzero,
        UTEEndpoint.outcome, uteBelowRuntimeOutcome]
    · have hne : binary i ≠ 0 := by
        rw [hcap]
        linarith
      have hcapne : s + 1 ≠ 0 := by linarith
      simp [uteBelowBinaryEndpoint, hprefix, hcap, hcapne,
        UTEEndpoint.outcome, uteBelowRuntimeOutcome]
  · rcases hbinary i with hzero | hcap
    · simp [uteBelowBinaryEndpoint, hprefix, hzero,
        UTEEndpoint.outcome, uteBelowRuntimeOutcome, hs.le]
    · have hne : binary i ≠ 0 := by
        rw [hcap]
        linarith
      have hcapne : s + 1 ≠ 0 := by linarith
      have hnot : ¬s + 1 ≤ s := by linarith
      simp [uteBelowBinaryEndpoint, hprefix, hcap, hcapne,
        UTEEndpoint.outcome, uteBelowRuntimeOutcome, hnot]

theorem uteBelowStatusExcess_binary_eq_endpointWordExcess
    {n k : ℕ} {s : ℝ} (hs : 0 < s)
    (binary : Fin n → ℝ)
    (hbinary :
      ∀ i, binary i = 0 ∨ binary i = s + 1) :
    uteBelowStatusExcess s k binary =
      uteEndpointWordExcess s
        (uteBelowBinaryEndpoint k binary) := by
  have hout :
      (fun i =>
        (uteBelowBinaryEndpoint k binary i).outcome) =
        uteBelowRuntimeOutcome k s binary := by
    funext i
    exact uteBelowBinaryEndpoint_outcome hs binary hbinary i
  have hprocessing :
      (fun i =>
        uteEndpointProcessing s
          (uteBelowBinaryEndpoint k binary i)) =
        binary := by
    funext i
    exact uteBelowBinaryEndpoint_processing hs binary hbinary i
  unfold uteBelowStatusExcess uteEndpointWordExcess
  rw [hout, hprocessing]

theorem uteBelowBinaryEndpoint_forced
    {n k : ℕ} (binary : Fin n → ℝ) :
    ∀ i, i.val < k →
      (uteBelowBinaryEndpoint k binary i).IsForced := by
  intro i hi
  unfold uteBelowBinaryEndpoint
  rw [if_pos hi]
  split <;> simp [UTEEndpoint.IsForced]

theorem uteBelowBinaryEndpoint_suffix
    {n k : ℕ} (binary : Fin n → ℝ) :
    ∀ i, k ≤ i.val →
      ¬(uteBelowBinaryEndpoint k binary i).IsForced := by
  intro i hi
  have hnot : ¬i.val < k := by omega
  unfold uteBelowBinaryEndpoint
  rw [if_neg hnot]
  split <;> simp [UTEEndpoint.IsForced]

theorem list_count_ofFn_eq_zero_of_ne
    {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (value : α)
    (hne : ∀ i, f i ≠ value) :
    (List.ofFn f).count value = 0 := by
  apply List.count_eq_zero.mpr
  intro hmem
  rcases List.mem_ofFn.mp hmem with ⟨i, hi⟩
  exact hne i hi

theorem uteBelowBinaryEndpoint_boundary_count_zero
    {n k : ℕ} (binary : Fin n → ℝ) :
    (List.ofFn (uteBelowBinaryEndpoint k binary)).count
        .boundaryDeferred = 0 := by
  apply list_count_ofFn_eq_zero_of_ne
  intro i
  unfold uteBelowBinaryEndpoint
  split <;> split <;> simp

theorem uteBelowBinaryEndpoint_immediateOne_count_zero
    {n k : ℕ} (binary : Fin n → ℝ) :
    (List.ofFn (uteBelowBinaryEndpoint k binary)).count
        .immediateOne = 0 := by
  apply list_count_ofFn_eq_zero_of_ne
  intro i
  unfold uteBelowBinaryEndpoint
  split <;> split <;> simp

theorem uteFixedSelfExcess_endpoint_le_below
    {s : ℝ} (hs : 0 < s) (endpoint : UTEEndpoint) :
    uteFixedSelfExcessAt s
        (uteEndpointProcessing s endpoint) ≤
      s + 2 := by
  have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
  have heff :
      0 ≤ uteEffectiveAt s
        (uteEndpointProcessing s endpoint) := by
    cases endpoint <;>
      simp [uteEffectiveAt, uteEndpointProcessing] <;>
      linarith
  have hp :
      uteEndpointProcessing s endpoint ≤ s + 1 := by
    cases endpoint <;>
      simp [uteEndpointProcessing] <;>
      linarith
  unfold uteFixedSelfExcessAt
  nlinarith [mul_nonneg hrho heff]

theorem uteEndpoint_self_sum_le_below
    {n : ℕ} {s : ℝ} (hs : 0 < s)
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
      exact uteFixedSelfExcess_endpoint_le_below
        hs (endpoint i)
    _ = (s + 2) * n := by
      simp
      ring

set_option maxHeartbeats 800000 in
theorem uteBelow_binary_statusExcess_le
    {n k : ℕ} {s b : ℝ}
    (hn : n ≠ 0)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb : b = uteB s)
    (hkLower : (k : ℝ) ≤ b * n)
    (hkUpper : b * n < k + 1)
    (binary : Fin n → ℝ)
    (hbinary :
      ∀ i, binary i = 0 ∨ binary i = s + 1) :
    uteBelowStatusExcess s k binary ≤
      ((s + 2) +
        (1 + uteRho s * (s + 1) / 2)) * n := by
  let endpoint : Fin n → UTEEndpoint :=
    uteBelowBinaryEndpoint k binary
  let values : List UTEEndpoint := List.ofFn endpoint
  let front := uteForcedEndpointBlock k endpoint
  let suffix := uteSuffixEndpointBlock k endpoint
  let af : ℕ := values.count .forcedCap
  let zf : ℕ := values.count .forcedZero
  let d : ℕ := values.count .cappedDeferred
  let zs : ℕ := values.count .suffixZero
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hkR : (k : ℝ) ≤ n := by
    have hproduct :
        0 ≤ (1 - b) * (n : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hb1) hn0
    nlinarith
  have hk : k ≤ n := by exact_mod_cast hkR
  have hfrontAll :
      ∀ value ∈ front, value.IsForced := by
    apply uteForcedEndpointBlock_all_forced hk endpoint
    intro i hi
    exact uteBelowBinaryEndpoint_forced binary i hi
  have hsuffixAll :
      ∀ value ∈ suffix, ¬value.IsForced := by
    apply uteSuffixEndpointBlock_all_suffix hk endpoint
    intro i hi
    exact uteBelowBinaryEndpoint_suffix binary i hi
  have hblocks :
      front ++ suffix = values := by
    exact uteEndpointBlocks_append k endpoint
  have hfrontLength : front.length = k := by
    simp [front, uteForcedEndpointBlock, hk]
  have hsuffixForcedCap :
      suffix.count .forcedCap = 0 :=
    uteEndpoint_suffix_forcedCap_count_zero
      suffix hsuffixAll
  have hsuffixForcedZero :
      suffix.count .forcedZero = 0 :=
    uteEndpoint_suffix_forcedZero_count_zero
      suffix hsuffixAll
  have hforced : af + zf = k := by
    have hfrontCounts :=
      uteEndpoint_forced_counts_eq_length
        front hfrontAll
    dsimp [af, zf]
    rw [← hblocks]
    simp only [List.count_append, hsuffixForcedCap,
      hsuffixForcedZero, add_zero]
    omega
  have ht0 :
      values.count .boundaryDeferred = 0 := by
    simpa [values, endpoint] using
      uteBelowBinaryEndpoint_boundary_count_zero binary
  have hm0 :
      values.count .immediateOne = 0 := by
    simpa [values, endpoint] using
      uteBelowBinaryEndpoint_immediateOne_count_zero binary
  have htotal : af + zf + d + zs = n := by
    have hall := uteEndpoint_all_counts values
    have hlength : values.length = n := by
      simp [values]
    dsimp [af, zf, d, zs]
    rw [ht0, hm0, hlength] at hall
    omega
  have hcanonical0 :=
    ute_listPairObjective_le_canonical
      hs.le front suffix hfrontAll hsuffixAll
  have hcanonical :
      listPairObjective (fun _ => 0)
          (uteALGPairCharge s) values ≤
        uteFiniteALGCore s af zf d 0 0 zs := by
    calc
      listPairObjective (fun _ => 0)
          (uteALGPairCharge s) values =
          listPairObjective (fun _ => 0)
            (uteALGPairCharge s) (front ++ suffix) := by
              rw [hblocks]
      _ ≤ listPairObjective (fun _ => 0)
          (uteCanonicalALGPairCharge s)
          (front ++ suffix) := hcanonical0
      _ = listPairObjective (fun _ => 0)
          (uteCanonicalALGPairCharge s) values := by
            rw [hblocks]
      _ = uteFiniteALGCore s af zf d 0 0 zs := by
            rw [listPairObjective_canonicalALG_eq_finiteCore]
            simp only [af, zf, d, zs, ht0, hm0]
  have hopt :
      listPairObjective (fun _ => 0)
          (uteOPTPairCharge s) values =
        uteFiniteOPTCore s af zf d 0 0 zs := by
    rw [listPairObjective_opt_eq_finiteCore]
    simp only [af, zf, d, zs, ht0, hm0]
  have hfinite :=
    uteFinite_binary_pairExcess_le
      hn hs hs1 hb0 hb1 hb hkLower hkUpper
      hforced htotal
  have hself :=
    uteEndpoint_self_sum_le_below hs endpoint
  rw [uteBelowStatusExcess_binary_eq_endpointWordExcess
      hs binary hbinary,
    uteEndpointWordExcess_eq_self_add_pairLists]
  change
    (∑ i,
        uteFixedSelfExcessAt s
          (uteEndpointProcessing s (endpoint i))) +
      listPairObjective (fun _ => 0)
          (uteALGPairCharge s) values -
      uteRho s *
        listPairObjective (fun _ => 0)
          (uteOPTPairCharge s) values ≤ _
  rw [hopt]
  nlinarith

theorem uteBelow_statusExcess_le_linear
    {n k : ℕ} {s b : ℝ}
    (hn : n ≠ 0)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hb : b = uteB s)
    (hkLower : (k : ℝ) ≤ b * n)
    (hkUpper : b * n < k + 1)
    (processing : Fin n → ℝ)
    (hprocessing :
      ∀ i, 0 ≤ processing i ∧ processing i ≤ s + 1) :
    uteBelowStatusExcess s k processing ≤
      ((s + 2) +
        (1 + uteRho s * (s + 1) / 2)) * n := by
  obtain ⟨binary, _hbox, hbinary, hround⟩ :=
    uteBelow_exists_binary_statusExcess_ge
      (k := k) hs hs1 processing hprocessing
  exact hround.trans
    (uteBelow_binary_statusExcess_le
      hn hs hs1 hb0 hb1 hb hkLower hkUpper
      binary hbinary)

theorem uteBelowStatusExcess_zero
    (s : ℝ) (k : ℕ) (processing : Fin 0 → ℝ) :
    uteBelowStatusExcess s k processing = 0 := by
  simp [uteBelowStatusExcess, uteStatusWordExcess]

namespace UpperBound

open LowerBound

/-- The complete Bernoulli extremalization and binary endpoint calculation
for the branch `uDiamond < s + 1 < 2`. -/
theorem uteBelowTwoCostBridge_verified
    {s : ℝ} (hsD : uDiamond - 1 < s) (hs1 : s < 1) :
    UTEBelowTwoCostBridge s := by
  have hs : 0 < s := by
    linarith [uDiamond_gt_one]
  let C : ℝ :=
    (s + 2) + (1 + uteRho s * (s + 1) / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hrho : 0 ≤ uteRho s := (uteRho_pos hs).le
    positivity
  refine ⟨C, hC, ?_⟩
  intro n input
  let k := Online.forcedPrefixCount n (uteB s)
  have hprocessing :
      ∀ i, 0 ≤ input.processingTime i ∧
        input.processingTime i ≤ s + 1 := by
    intro i
    exact input.admissible i
  have hoperational :
      strategyCost (.finite (s + 1))
            (uteEndpointStrategy s) n input -
          uteRho s *
            fixedOfflineCost (.finite (s + 1)) n input =
        uteBelowStatusExcess s k input.processingTime := by
    simpa [strategyCost, fixedOfflineCost,
      FixedInput.onlineCost, FixedInput.runResult,
      analysisFuel, uteEndpointStrategy, k] using
        (run_forcedPrefixUTE_below_excess_eq_statusExcess
          n (b := uteB s) hs hs1.le input.processingTime)
  by_cases hn : n = 0
  · subst n
    have hzero :=
      uteBelowStatusExcess_zero s k input.processingTime
    norm_num
    linarith
  · have hb0 : 0 ≤ uteB s :=
      (uteB_pos_below_two hs hs1).le
    have hb1 : uteB s ≤ 1 :=
      (uteB_lt_one_of_pos hs).le
    have hkLower :
        (k : ℝ) ≤ uteB s * n :=
      Online.forcedPrefixCount_cast_le hb0
    have hkUpper :
        uteB s * n < k + 1 :=
      Online.forcedPrefixCount_lt_add_one n (uteB s)
    have hstatus :=
      uteBelow_statusExcess_le_linear
        hn hs hs1.le hb0 hb1 rfl hkLower hkUpper
        input.processingTime hprocessing
    dsimp [C]
    nlinarith

end UpperBound

end

end SchedulingPaper
