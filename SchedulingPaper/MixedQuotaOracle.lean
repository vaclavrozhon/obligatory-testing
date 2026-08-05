import SchedulingPaper.MixedQuotaLower
import SchedulingPaper.HiddenStoppingPairAccounting
import Mathlib.Tactic

/-!
# The public mixed-quota oracle

The mixed construction has two public phases.  Before the quota line is
crossed, tests return the finite cap and raw first touches remain hidden.
The crossing touch itself belongs to this prefix.  Every later first touch
consumes one rank of a harmonic tail.

This file makes the phase boundary and the dynamically scaled tail literal.
The scan stores the suffix strictly after the first crossing touch together
with the number of labels that were still untouched at that instant.  In
particular, the tail scale is stable after crossing and raw tail touches
advance the same public rank as tests.
-/

namespace SchedulingPaper

noncomputable section

open Online

namespace LowerBound
namespace MixedQuotaOracle

open HiddenStoppingOracle

/-! ## A persistent public scan -/

/-- State of the left-to-right quota scan.  `tail` excludes the crossing
observation itself. -/
structure ScanState (n : ℕ) where
  seen : Online.Transcript n
  crossed : Bool
  tail : Online.Transcript n
  tailSize : ℕ

def initialScanState (n : ℕ) : ScanState n where
  seen := []
  crossed := false
  tail := []
  tailSize := 0

/-- One public scan step.  At the first crossing, `tailSize` freezes the
number of labels that have not yet been first-touched. -/
noncomputable def scanStep
    (n : ℕ) (u β : ℝ) (state : ScanState n)
    (observation : Online.Observation n) : ScanState n := by
  classical
  let next := state.seen ++ [observation]
  exact
    if state.crossed = true then
      { seen := next
        crossed := true
        tail := state.tail ++ [observation]
        tailSize := state.tailSize }
    else if HiddenStoppingOracle.Crossed n u β next then
      { seen := next
        crossed := true
        tail := state.tail
        tailSize := n - next.startedLabels.length }
    else
      { seen := next
        crossed := false
        tail := state.tail
        tailSize := state.tailSize }

noncomputable def scan
    (n : ℕ) (u β : ℝ) (transcript : Online.Transcript n) :
    ScanState n :=
  transcript.foldl (scanStep n u β) (initialScanState n)

@[simp] theorem scan_nil (n : ℕ) (u β : ℝ) :
    scan n u β [] = initialScanState n := rfl

theorem scan_append_singleton
    (n : ℕ) (u β : ℝ) (transcript : Online.Transcript n)
    (observation : Online.Observation n) :
    scan n u β (transcript ++ [observation]) =
      scanStep n u β (scan n u β transcript) observation := by
  simp [scan, List.foldl_append]

private theorem scanFold_seen
    (n : ℕ) (u β : ℝ) (state : ScanState n)
    (rest : Online.Transcript n) :
    (rest.foldl (scanStep n u β) state).seen =
      state.seen ++ rest := by
  induction rest generalizing state with
  | nil => simp
  | cons observation rest ih =>
      rw [List.foldl_cons, ih]
      simp only [scanStep]
      split_ifs <;> simp [List.append_assoc]

@[simp] theorem scan_seen
    (n : ℕ) (u β : ℝ) (transcript : Online.Transcript n) :
    (scan n u β transcript).seen = transcript := by
  simpa [scan, initialScanState] using
    scanFold_seen n u β (initialScanState n) transcript

/-- Once the stored phase bit is set, appending one observation appends
exactly that observation to the tail and leaves its total size fixed. -/
theorem scan_append_of_storedCrossed
    {n : ℕ} {u β : ℝ} {transcript : Online.Transcript n}
    (hcrossed : (scan n u β transcript).crossed = true)
    (observation : Online.Observation n) :
    let before := scan n u β transcript
    let after := scan n u β (transcript ++ [observation])
    after.crossed = true ∧
      after.tail = before.tail ++ [observation] ∧
      after.tailSize = before.tailSize := by
  dsimp only
  rw [scan_append_singleton]
  simp [scanStep, hcrossed]

/-- The first crossing observation is retained in the prefix, not in the
harmonic tail. -/
theorem scan_append_firstCrossing
    {n : ℕ} {u β : ℝ} {transcript : Online.Transcript n}
    (hstored : (scan n u β transcript).crossed = false)
    (observation : Online.Observation n)
    (hcross :
      HiddenStoppingOracle.Crossed n u β
        (transcript ++ [observation])) :
    let before := scan n u β transcript
    let after := scan n u β (transcript ++ [observation])
    after.crossed = true ∧
      after.tail = before.tail ∧
      after.tailSize =
        n - (transcript ++ [observation]).startedLabels.length := by
  dsimp only
  rw [scan_append_singleton]
  simp [scanStep, hstored, scan_seen, hcross]

/-! ## Crossing persistence -/

theorem crossed_append_testResult
    {n : ℕ} {u β : ℝ} {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) (p : ℝ) :
    HiddenStoppingOracle.Crossed n u β
      (transcript ++ [.testResult job p]) := by
  by_cases hp : p = u
  · subst p
    unfold HiddenStoppingOracle.Crossed at *
    rw [HiddenStoppingOracle.surplus_append_long]
    linarith
  · unfold HiddenStoppingOracle.Crossed at *
    rwa [HiddenStoppingOracle.surplus_append_testResult_ne
      n u β transcript job p hp]

theorem crossed_append_observation
    {n : ℕ} {u β : ℝ} {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (hβ : 0 ≤ β) (observation : Online.Observation n) :
    HiddenStoppingOracle.Crossed n u β
      (transcript ++ [observation]) := by
  cases observation with
  | testResult job p =>
      exact crossed_append_testResult hcross job p
  | processed job =>
      exact hcross.append_processed job
  | rawCompleted job =>
      exact hcross.append_raw hβ job

/-- For positive size and quota, the stored phase bit agrees exactly with
the mathematical crossing predicate. -/
theorem scan_crossed_iff
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) (transcript : Online.Transcript n) :
    (scan n u β transcript).crossed = true ↔
      HiddenStoppingOracle.Crossed n u β transcript := by
  induction transcript using List.reverseRecOn with
  | nil =>
      simp [scan, initialScanState,
        HiddenStoppingOracle.not_crossed_nil hn hβ]
  | append_singleton transcript observation ih =>
      rw [scan_append_singleton]
      by_cases hstored : (scan n u β transcript).crossed = true
      · have hcross :
          HiddenStoppingOracle.Crossed n u β transcript :=
        ih.mp hstored
        have hnext :=
          crossed_append_observation hcross hβ.le observation
        simp [scanStep, hstored, hnext]
      · have hstoredFalse :
          (scan n u β transcript).crossed = false := by
          exact Bool.eq_false_of_not_eq_true hstored
        have hnotCross :
            ¬ HiddenStoppingOracle.Crossed n u β transcript := by
          intro h
          exact hstored (ih.mpr h)
        by_cases hnext :
            HiddenStoppingOracle.Crossed n u β
              (transcript ++ [observation])
        · simp [scanStep, hstoredFalse, scan_seen, hnext]
        · simp [scanStep, hstoredFalse, scan_seen, hnext]

theorem scan_tail_eq_nil_of_not_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {transcript : Online.Transcript n}
    (hnot :
      ¬ HiddenStoppingOracle.Crossed n u β transcript) :
    (scan n u β transcript).tail = [] := by
  induction transcript using List.reverseRecOn with
  | nil =>
      rfl
  | append_singleton transcript observation ih =>
      have hnotBefore :
          ¬ HiddenStoppingOracle.Crossed n u β transcript := by
        intro hbefore
        exact hnot
          (crossed_append_observation hbefore hβ.le observation)
      have htail := ih hnotBefore
      have hstored :
          (scan n u β transcript).crossed = false := by
        have hiff :=
          scan_crossed_iff (u := u) (β := β) hn hβ transcript
        exact Bool.eq_false_of_not_eq_true
          (fun htrue => hnotBefore (hiff.mp htrue))
      rw [scan_append_singleton]
      simp [scanStep, hstored, scan_seen, hnot, htail]

/-! ## The post-crossing public rank -/

def tailRank
    (n : ℕ) (u β : ℝ) (transcript : Online.Transcript n) : ℕ :=
  (scan n u β transcript).tail.startedLabels.length

theorem tailRank_append_testResult_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) (p : ℝ) :
    tailRank n u β (transcript ++ [.testResult job p]) =
      tailRank n u β transcript + 1 := by
  have hstored :=
    (scan_crossed_iff hn hβ transcript).mpr hcross
  have hscan :=
    scan_append_of_storedCrossed hstored
      (Online.Observation.testResult job p)
  simp [tailRank, hscan.2.1]

theorem tailRank_append_raw_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) :
    tailRank n u β (transcript ++ [.rawCompleted job]) =
      tailRank n u β transcript + 1 := by
  have hstored :=
    (scan_crossed_iff hn hβ transcript).mpr hcross
  have hscan :=
    scan_append_of_storedCrossed hstored
      (Online.Observation.rawCompleted job)
  simp [tailRank, hscan.2.1]

theorem tailRank_append_processed_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) :
    tailRank n u β (transcript ++ [.processed job]) =
      tailRank n u β transcript := by
  have hstored :=
    (scan_crossed_iff hn hβ transcript).mpr hcross
  have hscan :=
    scan_append_of_storedCrossed hstored
      (Online.Observation.processed job)
  simp [tailRank, hscan.2.1]

/-! ## Exact virtual replay of tail raw operations -/

/-- Expand a bounded tail observation into its cap-free harmonic operation.
A raw completion consumes the current harmonic rank, then becomes an
immediate test/process pair. -/
def virtualTailStep
    (K Z : ℕ) (virtual : Online.Transcript n) :
    Online.Observation n → Online.Transcript n
  | .testResult job p =>
      virtual ++ [.testResult job p]
  | .processed job =>
      if job ∈ virtual.testResults.map Prod.fst then
        virtual ++ [.processed job]
      else
        virtual
  | .rawCompleted job =>
      let p :=
        harmonicRankValue K Z 0 virtual.testResults.length
      virtual ++ [.testResult job p, .processed job]

def virtualTail
    (n : ℕ) (u β : ℝ) (K Z : ℕ)
    (transcript : Online.Transcript n) : Online.Transcript n :=
  (scan n u β transcript).tail.foldl
    (virtualTailStep K Z) []

private theorem virtualTailFold_testLabels
    (K Z : ℕ)
    (virtual tail : Online.Transcript n) :
    ((tail.foldl (virtualTailStep K Z) virtual).testResults.map
        Prod.fst) =
      virtual.testResults.map Prod.fst ++ tail.startedLabels := by
  induction tail generalizing virtual with
  | nil =>
      simp
  | cons observation tail ih =>
      rw [List.foldl_cons, ih]
      cases observation with
      | testResult job p =>
          simp [virtualTailStep, List.append_assoc]
      | processed job =>
          simp only [virtualTailStep]
          split_ifs <;> simp
      | rawCompleted job =>
          simp [virtualTailStep, List.append_assoc]

theorem virtualTail_testLabels
    (n : ℕ) (u β : ℝ) (K Z : ℕ)
    (transcript : Online.Transcript n) :
    (virtualTail n u β K Z transcript).testResults.map Prod.fst =
      (scan n u β transcript).tail.startedLabels := by
  simpa [virtualTail] using
    virtualTailFold_testLabels K Z
      ([] : Online.Transcript n)
      (scan n u β transcript).tail

/-- Tests and raw first touches advance one common virtual revelation rank. -/
theorem virtualTail_testResults_length
    (n : ℕ) (u β : ℝ) (K Z : ℕ)
    (transcript : Online.Transcript n) :
    (virtualTail n u β K Z transcript).testResults.length =
      tailRank n u β transcript := by
  have hlength :=
    congrArg List.length
      (virtualTail_testLabels n u β K Z transcript)
  simpa [tailRank] using hlength

private theorem virtualTailFold_preserves_test_mem
    (K Z : ℕ)
    (virtual tail : Online.Transcript n)
    {job : Online.Label n} {p : ℝ}
    (hmem : (job, p) ∈ virtual.testResults) :
    (job, p) ∈
      (tail.foldl (virtualTailStep K Z) virtual).testResults := by
  induction tail generalizing virtual with
  | nil =>
      simpa using hmem
  | cons observation tail ih =>
      rw [List.foldl_cons]
      apply ih
      cases observation with
      | testResult job p =>
          simp [virtualTailStep, hmem]
      | processed job =>
          simp only [virtualTailStep]
          split_ifs <;> simp_all
      | rawCompleted job =>
          simp [virtualTailStep, hmem]

private theorem virtualTailFold_actual_test_mem
    (K Z : ℕ)
    (virtual tail : Online.Transcript n)
    {job : Online.Label n} {p : ℝ}
    (hmem : (job, p) ∈ tail.testResults) :
    (job, p) ∈
      (tail.foldl (virtualTailStep K Z) virtual).testResults := by
  induction tail generalizing virtual with
  | nil =>
      simp at hmem
  | cons observation tail ih =>
      cases observation with
      | testResult tested q =>
          simp only [Online.Transcript.testResults_testResult_cons,
            List.mem_cons] at hmem
          rw [List.foldl_cons]
          rcases hmem with hhead | htail
          · cases hhead
            apply virtualTailFold_preserves_test_mem
            simp [virtualTailStep]
          · exact ih
              (virtual ++ [.testResult tested q]) htail
      | processed processed =>
          rw [List.foldl_cons]
          simp only [virtualTailStep]
          split
          next h =>
            exact ih (virtual ++ [.processed processed]) hmem
          next h =>
            exact ih virtual hmem
      | rawCompleted raw =>
          rw [List.foldl_cons]
          exact ih
            (virtual ++
              [.testResult raw
                (harmonicRankValue K Z 0
                  virtual.testResults.length),
                .processed raw])
            hmem

theorem virtualTail_actual_test_mem
    (n : ℕ) (u β : ℝ) (K Z : ℕ)
    (transcript : Online.Transcript n)
    {job : Online.Label n} {p : ℝ}
    (hmem :
      (job, p) ∈
        (scan n u β transcript).tail.testResults) :
    (job, p) ∈
      (virtualTail n u β K Z transcript).testResults := by
  exact virtualTailFold_actual_test_mem
    K Z [] (scan n u β transcript).tail hmem

/-- Appending one physical post-crossing observation applies exactly one
virtual tail step. -/
theorem virtualTail_append_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    (K Z : ℕ) {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (observation : Online.Observation n) :
    virtualTail n u β K Z (transcript ++ [observation]) =
      virtualTailStep K Z
        (virtualTail n u β K Z transcript) observation := by
  have hstored :=
    (scan_crossed_iff hn hβ transcript).mpr hcross
  have hscan :=
    scan_append_of_storedCrossed hstored observation
  unfold virtualTail
  rw [hscan.2.1, List.foldl_append]
  rfl

theorem scan_tailSize_append_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (observation : Online.Observation n) :
    (scan n u β (transcript ++ [observation])).tailSize =
      (scan n u β transcript).tailSize := by
  have hstored :=
    (scan_crossed_iff hn hβ transcript).mpr hcross
  exact
    (scan_append_of_storedCrossed hstored observation).2.2

/-! ## Dynamic integral tail split and oracle -/

def quotaFraction (M A B : ℕ) : ℝ :=
  (M : ℝ) / (M + A + B : ℕ)

def tailPositiveCount (A B H : ℕ) : ℕ :=
  A * H / (A + B)

def tailZeroCount (A B H : ℕ) : ℕ :=
  H - tailPositiveCount A B H

@[simp] theorem tail_split
    (A B H : ℕ) :
    tailPositiveCount A B H + tailZeroCount A B H = H := by
  unfold tailPositiveCount tailZeroCount
  have hle :
      A * H / (A + B) ≤ H := by
    by_cases hden : A + B = 0
    · simp [hden]
    · have hmul :
          (A + B) * (A * H / (A + B)) ≤ A * H :=
        Nat.mul_div_le _ _
      have hAH : A * H ≤ (A + B) * H := by
        exact Nat.mul_le_mul_right H (Nat.le_add_right A B)
      exact Nat.le_of_mul_le_mul_left
        (hmul.trans hAH) (Nat.pos_of_ne_zero hden)
  exact Nat.add_sub_of_le hle

theorem tailPositiveCount_lt
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H) :
    tailPositiveCount A B H < H := by
  let K := tailPositiveCount A B H
  have hden : 0 < A + B := by omega
  have hmul :
      (A + B) * K ≤ A * H := by
    dsimp [K, tailPositiveCount]
    exact Nat.mul_div_le _ _
  have hstrict : A * H < (A + B) * H := by
    rw [add_mul]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos hB hH)
  exact Nat.lt_of_mul_lt_mul_left (hmul.trans_lt hstrict)

theorem tailZeroCount_pos
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H) :
    0 < tailZeroCount A B H := by
  unfold tailZeroCount
  exact Nat.sub_pos_of_lt (tailPositiveCount_lt hB hH)

theorem tail_split_cross_mul
    (A B H : ℕ) :
    B * tailPositiveCount A B H ≤
      A * tailZeroCount A B H := by
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  by_cases hden : A + B = 0
  · have hA : A = 0 := by omega
    have hB : B = 0 := by omega
    simp [hA, hB]
  · have hmul :
        (A + B) * K ≤ A * H := by
      dsimp [K, tailPositiveCount]
      exact Nat.mul_div_le _ _
    have hsplit : K + Z = H := by
      simpa [K, Z] using tail_split A B H
    have hmulReal :
        ((A + B : ℕ) : ℝ) * (K : ℝ) ≤
          (A : ℝ) * (H : ℝ) := by
      exact_mod_cast hmul
    have hsplitReal :
        (K : ℝ) + (Z : ℝ) = (H : ℝ) := by
      exact_mod_cast hsplit
    have hcrossReal :
        (B : ℝ) * (K : ℝ) ≤ (A : ℝ) * (Z : ℝ) := by
      push_cast at hmulReal
      nlinarith
    exact_mod_cast hcrossReal

theorem tail_ratio_le
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H) :
    (tailPositiveCount A B H : ℝ) /
        (tailZeroCount A B H : ℝ) ≤
      (A : ℝ) / (B : ℝ) := by
  have hZ : 0 < tailZeroCount A B H :=
    tailZeroCount_pos hB hH
  have hZreal : (0 : ℝ) < tailZeroCount A B H := by
    exact_mod_cast hZ
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  rw [div_le_div_iff₀ hZreal hBreal]
  have hcross := tail_split_cross_mul A B H
  simpa [mul_comm] using (show
    (B : ℝ) * (tailPositiveCount A B H : ℝ) ≤
      (A : ℝ) * (tailZeroCount A B H : ℝ) by
        exact_mod_cast hcross)

theorem quotaFraction_pos
    {M A B : ℕ} (hM : 0 < M) :
    0 < quotaFraction M A B := by
  unfold quotaFraction
  positivity

theorem quotaFraction_lt_one
    {M A B : ℕ} (hA : 0 < A) :
    quotaFraction M A B < 1 := by
  unfold quotaFraction
  rw [div_lt_one]
  · exact_mod_cast (by omega : M < M + A + B)
  · positivity

/-- The dynamically scaled quota oracle.  The crossing prefix fixes a tail
of size `H`; that tail is split in the prescribed rational proportion
`A : B`, with the positive part rounded down. -/
noncomputable def oracle
    (n : ℕ) (u : ℝ) (M A B : ℕ) : Online.Oracle n := by
  classical
  exact fun transcript _job =>
    let β := quotaFraction M A B
    if HiddenStoppingOracle.Crossed n u β transcript then
      let H := (scan n u β transcript).tailSize
      let K := tailPositiveCount A B H
      let Z := tailZeroCount A B H
      harmonicRankValue K Z 0 (tailRank n u β transcript)
    else u

theorem oracle_eq_cap_of_not_crossed
    {n : ℕ} {u : ℝ} {M A B : ℕ}
    {transcript : Online.Transcript n}
    (h :
      ¬ HiddenStoppingOracle.Crossed n u
        (quotaFraction M A B) transcript)
    (job : Online.Label n) :
    oracle n u M A B transcript job = u := by
  simp [oracle, h]

theorem oracle_eq_harmonic_of_crossed
    {n : ℕ} {u : ℝ} {M A B : ℕ}
    {transcript : Online.Transcript n}
    (h :
      HiddenStoppingOracle.Crossed n u
        (quotaFraction M A B) transcript)
    (job : Online.Label n) :
    oracle n u M A B transcript job =
      let H :=
        (scan n u (quotaFraction M A B) transcript).tailSize
      harmonicRankValue
        (tailPositiveCount A B H) (tailZeroCount A B H) 0
        (tailRank n u (quotaFraction M A B) transcript) := by
  simp [oracle, h]

/-- Runtime identity in cap-free form: after crossing, the next oracle value
is indexed by the number of tests in the virtual tail in which every raw
touch has already been expanded to a test/process pair. -/
theorem oracle_eq_virtual_rank_of_crossed
    {n : ℕ} {u : ℝ} {M A B : ℕ}
    {transcript : Online.Transcript n}
    (h :
      HiddenStoppingOracle.Crossed n u
        (quotaFraction M A B) transcript)
    (job : Online.Label n) :
    oracle n u M A B transcript job =
      let β := quotaFraction M A B
      let H := (scan n u β transcript).tailSize
      let K := tailPositiveCount A B H
      let Z := tailZeroCount A B H
      harmonicRankValue K Z 0
        (virtualTail n u β K Z transcript).testResults.length := by
  rw [oracle_eq_harmonic_of_crossed h job]
  dsimp only
  rw [virtualTail_testResults_length]

/-- Every public answer of the mixed oracle is legal at the finite cap.
The stronger raw margin is used only in the harmonic phase; the cap phase
returns `u` itself. -/
theorem oracle_admissible
    {n : ℕ} {u : ℝ} {M A B : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u) :
    (oracle n u M A B).Admissible (.finite u) := by
  have hu : 0 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  intro transcript job
  by_cases hcross :
      HiddenStoppingOracle.Crossed n u
        (quotaFraction M A B) transcript
  · rw [oracle_eq_harmonic_of_crossed hcross job]
    dsimp only
    let H :=
      (scan n u (quotaFraction M A B) transcript).tailSize
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    by_cases hH : H = 0
    · simp [K, Z, H, hH, tailPositiveCount, tailZeroCount,
        harmonicRankValue, Online.ValueAdmissible, hu.le]
    · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
      have hZ : 0 < Z := by
        dsimp [Z]
        exact tailZeroCount_pos hB hHpos
      have hratio :
          (K : ℝ) / (Z : ℝ) ≤ (A : ℝ) / (B : ℝ) := by
        dsimp [K, Z]
        exact tail_ratio_le hB hHpos
      let rank :=
        tailRank n u (quotaFraction M A B) transcript
      by_cases hrank : rank < K
      · rw [harmonicRankValue_of_lt hrank]
        have hindex : K - 1 - rank ≤ K := by omega
        have hlevel :=
          harmonicLevel_le_one_add_ratio hZ hindex
        have hnonneg :
            0 ≤ harmonicLevel (Z : ℝ) 0 (K - 1 - rank) :=
          (harmonicLevel_one_le
            (by exact_mod_cast hZ) (le_refl 0) _).trans'
              zero_le_one
        constructor
        · exact hnonneg
        · linarith
      · rw [harmonicRankValue_of_ge
          (Nat.le_of_not_gt hrank)]
        exact ⟨le_rfl, hu.le⟩
  · rw [oracle_eq_cap_of_not_crossed hcross job]
    exact ⟨hu.le, le_rfl⟩

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
