import SchedulingPaper.MixedQuotaTerminalAccounting
import SchedulingPaper.MixedQuotaCapExchange
import SchedulingPaper.MixedQuotaNoCross
import SchedulingPaper.CompletionPairDecomposition
import SchedulingPaper.MixedQuotaExchangeAlgebra
import Mathlib.Tactic

/-!
# Global exchange for the completed mixed-quota run

This file first recovers the literal first-crossing prefix from a
post-crossing history.  In particular it exposes the raw/cap counts used by
the finite mixed benchmark and proves their exact size identity and quota
window.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- A public prefix ends at the first crossing, which is either a cap test
or a raw first touch. -/
def IsMixedFirstCrossingPrefix
    (n : ℕ) (u β : ℝ)
    (crossingPrefix : Online.Transcript n) : Prop :=
  (∃ before job,
      crossingPrefix =
        before ++ [Online.Observation.testResult job u] ∧
      HiddenStoppingOracle.FirstCrossingAt
        n u β before (.testResult job u)) ∨
    (∃ before job,
      crossingPrefix =
        before ++ [Online.Observation.rawCompleted job] ∧
      HiddenStoppingOracle.FirstCrossingAt
        n u β before (.rawCompleted job))

/-- The persistent data attached to the literal first-crossing prefix. -/
def CrossingPrefixData
    (n : ℕ) (u β : ℝ) (H : ℕ)
    (transcript : Online.Transcript n) : Prop :=
  ∃ crossingPrefix : Online.Transcript n,
    transcript =
      crossingPrefix ++ (scan n u β transcript).tail ∧
    IsMixedFirstCrossingPrefix n u β crossingPrefix ∧
    crossingPrefix.AllTestsEqual u ∧
    crossingPrefix.startedLabels.Nodup ∧
    H = n - crossingPrefix.startedLabels.length

private theorem allTestsEqual_append_cap
    {u : ℝ} {transcript : Online.Transcript n}
    (hall : transcript.AllTestsEqual u)
    (job : Online.Label n) :
    (transcript ++
      [Online.Observation.testResult job u]).AllTestsEqual u := by
  intro tested p hp
  rw [Online.Transcript.testResults_append] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hall tested p hp
  · have heq : (tested, p) = (job, u) := by
      simpa using hp
    exact congrArg Prod.snd heq

private theorem allTestsEqual_append_raw
    {u : ℝ} {transcript : Online.Transcript n}
    (hall : transcript.AllTestsEqual u)
    (job : Online.Label n) :
    (transcript ++
      [Online.Observation.rawCompleted job]).AllTestsEqual u := by
  intro tested p hp
  rw [Online.Transcript.testResults_append] at hp
  exact hall tested p (by simpa using hp)

private theorem CrossingPrefixData.append
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    {H : ℕ} {transcript : Online.Transcript n}
    (hcross :
      HiddenStoppingOracle.Crossed n u β transcript)
    (data : CrossingPrefixData n u β H transcript)
    (observation : Online.Observation n) :
    CrossingPrefixData n u β H
      (transcript ++ [observation]) := by
  obtain
    ⟨crossingPrefix, hdecomp, hfirst, hall, hnodup, hH⟩ :=
      data
  have hscan :=
    scan_append_of_storedCrossed
      ((scan_crossed_iff hn hβ transcript).mpr hcross)
      observation
  refine ⟨crossingPrefix, ?_, hfirst, hall, hnodup, hH⟩
  rw [hscan.2.1]
  calc
    transcript ++ [observation] =
        (crossingPrefix ++ (scan n u β transcript).tail) ++
          [observation] :=
      congrArg (fun xs => xs ++ [observation]) hdecomp
    _ = crossingPrefix ++
        ((scan n u β transcript).tail ++ [observation]) := by
      rw [List.append_assoc]

/-- Phase-indexed form of the retained first-crossing data. -/
def MixedPhase.crossingPrefixInvariant
    (n : ℕ) (u β : ℝ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post H _ _ _ _ =>
      CrossingPrefixData n u β H config.transcript

theorem MixedQuotaHistory.crossingPrefix_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.crossingPrefixInvariant n u β config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow =>
      trivial
  | preProcessCap =>
      trivial
  | preRawBelow =>
      trivial
  | @preTestCross caps config previous job hjob hcross H hH =>
      have hfull :=
        MixedQuotaHistory.preTestCross
          previous job hjob hcross H hH
      have hbefore := previous.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.testResult job u) hcross
      simp only [MixedPhase.crossingPrefixInvariant]
      refine
        ⟨config.transcript ++ [.testResult job u],
          ?_, Or.inl ⟨config.transcript, job, rfl,
            ⟨hbefore, hcross⟩⟩,
          allTestsEqual_append_cap
            previous.pre_allTestsEqual job,
          hfull.started_history_invariant.nodup, hH⟩
      simp [hscan.2.1, htail]
  | @preRawCross caps config previous job hjob hcross H hH =>
      have hfull :=
        MixedQuotaHistory.preRawCross
          previous job hjob hcross H hH
      have hbefore := previous.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.rawCompleted job) hcross
      simp only [MixedPhase.crossingPrefixInvariant]
      refine
        ⟨config.transcript ++ [.rawCompleted job],
          ?_, Or.inr ⟨config.transcript, job, rfl,
            ⟨hbefore, hcross⟩⟩,
          allTestsEqual_append_raw
            previous.pre_allTestsEqual job,
          hfull.started_history_invariant.nodup, hH⟩
      simp [hscan.2.1, htail]
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ)
        (.testResult job
          (harmonicLevel
            (tailZeroCount A B H : ℝ) 0 (L - 1)))
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ)
        (.testResult job 0)
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ) (.processed job)
  | @postProcessZero H L z caps pending config
      history job hjob hvirtual ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ) (.processed job)
  | @postProcessCap H L z before after pending config
      job history hjob hvirtual ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ) (.processed job)
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ) (.rawCompleted job)
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      simp only [MixedPhase.crossingPrefixInvariant] at ih ⊢
      exact ih.append hn hβ
        (history.post_crossed hn hβ) (.rawCompleted job)

/-- Every reachable post state retains its actual first-crossing prefix. -/
theorem MixedQuotaHistory.crossingPrefixData
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    CrossingPrefixData n u β H config.transcript :=
  history.crossingPrefix_invariant hn hβ

/-- Concrete raw and cap-test counts of a crossing prefix. -/
def crossingRawCount
    (crossingPrefix : Online.Transcript n) : ℕ :=
  HiddenStoppingOracle.rawCount crossingPrefix

def crossingCapCount
    (crossingPrefix : Online.Transcript n) : ℕ :=
  crossingPrefix.testResults.length

/-- The crossing prefix partitions the ambient labels into raw-prefix,
cap-tested, and dynamically rounded harmonic-tail labels. -/
theorem CrossingPrefixData.size_identity
    {n : ℕ} {u β : ℝ} {A B H : ℕ}
    {transcript : Online.Transcript n}
    (data : CrossingPrefixData n u β H transcript) :
    ∃ crossingPrefix : Online.Transcript n,
      transcript =
          crossingPrefix ++ (scan n u β transcript).tail ∧
      IsMixedFirstCrossingPrefix n u β crossingPrefix ∧
      crossingPrefix.AllTestsEqual u ∧
      crossingPrefix.startedLabels.Nodup ∧
      n =
        crossingRawCount crossingPrefix +
          crossingCapCount crossingPrefix +
          tailPositiveCount A B H +
          tailZeroCount A B H := by
  obtain
    ⟨crossingPrefix, hdecomp, hfirst, hall, hnodup, hH⟩ :=
      data
  have hstarted :=
    crossingPrefix.startedLabels_length_eq_raw_add_tests
  have hsplit := tail_split A B H
  have hbound :
      crossingPrefix.startedLabels.length ≤ n := by
    calc
      crossingPrefix.startedLabels.length =
          crossingPrefix.startedLabels.toFinset.card := by
        rw [List.toFinset_card_of_nodup hnodup]
      _ ≤ Fintype.card (Online.Label n) :=
        Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  refine
    ⟨crossingPrefix, hdecomp, hfirst, hall, hnodup, ?_⟩
  unfold crossingRawCount crossingCapCount
  omega

/-- Normalized one-job quota window at the recovered first crossing. -/
theorem CrossingPrefixData.quota_window
    {n : ℕ} {u β : ℝ} {H : ℕ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hH : 0 < H)
    {transcript : Online.Transcript n}
    (data : CrossingPrefixData n u β H transcript) :
    ∃ crossingPrefix : Online.Transcript n,
      transcript =
          crossingPrefix ++ (scan n u β transcript).tail ∧
      β ≤
          (crossingCapCount crossingPrefix : ℝ) /
            ((n : ℝ) - crossingRawCount crossingPrefix) ∧
      (crossingCapCount crossingPrefix : ℝ) /
            ((n : ℝ) - crossingRawCount crossingPrefix) - β <
        1 / ((n : ℝ) - crossingRawCount crossingPrefix) := by
  obtain
    ⟨crossingPrefix, hdecomp, hfirst, hall, hnodup, hHdef⟩ :=
      data
  have hlong :
      HiddenStoppingOracle.longCount u crossingPrefix =
        crossingCapCount crossingPrefix := by
    simpa [crossingCapCount] using
      HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
        hall
  refine ⟨crossingPrefix, hdecomp, ?_⟩
  have hbound :
      crossingPrefix.startedLabels.length ≤ n := by
    calc
      crossingPrefix.startedLabels.length =
          crossingPrefix.startedLabels.toFinset.card := by
        rw [List.toFinset_card_of_nodup hnodup]
      _ ≤ Fintype.card (Online.Label n) :=
        Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hlength :
      crossingPrefix.startedLabels.length + H = n := by
    omega
  rcases hfirst with
      ⟨before, job, rfl, hcross⟩ |
      ⟨before, job, rfl, hcross⟩
  · have hv :
        crossingRawCount
            (before ++ [.testResult job u]) =
          HiddenStoppingOracle.rawCount before := by
        simp [crossingRawCount, HiddenStoppingOracle.rawCount]
    have hk :
        crossingCapCount
            (before ++ [.testResult job u]) =
          HiddenStoppingOracle.longCount u before + 1 := by
        rw [← hlong]
        simp [HiddenStoppingOracle.longCount]
    have hremainingNat :
        HiddenStoppingOracle.rawCount before < n := by
      have hstarted :=
        (before ++
          [Online.Observation.testResult job u]).startedLabels_length_eq_raw_add_tests
      have hprefixLen :
          (before ++
            [Online.Observation.testResult job u]).startedLabels.length =
            before.startedLabels.length + 1 := by simp
      have hbeforeStarted :=
        before.startedLabels_length_eq_raw_add_tests
      omega
    have hremaining :
        0 < (n : ℝ) -
          HiddenStoppingOracle.rawCount before := by
      exact sub_pos.mpr (by exact_mod_cast hremainingNat)
    have hover :=
      HiddenStoppingOracle.firstCrossing_long_overshoot
        hcross hremaining
    dsimp only at hover
    rw [hv, hk]
    push_cast
    constructor
    · linarith [hover.1]
    · exact hover.2
  · have hv :
        crossingRawCount
            (before ++ [.rawCompleted job]) =
          HiddenStoppingOracle.rawCount before + 1 := by
        simp [crossingRawCount, HiddenStoppingOracle.rawCount]
    have hk :
        crossingCapCount
            (before ++ [.rawCompleted job]) =
          HiddenStoppingOracle.longCount u before := by
        rw [← hlong]
        simp [HiddenStoppingOracle.longCount]
    have hremainingNat :
        HiddenStoppingOracle.rawCount before + 1 < n := by
      have hstarted :=
        (before ++
          [Online.Observation.rawCompleted job]).startedLabels_length_eq_raw_add_tests
      have hprefixLen :
          (before ++
            [Online.Observation.rawCompleted job]).startedLabels.length =
            before.startedLabels.length + 1 := by simp
      have hbeforeStarted :=
        before.startedLabels_length_eq_raw_add_tests
      omega
    have hremaining :
        0 < (n : ℝ) -
          ((HiddenStoppingOracle.rawCount before : ℝ) + 1) := by
      have hcast :
          ((HiddenStoppingOracle.rawCount before + 1 : ℕ) : ℝ) <
            (n : ℝ) := by
        exact_mod_cast hremainingNat
      push_cast at hcast
      linarith
    have hover :=
      HiddenStoppingOracle.firstCrossing_raw_overshoot
        hβ0 hβ1 hcross hremaining
    dsimp only at hover
    rw [hv, hk]
    norm_num
    constructor
    · linarith [hover.1]
    · simpa using hover.2

/-! ## The harmonic tail with the crossing caps already pending -/

/-- Turn the cap jobs which are still tested at the crossing into ordinary
positive pending entries.  This lets the existing harmonic potential account
for their later processing without introducing a second potential. -/
def capPendingEntries
    (u : ℝ) (caps : MixedCapPending n) : MixedTailPending n :=
  caps.map (fun job => (job, u))

@[simp] theorem capPendingEntries_nil (u : ℝ) :
    capPendingEntries u ([] : MixedCapPending n) = [] := rfl

@[simp] theorem capPendingEntries_append
    (u : ℝ) (left right : MixedCapPending n) :
    capPendingEntries u (left ++ right) =
      capPendingEntries u left ++ capPendingEntries u right := by
  simp [capPendingEntries]

@[simp] theorem capPendingEntries_cons
    (u : ℝ) (job : Online.Label n) (rest : MixedCapPending n) :
    capPendingEntries u (job :: rest) =
      (job, u) :: capPendingEntries u rest := rfl

@[simp] theorem capPendingEntries_values
    (u : ℝ) (caps : MixedCapPending n) :
    (capPendingEntries u caps).values =
      List.replicate caps.length u := by
  induction caps with
  | nil => rfl
  | cons job caps ih =>
      rw [capPendingEntries_cons,
        MixedTailPending.values_cons, ih]
      change
        u :: List.replicate caps.length u =
          List.replicate (caps.length + 1) u
      rw [show caps.length + 1 = Nat.succ caps.length by omega,
        List.replicate_succ]

/-- A harmonic history whose initial state may already contain the cap jobs
tested before the first crossing.  Apart from that initial pending list this
is the same state machine as `MixedTailHistory`. -/
inductive MixedAugmentedTailHistory
    (K Z : ℕ) (u : ℝ) (initialCaps : MixedCapPending n) :
    (L z : ℕ) → MixedTailPending n →
      Online.Transcript n → Prop
  | initial :
      MixedAugmentedTailHistory K Z u initialCaps
        K Z (capPendingEntries u initialCaps) []
  | testPositive
      {L z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history :
        MixedAugmentedTailHistory K Z u initialCaps
          L z pending transcript)
      (hL : 0 < L) (job : Online.Label n) :
      MixedAugmentedTailHistory K Z u initialCaps
        (L - 1) z
        (pending ++
          [(job, harmonicLevel (Z : ℝ) 0 (L - 1))])
        (transcript ++
          [.testResult job
            (harmonicLevel (Z : ℝ) 0 (L - 1))])
  | testZero
      {z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history :
        MixedAugmentedTailHistory K Z u initialCaps
          0 z pending transcript)
      (hz : 0 < z) (job : Online.Label n) :
      MixedAugmentedTailHistory K Z u initialCaps
        0 (z - 1) pending
        (transcript ++ [.testResult job 0])
  | processPositive
      {L z : ℕ} {before after : MixedTailPending n}
      {transcript : Online.Transcript n}
      (job : Online.Label n) (p : ℝ)
      (history :
        MixedAugmentedTailHistory K Z u initialCaps
          L z (before ++ (job, p) :: after) transcript) :
      MixedAugmentedTailHistory K Z u initialCaps
        L z (before ++ after)
        (transcript ++ [.processed job])
  | processZero
      {L z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history :
        MixedAugmentedTailHistory K Z u initialCaps
          L z pending transcript)
      (job : Online.Label n) :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending (transcript ++ [.processed job])

/-- Every pending value in an augmented history dominates the next hidden
harmonic level.  The only new base case is supplied by raw safety for `u`. -/
theorem MixedAugmentedTailHistory.pending_lower
    {K Z : ℕ} (hZ : 0 < Z) {u : ℝ}
    {initialCaps : MixedCapPending n}
    (huLevel : harmonicLevel (Z : ℝ) 0 K ≤ u)
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending transcript) :
    ∀ entry ∈ pending,
      harmonicLevel (Z : ℝ) 0 L ≤ entry.2 := by
  induction history with
  | initial =>
      intro entry hentry
      rcases List.mem_map.mp hentry with ⟨job, _hjob, rfl⟩
      exact huLevel
  | @testPositive L z pending transcript history hL job ih =>
      intro entry hentry
      rw [List.mem_append] at hentry
      rcases hentry with hold | hnew
      · exact
          (harmonicLevel_strictMono
            (γ := 0) (by exact_mod_cast hZ)
            (Nat.sub_lt (Nat.zero_lt_of_lt hL) (by omega))).le.trans
            (ih entry hold)
      · simp only [List.mem_singleton] at hnew
        rcases hnew with rfl
        rfl
  | testZero history hz job ih =>
      simpa using ih
  | @processPositive L z before after transcript job p history ih =>
      intro entry hentry
      apply ih entry
      rw [List.mem_append] at hentry ⊢
      rcases hentry with hbefore | hafter
      · exact Or.inl hbefore
      · exact Or.inr (by simp [hafter])
  | processZero history job ih =>
      exact ih

theorem MixedAugmentedTailHistory.positive_phase
    {K Z : ℕ} {u : ℝ} {initialCaps : MixedCapPending n}
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending transcript) :
    L = 0 ∨ z = Z := by
  induction history with
  | initial =>
      by_cases hK : K = 0
      · exact Or.inl hK
      · exact Or.inr rfl
  | @testPositive L z pending transcript history hL job ih =>
      by_cases hnext : L - 1 = 0
      · exact Or.inl hnext
      · rcases ih with hzero | hz
        · exact (hL.ne' hzero).elim
        · exact Or.inr hz
  | testZero history hz job ih =>
      exact Or.inl rfl
  | processPositive history job p ih =>
      exact ih
  | processZero history job ih =>
      exact ih

/-- A pending positive entry either was already a crossing cap, or its test
appears in the augmented tail transcript. -/
theorem MixedAugmentedTailHistory.pending_mem_source
    {K Z : ℕ} {u : ℝ} {initialCaps : MixedCapPending n}
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending transcript) :
    ∀ entry ∈ pending,
      entry ∈ capPendingEntries u initialCaps ∨
        entry ∈ transcript.testResults := by
  induction history with
  | initial =>
      intro entry hentry
      exact Or.inl hentry
  | @testPositive L z pending transcript history hL job ih =>
      intro entry hentry
      rw [List.mem_append] at hentry
      rcases hentry with hold | hnew
      · rcases ih entry hold with hcap | htest
        · exact Or.inl hcap
        · exact Or.inr (by
            rw [Online.Transcript.testResults_append]
            exact List.mem_append.mpr (Or.inl htest))
      · right
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inr (by simpa using hnew))
  | testZero history hz job ih =>
      intro entry hentry
      rcases ih entry hentry with hcap | htest
      · exact Or.inl hcap
      · exact Or.inr (by
          rw [Online.Transcript.testResults_append]
          exact List.mem_append.mpr (Or.inl htest))
  | @processPositive L z before after transcript job p history ih =>
      intro entry hentry
      have hold : entry ∈ before ++ (job, p) :: after := by
        rw [List.mem_append] at hentry ⊢
        rcases hentry with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by simp [hafter])
      rcases ih entry hold with hcap | htest
      · exact Or.inl hcap
      · exact Or.inr (by simpa using htest)
  | processZero history job ih =>
      intro entry hentry
      rcases ih entry hentry with hcap | htest
      · exact Or.inl hcap
      · exact Or.inr (by
          rw [Online.Transcript.testResults_append]
          exact List.mem_append.mpr (Or.inl htest))

/-- The ordinary harmonic amortized lower bound remains valid when the
initial pending list consists of cap jobs. -/
theorem MixedAugmentedTailHistory.amortized_lower
    {K Z : ℕ} (hZ : 0 < Z) {u : ℝ}
    {initialCaps : MixedCapPending n}
    (huLevel : harmonicLevel (Z : ℝ) 0 K ≤ u)
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending transcript)
    (processingTime : Online.Label n → ℝ)
    (hcaps :
      ∀ job ∈ initialCaps, processingTime job = u)
    (hmatch : MixedTailMatches processingTime transcript) :
    harmonicDynamicPotential (Z : ℝ) 0 K Z
        (capPendingEntries u initialCaps).values ≤
      Online.completionCost .infinite processingTime transcript +
        Online.transcriptElapsed .infinite processingTime transcript *
          harmonicUnfinished L z pending +
        harmonicDynamicPotential (Z : ℝ) 0 L z pending.values := by
  induction history with
  | initial =>
      simp [harmonicUnfinished, Online.completionCost,
        Online.completionCostFrom]
  | @testPositive L z pending transcript history hL job ih =>
      let p := harmonicLevel (Z : ℝ) 0 (L - 1)
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hmatch.1 job p
        simp [p]
      have hp1 : 1 ≤ p := by
        dsimp [p]
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) _
      have hp0 : p ≠ 0 := by
        linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.testResult job p)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.testResult job p)
      have hpot :=
        harmonicDynamicPotential_test_positive
          (Z : ℝ) 0 (z := z) pending.values hL
      simp only [MixedTailPending.values_append,
        MixedTailPending.values_cons, MixedTailPending.values_nil,
        List.append_nil, p] at hpot ⊢
      simp [Online.Observation.completionLabel, hp0,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_singleton]
      push_cast at hpot hold ⊢
      have hLcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hL))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hLcast]
      simp only [MixedTailPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @testZero z pending transcript history hz job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.testResult job 0)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.testResult job 0)
      have hpot :=
        harmonicDynamicPotential_test_zero
          (Z : ℝ) 0 pending.values hz
      simp [Online.Observation.completionLabel,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      push_cast at hpot hold ⊢
      have hzcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hz))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hzcast]
      simp only [MixedTailPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @processPositive L z before after transcript job p history ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        rcases history.pending_mem_source (job, p) (by simp) with
            hcap | htest
        · rcases List.mem_map.mp hcap with
            ⟨capJob, hcapJob, heq⟩
          have hjobEq : capJob = job :=
            congrArg Prod.fst heq
          have hpEq : u = p :=
            congrArg Prod.snd heq
          subst capJob
          exact (hcaps job hcapJob).trans hpEq
        · exact hprefix.1 job p htest
      have hpLower :
          harmonicLevel (Z : ℝ) 0 L ≤ p := by
        apply history.pending_lower hZ huLevel (job, p)
        simp
      have hp1 : 1 ≤ p :=
        (harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) L).trans hpLower
      have hp0 : p ≠ 0 := by
        linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.processed job)
      have hpot :=
        harmonicDynamicPotential_process
          (ξ := (Z : ℝ)) (γ := 0)
          (by exact_mod_cast hZ) (le_refl 0)
          (L := L) (z := z)
          (before := before.values) (after := after.values)
          (p := p)
          (by
            rcases history.positive_phase with hzero | hzEq
            · exact Or.inl hzero
            · exact Or.inr (by exact_mod_cast hzEq))
          hpLower
      simp only [MixedTailPending.values_append,
        MixedTailPending.values_cons] at hpot hold ⊢
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap, hp0] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_cons,
        MixedTailPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      rw [hcost, htime]
      ring_nf at hpot hold ⊢
      nlinarith
  | @processZero L z pending transcript history job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpnonneg : 0 ≤ processingTime job :=
        hprefix.2 job
      have htimeNonneg :
          0 ≤ Online.transcriptElapsed .infinite
            processingTime transcript := by
        exact Online.transcriptElapsed_nonneg
          (by simp [Cap.Valid]) hprefix.2 transcript
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.processed job)
      by_cases hpzero : processingTime job = 0
      · simp [Online.Observation.completionLabel,
          Online.Observation.duration, hpzero] at hcost htime
        rw [hcost, htime]
        simpa [harmonicUnfinished] using hold
      · have hppos : 0 < processingTime job :=
          lt_of_le_of_ne hpnonneg (Ne.symm hpzero)
        simp [Online.Observation.completionLabel,
          Online.Observation.duration, hpzero] at hcost htime
        rw [hcost, htime]
        unfold harmonicUnfinished at *
        push_cast at hold ⊢
        ring_nf at hold ⊢
        nlinarith

/-- The augmented tail has enough completion observations to finish every
new tail job and every cap which was pending at the crossing.  Administrative
processing of a zero-valued job can only make the displayed lower bound
stronger. -/
theorem MixedAugmentedTailHistory.completionCount_lower
    {K Z : ℕ} (hZ : 0 < Z) {u : ℝ}
    {initialCaps : MixedCapPending n}
    (huLevel : harmonicLevel (Z : ℝ) 0 K ≤ u)
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history :
      MixedAugmentedTailHistory K Z u initialCaps
        L z pending transcript)
    (processingTime : Online.Label n → ℝ)
    (hcaps :
      ∀ job ∈ initialCaps, processingTime job = u)
    (hmatch : MixedTailMatches processingTime transcript) :
    initialCaps.length + K + Z ≤
      Online.completionCount processingTime transcript +
        L + z + pending.length := by
  induction history with
  | initial =>
      simp [capPendingEntries, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | @testPositive L z pending transcript history hL job ih =>
      let p := harmonicLevel (Z : ℝ) 0 (L - 1)
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hmatch.1 job p
        simp [p]
      have hp1 : 1 ≤ p := by
        dsimp [p]
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) _
      have hp0 : processingTime job ≠ 0 := by
        rw [hpmap]
        linarith
      rw [Online.completionCount_append_singleton]
      simp [Online.Observation.completionLabel, hp0]
      omega
  | @testZero z pending transcript history hz job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = 0 := by
        apply hmatch.1 job 0
        simp
      rw [Online.completionCount_append_singleton]
      simp [Online.Observation.completionLabel, hpmap]
      omega
  | @processPositive L z before after transcript job p history ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        rcases history.pending_mem_source (job, p) (by simp) with
            hcap | htest
        · rcases List.mem_map.mp hcap with
            ⟨capJob, hcapJob, heq⟩
          have hjobEq : capJob = job :=
            congrArg Prod.fst heq
          have hpEq : u = p :=
            congrArg Prod.snd heq
          subst capJob
          exact (hcaps job hcapJob).trans hpEq
        · exact hprefix.1 job p htest
      have hpLower :
          harmonicLevel (Z : ℝ) 0 L ≤ p := by
        apply history.pending_lower hZ huLevel (job, p)
        simp
      have hp1 : 1 ≤ p :=
        (harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) L).trans hpLower
      have hp0 : processingTime job ≠ 0 := by
        rw [hpmap]
        linarith
      rw [Online.completionCount_append_singleton]
      simp [Online.Observation.completionLabel, hp0] at *
      omega
  | @processZero L z pending transcript history job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      rw [Online.completionCount_append_singleton]
      by_cases hp0 : processingTime job = 0
      · simpa [Online.Observation.completionLabel, hp0] using hold
      · simp [Online.Observation.completionLabel, hp0]
        omega

/-! ## Expanding finite raw completions while retaining cap processings -/

/-- Structural relation between the physical post-crossing suffix and the
augmented infinite-cap transcript.  Unlike `virtualTail`, this expansion
retains process observations for caps which were tested before crossing. -/
inductive MixedTailExpansion :
    Online.Transcript n → Online.Transcript n → Prop
  | initial :
      MixedTailExpansion ([] : Online.Transcript n) []
  | testResult
      {physical virtual : Online.Transcript n}
      (expansion : MixedTailExpansion physical virtual)
      (job : Online.Label n) (p : ℝ) :
      MixedTailExpansion
        (physical ++ [.testResult job p])
        (virtual ++ [.testResult job p])
  | processed
      {physical virtual : Online.Transcript n}
      (expansion : MixedTailExpansion physical virtual)
      (job : Online.Label n) :
      MixedTailExpansion
        (physical ++ [.processed job])
        (virtual ++ [.processed job])
  | rawCompleted
      {physical virtual : Online.Transcript n}
      (expansion : MixedTailExpansion physical virtual)
      (job : Online.Label n) (p : ℝ) :
      MixedTailExpansion
        (physical ++ [.rawCompleted job])
        (virtual ++ [.testResult job p, .processed job])

/-- Raw expansion preserves the number of completed jobs: its virtual
test/process pair has exactly one completion observation, whether the job
has zero or positive processing time. -/
theorem MixedTailExpansion.completionCount_eq
    {physical virtual : Online.Transcript n}
    (expansion : MixedTailExpansion physical virtual)
    (processingTime : Online.Label n → ℝ)
    (hmatch : MixedTailMatches processingTime virtual) :
    Online.completionCount processingTime physical =
      Online.completionCount processingTime virtual := by
  induction expansion with
  | initial =>
      rfl
  | testResult expansion job p ih =>
      have hprefix := hmatch.of_append
      rw [Online.completionCount_append_singleton,
        Online.completionCount_append_singleton, ih hprefix]
  | processed expansion job ih =>
      have hprefix := hmatch.of_append
      rw [Online.completionCount_append_singleton,
        Online.completionCount_append_singleton, ih hprefix]
  | @rawCompleted physical virtual expansion job p ih =>
      have hmatchAssoc :
          MixedTailMatches processingTime
            ((virtual ++
                [Online.Observation.testResult job p]) ++
              [Online.Observation.processed job]) := by
        simpa [List.append_assoc] using hmatch
      have hprefix :=
        hmatchAssoc.of_append.of_append
      have hpmap : processingTime job = p := by
        apply hmatch.1 job p
        simp
      have hshape :
          virtual ++
              [Online.Observation.testResult job p,
                Online.Observation.processed job] =
            (virtual ++
              [Online.Observation.testResult job p]) ++
                [Online.Observation.processed job] := by
        simp [List.append_assoc]
      rw [hshape]
      rw [Online.completionCount_append_singleton,
        Online.completionCount_append_singleton,
        Online.completionCount_append_singleton, ih hprefix]
      by_cases hp : p = 0
      · simp [Online.Observation.completionLabel, hpmap, hp]
      · simp [Online.Observation.completionLabel, hpmap, hp]

/-- A safe harmonic expansion creates no new cap-valued public test in its
physical transcript. -/
theorem MixedTailExpansion.physical_longCount_zero_of_safe
    {u : ℝ} {physical virtual : Online.Transcript n}
    (expansion : MixedTailExpansion physical virtual)
    (hsafe :
      ∀ job p, (job, p) ∈ virtual.testResults →
        1 + p ≤ u) :
    HiddenStoppingOracle.longCount u physical = 0 := by
  induction expansion with
  | initial =>
      simp
  | @testResult physical virtual expansion job p ih =>
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        apply hsafe tested q
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hq)
      have hold := ih hsafePrefix
      have hpne : p ≠ u := by
        intro hp
        subst p
        have := hsafe job u (by simp)
        linarith
      rw [HiddenStoppingOracle.longCount_append]
      simp [HiddenStoppingOracle.longCount, hold, hpne]
  | @processed physical virtual expansion job ih =>
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        exact hsafe tested q (by simpa using hq)
      have hold := ih hsafePrefix
      simpa using hold
  | @rawCompleted physical virtual expansion job p ih =>
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        apply hsafe tested q
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hq)
      have hold := ih hsafePrefix
      simpa using hold

/-- Expanding a raw completion into its safe test/process block, while
leaving every other observation unchanged, can only decrease cost and
elapsed time. -/
theorem MixedTailExpansion.dominates
    {n : ℕ} {u : ℝ} (hu : 0 < u)
    {physical virtual : Online.Transcript n}
    (expansion : MixedTailExpansion physical virtual)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job,
        Online.ValueAdmissible (.finite u) (processingTime job))
    (hmatch : MixedTailMatches processingTime virtual)
    (hsafe :
      ∀ job p, (job, p) ∈ virtual.testResults →
        1 + p ≤ u) :
    Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical ∧
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical := by
  induction expansion with
  | initial =>
      simp [Online.completionCost, Online.completionCostFrom]
  | @testResult physical virtual expansion job p ih =>
      have hprefix : MixedTailMatches processingTime virtual :=
        hmatch.of_append
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        apply hsafe tested q
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hq)
      have hold := ih hprefix hsafePrefix
      rw [completionCost_append_singleton,
        completionCost_append_singleton,
        transcriptElapsed_append_singleton,
        transcriptElapsed_append_singleton]
      simp only [Online.Observation.completionLabel,
        Online.Observation.duration]
      by_cases hp : p = 0
      · simp [hp]
        exact ⟨add_le_add hold.1
          (add_le_add hold.2 (le_refl 1)), hold.2⟩
      · simp [hp]
        exact hold
  | @processed physical virtual expansion job ih =>
      have hprefix : MixedTailMatches processingTime virtual :=
        hmatch.of_append
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        exact hsafe tested q (by simpa using hq)
      have hold := ih hprefix hsafePrefix
      rw [completionCost_append_singleton,
        completionCost_append_singleton,
        transcriptElapsed_append_singleton,
        transcriptElapsed_append_singleton]
      simp only [Online.Observation.completionLabel,
        Online.Observation.duration]
      by_cases hp : processingTime job = 0
      · simp [hp]
        exact hold
      · simp [hp]
        exact ⟨add_le_add hold.1
          (add_le_add hold.2 (le_refl _)),
          hold.2⟩
  | @rawCompleted physical virtual expansion job p ih =>
      have hmatchAssoc :
          MixedTailMatches processingTime
            ((virtual ++ [.testResult job p]) ++
              [.processed job]) := by
        simpa [List.append_assoc] using hmatch
      have hprefix :
          MixedTailMatches processingTime virtual :=
        hmatchAssoc.of_append.of_append
      have hnew :
          (job, p) ∈
            (virtual ++
              [Online.Observation.testResult job p,
                Online.Observation.processed job]).testResults := by
        rw [Online.Transcript.testResults_append]
        simp
      have hpmap : processingTime job = p :=
        hmatch.1 job p hnew
      have hpSafe : 1 + p ≤ u :=
        hsafe job p hnew
      have hsafePrefix :
          ∀ tested q, (tested, q) ∈ virtual.testResults →
            1 + q ≤ u := by
        intro tested q hq
        apply hsafe tested q
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hq)
      have hold := ih hprefix hsafePrefix
      rw [show
          virtual ++ [.testResult job p, .processed job] =
            (virtual ++ [.testResult job p]) ++
              [.processed job] by simp [List.append_assoc]]
      simp only [completionCost_append_singleton,
        transcriptElapsed_append_singleton,
        Online.Observation.completionLabel,
        Online.Observation.duration, Online.rawDuration, hpmap]
      by_cases hpzero : p = 0
      · simp [hpzero] at hpSafe ⊢
        constructor <;> linarith
      · simp [hpzero]
        constructor <;> linarith

/-! ## Extracting the augmented tail from the concrete mixed history -/

/-- Phase-indexed record that every live pre-crossing cap has its public
cap-valued test. -/
def MixedPhase.capTestInvariant
    (u : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre caps =>
      ∀ job ∈ caps, (job, u) ∈ config.transcript.testResults
  | .post _ _ _ _ _ => True

theorem MixedQuotaHistory.capTest_invariant
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.capTestInvariant u config := by
  induction history with
  | initial =>
      intro job hmem
      simp at hmem
  | @preTestBelow caps config history tested hjob hbelow ih =>
      intro job hmem
      rw [List.mem_append] at hmem
      rw [Online.Transcript.testResults_append]
      rcases hmem with hold | hnew
      · exact List.mem_append.mpr (Or.inl (ih job hold))
      · have heq : job = tested := by simpa using hnew
        subst job
        simp
  | @preProcessCap before after config processed history hjob ih =>
      intro job hmem
      rw [List.mem_append] at hmem
      have hold :
          job ∈ before ++ processed :: after := by
        rw [List.mem_append]
        rcases hmem with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by simp [hafter])
      simpa using ih job hold
  | @preRawBelow caps config history raw hjob hbelow ih =>
      intro job hmem
      simpa using ih job hmem
  | preTestCross =>
      trivial
  | preRawCross =>
      trivial
  | postTestPositive =>
      trivial
  | postTestZero =>
      trivial
  | postProcessPositive =>
      trivial
  | postProcessZero =>
      trivial
  | postProcessCap =>
      trivial
  | postRawPositive =>
      trivial
  | postRawZero =>
      trivial

/-- Every cap which is live during the pre phase has its cap-valued test in
the public transcript. -/
theorem MixedQuotaHistory.pre_cap_testResult
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {caps : MixedCapPending n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config) :
    ∀ job ∈ caps, (job, u) ∈ config.transcript.testResults :=
  history.capTest_invariant

/-- In the pre-crossing phase, every cap test is either still live or has
already acquired its matching process observation. -/
def MixedPhase.preCapCountInvariant
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre caps =>
      config.transcript.processedLabels.length + caps.length =
        config.transcript.testResults.length
  | .post _ _ _ _ _ => True

theorem MixedQuotaHistory.preCapCount_invariant
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.preCapCountInvariant config := by
  induction history with
  | initial =>
      simp [MixedPhase.preCapCountInvariant, Online.Config.initial,
        Online.Transcript.processedLabels]
  | @preTestBelow caps config history job hjob hbelow ih =>
      simp [MixedPhase.preCapCountInvariant,
        Online.Transcript.processedLabels] at ih ⊢
      omega
  | preTestCross =>
      trivial
  | @preProcessCap before after config job history hjob ih =>
      simp [MixedPhase.preCapCountInvariant,
        Online.Transcript.processedLabels] at ih ⊢
      omega
  | @preRawBelow caps config history job hjob hbelow ih =>
      simpa [MixedPhase.preCapCountInvariant] using ih
  | preRawCross =>
      trivial
  | postTestPositive =>
      trivial
  | postTestZero =>
      trivial
  | postProcessPositive =>
      trivial
  | postProcessZero =>
      trivial
  | postProcessCap =>
      trivial
  | postRawPositive =>
      trivial
  | postRawZero =>
      trivial

/-- Concrete pre-phase cap-count identity. -/
theorem MixedQuotaHistory.pre_cap_count
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {caps : MixedCapPending n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config) :
    config.transcript.processedLabels.length + caps.length =
      config.transcript.testResults.length :=
  history.preCapCount_invariant

/-- Before the first crossing we retain both lifecycle information and the
canonical prefix-cost lower bound. -/
def MixedPhase.preAccountingInvariant
    (u : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ =>
      config.ProcessHistoryInvariant ∧
        config.PreCostInvariant u
  | .post _ _ _ _ _ => True

theorem MixedQuotaHistory.preAccounting_invariant
    {n : ℕ} {u β : ℝ} (hu : 0 < u) {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.preAccountingInvariant u config := by
  induction history with
  | initial =>
      exact
        ⟨Online.Config.initial_processHistoryInvariant n,
          Online.Config.initial_preCostInvariant n u⟩
  | @preTestBelow caps config history job hjob hbelow ih =>
      have hstep :
          config.step (.finite u) (fun _ _ => u) (.test job) =
            some
              {
                jobs := Function.update config.jobs job (.tested u)
                transcript :=
                  config.transcript ++ [.testResult job u]
              } := by
        simp [Online.Config.step, hjob]
      have hfull :=
        MixedQuotaHistory.preTestBelow
          history job hjob hbelow
      exact
        ⟨Online.Config.processHistoryInvariant_step
            ih.1 history.started_history_invariant hstep,
          Online.Config.preCostInvariant_step_of_allTestsEqual
            hu ih.1 ih.2 hstep hfull.pre_allTestsEqual⟩
  | preTestCross =>
      trivial
  | @preProcessCap before after config job history hjob ih =>
      have hstep :
          config.step (.finite u) (fun _ _ => u) (.process job) =
            some
              {
                jobs := Function.update config.jobs job .done
                transcript := config.transcript ++ [.processed job]
              } := by
        simp [Online.Config.step, hjob]
      have hfull :=
        MixedQuotaHistory.preProcessCap history hjob
      exact
        ⟨Online.Config.processHistoryInvariant_step
            ih.1 history.started_history_invariant hstep,
          Online.Config.preCostInvariant_step_of_allTestsEqual
            hu ih.1 ih.2 hstep hfull.pre_allTestsEqual⟩
  | @preRawBelow caps config history job hjob hbelow ih =>
      have hstep :
          config.step (.finite u) (fun _ _ => u) (.raw job) =
            some
              {
                jobs := Function.update config.jobs job .done
                transcript := config.transcript ++ [.rawCompleted job]
              } := by
        simp [Online.Config.step, hjob]
      have hfull :=
        MixedQuotaHistory.preRawBelow
          history job hjob hbelow
      exact
        ⟨Online.Config.processHistoryInvariant_step
            ih.1 history.started_history_invariant hstep,
          Online.Config.preCostInvariant_step_of_allTestsEqual
            hu ih.1 ih.2 hstep hfull.pre_allTestsEqual⟩
  | preRawCross =>
      trivial
  | postTestPositive =>
      trivial
  | postTestZero =>
      trivial
  | postProcessPositive =>
      trivial
  | postProcessZero =>
      trivial
  | postProcessCap =>
      trivial
  | postRawPositive =>
      trivial
  | postRawZero =>
      trivial

/-- All operational information about the literal first-crossing prefix
needed by the final global exchange. -/
structure CrossingPrefixAccountingData
    (n : ℕ) (u β : ℝ) (H : ℕ)
    (crossingPrefix : Online.Transcript n) : Prop where
  firstCrossing :
    IsMixedFirstCrossingPrefix n u β crossingPrefix
  allTestsEqual :
    crossingPrefix.AllTestsEqual u
  startedNodup :
    crossingPrefix.startedLabels.Nodup
  processedRecorded :
    ∀ job ∈ crossingPrefix.processedLabels,
      job ∈ crossingPrefix.testResults.map Prod.fst
  remaining :
    H = n - crossingPrefix.startedLabels.length
  preCost :
    prefixCost (crossingPrefix.preCompletionWeights u) ≤
      Online.suffixWeightedDuration (.finite u)
        (fun _ => u) crossingPrefix

/-- Phase-indexed decomposition into the literal crossing prefix, a physical
suffix, and its cap-retaining harmonic expansion. -/
def MixedPhase.augmentedTailInvariant
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post H L z caps pending =>
      ∃ crossingPrefix physical virtual :
          Online.Transcript n,
        ∃ initialCaps : MixedCapPending n,
          config.transcript = crossingPrefix ++ physical ∧
          CrossingPrefixAccountingData
            n u β H crossingPrefix ∧
          crossingPrefix.processedLabels.length +
              initialCaps.length =
            crossingPrefix.testResults.length ∧
          (∀ job ∈ initialCaps,
            (job, u) ∈ crossingPrefix.testResults) ∧
          virtual.testResults =
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults ∧
          MixedAugmentedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H) u initialCaps
            L z (capPendingEntries u caps ++ pending) virtual ∧
          MixedTailExpansion physical virtual

theorem MixedQuotaHistory.augmentedTail_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hu : 0 < u) (hβ : 0 < β)
    {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.augmentedTailInvariant n u β A B config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow =>
      trivial
  | preProcessCap =>
      trivial
  | preRawBelow =>
      trivial
  | @preTestCross caps config previous job hjob hcross H hH =>
      simp only [MixedPhase.augmentedTailInvariant]
      have hbefore := previous.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.testResult job u) hcross
      have hfull :=
        MixedQuotaHistory.preTestCross
          previous job hjob hcross H hH
      have hall :=
        allTestsEqual_append_cap
          previous.pre_allTestsEqual job
      have hpre := previous.preAccounting_invariant hu
      have hstep :
          config.step (.finite u) (fun _ _ => u) (.test job) =
            some
              {
                jobs := Function.update config.jobs job (.tested u)
                transcript :=
                  config.transcript ++ [.testResult job u]
              } := by
        simp [Online.Config.step, hjob]
      have hcost :=
        Online.Config.preCostInvariant_step_of_allTestsEqual
          hu hpre.1 hpre.2 hstep hall
      have hprocess :=
        Online.Config.processHistoryInvariant_step
          hpre.1 previous.started_history_invariant hstep
      have hcount :
          (config.transcript ++
              [Online.Observation.testResult job u]).processedLabels.length +
                (caps ++ [job]).length =
            (config.transcript ++
              [Online.Observation.testResult job u]).testResults.length := by
        have hold := previous.pre_cap_count
        simp [Online.Transcript.processedLabels] at hold ⊢
        omega
      have hdata :
          CrossingPrefixAccountingData n u β H
            (config.transcript ++ [.testResult job u]) :=
        {
          firstCrossing :=
            Or.inl ⟨config.transcript, job, rfl,
              ⟨hbefore, hcross⟩⟩
          allTestsEqual := hall
          startedNodup := hfull.started_history_invariant.nodup
          processedRecorded := hprocess.processedRecorded
          remaining := hH
          preCost := hcost
        }
      refine
        ⟨config.transcript ++ [.testResult job u],
          [], [], caps ++ [job], ?_, hdata,
          hcount, ?_, ?_, ?_, .initial⟩
      · simp
      · intro tested hmem
        rw [List.mem_append] at hmem
        rw [Online.Transcript.testResults_append]
        rcases hmem with hold | hnew
        · exact List.mem_append.mpr
            (Or.inl (previous.pre_cap_testResult tested hold))
        · have heq : tested = job := by simpa using hnew
          subst tested
          simp
      · simp [virtualTail, hscan.2.1, htail]
      · simpa using
          (MixedAugmentedTailHistory.initial :
            MixedAugmentedTailHistory
              (tailPositiveCount A B H)
              (tailZeroCount A B H) u (caps ++ [job])
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              (capPendingEntries u (caps ++ [job])) [])
  | @preRawCross caps config previous job hjob hcross H hH =>
      simp only [MixedPhase.augmentedTailInvariant]
      have hbefore := previous.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.rawCompleted job) hcross
      have hfull :=
        MixedQuotaHistory.preRawCross
          previous job hjob hcross H hH
      have hall :=
        allTestsEqual_append_raw
          previous.pre_allTestsEqual job
      have hpre := previous.preAccounting_invariant hu
      have hstep :
          config.step (.finite u) (fun _ _ => u) (.raw job) =
            some
              {
                jobs := Function.update config.jobs job .done
                transcript :=
                  config.transcript ++ [.rawCompleted job]
              } := by
        simp [Online.Config.step, hjob]
      have hcost :=
        Online.Config.preCostInvariant_step_of_allTestsEqual
          hu hpre.1 hpre.2 hstep hall
      have hprocess :=
        Online.Config.processHistoryInvariant_step
          hpre.1 previous.started_history_invariant hstep
      have hcount :
          (config.transcript ++
              [Online.Observation.rawCompleted job]).processedLabels.length +
                caps.length =
            (config.transcript ++
              [Online.Observation.rawCompleted job]).testResults.length := by
        simpa [Online.Transcript.processedLabels] using
          previous.pre_cap_count
      have hdata :
          CrossingPrefixAccountingData n u β H
            (config.transcript ++ [.rawCompleted job]) :=
        {
          firstCrossing :=
            Or.inr ⟨config.transcript, job, rfl,
              ⟨hbefore, hcross⟩⟩
          allTestsEqual := hall
          startedNodup := hfull.started_history_invariant.nodup
          processedRecorded := hprocess.processedRecorded
          remaining := hH
          preCost := hcost
        }
      refine
        ⟨config.transcript ++ [.rawCompleted job],
          [], [], caps, ?_, hdata,
          hcount, ?_, ?_, ?_, .initial⟩
      · simp
      · intro tested hmem
        simpa using previous.pre_cap_testResult tested hmem
      · simp [virtualTail, hscan.2.1, htail]
      · simpa using
          (MixedAugmentedTailHistory.initial :
            MixedAugmentedTailHistory
              (tailPositiveCount A B H)
              (tailZeroCount A B H) u caps
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              (capPendingEntries u caps) [])
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      let p :=
        harmonicLevel
          (tailZeroCount A B H : ℝ) 0 (L - 1)
      refine
        ⟨crossingPrefix,
          physical ++ [.testResult job p],
          virtual ++ [.testResult job p],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, ?_,
          MixedTailExpansion.testResult hexpansion job p⟩
      · simpa [p, List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.testResult job p]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.testResult job p)
        rw [htail]
        simp [virtualTailStep, htestEq, p]
      · simpa [p, List.append_assoc] using
          MixedAugmentedTailHistory.testPositive
            hvirtual hL job
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      refine
        ⟨crossingPrefix,
          physical ++ [.testResult job 0],
          virtual ++ [.testResult job 0],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, ?_,
          MixedTailExpansion.testResult hexpansion job 0⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.testResult job 0]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.testResult job 0)
        rw [htail]
        simp [virtualTailStep, htestEq]
      · simpa [List.append_assoc] using
          MixedAugmentedTailHistory.testZero
            hvirtual hz job
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      have hstep :
          MixedAugmentedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H) u initialCaps
            L z
            (capPendingEntries u caps ++ before ++ after)
            (virtual ++ [.processed job]) := by
        exact
          MixedAugmentedTailHistory.processPositive
            (before := capPendingEntries u caps ++ before)
            (after := after) job p
            (by simpa [List.append_assoc] using hvirtual)
      refine
        ⟨crossingPrefix,
          physical ++ [.processed job],
          virtual ++ [.processed job],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, ?_,
          MixedTailExpansion.processed hexpansion job⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.processed job]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.processed job)
        rw [htail]
        simp only [virtualTailStep]
        split <;> simp [htestEq]
      · simpa [List.append_assoc] using hstep
  | @postProcessZero H L z caps pending config
      history job hjob hlabel ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      refine
        ⟨crossingPrefix,
          physical ++ [.processed job],
          virtual ++ [.processed job],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_,
          MixedAugmentedTailHistory.processZero hvirtual job,
          MixedTailExpansion.processed hexpansion job⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.processed job]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.processed job)
        rw [htail]
        simp only [virtualTailStep]
        split <;> simp [htestEq]
  | @postProcessCap H L z before after pending config
      job history hjob hlabel ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      have hstep :
          MixedAugmentedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H) u initialCaps
            L z
            (capPendingEntries u (before ++ after) ++ pending)
            (virtual ++ [.processed job]) := by
        have hraw :=
          MixedAugmentedTailHistory.processPositive
            (before := capPendingEntries u before)
            (after := capPendingEntries u after ++ pending)
            job u
            (by simpa [List.append_assoc] using hvirtual)
        simpa [List.append_assoc] using hraw
      refine
        ⟨crossingPrefix,
          physical ++ [.processed job],
          virtual ++ [.processed job],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, hstep,
          MixedTailExpansion.processed hexpansion job⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.processed job]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.processed job)
        rw [htail]
        simp only [virtualTailStep]
        split <;> simp [htestEq]
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      let p :=
        harmonicLevel
          (tailZeroCount A B H : ℝ) 0 (L - 1)
      have htested :=
        MixedAugmentedTailHistory.testPositive
          hvirtual hL job
      have hprocessed :
          MixedAugmentedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H) u initialCaps
            (L - 1) z
            (capPendingEntries u caps ++ pending)
            ((virtual ++ [.testResult job p]) ++
              [.processed job]) := by
        have hraw :=
          MixedAugmentedTailHistory.processPositive
            (before := capPendingEntries u caps ++ pending)
            (after := []) job p
            (by simpa [p, List.append_assoc] using htested)
        simpa using hraw
      refine
        ⟨crossingPrefix,
          physical ++ [.rawCompleted job],
          virtual ++ [.testResult job p, .processed job],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, ?_,
          MixedTailExpansion.rawCompleted
            hexpansion job p⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.rawCompleted job]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.rawCompleted job)
        have hrank :=
          (history.post_virtual_history hn hβ).rank_value_of_positive hL
        rw [htail]
        simp [virtualTailStep, htestEq, hrank, p]
      · simpa [List.append_assoc] using hprocessed

  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      simp only [MixedPhase.augmentedTailInvariant] at ih ⊢
      obtain
        ⟨crossingPrefix, physical, virtual, initialCaps,
          hdecomp, hdata, hcount, hinitialTests, htestEq,
          hvirtual, hexpansion⟩ := ih
      have htested :=
        MixedAugmentedTailHistory.testZero
          hvirtual hz job
      have hprocessed :
          MixedAugmentedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H) u initialCaps
            0 (z - 1)
            (capPendingEntries u caps ++ pending)
            ((virtual ++ [.testResult job 0]) ++
              [.processed job]) :=
        MixedAugmentedTailHistory.processZero htested job
      refine
        ⟨crossingPrefix,
          physical ++ [.rawCompleted job],
          virtual ++ [.testResult job 0, .processed job],
          initialCaps, ?_, hdata, hcount, hinitialTests, ?_, ?_,
          MixedTailExpansion.rawCompleted
            hexpansion job 0⟩
      · simpa [List.append_assoc] using
          congrArg
            (fun xs => xs ++
              [Online.Observation.rawCompleted job]) hdecomp
      · have htail :=
          virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (history.post_crossed hn hβ)
            (Online.Observation.rawCompleted job)
        have hrank :=
          (history.post_virtual_history hn hβ).rank_value_of_zero rfl
        rw [htail]
        simp [virtualTailStep, htestEq, hrank]
      · simpa [List.append_assoc] using hprocessed

/-! ## Closed terminal value of the cap-augmented potential -/

theorem pairCost_replicate_append_of_le
    (u : ℝ) (R : ℕ) (xs : List ℝ)
    (hupper : ∀ x ∈ xs, x ≤ u) :
    pairCost (List.replicate R u ++ xs) =
      pairCost xs + (R : ℝ) * xs.sum +
        u * triangular R := by
  induction R with
  | zero =>
      simp [triangular]
  | succ R ih =>
      let rest := List.replicate R u ++ xs
      have hrest : ∀ x ∈ rest, x ≤ u := by
        intro x hx
        rcases List.mem_append.mp hx with hrep | hxs
        · exact ((List.mem_replicate.mp hrep).2).le
        · exact hupper x hxs
      have hmap :
          rest.map (min u) = rest := by
        calc
          rest.map (min u) =
              rest.map (fun x => x) := by
            apply List.map_congr_left
            intro x hx
            exact min_eq_right (hrest x hx)
          _ = rest := by simp
      have hstep :
          pairCost (u :: rest) =
            pairCost rest + u + rest.sum := by
        unfold pairCost
        simp only [List.sum_cons, pairMinCost_cons, hmap]
        ring
      rw [List.replicate_succ]
      change pairCost (u :: rest) = _
      rw [hstep, ih]
      simp only [rest, List.sum_append,
        List.sum_replicate, nsmul_eq_mul]
      rw [triangular_succ]
      push_cast
      ring

/-- Initial pending caps contribute exactly their self/cap-pair cost and
their interactions with every harmonic tail job. -/
theorem harmonicDynamicPotential_capPending
    {Z : ℕ} (hZ : 0 < Z) {u : ℝ} (K R : ℕ)
    (huLevel : harmonicLevel (Z : ℝ) 0 K ≤ u) :
    harmonicDynamicPotential (Z : ℝ) 0 K Z
        (List.replicate R u) =
      harmonicFiniteOnline K Z 0 +
        (R : ℝ) *
          ((K + Z : ℕ) +
            (harmonicFutureLevels (Z : ℝ) 0 K).sum) +
        u * triangular R := by
  have hfuture :
      ∀ p ∈ harmonicFutureLevels (Z : ℝ) 0 K,
        p ≤ u := by
    intro p hp
    exact
      (harmonicFutureLevels_le_level
        (ξ := (Z : ℝ)) (γ := 0)
        (by exact_mod_cast hZ) p hp).trans huLevel
  have hpair :=
    pairCost_replicate_append_of_le u R
      (harmonicFutureLevels (Z : ℝ) 0 K) hfuture
  unfold harmonicFiniteOnline harmonicDynamicPotential
  dsimp only
  simp only [List.length_replicate,
    List.length_nil, add_zero, List.nil_append]
  rw [hpair]
  push_cast
  ring

/-! ## Terminal operational lower bound for the whole post-crossing suffix -/

/-- At a completed mixed tail, the physical suffix pays the harmonic online
benchmark together with the exact contribution of every cap that was still
pending at the crossing. -/
theorem MixedQuotaHistory.terminalProcessing_augmentedTail_lower
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β)
    {A B H : ℕ} (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 [] []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    ∃ crossingPrefix physical : Online.Transcript n,
      ∃ initialCaps : MixedCapPending n,
        config.transcript = crossingPrefix ++ physical ∧
        CrossingPrefixAccountingData
          n u β H crossingPrefix ∧
        crossingPrefix.processedLabels.length +
            initialCaps.length =
          crossingPrefix.testResults.length ∧
        HiddenStoppingOracle.longCount u physical = 0 ∧
        H + initialCaps.length ≤
          Online.completionCount
            (terminalProcessing n u β A B
              config.transcript assignment)
            physical ∧
        harmonicFiniteOnline
              (tailPositiveCount A B H)
              (tailZeroCount A B H) 0 +
            (initialCaps.length : ℝ) *
              (((tailPositiveCount A B H +
                    tailZeroCount A B H : ℕ) : ℝ) +
                (harmonicFutureLevels
                  (tailZeroCount A B H : ℝ) 0
                  (tailPositiveCount A B H)).sum) +
            u * triangular initialCaps.length ≤
          Online.completionCost (.finite u)
            (terminalProcessing n u β A B
              config.transcript assignment)
            physical := by
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  let processing :=
    terminalProcessing n u β A B
      config.transcript assignment
  have hu : 0 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  have hZ : 0 < Z := by
    dsimp [Z]
    exact tailZeroCount_pos hB hH
  have hdefault :
      ∀ job,
        Online.ValueAdmissible (.finite u)
          (mixedQuotaDefault n u β A B
            config.transcript job) :=
    history.mixedQuotaDefault_admissible
      hn hβ hB hraw
  have hadmissible :
      ∀ job,
        Online.ValueAdmissible (.finite u)
          (processing job) := by
    exact Online.completeAssignment_admissible
      (.finite u)
      (mixedQuotaDefault n u β A B config.transcript)
      assignment hdefault hassignment
  obtain
    ⟨crossingPrefix, physical, virtual, initialCaps,
      hdecomp, hdata, hcount, hinitialTests, htestEq,
      hvirtual, hexpansion⟩ :=
        history.augmentedTail_invariant hn hu hβ
  have hstandardMatch :
      MixedTailMatches processing
        (virtualTail n u β K Z config.transcript) := by
    simpa [processing, K, Z, terminalProcessing] using
      history.completeAssignment_matches_virtual
        hn hβ hB hraw assignment hsupported hassignment
  have hvirtualMatch :
      MixedTailMatches processing virtual := by
    constructor
    · intro job p hp
      apply hstandardMatch.1 job p
      rw [← htestEq]
      exact hp
    · exact hstandardMatch.2
  have hcaps :
      ∀ job ∈ initialCaps, processing job = u := by
    intro job hjob
    have hprefixTest := hinitialTests job hjob
    have hfullTest :
        (job, u) ∈ config.transcript.testResults := by
      rw [hdecomp, Online.Transcript.testResults_append]
      exact List.mem_append.mpr (Or.inl hprefixTest)
    have hassigned : assignment job = some u :=
      hmatches job u hfullTest
    simpa [processing, terminalProcessing] using
      Online.completeAssignment_eq_assigned
        (mixedQuotaDefault n u β A B config.transcript)
        assignment job u hassigned
  have huLevel :
      harmonicLevel (Z : ℝ) 0 K ≤ u := by
    have hsafe :=
      dynamicTail_static_rawSafe hB hH hraw K (le_refl K)
    dsimp [K, Z] at hsafe ⊢
    linarith
  have hsafe :
      ∀ job p, (job, p) ∈ virtual.testResults →
        1 + p ≤ u := by
    intro job p hp
    have hpStandard :
        (job, p) ∈
          (virtualTail n u β K Z
            config.transcript).testResults := by
      rw [← htestEq]
      exact hp
    have hpDefault :=
      history.mixedQuotaDefault_eq_of_virtual_testResult
        hn hβ (by simpa [K, Z] using hpStandard)
    have hpSafe :=
      (history.mixedQuotaDefault_rawSafe
        hn hβ hB hraw job).2
    rw [hpDefault] at hpSafe
    exact hpSafe
  have hamortized :=
    hvirtual.amortized_lower hZ huLevel
      processing hcaps hvirtualMatch
  have hpotential :=
    harmonicDynamicPotential_capPending
      hZ K initialCaps.length huLevel
  have hvirtualLower :
      harmonicFiniteOnline K Z 0 +
            (initialCaps.length : ℝ) *
              (((K + Z : ℕ) : ℝ) +
                (harmonicFutureLevels
                  (Z : ℝ) 0 K).sum) +
            u * triangular initialCaps.length ≤
        Online.completionCost .infinite processing virtual := by
    rw [← hpotential]
    simpa [capPendingEntries_values,
      harmonicUnfinished,
      harmonicDynamicPotential_terminal] using hamortized
  have hdominates :=
    hexpansion.dominates hu processing
      hadmissible hvirtualMatch hsafe
  have hphysicalLong :
      HiddenStoppingOracle.longCount u physical = 0 :=
    hexpansion.physical_longCount_zero_of_safe hsafe
  have hcompletionVirtual :=
    hvirtual.completionCount_lower hZ huLevel
      processing hcaps hvirtualMatch
  have hcompletionPhysical :
      H + initialCaps.length ≤
        Online.completionCount processing physical := by
    have hsplit : K + Z = H := by
      dsimp [K, Z]
      exact tail_split A B H
    rw [hexpansion.completionCount_eq processing hvirtualMatch]
    simp [capPendingEntries] at hcompletionVirtual
    omega
  refine
    ⟨crossingPrefix, physical, initialCaps,
      hdecomp, hdata, hcount, hphysicalLong,
      (by simpa [processing] using hcompletionPhysical), ?_⟩
  dsimp [K, Z, processing] at hvirtualLower hdominates ⊢
  exact hvirtualLower.trans hdominates.1

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
