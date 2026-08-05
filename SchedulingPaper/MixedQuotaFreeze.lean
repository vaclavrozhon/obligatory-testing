import SchedulingPaper.MixedTailOperational
import Mathlib.Tactic

/-!
# Freezing the mixed quota oracle

Raw operations do not commit a hidden value in the adaptive replay.  After
the run, their canonical default is the unique value assigned to the same
label by the virtual harmonic tail.  Prefix raw jobs, which do not occur in
that virtual transcript, receive zero.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Equality of values attached to a label in a test list with distinct
labels. -/
theorem pair_snd_eq_of_virtual_labels_nodup
    {xs : List (α × β)} {a : α} {b c : β}
    (hnodup : (xs.map Prod.fst).Nodup)
    (hb : (a, b) ∈ xs) (hc : (a, c) ∈ xs) :
    b = c := by
  induction xs with
  | nil =>
      simp at hb
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      simp only [List.mem_cons] at hb hc
      rcases hb with hb | hb <;> rcases hc with hc | hc
      · exact congrArg Prod.snd (hb.trans hc.symm)
      · subst head
        exact (hhead
          (List.mem_map.mpr ⟨(a, c), hc, rfl⟩)).elim
      · subst head
        exact (hhead
          (List.mem_map.mpr ⟨(a, b), hb, rfl⟩)).elim
      · exact ih htail hb hc

/-- The canonical completion of the adaptive partial assignment.  Its
dynamic scale is read from the persistent crossing scan. -/
noncomputable def mixedQuotaDefault
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (transcript : Online.Transcript n) :
    Online.Label n → ℝ := by
  classical
  let H := (scan n u β transcript).tailSize
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  exact fun job =>
    if h : ∃ p,
        (job, p) ∈
          (virtualTail n u β K Z transcript).testResults
    then Classical.choose h
    else 0

/-- The virtual tail inherits distinct first-touch labels from the physical
run. -/
theorem MixedQuotaHistory.post_virtual_testLabels_nodup
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    ((virtualTail n u β
      (tailPositiveCount A B H)
      (tailZeroCount A B H)
      config.transcript).testResults.map Prod.fst).Nodup := by
  rw [virtualTail_testLabels]
  obtain ⟨headTranscript, hdecomp⟩ :=
    history.post_tail_decomposition hn hβ
  have hstarted := history.started_history_invariant.nodup
  have hlabels :=
    congrArg Online.Transcript.startedLabels hdecomp
  rw [Online.Transcript.startedLabels_append] at hlabels
  rw [hlabels] at hstarted
  exact (List.nodup_append.mp hstarted).2.1

theorem MixedQuotaHistory.mixedQuotaDefault_eq_of_virtual_testResult
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    {job : Online.Label n} {p : ℝ}
    (hmem :
      (job, p) ∈
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript).testResults) :
    mixedQuotaDefault n u β A B config.transcript job = p := by
  unfold mixedQuotaDefault
  rw [history.post_tailSize_eq hn hβ]
  rw [dif_pos ⟨p, hmem⟩]
  let witness :
      ∃ q,
        (job, q) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults :=
    ⟨p, hmem⟩
  have hchosen :
      (job, Classical.choose witness) ∈
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript).testResults :=
    Classical.choose_spec witness
  exact pair_snd_eq_of_virtual_labels_nodup
    (history.post_virtual_testLabels_nodup hn hβ)
    hchosen hmem

/-- Pointwise cap safety for every value in a dynamically rounded harmonic
tail. -/
theorem mixedDynamicFullValue_rawSafe
    {u : ℝ} {A B H : ℕ}
    (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {p : ℝ}
    (hp :
      p ∈
        harmonicDescendingLevels
            (tailZeroCount A B H : ℝ) 0
            (tailPositiveCount A B H) ++
          List.replicate (tailZeroCount A B H) 0) :
    0 ≤ p ∧ 1 + p ≤ u := by
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  have hZ : 0 < Z := by
    dsimp [Z]
    exact tailZeroCount_pos hB hH
  have hratio :
      (K : ℝ) / (Z : ℝ) ≤ (A : ℝ) / (B : ℝ) := by
    dsimp [K, Z]
    exact tail_ratio_le hB hH
  rcases List.mem_append.mp hp with hp | hp
  · simp only [harmonicDescendingLevels, List.mem_reverse,
      harmonicFutureLevels, List.mem_map] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    have hmK : m < K := by simpa [K] using hm
    have hZreal : (0 : ℝ) < (Z : ℝ) := by
      exact_mod_cast hZ
    have hpOne :
        1 ≤ harmonicLevel (Z : ℝ) 0 m :=
      harmonicLevel_one_le hZreal (le_refl 0) m
    have hpUpper :=
      harmonicLevel_le_one_add_ratio hZ
        (Nat.le_of_lt hmK)
    change
      harmonicLevel (Z : ℝ) 0 m ≤
        1 + (K : ℝ) / (Z : ℝ) at hpUpper
    constructor
    · linarith
    · linarith
  · have hpzero : p = 0 := (List.mem_replicate.mp hp).2
    subst p
    constructor
    · norm_num
    · have hratioNonneg :
          0 ≤ (A : ℝ) / (B : ℝ) := by positivity
      linarith

/-- The mixed default is nonnegative and raw-safe at every reachable post
state. -/
theorem MixedQuotaHistory.mixedQuotaDefault_rawSafe
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    ∀ job,
      0 ≤ mixedQuotaDefault n u β A B config.transcript job ∧
      1 + mixedQuotaDefault n u β A B config.transcript job ≤ u := by
  intro job
  have hvirtual := history.post_virtual_history hn hβ
  unfold mixedQuotaDefault
  rw [history.post_tailSize_eq hn hβ]
  split
  next hexists =>
    let p := Classical.choose hexists
    have hp :
        (job, p) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults :=
      Classical.choose_spec hexists
    by_cases hH : H = 0
    · subst H
      have hcount := hvirtual.test_count
      have hpLength :
          0 <
            (virtualTail n u β
              (tailPositiveCount A B 0)
              (tailZeroCount A B 0)
              config.transcript).testResults.length :=
        List.length_pos_of_mem hp
      have hK : tailPositiveCount A B 0 = 0 := by
        simp [tailPositiveCount]
      have hZ : tailZeroCount A B 0 = 0 := by
        simp [tailZeroCount, hK]
      have hcount' :
          (virtualTail n u β
              (tailPositiveCount A B 0)
              (tailZeroCount A B 0)
              config.transcript).testResults.length + L + z = 0 := by
        simpa [hK, hZ] using hcount
      omega
    · have hpValues :
          p ∈
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults.map Prod.snd :=
        List.mem_map.mpr ⟨(job, p), hp, rfl⟩
      have hpExtended :
          p ∈
            (virtualTail n u β
                (tailPositiveCount A B H)
                (tailZeroCount A B H)
                config.transcript).testResults.map Prod.snd ++
              harmonicDescendingLevels
                (tailZeroCount A B H : ℝ) 0 L ++
              List.replicate z 0 := by
        simp [hpValues]
      rw [hvirtual.testValues_append_remaining] at hpExtended
      exact mixedDynamicFullValue_rawSafe
        hB (Nat.pos_of_ne_zero hH) hraw hpExtended
  next hnone =>
    constructor
    · norm_num
    · have hratioNonneg :
          0 ≤ (A : ℝ) / (B : ℝ) := by positivity
      linarith

theorem MixedQuotaHistory.mixedQuotaDefault_matches_virtual
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    MixedTailMatches
      (mixedQuotaDefault n u β A B config.transcript)
      (virtualTail n u β
        (tailPositiveCount A B H)
        (tailZeroCount A B H)
        config.transcript) := by
  constructor
  · intro job p hp
    exact history.mixedQuotaDefault_eq_of_virtual_testResult
      hn hβ hp
  · intro job
    exact (history.mixedQuotaDefault_rawSafe
      hn hβ hB hraw job).1

theorem MixedQuotaHistory.mixedQuotaDefault_admissible
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    ∀ job,
      Online.ValueAdmissible (.finite u)
        (mixedQuotaDefault n u β A B config.transcript job) := by
  intro job
  have hsafe :=
    history.mixedQuotaDefault_rawSafe hn hβ hB hraw job
  exact ⟨hsafe.1, by linarith⟩

/-- Any hidden assignment supported by the physical transcript agrees with
the virtual-tail default on every tail label.  A test in the prefix cannot
share such a label, by uniqueness of first touches. -/
theorem MixedQuotaHistory.completeAssignment_eq_mixedQuotaDefault_on_virtual
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (job : Online.Label n)
    (hlabel :
      job ∈
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript).testResults.map Prod.fst) :
    Online.completeAssignment
        (mixedQuotaDefault n u β A B config.transcript)
        assignment job =
      mixedQuotaDefault n u β A B config.transcript job := by
  let default :=
    mixedQuotaDefault n u β A B config.transcript
  cases hassigned : assignment job with
  | none =>
      simp [Online.completeAssignment, hassigned]
  | some q =>
      have hactual :
          (job, q) ∈ config.transcript.testResults :=
        hsupported job q hassigned
      obtain ⟨headTranscript, hdecomp⟩ :=
        history.post_tail_decomposition hn hβ
      have hresults :=
        congrArg Online.Transcript.testResults hdecomp
      rw [Online.Transcript.testResults_append] at hresults
      rw [hresults] at hactual
      have hstarted := history.started_history_invariant.nodup
      have hstartedEq :=
        congrArg Online.Transcript.startedLabels hdecomp
      rw [Online.Transcript.startedLabels_append] at hstartedEq
      rw [hstartedEq] at hstarted
      have hcross := (List.nodup_append.mp hstarted).2.2
      have htailLabel :
          job ∈
            (scan n u β config.transcript).tail.startedLabels := by
        rw [← virtualTail_testLabels n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript]
        exact hlabel
      rcases List.mem_append.mp hactual with hhead | htail
      · have hheadLabel :
            job ∈ headTranscript.startedLabels :=
          transcript_mem_started_of_testResult hhead
        exact
          (hcross job hheadLabel job htailLabel rfl).elim
      · have hvirtual :
            (job, q) ∈
              (virtualTail n u β
                (tailPositiveCount A B H)
                (tailZeroCount A B H)
                config.transcript).testResults :=
          virtualTail_actual_test_mem
            n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript htail
        have hdefault :
            default job = q :=
          history.mixedQuotaDefault_eq_of_virtual_testResult
            hn hβ hvirtual
        simp [Online.completeAssignment, hassigned,
          default, hdefault]

/-- Generic frozen-map form of the virtual-tail matching theorem. -/
theorem MixedQuotaHistory.completeAssignment_matches_virtual
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    MixedTailMatches
      (Online.completeAssignment
        (mixedQuotaDefault n u β A B config.transcript)
        assignment)
      (virtualTail n u β
        (tailPositiveCount A B H)
        (tailZeroCount A B H)
        config.transcript) := by
  let default :=
    mixedQuotaDefault n u β A B config.transcript
  constructor
  · intro job p hp
    have hlabel :
        job ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults.map Prod.fst :=
      List.mem_map.mpr ⟨(job, p), hp, rfl⟩
    rw [history.completeAssignment_eq_mixedQuotaDefault_on_virtual
      hn hβ assignment hsupported job hlabel]
    exact history.mixedQuotaDefault_eq_of_virtual_testResult
      hn hβ hp
  · intro job
    cases hassigned : assignment job with
    | none =>
        simp [Online.completeAssignment, hassigned, default]
        exact
          (history.mixedQuotaDefault_rawSafe
            hn hβ hB hraw job).1
    | some p =>
        have hp := hassignment job p hassigned
        simpa [Online.completeAssignment, hassigned] using hp.1

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
