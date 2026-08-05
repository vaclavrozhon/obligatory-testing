import SchedulingPaper.MixedQuotaTerminalAccounting
import Mathlib.Tactic

/-!
# Automatic frozen multiset for a terminal mixed-quota run

The terminal accounting API previously accepted the permutation of the
canonical four-block vector as an external premise.  This module derives
that permutation directly from a completed adaptive run.
-/

namespace SchedulingPaper

noncomputable section

open Online

namespace LowerBound
namespace MixedQuotaOracle

/-- In the pre phase all physical tests have value `u`.  In the post phase
every physical test is either such a prefix test or occurs, with the same
value, in the expanded virtual harmonic tail. -/
def MixedPhase.testValueClassification
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ =>
      ∀ job p, (job, p) ∈ config.transcript.testResults → p = u
  | .post H _ _ _ _ =>
      ∀ job p, (job, p) ∈ config.transcript.testResults →
        p = u ∨
          (job, p) ∈
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults

theorem MixedQuotaHistory.testValue_classification
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history : MixedQuotaHistory n u β A B phase config) :
    phase.testValueClassification n u β A B config := by
  induction history with
  | initial =>
      intro job p hp
      simp [Online.Config.initial] at hp
  | @preTestBelow caps config history tested hjob hbelow ih =>
      intro job p hp
      rw [Online.Transcript.testResults_append] at hp
      rcases List.mem_append.mp hp with hold | hnew
      · exact ih job p hold
      · simp at hnew
        exact hnew.2
  | @preTestCross caps config history tested hjob hcross H hH ih =>
      intro job p hp
      rw [Online.Transcript.testResults_append] at hp
      rcases List.mem_append.mp hp with hold | hnew
      · exact Or.inl (ih job p hold)
      · simp at hnew
        exact Or.inl hnew.2
  | @preProcessCap before after config job history hjob ih =>
      simpa [MixedPhase.testValueClassification] using ih
  | @preRawBelow caps config history job hjob hbelow ih =>
      simpa [MixedPhase.testValueClassification] using ih
  | @preRawCross caps config history job hjob hcross H hH ih =>
      intro tested p hp
      exact Or.inl (ih tested p (by simpa using hp))
  | @postTestPositive H L z caps pending config
      history hL tested hjob ih =>
      intro job p hp
      rw [Online.Transcript.testResults_append] at hp
      rcases List.mem_append.mp hp with hold | hnew
      · rcases ih job p hold with hcap | hvirtual
        · exact Or.inl hcap
        · right
          have hcross := history.post_crossed hn hβ
          rw [virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H) hcross]
          simp only [virtualTailStep]
          rw [Online.Transcript.testResults_append]
          exact List.mem_append.mpr (Or.inl hvirtual)
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp only [virtualTailStep]
        rw [Online.Transcript.testResults_append]
        simpa using List.mem_append.mpr (Or.inr hnew)
  | @postTestZero H z caps pending config
      history hz tested hjob ih =>
      intro job p hp
      rw [Online.Transcript.testResults_append] at hp
      rcases List.mem_append.mp hp with hold | hnew
      · rcases ih job p hold with hcap | hvirtual
        · exact Or.inl hcap
        · right
          have hcross := history.post_crossed hn hβ
          rw [virtualTail_append_of_crossed hn hβ
            (tailPositiveCount A B H)
            (tailZeroCount A B H) hcross]
          simp only [virtualTailStep]
          rw [Online.Transcript.testResults_append]
          exact List.mem_append.mpr (Or.inl hvirtual)
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp only [virtualTailStep]
        rw [Online.Transcript.testResults_append]
        simpa using List.mem_append.mpr (Or.inr hnew)
  | @postProcessPositive H L z caps before after config
      processed p history hjob ih =>
      intro job q hq
      have hqOld : (job, q) ∈ config.transcript.testResults := by
        simpa using hq
      rcases ih job q hqOld with hcap | hvirtual
      · exact Or.inl hcap
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp only [virtualTailStep]
        split <;> simpa using hvirtual
  | @postProcessZero H L z caps pending config
      history processed hjob hlabel ih =>
      intro job q hq
      have hqOld : (job, q) ∈ config.transcript.testResults := by
        simpa using hq
      rcases ih job q hqOld with hcap | hvirtual
      · exact Or.inl hcap
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp [virtualTailStep, hlabel, hvirtual]
  | @postProcessCap H L z before after pending config
      processed history hjob hlabel ih =>
      intro job q hq
      have hqOld : (job, q) ∈ config.transcript.testResults := by
        simpa using hq
      rcases ih job q hqOld with hcap | hvirtual
      · exact Or.inl hcap
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp [virtualTailStep, hlabel, hvirtual]
  | @postRawPositive H L z caps pending config
      history hL raw hjob ih =>
      intro job q hq
      have hqOld : (job, q) ∈ config.transcript.testResults := by
        simpa using hq
      rcases ih job q hqOld with hcap | hvirtual
      · exact Or.inl hcap
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp only [virtualTailStep]
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hvirtual)
  | @postRawZero H z caps pending config
      history hz raw hjob ih =>
      intro job q hq
      have hqOld : (job, q) ∈ config.transcript.testResults := by
        simpa using hq
      rcases ih job q hqOld with hcap | hvirtual
      · exact Or.inl hcap
      · right
        have hcross := history.post_crossed hn hβ
        rw [virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H) hcross]
        simp only [virtualTailStep]
        rw [Online.Transcript.testResults_append]
        exact List.mem_append.mpr (Or.inl hvirtual)

/-- The recursive binary counter never exceeds the list length. -/
theorem binaryLongCount_le_length
    (u : ℝ) (xs : List ℝ) :
    binaryLongCount u xs ≤ xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [binaryLongCount_cons, List.length_cons]
      split <;> omega

/-- The recursive counter of mapped values is the length of the
corresponding label filter. -/
theorem binaryLongCount_map_eq_filter_length
    (u : ℝ) (labels : List α) (f : α → ℝ) :
    binaryLongCount u (labels.map f) =
      (labels.filter (fun label => f label = u)).length := by
  induction labels with
  | nil =>
      simp
  | cons label labels ih =>
      by_cases h : f label = u <;>
        simp [h, ih] <;> omega

/-- A list whose entries are all `1` or `u` has the expected canonical
two-block multiset. -/
theorem binaryBlocks_perm
    {u : ℝ} (hu : 1 < u) (xs : List ℝ)
    (hbinary : ∀ x ∈ xs, x = 1 ∨ x = u) :
    (List.replicate (xs.length - binaryLongCount u xs) 1 ++
        List.replicate (binaryLongCount u xs) u).Perm xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, y = 1 ∨ y = u := by
        intro y hy
        exact hbinary y (by simp [hy])
      have ih' := ih htail
      rcases hbinary x (by simp) with hx | hx
      · subst x
        have hne : (1 : ℝ) ≠ u := ne_of_lt hu
        have hcount :
            binaryLongCount u (1 :: xs) =
              binaryLongCount u xs := by
          simp [binaryLongCount, hne]
        have hle := binaryLongCount_le_length u xs
        have hsub :
            (1 :: xs).length -
                binaryLongCount u (1 :: xs) =
              (xs.length - binaryLongCount u xs) + 1 := by
          simp only [List.length_cons, hcount]
          omega
        rw [hsub, List.replicate_succ, hcount]
        simpa using ih'.cons 1
      · subst x
        have hcount :
            binaryLongCount u (u :: xs) =
              binaryLongCount u xs + 1 := by
          simp [binaryLongCount, Nat.add_comm]
        have hle := binaryLongCount_le_length u xs
        have hsub :
            (u :: xs).length -
                binaryLongCount u (u :: xs) =
              xs.length - binaryLongCount u xs := by
          simp only [List.length_cons, hcount]
          omega
        rw [hsub, hcount, List.replicate_succ]
        exact List.perm_middle.trans (ih'.cons u)

/-- Labels represented by the expanded virtual harmonic tail. -/
def terminalVirtualLabels
    (n : ℕ) (u β : ℝ) (A B H : ℕ)
    (transcript : Online.Transcript n) :
    List (Online.Label n) :=
  (virtualTail n u β
    (tailPositiveCount A B H)
    (tailZeroCount A B H)
    transcript).testResults.map Prod.fst

/-- The complementary labels, kept in the canonical `Fin` enumeration
order. -/
def terminalPrefixLabels
    (n : ℕ) (u β : ℝ) (A B H : ℕ)
    (transcript : Online.Transcript n) :
    List (Online.Label n) :=
  (List.ofFn (fun job : Online.Label n => job)).filter
    (fun job =>
      job ∉ terminalVirtualLabels n u β A B H transcript)

theorem MixedQuotaHistory.terminalPrefix_append_virtual_perm_all
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    (terminalPrefixLabels n u β A B H config.transcript ++
        terminalVirtualLabels n u β A B H config.transcript).Perm
      (List.ofFn (fun job : Online.Label n => job)) := by
  classical
  apply List.Perm.of_nodup_mem_iff
  · rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Nodup.filter _ (List.nodup_ofFn.mpr Function.injective_id)
    · exact history.post_virtual_testLabels_nodup hn hβ
    · intro a ha b hb hab
      subst b
      have hnot :
          a ∉ terminalVirtualLabels n u β A B H
            config.transcript := by
        exact of_decide_eq_true (List.mem_filter.mp ha).2
      exact hnot hb
  · exact List.nodup_ofFn.mpr Function.injective_id
  · intro job
    by_cases hvirtual :
        job ∈ terminalVirtualLabels n u β A B H
          config.transcript
    · simp [terminalPrefixLabels, hvirtual]
    · simp [terminalPrefixLabels, hvirtual]

/-- At a terminal harmonic tail the virtual block has exactly the frozen
tail size `H`. -/
theorem MixedQuotaHistory.terminalVirtualLabels_length
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config) :
    (terminalVirtualLabels n u β A B H
      config.transcript).length = H := by
  have hvirtual := history.post_virtual_history hn hβ
  have hcount := hvirtual.test_count
  have hsplit := tail_split A B H
  simpa [terminalVirtualLabels] using (show
    (virtualTail n u β
      (tailPositiveCount A B H)
      (tailZeroCount A B H)
      config.transcript).testResults.length = H by omega)

/-- Consequently the complementary physical prefix has length `n-H`. -/
theorem MixedQuotaHistory.terminalPrefixLabels_length
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config) :
    (terminalPrefixLabels n u β A B H
      config.transcript).length = n - H := by
  have hperm :=
    history.terminalPrefix_append_virtual_perm_all hn hβ
  have hlength := List.Perm.length_eq hperm
  have htail := history.terminalVirtualLabels_length hn hβ
  simp only [List.length_append, List.length_ofFn] at hlength
  omega

/-- The virtual labels of a terminal state carry exactly the canonical
finite harmonic effective-length multiset. -/
theorem MixedQuotaHistory.terminalVirtual_effective_perm_harmonic
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (processing : Online.Label n → ℝ)
    (hmatch :
      MixedTailMatches processing
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript)) :
    (mixedHarmonicEffectiveCandidate
        (tailPositiveCount A B H)
        (tailZeroCount A B H)).Perm
      ((terminalVirtualLabels n u β A B H
          config.transcript).map
        (fun job =>
          effectiveLength (.finite u) (processing job))) := by
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  let virtual :=
    virtualTail n u β K Z config.transcript
  have hvirtual := history.post_virtual_history hn hβ
  have hvalues :
      virtual.testResults.map Prod.snd =
        (terminalVirtualLabels n u β A B H
          config.transcript).map processing := by
    unfold terminalVirtualLabels
    change virtual.testResults.map Prod.snd =
      (virtual.testResults.map Prod.fst).map processing
    rw [List.map_map]
    apply List.map_congr_left
    intro result hresult
    exact (hmatch.1 result.1 result.2 hresult).symm
  have hterminal :
      virtual.testResults.map Prod.snd =
        harmonicDescendingLevels (Z : ℝ) 0 K ++
          List.replicate Z 0 := by
    simpa [virtual, K, Z] using
      hvirtual.testValues_eq_of_terminal
  have hrawEffective :
      (harmonicDescendingLevels (Z : ℝ) 0 K ++
          List.replicate Z 0).map
          (fun p => effectiveLength (.finite u) p) =
        (harmonicDescendingLevels (Z : ℝ) 0 K ++
          List.replicate Z 0).map (fun p => 1 + p) := by
    apply List.map_congr_left
    intro p hp
    have hsafe :
        1 + p ≤ u :=
      (mixedDynamicFullValue_rawSafe hB hH hraw hp).2
    simp [effectiveLength_finite, min_eq_right hsafe]
  have hprocessingEffective :
      (harmonicDescendingLevels (Z : ℝ) 0 K ++
          List.replicate Z 0).map
          (fun p => effectiveLength (.finite u) p) =
        (terminalVirtualLabels n u β A B H
          config.transcript).map
          (fun job =>
            effectiveLength (.finite u) (processing job)) := by
    rw [← hterminal, hvalues, List.map_map]
    simp [Function.comp_apply]
  have hreverse :
      (harmonicDescendingLevels (Z : ℝ) 0 K).Perm
        (harmonicFutureLevels (Z : ℝ) 0 K) := by
    simpa [harmonicDescendingLevels] using
      (List.reverse_perm
        (harmonicFutureLevels (Z : ℝ) 0 K))
  have hpositive :=
    hreverse.map (fun p : ℝ => 1 + p)
  have hcandidateToRaw :
      (mixedHarmonicEffectiveCandidate K Z).Perm
        ((harmonicDescendingLevels (Z : ℝ) 0 K).map
            (fun p => 1 + p) ++
          List.replicate Z 1) := by
    exact
      (List.perm_append_comm.trans
        (List.Perm.append_right _ hpositive.symm))
  apply hcandidateToRaw.trans
  rw [← hprocessingEffective, hrawEffective]
  simp [mixedHarmonicEffectiveCandidate, List.map_append]

/-- Outside the virtual tail, canonical completion is binary: an untested
prefix/raw label receives zero and every tested prefix label receives `u`. -/
theorem MixedQuotaHistory.terminalPrefix_processing_binary
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    {job : Online.Label n}
    (hprefix :
      job ∈ terminalPrefixLabels n u β A B H
        config.transcript) :
    terminalProcessing n u β A B config.transcript assignment job = 0 ∨
      terminalProcessing n u β A B config.transcript assignment job = u := by
  classical
  have hnotVirtual :
      job ∉ terminalVirtualLabels n u β A B H
        config.transcript :=
    of_decide_eq_true (List.mem_filter.mp hprefix).2
  cases hassigned : assignment job with
  | none =>
      left
      simp only [terminalProcessing, Online.completeAssignment, hassigned]
      unfold mixedQuotaDefault
      rw [history.post_tailSize_eq hn hβ]
      have hnone :
          ¬ ∃ p,
            (job, p) ∈
              (virtualTail n u β
                (tailPositiveCount A B H)
                (tailZeroCount A B H)
                config.transcript).testResults := by
        intro hexists
        obtain ⟨p, hp⟩ := hexists
        apply hnotVirtual
        exact List.mem_map.mpr ⟨(job, p), hp, rfl⟩
      exact dif_neg hnone
  | some p =>
      have hp :
          (job, p) ∈ config.transcript.testResults :=
        hsupported job p hassigned
      rcases history.testValue_classification hn hβ job p hp with
        hcap | hvirtual
      · right
        simp [terminalProcessing, Online.completeAssignment,
          hassigned, hcap]
      · exact (hnotVirtual
          (List.mem_map.mpr ⟨(job, p), hvirtual, rfl⟩)).elim

/-- An unassigned complementary label receives the literal zero default. -/
theorem MixedQuotaHistory.terminalPrefix_processing_eq_zero_of_unassigned
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    {job : Online.Label n}
    (hprefix :
      job ∈ terminalPrefixLabels n u β A B H
        config.transcript)
    (hunassigned : assignment job = none) :
    terminalProcessing n u β A B config.transcript assignment job = 0 := by
  classical
  have hnotVirtual :
      job ∉ terminalVirtualLabels n u β A B H
        config.transcript :=
    of_decide_eq_true (List.mem_filter.mp hprefix).2
  simp only [terminalProcessing, Online.completeAssignment, hunassigned]
  unfold mixedQuotaDefault
  rw [history.post_tailSize_eq hn hβ]
  have hnone :
      ¬ ∃ p,
        (job, p) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults := by
    intro hexists
    obtain ⟨p, hp⟩ := hexists
    apply hnotVirtual
    exact List.mem_map.mpr ⟨(job, p), hp, rfl⟩
  exact dif_neg hnone

/-- Prefix effective lengths are therefore binary `1/u`. -/
theorem MixedQuotaHistory.terminalPrefix_effective_binary
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) (hu : 1 < u) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    {job : Online.Label n}
    (hprefix :
      job ∈ terminalPrefixLabels n u β A B H
        config.transcript) :
    effectiveLength (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment job) = 1 ∨
      effectiveLength (.finite u)
        (terminalProcessing n u β A B
          config.transcript assignment job) = u := by
  rcases history.terminalPrefix_processing_binary
      hn hβ assignment hsupported hprefix with hzero | hcap
  · left
    rw [hzero, effectiveLength_finite]
    norm_num
    exact hu.le
  · right
    rw [hcap, effectiveLength_finite]
    exact min_eq_left (by linarith)

/-- Effective lengths of the labels outside the virtual harmonic tail. -/
def terminalPrefixEffective
    (n : ℕ) (u β : ℝ) (A B H : ℕ)
    (transcript : Online.Transcript n)
    (assignment : Online.PartialAssignment n) : List ℝ :=
  (terminalPrefixLabels n u β A B H transcript).map
    (fun job =>
      effectiveLength (.finite u)
        (terminalProcessing n u β A B transcript assignment job))

theorem MixedQuotaHistory.terminalPrefixEffective_perm_binaryBlocks
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) (hu : 1 < u) {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript) :
    (List.replicate
          ((terminalPrefixEffective n u β A B H
              config.transcript assignment).length -
            binaryLongCount u
              (terminalPrefixEffective n u β A B H
                config.transcript assignment)) 1 ++
        List.replicate
          (binaryLongCount u
            (terminalPrefixEffective n u β A B H
              config.transcript assignment)) u).Perm
      (terminalPrefixEffective n u β A B H
        config.transcript assignment) := by
  apply binaryBlocks_perm hu
  intro x hx
  rcases List.mem_map.mp hx with ⟨job, hjob, rfl⟩
  exact history.terminalPrefix_effective_binary
    hn hβ hu assignment hsupported hjob

/-- The number of `u` entries in the complementary effective block is
exactly the public number of tests that returned `u`. -/
theorem MixedQuotaHistory.terminalPrefixEffective_binaryLongCount_eq_longCount
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript) :
    binaryLongCount u
        (terminalPrefixEffective n u β A B H
          config.transcript assignment) =
      HiddenStoppingOracle.longCount u config.transcript := by
  classical
  have hu : 1 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  let prefixLabels :=
    terminalPrefixLabels n u β A B H config.transcript
  let processing :=
    terminalProcessing n u β A B config.transcript assignment
  let effective :=
    fun job : Online.Label n =>
      effectiveLength (.finite u) (processing job)
  have hprefixNodup : prefixLabels.Nodup := by
    exact List.Nodup.filter _
      (List.nodup_ofFn.mpr Function.injective_id)
  have hlongNodup :
      (config.transcript.longTestLabels u).Nodup := by
    exact List.Nodup.sublist
      (config.transcript.longTestLabels_sublist_startedLabels u)
      history.started_history_invariant.nodup
  have hfiltered :
      (prefixLabels.filter (fun job => effective job = u)).Perm
        (config.transcript.longTestLabels u) := by
    apply List.Perm.of_nodup_mem_iff
    · exact List.Nodup.filter _ hprefixNodup
    · exact hlongNodup
    · intro job
      constructor
      · intro hjob
        have hparts := List.mem_filter.mp hjob
        have hprefix : job ∈ prefixLabels := hparts.1
        have heffective : effective job = u :=
          of_decide_eq_true hparts.2
        have hprocessingBinary :
            processing job = 0 ∨ processing job = u := by
          exact history.terminalPrefix_processing_binary
            hn hβ assignment hsupported hprefix
        have hprocessingLong : processing job = u :=
          (effectiveLength_eq_long_iff hu
            hprocessingBinary).mp heffective
        cases hassigned : assignment job with
        | none =>
            have hzero :
                processing job = 0 := by
              exact
                history.terminalPrefix_processing_eq_zero_of_unassigned
                  hn hβ assignment hprefix hassigned
            linarith
        | some p =>
            have hp : p = u := by
              simpa [processing, terminalProcessing,
                Online.completeAssignment, hassigned] using
                hprocessingLong
            subst p
            exact config.transcript.mem_longTestLabels_iff.mpr
              (hsupported job u hassigned)
      · intro hjob
        have hlong :
            (job, u) ∈ config.transcript.testResults :=
          config.transcript.mem_longTestLabels_iff.mp hjob
        have hassigned : assignment job = some u :=
          hmatches job u hlong
        have hnotVirtual :
            job ∉ terminalVirtualLabels n u β A B H
              config.transcript := by
          intro hvirtual
          have heq :=
            history.completeAssignment_eq_mixedQuotaDefault_on_virtual
              hn hβ assignment hsupported job hvirtual
          have hprocessingLong : processing job = u := by
            simp [processing, terminalProcessing,
              Online.completeAssignment, hassigned]
          have hdefault :
              mixedQuotaDefault n u β A B
                config.transcript job = u := by
            have hprocessingLong' :
                Online.completeAssignment
                    (mixedQuotaDefault n u β A B config.transcript)
                    assignment job = u := by
              simpa [processing, terminalProcessing] using
                hprocessingLong
            rw [hprocessingLong'] at heq
            exact heq.symm
          have hsafe :=
            (history.mixedQuotaDefault_rawSafe
              hn hβ hB hraw job).2
          rw [hdefault] at hsafe
          linarith
        have hprefix : job ∈ prefixLabels := by
          simp [prefixLabels, terminalPrefixLabels, hnotVirtual]
        apply List.mem_filter.mpr
        refine ⟨hprefix, ?_⟩
        have heffective : effective job = u := by
          have hprocessingLong : processing job = u := by
            simp [processing, terminalProcessing,
              Online.completeAssignment, hassigned]
          change effectiveLength (.finite u) (processing job) = u
          rw [hprocessingLong, effectiveLength_finite]
          exact min_eq_left (by linarith)
        exact decide_eq_true heffective
  unfold terminalPrefixEffective
  change binaryLongCount u (prefixLabels.map effective) =
    HiddenStoppingOracle.longCount u config.transcript
  rw [binaryLongCount_map_eq_filter_length]
  calc
    (prefixLabels.filter (fun job => effective job = u)).length =
        (config.transcript.longTestLabels u).length :=
      List.Perm.length_eq hfiltered
    _ = HiddenStoppingOracle.longCount u config.transcript :=
      config.transcript.longTestLabels_length u

/-- The formerly external four-block permutation premise follows from the
terminal history and the ordinary replay invariants. -/
theorem MixedQuotaHistory.terminalProcessing_frozenMultiset
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    (hB : 0 < B) (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    let C := HiddenStoppingOracle.longCount u config.transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)) ∧
      n = v + C + K + Z := by
  dsimp only
  let C := HiddenStoppingOracle.longCount u config.transcript
  let v := n - C - H
  let K := tailPositiveCount A B H
  let Z := tailZeroCount A B H
  let processing :=
    terminalProcessing n u β A B config.transcript assignment
  let prefixEffective :=
    terminalPrefixEffective n u β A B H
      config.transcript assignment
  let virtualEffective :=
    (terminalVirtualLabels n u β A B H
      config.transcript).map
      (fun job => effectiveLength (.finite u) (processing job))
  have hu : 1 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  have hcount :
      binaryLongCount u prefixEffective = C := by
    simpa [prefixEffective, C] using
      history.terminalPrefixEffective_binaryLongCount_eq_longCount
        hn hβ hB hraw assignment hsupported hmatches
  have hprefixLength :
      prefixEffective.length = n - H := by
    simp [prefixEffective, terminalPrefixEffective,
      history.terminalPrefixLabels_length hn hβ]
  have hprefixPlusTail :
      prefixEffective.length + H = n := by
    have hlabelLength :=
      List.Perm.length_eq
        (history.terminalPrefix_append_virtual_perm_all hn hβ)
    have htailLength :=
      history.terminalVirtualLabels_length hn hβ
    simp only [List.length_append, List.length_ofFn] at hlabelLength
    dsimp [prefixEffective, terminalPrefixEffective]
    simp only [List.length_map]
    omega
  have hcountLe : C ≤ n - H := by
    rw [← hprefixLength, ← hcount]
    exact binaryLongCount_le_length u prefixEffective
  have hv :
      prefixEffective.length - binaryLongCount u prefixEffective = v := by
    rw [hprefixLength, hcount]
    dsimp [v]
    omega
  have hpref :
      (List.replicate v 1 ++ List.replicate C u).Perm
        prefixEffective := by
    have hpref' :=
      history.terminalPrefixEffective_perm_binaryBlocks
        hn hβ hu assignment hsupported
    rw [← hv, ← hcount]
    simpa [prefixEffective] using hpref'
  have htailMatch :
      MixedTailMatches processing
        (virtualTail n u β K Z config.transcript) := by
    simpa [processing, K, Z, terminalProcessing] using
      history.completeAssignment_matches_virtual
        hn hβ hB hraw assignment hsupported hassignment
  have htail :
      (mixedHarmonicEffectiveCandidate K Z).Perm
        virtualEffective := by
    simpa [K, Z, processing, virtualEffective] using
      history.terminalVirtual_effective_perm_harmonic
        hn hβ hB hH hraw processing htailMatch
  have hlabels :=
    history.terminalPrefix_append_virtual_perm_all hn hβ
  have hfullMapped :=
    hlabels.map
      (fun job =>
        effectiveLength (.finite u) (processing job))
  have hfull :
      (prefixEffective ++ virtualEffective).Perm
        (vectorEffectiveLengths (.finite u) processing) := by
    simpa [prefixEffective, virtualEffective,
      terminalPrefixEffective, vectorEffectiveLengths,
      List.map_append, Function.comp_apply] using hfullMapped
  have hblocks :
      ((List.replicate v 1 ++ List.replicate C u) ++
          mixedHarmonicEffectiveCandidate K Z).Perm
        (prefixEffective ++ virtualEffective) :=
    hpref.append htail
  have horder :
      (List.replicate v 1 ++
          mixedHarmonicEffectiveCandidate K Z ++
          List.replicate C u).Perm
        ((List.replicate v 1 ++ List.replicate C u) ++
          mixedHarmonicEffectiveCandidate K Z) := by
    simpa [List.append_assoc] using
      (List.Perm.append_left (List.replicate v 1)
        (List.perm_append_comm :
          (mixedHarmonicEffectiveCandidate K Z ++
            List.replicate C u).Perm
          (List.replicate C u ++
            mixedHarmonicEffectiveCandidate K Z)))
  constructor
  · change
      (List.replicate v 1 ++
          (mixedHarmonicEffectiveCandidate K Z ++
            List.replicate C u)).Perm
        (vectorEffectiveLengths (.finite u) processing)
    simpa only [List.append_assoc] using
      horder.trans (hblocks.trans hfull)
  · have hsplit := tail_split A B H
    have hCH : C + H ≤ n := by omega
    have hlocal : n = v + C + K + Z := by omega
    exact hlocal

/-- Degenerate crossing at the last first-touch: the virtual tail is empty
and the entire frozen vector is the binary prefix block. -/
theorem MixedQuotaHistory.terminalProcessing_frozenMultiset_zeroTail
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post 0 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript) :
    let C := HiddenStoppingOracle.longCount u config.transcript
    let v := n - C
    (mixedExtendedEffectiveCandidate u v C 0 0).Perm
        (vectorEffectiveLengths (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)) ∧
      n = v + C := by
  dsimp only
  let C := HiddenStoppingOracle.longCount u config.transcript
  let v := n - C
  let processing :=
    terminalProcessing n u β A B config.transcript assignment
  let prefixEffective :=
    terminalPrefixEffective n u β A B 0
      config.transcript assignment
  have hu : 1 < u := by
    have hratio : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
    linarith
  have hcount :
      binaryLongCount u prefixEffective = C := by
    simpa [prefixEffective, C] using
      history.terminalPrefixEffective_binaryLongCount_eq_longCount
        hn hβ hB hraw assignment hsupported hmatches
  have hprefixLength : prefixEffective.length = n := by
    simp [prefixEffective, terminalPrefixEffective,
      history.terminalPrefixLabels_length hn hβ]
  have hcountLe : C ≤ n := by
    rw [← hprefixLength, ← hcount]
    exact binaryLongCount_le_length u prefixEffective
  have hv :
      prefixEffective.length - binaryLongCount u prefixEffective = v := by
    simp [hprefixLength, hcount, v]
  have hpref :
      (List.replicate v 1 ++ List.replicate C u).Perm
        prefixEffective := by
    have hpref' :=
      history.terminalPrefixEffective_perm_binaryBlocks
        hn hβ hu assignment hsupported
    rw [← hv, ← hcount]
    simpa [prefixEffective] using hpref'
  have hvirtualNil :
      terminalVirtualLabels n u β A B 0 config.transcript = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using history.terminalVirtualLabels_length hn hβ
  have hlabels :=
    history.terminalPrefix_append_virtual_perm_all hn hβ
  have hfullMapped :=
    hlabels.map
      (fun job =>
        effectiveLength (.finite u) (processing job))
  have hfull :
      prefixEffective.Perm
        (vectorEffectiveLengths (.finite u) processing) := by
    simpa [prefixEffective, terminalPrefixEffective,
      hvirtualNil, vectorEffectiveLengths,
      List.map_append, Function.comp_apply] using hfullMapped
  constructor
  · change
      (mixedExtendedEffectiveCandidate u v C 0 0).Perm
        (vectorEffectiveLengths (.finite u) processing)
    have hcandidate :
        mixedExtendedEffectiveCandidate u v C 0 0 =
          List.replicate v 1 ++ List.replicate C u := by
      simp [mixedExtendedEffectiveCandidate,
        mixedEffectiveCandidate,
        mixedHarmonicEffectiveCandidate,
        harmonicFutureLevels]
    rw [hcandidate]
    exact hpref.trans hfull
  · omega

/-- Uniform terminal multiset theorem, including the `H = 0` crossing
branch. -/
theorem MixedQuotaHistory.terminalProcessing_frozenMultiset_all
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H : ℕ}
    (hB : 0 < B)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (assignment : Online.PartialAssignment n)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hmatches :
      Online.MatchesTranscript assignment config.transcript)
    (hassignment :
      Online.AssignmentAdmissible (.finite u) assignment) :
    let C := HiddenStoppingOracle.longCount u config.transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u)
          (terminalProcessing n u β A B
            config.transcript assignment)) ∧
      n = v + C + K + Z := by
  by_cases hH : H = 0
  · subst H
    simpa [tailPositiveCount, tailZeroCount] using
      history.terminalProcessing_frozenMultiset_zeroTail
        hn hβ hB hraw assignment hsupported hmatches
  · exact history.terminalProcessing_frozenMultiset
      hn hβ hB (Nat.pos_of_ne_zero hH) hraw
      assignment hsupported hmatches hassignment

/-- Actual-run export: support, transcript matching, and assignment
admissibility are discharged automatically from `adaptiveRun`. -/
theorem adaptiveRun_terminalProcessing_frozenMultiset
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H 0 0 caps [])
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u)
          (terminalProcessing n u (quotaFraction M A B) A B
            transcript run.assigned)) ∧
      n = v + C + K + Z := by
  dsimp only
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hsupported :
      Online.SupportedByTranscript
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config.transcript := by
    simpa [Online.adaptiveRun] using
      (Online.runAdaptiveFuel_supportedByTranscript
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (by
          simp [Online.SupportedByTranscript,
            Online.Config.initial, Online.emptyAssignment]))
  have hmatches :
      Online.MatchesTranscript
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config.transcript := by
    simpa [Online.adaptiveRun] using
      (Online.runAdaptiveFuel_matchesTranscript
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (by
          simp [Online.MatchesTranscript,
            Online.Config.initial, Online.emptyAssignment]))
  have hassignment :
      Online.AssignmentAdmissible (.finite u)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned := by
    simpa [Online.adaptiveRun] using
      (Online.runAdaptiveFuel_assignment_admissible
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (oracle_admissible hB hraw)
        (Online.emptyAssignment_admissible (.finite u)))
  exact history.terminalProcessing_frozenMultiset
    hn hβ hB hH hraw
    (Online.adaptiveRun (.finite u)
      (oracle n u M A B) strategy fuel).assigned
    hsupported hmatches hassignment

/-- Actual-run terminal multiset export valid for every frozen tail size,
including `H = 0`. -/
theorem adaptiveRun_terminalProcessing_frozenMultiset_all
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (hB : 0 < B) {H : ℕ}
    (hraw : 2 + (A : ℝ) / (B : ℝ) < u)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {caps : MixedCapPending n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        (.post H 0 0 caps [])
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config) :
    let run :=
      Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel
    let transcript := run.result.config.transcript
    let C := HiddenStoppingOracle.longCount u transcript
    let v := n - C - H
    let K := tailPositiveCount A B H
    let Z := tailZeroCount A B H
    (mixedExtendedEffectiveCandidate u v C K Z).Perm
        (vectorEffectiveLengths (.finite u)
          (terminalProcessing n u (quotaFraction M A B) A B
            transcript run.assigned)) ∧
      n = v + C + K + Z := by
  dsimp only
  have hβ : 0 < quotaFraction M A B :=
    quotaFraction_pos hM
  have hreachable :=
    Online.adaptiveRun_reachable (.finite u)
      (oracle n u M A B) strategy fuel
  have hsupported :=
    hreachable.supportedByTranscript
  have hmatches :
      Online.MatchesTranscript
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).result.config.transcript := by
    simpa [Online.adaptiveRun] using
      (Online.runAdaptiveFuel_matchesTranscript
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (by
          simp [Online.MatchesTranscript,
            Online.Config.initial, Online.emptyAssignment]))
  have hassignment :
      Online.AssignmentAdmissible (.finite u)
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B) strategy fuel).assigned := by
    simpa [Online.adaptiveRun] using
      (Online.runAdaptiveFuel_assignment_admissible
        (.finite u) (oracle n u M A B) strategy fuel
        (Online.Config.initial n) Online.emptyAssignment
        (oracle_admissible hB hraw)
        (Online.emptyAssignment_admissible (.finite u)))
  exact history.terminalProcessing_frozenMultiset_all
    hn hβ hB hraw
    (Online.adaptiveRun (.finite u)
      (oracle n u M A B) strategy fuel).assigned
    hsupported hmatches hassignment

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
