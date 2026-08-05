import SchedulingPaper.HarmonicDynamic
import SchedulingPaper.TranscriptPairAccounting
import SchedulingPaper.StrategyTermination
import Mathlib.Tactic

/-!
# The obligatory harmonic revelation oracle
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Online

def harmonicRankValue (K Z : ℕ) (γ : ℝ) (rank : ℕ) : ℝ :=
  if rank < K then
    harmonicLevel (Z : ℝ) γ (K - 1 - rank)
  else 0

def harmonicRevelationOracle
    (K Z : ℕ) (γ : ℝ) : Online.Oracle (K + Z) :=
  fun transcript _job =>
    harmonicRankValue K Z γ transcript.testResults.length

theorem harmonicRankValue_of_lt
    {K Z rank : ℕ} {γ : ℝ} (h : rank < K) :
    harmonicRankValue K Z γ rank =
      harmonicLevel (Z : ℝ) γ (K - 1 - rank) := by
  simp [harmonicRankValue, h]

theorem harmonicRankValue_of_ge
    {K Z rank : ℕ} {γ : ℝ} (h : K ≤ rank) :
    harmonicRankValue K Z γ rank = 0 := by
  simp [harmonicRankValue, Nat.not_lt.mpr h]

theorem harmonicRankValue_nonneg
    {K Z rank : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ) :
    0 ≤ harmonicRankValue K Z γ rank := by
  by_cases h : rank < K
  · rw [harmonicRankValue_of_lt h]
    exact (harmonicLevel_one_le
      (by exact_mod_cast hZ) hγ _).trans' zero_le_one
  · rw [harmonicRankValue_of_ge (Nat.le_of_not_gt h)]

theorem harmonicRevelationOracle_admissible
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ) :
    (harmonicRevelationOracle K Z γ).Admissible .infinite := by
  intro transcript job
  exact harmonicRankValue_nonneg hZ hγ

theorem harmonic_zero_default_admissible
    {n : ℕ} :
    ∀ job : Online.Label n,
      Online.ValueAdmissible .infinite ((fun _ => 0) job) := by
  intro job
  simp [Online.ValueAdmissible]

abbrev HarmonicPending (n : ℕ) := List (Online.Label n × ℝ)

def HarmonicPending.values
    (pending : HarmonicPending n) : List ℝ :=
  pending.map Prod.snd

@[simp] theorem HarmonicPending.values_nil :
    HarmonicPending.values ([] : HarmonicPending n) = [] := rfl

@[simp] theorem HarmonicPending.values_append
    (left right : HarmonicPending n) :
    (left ++ right).values = left.values ++ right.values := by
  simp [HarmonicPending.values]

@[simp] theorem HarmonicPending.values_cons
    (entry : Online.Label n × ℝ) (rest : HarmonicPending n) :
    HarmonicPending.values (entry :: rest) =
      entry.2 :: HarmonicPending.values rest := rfl

@[simp] theorem HarmonicPending.values_length
    (pending : HarmonicPending n) :
    pending.values.length = pending.length := by
  simp [HarmonicPending.values]

/-- Reachability invariant for the explicit revelation.  `L` and `z` are
the numbers of untested positive and zero ranks, while `pending` contains
exactly the tested positive jobs that have not yet been processed. -/
inductive HarmonicHistory (K Z : ℕ) (γ : ℝ) :
    ℕ → ℕ → HarmonicPending (K + Z) →
      Online.Config (K + Z) → Prop
  | initial :
      HarmonicHistory K Z γ K Z []
        (Online.Config.initial (K + Z))
  | testPositive
      {L z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : HarmonicHistory K Z γ L z pending config)
      (hL : 0 < L) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched) :
      HarmonicHistory K Z γ (L - 1) z
        (pending ++ [(job,
          harmonicLevel (Z : ℝ) γ (L - 1))])
        {
          jobs := Function.update config.jobs job
            (.tested (harmonicLevel (Z : ℝ) γ (L - 1)))
          transcript := config.transcript ++
            [.testResult job
              (harmonicLevel (Z : ℝ) γ (L - 1))]
        }
  | testZero
      {z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : HarmonicHistory K Z γ 0 z pending config)
      (hz : 0 < z) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched) :
      HarmonicHistory K Z γ 0 (z - 1) pending
        {
          jobs := Function.update config.jobs job (.tested 0)
          transcript := config.transcript ++ [.testResult job 0]
        }
  | processPositive
      {L z : ℕ}
      {before after : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      {job : Online.Label (K + Z)} {p : ℝ}
      (history :
        HarmonicHistory K Z γ L z
          (before ++ (job, p) :: after) config)
      (hjob : config.jobs job = .tested p) :
      HarmonicHistory K Z γ L z (before ++ after)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | processZero
      {L z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      {job : Online.Label (K + Z)}
      (history : HarmonicHistory K Z γ L z pending config)
      (hjob : config.jobs job = .tested 0) :
      HarmonicHistory K Z γ L z pending
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }

theorem HarmonicHistory.test_count
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    config.transcript.testResults.length + L + z = K + Z := by
  induction history with
  | initial => simp [Online.Config.initial]
  | testPositive history hL job hjob ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.length_append, List.length_singleton]
      omega
  | testZero history hz job hjob ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.length_append, List.length_singleton]
      omega
  | processPositive history hjob ih =>
      simpa using ih
  | processZero history hjob ih =>
      simpa using ih

theorem HarmonicHistory.positive_phase
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    L = 0 ∨ z = Z := by
  induction history with
  | initial =>
      by_cases hK : K = 0
      · exact Or.inl hK
      · exact Or.inr rfl
  | @testPositive L z pending config history hL job hjob ih =>
      by_cases hnext : L - 1 = 0
      · exact Or.inl hnext
      · rcases ih with hzero | hz
        · exact (hL.ne' hzero).elim
        · exact Or.inr hz
  | testZero history hz job hjob ih => exact Or.inl rfl
  | processPositive history hjob ih => exact ih
  | processZero history hjob ih => exact ih

theorem HarmonicHistory.remaining_bounds
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    L ≤ K ∧ z ≤ Z := by
  induction history with
  | initial => exact ⟨le_rfl, le_rfl⟩
  | testPositive history hL job hjob ih =>
      exact ⟨(Nat.sub_le _ _).trans ih.1, ih.2⟩
  | testZero history hz job hjob ih =>
      exact ⟨ih.1, (Nat.sub_le _ _).trans ih.2⟩
  | processPositive history hjob ih => exact ih
  | processZero history hjob ih => exact ih

theorem HarmonicHistory.pending_lower
    {K Z : ℕ} {γ : ℝ} (hZ : 0 < Z)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    ∀ entry ∈ pending,
      harmonicLevel (Z : ℝ) γ L ≤ entry.2 := by
  induction history with
  | initial =>
      simp
  | @testPositive L z pending config history hL job hjob ih =>
      intro entry hentry
      rw [List.mem_append] at hentry
      rcases hentry with hold | hnew
      · exact
          (harmonicLevel_strictMono
            (γ := γ) (by exact_mod_cast hZ)
            (Nat.sub_lt (Nat.zero_lt_of_lt hL) (by omega))).le.trans
            (ih entry hold)
      · simp only [List.mem_singleton] at hnew
        rcases hnew with rfl
        rfl
  | testZero history hz job hjob ih =>
      simpa using ih
  | @processPositive L z before after config job p history hjob ih =>
      intro entry hentry
      apply ih entry
      rw [List.mem_append] at hentry ⊢
      rcases hentry with hbefore | hafter
      · exact Or.inl hbefore
      · exact Or.inr (by simp [hafter])
  | processZero history hjob ih =>
      exact ih

theorem HarmonicHistory.tested_result
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)} {p : ℝ}
    (hjob : config.jobs job = .tested p) :
    (job, p) ∈ config.transcript.testResults := by
  induction history with
  | initial =>
      simp [Online.Config.initial] at hjob
  | @testPositive L z pending config history hL tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        subst p
        simp
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton]
        exact Or.inl (ih hold)
  | @testZero z pending config history hz tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        subst p
        simp
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton]
        exact Or.inl (ih hold)
  | @processPositive L z before after config processed q history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold
  | @processZero L z pending config processed history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold

theorem HarmonicHistory.tested_positive_mem_pending
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)} {p : ℝ}
    (hjob : config.jobs job = .tested p) (hp : p ≠ 0) :
    (job, p) ∈ pending := by
  induction history with
  | initial =>
      simp [Online.Config.initial] at hjob
  | @testPositive L z pending config history hL tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        subst p
        simp
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        exact List.mem_append.mpr (Or.inl (ih hold))
  | @testZero z pending config history hz tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        exact (hp hjob.symm).elim
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        exact ih hold
  | @processPositive L z before after config processed q history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        have hmem := ih hold
        rw [List.mem_append] at hmem ⊢
        rcases hmem with hbefore | htail
        · exact Or.inl hbefore
        · simp only [List.mem_cons] at htail
          rcases htail with he | hafter
          · exact (heq (Prod.ext_iff.mp he).1).elim
          · exact Or.inr hafter
  | @processZero L z pending config processed history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        exact ih hold

theorem HarmonicHistory.untouched_not_tested
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)}
    (hjob : config.jobs job = .untouched) :
    ¬ ∃ p, (job, p) ∈ config.transcript.testResults := by
  induction history with
  | initial =>
      simp [Online.Config.initial]
  | @testPositive L z pending config history hL tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .untouched := by
          simpa [Function.update, heq] using hjob
        intro hmem
        rcases hmem with ⟨p, hp⟩
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact ih hold ⟨p, hp⟩
        · exact heq (congrArg Prod.fst hp)
  | @testZero z pending config history hz tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .untouched := by
          simpa [Function.update, heq] using hjob
        intro hmem
        rcases hmem with ⟨p, hp⟩
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton] at hp
        rcases hp with hp | hp
        · exact ih hold ⟨p, hp⟩
        · exact heq (congrArg Prod.fst hp)
  | @processPositive L z before after config processed p history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .untouched := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold
  | @processZero L z pending config processed history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .untouched := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold

theorem HarmonicHistory.testLabels_nodup
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    config.transcript.testResults.map Prod.fst |>.Nodup := by
  induction history with
  | initial =>
      simp [Online.Config.initial]
  | @testPositive L z pending config history hL tested htested ih =>
      simp only [Online.Transcript.testResults_append,
        List.map_append, Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil, List.map_singleton,
        List.nodup_append, List.nodup_singleton, and_true]
      constructor
      · exact ih
      · constructor
        · trivial
        · intro job hjob tested' hsingle
          simp only [List.mem_singleton] at hsingle
          subst tested'
          intro heq
          subst job
          have hnot := history.untouched_not_tested htested
          exact hnot (by
            rcases List.mem_map.mp hjob with
              ⟨⟨j, p⟩, hp, hj⟩
            simp only at hj
            subst j
            exact ⟨p, hp⟩)
  | @testZero z pending config history hz tested htested ih =>
      simp only [Online.Transcript.testResults_append,
        List.map_append, Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil, List.map_singleton,
        List.nodup_append, List.nodup_singleton, and_true]
      constructor
      · exact ih
      · constructor
        · trivial
        · intro job hjob tested' hsingle
          simp only [List.mem_singleton] at hsingle
          subst tested'
          intro heq
          subst job
          have hnot := history.untouched_not_tested htested
          exact hnot (by
            rcases List.mem_map.mp hjob with
              ⟨⟨j, p⟩, hp, hj⟩
            simp only at hj
            subst j
            exact ⟨p, hp⟩)
  | processPositive history hjob ih =>
      simpa using ih
  | processZero history hjob ih =>
      simpa using ih

theorem HarmonicHistory.no_untouched_of_finished_tests
    {K Z : ℕ} {γ : ℝ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config) :
    ∀ job, config.jobs job ≠ .untouched := by
  intro job hjob
  have hnot :=
    history.untouched_not_tested hjob
  have hnodup := history.testLabels_nodup
  have hlength :
      config.transcript.testResults.length = K + Z := by
    have hc := history.test_count
    omega
  let labels :=
    config.transcript.testResults.map Prod.fst
  have hjobNot : job ∉ labels := by
    intro hmem
    rcases List.mem_map.mp hmem with
      ⟨⟨j, p⟩, hp, hj⟩
    simp only at hj
    subst j
    exact hnot ⟨p, hp⟩
  have hsub :
      labels.toFinset ⊆ Finset.univ.erase job := by
    intro other hother
    simp only [List.mem_toFinset, Finset.mem_erase,
      Finset.mem_univ, and_true] at hother ⊢
    intro heq
    subst other
    exact hjobNot hother
  have hcard := Finset.card_le_card hsub
  have hlabelsCard :
      labels.toFinset.card = K + Z := by
    rw [List.toFinset_card_of_nodup]
    · simpa [labels] using hlength
    · simpa [labels] using hnodup
  rw [hlabelsCard] at hcard
  simp at hcard
  have hnpos : 0 < K + Z := by
    have := job.isLt
    omega
  omega

/-- Pending entries are pairwise distinct and are exactly live positive
tested jobs.  The conjunction is proved together because distinctness is
what justifies deleting the processed occurrence. -/
theorem HarmonicHistory.pending_invariant
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    pending.Nodup ∧
      ∀ entry ∈ pending,
        config.jobs entry.1 = .tested entry.2 := by
  induction history with
  | initial =>
      simp [Online.Config.initial]
  | @testPositive L z pending config history hL job hjob ih =>
      rcases ih with ⟨hnodup, hlive⟩
      let p := harmonicLevel (Z : ℝ) γ (L - 1)
      have hnot : (job, p) ∉ pending := by
        intro hmem
        have hold := hlive (job, p) hmem
        rw [hjob] at hold
        contradiction
      constructor
      · exact List.nodup_append.mpr
          ⟨hnodup, by simp, by
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact fun hab => hnot (hab ▸ ha)⟩
      · intro entry hentry
        rw [List.mem_append] at hentry
        rcases hentry with hold | hnew
        · have hstate := hlive entry hold
          have hne : entry.1 ≠ job := by
            intro heq
            rw [heq, hjob] at hstate
            contradiction
          simpa [Function.update, hne] using hstate
        · simp only [List.mem_singleton] at hnew
          subst entry
          simp [Function.update, p]
  | @testZero z pending config history hz job hjob ih =>
      rcases ih with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        rw [heq, hjob] at hstate
        contradiction
      simpa [Function.update, hne] using hstate
  | @processPositive L z before after config job p history hjob ih =>
      rcases ih with ⟨hnodup, hlive⟩
      have hparts := List.nodup_append.mp hnodup
      rcases hparts with ⟨hbefore, htail, hcross⟩
      have htailParts := List.nodup_cons.mp htail
      rcases htailParts with ⟨hnotAfter, hafter⟩
      have hnewNodup : (before ++ after).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hbefore, hafter, ?_⟩
        intro a ha b hb
        exact hcross a ha b (by simp [hb])
      constructor
      · exact hnewNodup
      · intro entry hentry
        have holdMem :
            entry ∈ before ++ (job, p) :: after := by
          rw [List.mem_append] at hentry ⊢
          rcases hentry with hb | ha
          · exact Or.inl hb
          · exact Or.inr (by simp [ha])
        have hstate := hlive entry holdMem
        have hne : entry.1 ≠ job := by
          intro heq
          have hpEq : entry.2 = p := by
            rw [heq, hjob] at hstate
            exact Online.JobState.tested.inj hstate.symm
          have hentryEq : entry = (job, p) := by
            apply Prod.ext
            · exact heq
            · exact hpEq
          subst entry
          rw [List.mem_append] at hentry
          rcases hentry with hb | ha
          · exact hcross (job, p) hb (job, p)
              (by simp) rfl
          · exact hnotAfter ha
        simpa [Function.update, hne] using hstate
  | @processZero L z pending config job history hjob ih =>
      rcases ih with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        have hpZero : entry.2 = 0 := by
          rw [heq, hjob] at hstate
          exact Online.JobState.tested.inj hstate.symm
        have hpLower := history.pending_lower hZ entry hentry
        have hone :
            1 ≤ harmonicLevel (Z : ℝ) γ L :=
          harmonicLevel_one_le (by exact_mod_cast hZ) hγ L
        rw [hpZero] at hpLower
        linarith
      simpa [Function.update, hne] using hstate

theorem HarmonicHistory.done_has_testResult
    {K Z : ℕ} {γ : ℝ}
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)}
    (hjob : config.jobs job = .done) :
    ∃ p, (job, p) ∈ config.transcript.testResults := by
  induction history with
  | initial =>
      simp [Online.Config.initial] at hjob
  | @testPositive L z pending config history hL tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .done := by
          simpa [Function.update, heq] using hjob
        obtain ⟨p, hp⟩ := ih hold
        exact ⟨p, by simp [hp]⟩
  | @testZero z pending config history hz tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .done := by
          simpa [Function.update, heq] using hjob
        obtain ⟨p, hp⟩ := ih hold
        exact ⟨p, by simp [hp]⟩
  | @processPositive L z before after config processed p history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        exact ⟨p, by
          simpa using history.tested_result hprocessed⟩
      · have hold : config.jobs job = .done := by
          simpa [Function.update, heq] using hjob
        obtain ⟨q, hq⟩ := ih hold
        exact ⟨q, by simpa using hq⟩
  | @processZero L z pending config processed history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        exact ⟨0, by
          simpa using history.tested_result hprocessed⟩
      · have hold : config.jobs job = .done := by
          simpa [Function.update, heq] using hjob
        obtain ⟨q, hq⟩ := ih hold
        exact ⟨q, by simpa using hq⟩

theorem HarmonicHistory.terminal_indices
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    (hdone : ∀ job, config.jobs job = .done) :
    L = 0 ∧ z = 0 ∧ pending = [] := by
  have hlabelsAll :
      ∀ job : Online.Label (K + Z),
        job ∈ config.transcript.testResults.map Prod.fst := by
    intro job
    obtain ⟨p, hp⟩ := history.done_has_testResult (hdone job)
    exact List.mem_map.mpr ⟨(job, p), hp, rfl⟩
  have hlengthLower :
      K + Z ≤ config.transcript.testResults.length := by
    let labels := config.transcript.testResults.map Prod.fst
    have huniv : labels.toFinset = Finset.univ := by
      ext job
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hlabelsAll job
    have hcard :
        K + Z = labels.toFinset.card := by
      rw [huniv]
      simp
    calc
      K + Z = labels.toFinset.card := hcard
      _ ≤ labels.length := List.toFinset_card_le labels
      _ = config.transcript.testResults.length := by
        simp [labels]
  have hcount := history.test_count
  have hLz : L = 0 ∧ z = 0 := by omega
  rcases hLz with ⟨rfl, rfl⟩
  have hlive := (history.pending_invariant hZ hγ).2
  have hnoMem : ∀ entry, entry ∉ pending := by
    intro entry hentry
    have hstate := hlive entry hentry
    rw [hdone entry.1] at hstate
    contradiction
  have hpending : pending = [] :=
    List.eq_nil_iff_forall_not_mem.mpr hnoMem
  exact ⟨rfl, rfl, hpending⟩

def harmonicDescendingLevels (ξ γ : ℝ) (K : ℕ) : List ℝ :=
  (harmonicFutureLevels ξ γ K).reverse

@[simp] theorem harmonicDescendingLevels_zero (ξ γ : ℝ) :
    harmonicDescendingLevels ξ γ 0 = [] := rfl

theorem harmonicDescendingLevels_succ (ξ γ : ℝ) (K : ℕ) :
    harmonicDescendingLevels ξ γ (K + 1) =
      harmonicLevel ξ γ K :: harmonicDescendingLevels ξ γ K := by
  rw [harmonicDescendingLevels, harmonicFutureLevels_succ]
  simp [harmonicDescendingLevels]

@[simp] theorem harmonicDescendingLevels_length
    (ξ γ : ℝ) (K : ℕ) :
    (harmonicDescendingLevels ξ γ K).length = K := by
  simp [harmonicDescendingLevels]

/-- At every reachable state, the values already revealed followed by the
still-hidden descending harmonic tail and the remaining zeros form the fixed
full value list. -/
theorem HarmonicHistory.testValues_append_remaining
    {K Z : ℕ} {γ : ℝ}
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config) :
    config.transcript.testResults.map Prod.snd ++
        harmonicDescendingLevels (Z : ℝ) γ L ++
        List.replicate z 0 =
      harmonicDescendingLevels (Z : ℝ) γ K ++
        List.replicate Z 0 := by
  induction history with
  | initial =>
      simp [Online.Config.initial]
  | @testPositive L z pending config history hL job hjob ih =>
      obtain ⟨L, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
      rw [harmonicDescendingLevels_succ] at ih
      simpa only [Nat.succ_sub_one,
        Online.Transcript.testResults_append,
        List.map_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.map_singleton, Prod.snd, List.append_assoc] using ih
  | @testZero z pending config history hz job hjob ih =>
      obtain ⟨z, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hz)
      simpa only [Nat.succ_sub_one,
        Online.Transcript.testResults_append,
        List.map_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.map_singleton, Prod.snd,
        harmonicDescendingLevels_zero,
        List.nil_append, List.replicate_succ,
        List.append_assoc] using ih
  | processPositive history hjob ih =>
      simpa using ih
  | processZero history hjob ih =>
      simpa using ih

theorem HarmonicHistory.testValues_eq_of_terminal
    {K Z : ℕ} {γ : ℝ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config) :
    config.transcript.testResults.map Prod.snd =
      harmonicDescendingLevels (Z : ℝ) γ K ++
        List.replicate Z 0 := by
  simpa using history.testValues_append_remaining

theorem HarmonicHistory.adaptiveStep
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config next : Online.Config (K + Z)}
    {assignment nextAssignment : Online.PartialAssignment (K + Z)}
    {action : Online.Action (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hstep :
      Online.adaptiveStep .infinite
        (harmonicRevelationOracle K Z γ)
        config assignment action =
          some (next, nextAssignment)) :
    ∃ L' z' pending',
      HarmonicHistory K Z γ L' z' pending' next := by
  cases action with
  | raw job =>
      simp [Online.adaptiveStep, Online.Config.step] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          by_cases hp : p = 0
          · subst p
            exact ⟨L, z, pending,
              HarmonicHistory.processZero history hjob⟩
          · have hmem :=
              history.tested_positive_mem_pending hjob hp
            obtain ⟨before, after, hpending⟩ :=
              List.append_of_mem hmem
            subst pending
            exact ⟨L, z, before ++ after,
              HarmonicHistory.processPositive history hjob⟩
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          have hunassigned : assignment job = none := by
            cases hassigned : assignment job with
            | none => rfl
            | some p =>
                have htested := hsupported job p hassigned
                exact
                  (history.untouched_not_tested hjob ⟨p, htested⟩).elim
          by_cases hL : 0 < L
          · have hzEq : z = Z := by
              rcases history.positive_phase with hzero | hz
              · exact (hL.ne' hzero).elim
              · exact hz
            have hcount := history.test_count
            have hrank :
                config.transcript.testResults.length = K - L := by
              omega
            have hrankLt :
                config.transcript.testResults.length < K := by
              have hLK := history.remaining_bounds.1
              omega
            have hLK : L ≤ K :=
              history.remaining_bounds.1
            have hidx :
                K - 1 - (K - L) = L - 1 := by
              omega
            have hvalue :
                Online.adaptiveValue
                    (harmonicRevelationOracle K Z γ)
                    assignment config.transcript job =
                  harmonicLevel (Z : ℝ) γ (L - 1) := by
              unfold Online.adaptiveValue
              rw [hunassigned]
              simp only [Option.getD_none]
              unfold harmonicRevelationOracle harmonicRankValue
              rw [if_pos hrankLt, hrank, hidx]
            simp [Online.adaptiveStep, Online.Config.step, hjob,
              Online.adaptiveOracle, hvalue] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact ⟨L - 1, z,
              pending ++ [(job,
                harmonicLevel (Z : ℝ) γ (L - 1))],
              HarmonicHistory.testPositive history hL job hjob⟩
          · have hLzero : L = 0 := Nat.eq_zero_of_not_pos hL
            subst L
            have hz : 0 < z := by
              by_contra hnot
              have hz0 : z = 0 := Nat.eq_zero_of_not_pos hnot
              subst z
              exact history.no_untouched_of_finished_tests job hjob
            have hcount := history.test_count
            have hzZ := history.remaining_bounds.2
            have hrankGe :
                K ≤ config.transcript.testResults.length := by
              omega
            have hvalue :
                Online.adaptiveValue
                    (harmonicRevelationOracle K Z γ)
                    assignment config.transcript job = 0 := by
              simp [Online.adaptiveValue, hunassigned,
                harmonicRevelationOracle,
                harmonicRankValue, Nat.not_lt.mpr hrankGe]
            simp [Online.adaptiveStep, Online.Config.step, hjob,
              Online.adaptiveOracle, hvalue] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact ⟨0, z - 1, pending,
              HarmonicHistory.testZero history hz job hjob⟩

theorem runAdaptiveFuel_harmonicHistory
    {K Z : ℕ} {γ : ℝ}
    (strategy : Online.Strategy (K + Z))
    (fuel : ℕ) {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    {assignment : Online.PartialAssignment (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript) :
    ∃ L' z' pending',
      HarmonicHistory K Z γ L' z' pending'
        (Online.runAdaptiveFuel .infinite
          (harmonicRevelationOracle K Z γ)
          strategy fuel config assignment).result.config := by
  induction fuel generalizing L z pending config assignment with
  | zero =>
      exact ⟨L, z, pending, history⟩
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [Online.runAdaptiveFuel, haction] using
            (show ∃ L' z' pending',
              HarmonicHistory K Z γ L' z' pending' config from
                ⟨L, z, pending, history⟩)
      | some action =>
          cases hstep :
              Online.adaptiveStep .infinite
                (harmonicRevelationOracle K Z γ)
                config assignment action with
          | none =>
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                (show ∃ L' z' pending',
                  HarmonicHistory K Z γ L' z' pending' config from
                    ⟨L, z, pending, history⟩)
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              obtain ⟨Lnext, znext, pendingNext, historyNext⟩ :=
                history.adaptiveStep hsupported hstep
              have hsupportedNext :=
                Online.adaptiveStep_supportedByTranscript
                  .infinite (harmonicRevelationOracle K Z γ)
                  config next assignment nextAssignment action
                  hsupported hstep
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                ih historyNext hsupportedNext

theorem adaptiveRun_harmonicHistory
    (K Z : ℕ) (γ : ℝ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ) :
    ∃ L z pending,
      HarmonicHistory K Z γ L z pending
        (Online.adaptiveRun .infinite
          (harmonicRevelationOracle K Z γ)
          strategy fuel).result.config := by
  unfold Online.adaptiveRun
  apply runAdaptiveFuel_harmonicHistory
    strategy fuel (HarmonicHistory.initial (K := K) (Z := Z) (γ := γ))
  simp [Online.SupportedByTranscript,
    Online.Config.initial, Online.emptyAssignment]

theorem adaptiveStep_remainingWork
    {n : ℕ} {adversary : Online.Oracle n}
    {config next : Online.Config n}
    {assignment nextAssignment : Online.PartialAssignment n}
    {action : Online.Action n}
    (hstep :
      Online.adaptiveStep .infinite adversary
        config assignment action = some (next, nextAssignment)) :
    next.remainingWork + 1 = config.remainingWork := by
  cases action with
  | raw job =>
      simp [Online.adaptiveStep, Online.Config.step] at hstep
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact Online.remainingWork_update_test
            config.jobs job
              (Online.adaptiveValue adversary assignment
                config.transcript job) hjob
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact Online.remainingWork_update_process
            config.jobs job p hjob

theorem runAdaptiveFuel_settled_of_remainingWork_lt
    {n : ℕ} (adversary : Online.Oracle n)
    (strategy : Online.Strategy n)
    (fuel : ℕ) (config : Online.Config n)
    (assignment : Online.PartialAssignment n)
    (hwork : config.remainingWork < fuel) :
    (Online.runAdaptiveFuel .infinite adversary strategy
      fuel config assignment).result.reason ≠ .outOfFuel := by
  induction fuel generalizing config assignment with
  | zero =>
      omega
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simp [Online.runAdaptiveFuel, haction]
      | some action =>
          cases hstep :
              Online.adaptiveStep .infinite adversary
                config assignment action with
          | none =>
              simp [Online.runAdaptiveFuel, haction, hstep]
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hdecrease :=
                adaptiveStep_remainingWork hstep
              have hnext : next.remainingWork < fuel := by
                omega
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem harmonic_analysisFuel_settled
    (K Z : ℕ) (γ : ℝ)
    (strategy : Online.Strategy (K + Z)) :
    (Online.adaptiveRun .infinite
      (harmonicRevelationOracle K Z γ)
      strategy (2 * (K + Z) + 1)).result.reason ≠
        .outOfFuel := by
  unfold Online.adaptiveRun
  apply runAdaptiveFuel_settled_of_remainingWork_lt
  rw [Online.Config.initial_remainingWork]
  omega

def HarmonicMatches
    (processingTime : Online.Label n → ℝ)
    (transcript : Online.Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults →
    processingTime job = p

theorem HarmonicMatches.of_append
    {processingTime : Online.Label n → ℝ}
    {transcript : Online.Transcript n}
    {observation : Online.Observation n}
    (hmatch :
      HarmonicMatches processingTime (transcript ++ [observation])) :
    HarmonicMatches processingTime transcript := by
  intro job p hp
  apply hmatch job p
  rw [Online.Transcript.testResults_append]
  exact List.mem_append.mpr (Or.inl hp)

theorem transcriptElapsed_append_singleton
    (cap : Cap) (processingTime : Online.Label n → ℝ)
    (transcript : Online.Transcript n)
    (observation : Online.Observation n) :
    Online.transcriptElapsed cap processingTime
        (transcript ++ [observation]) =
      Online.transcriptElapsed cap processingTime transcript +
        observation.duration cap processingTime := by
  induction transcript with
  | nil =>
      simp [Online.transcriptElapsed]
  | cons head tail ih =>
      simp only [List.cons_append,
        Online.transcriptElapsed_cons, ih]
      ring

theorem completionCost_append_singleton
    (cap : Cap) (processingTime : Online.Label n → ℝ)
    (transcript : Online.Transcript n)
    (observation : Online.Observation n) :
    Online.completionCost cap processingTime
        (transcript ++ [observation]) =
      Online.completionCost cap processingTime transcript +
        if (observation.completionLabel processingTime).isSome
          then Online.transcriptElapsed cap processingTime transcript +
            observation.duration cap processingTime
          else 0 := by
  rw [Online.completionCost_eq_suffixWeightedDuration,
    Online.suffixWeightedDuration_append_singleton,
    ← Online.completionCost_eq_suffixWeightedDuration]
  by_cases h :
      (observation.completionLabel processingTime).isSome
  · simp [h]
    <;> ring
  · simp [h]

def harmonicUnfinished
    (L z : ℕ) (pending : HarmonicPending n) : ℕ :=
  L + z + pending.length

theorem HarmonicHistory.amortized_lower
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ L z pending config)
    (processingTime : Online.Label (K + Z) → ℝ)
    (hmatch : HarmonicMatches processingTime config.transcript) :
    harmonicDynamicPotential (Z : ℝ) γ K Z [] ≤
      Online.completionCost .infinite processingTime
          config.transcript +
        Online.transcriptElapsed .infinite processingTime
            config.transcript *
          harmonicUnfinished L z pending +
        harmonicDynamicPotential (Z : ℝ) γ L z pending.values := by
  induction history with
  | initial =>
      simp [Online.Config.initial, harmonicUnfinished,
        Online.completionCost, Online.completionCostFrom]
  | @testPositive L z pending config history hL job hjob ih =>
      let p := harmonicLevel (Z : ℝ) γ (L - 1)
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hmatch job p
        simp [p]
      have hp1 : 1 ≤ p := by
        dsimp [p]
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) hγ _
      have hp0 : p ≠ 0 := by linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          config.transcript (.testResult job p)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          config.transcript (.testResult job p)
      have hpot :=
        harmonicDynamicPotential_test_positive
          (Z : ℝ) γ (z := z) pending.values hL
      simp only [HarmonicPending.values_append,
        HarmonicPending.values_cons, HarmonicPending.values_nil,
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
      simp only [HarmonicPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @testZero z pending config history hz job hjob ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          config.transcript (.testResult job 0)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          config.transcript (.testResult job 0)
      have hpot :=
        harmonicDynamicPotential_test_zero
          (Z : ℝ) γ pending.values hz
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
      simp only [HarmonicPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @processPositive L z before after config job p history hjob ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hprefix job p
        exact history.tested_result hjob
      have hpLower :
          harmonicLevel (Z : ℝ) γ L ≤ p := by
        apply history.pending_lower hZ (job, p)
        simp
      have hp1 : 1 ≤ p :=
        (harmonicLevel_one_le
          (by exact_mod_cast hZ) hγ L).trans hpLower
      have hp0 : p ≠ 0 := by linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          config.transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          config.transcript (.processed job)
      have hpot :=
        harmonicDynamicPotential_process
          (ξ := (Z : ℝ)) (γ := γ)
          (by exact_mod_cast hZ) hγ
          (L := L) (z := z)
          (before := before.values) (after := after.values)
          (p := p)
          (by
            rcases history.positive_phase with hzero | hzEq
            · exact Or.inl hzero
            · exact Or.inr (by exact_mod_cast hzEq))
          hpLower
      simp only [HarmonicPending.values_append,
        HarmonicPending.values_cons] at hpot hold ⊢
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap, hp0] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_cons,
        HarmonicPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      have hlength :
          ((List.length before + 1 + List.length after : ℕ) : ℝ) =
            (List.length before : ℝ) + 1 +
              (List.length after : ℝ) := by
        push_cast
        ring
      rw [hcost, htime]
      ring_nf at hpot hold ⊢
      nlinarith
  | @processZero L z pending config job history hjob ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = 0 := by
        apply hprefix job 0
        exact history.tested_result hjob
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          config.transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          config.transcript (.processed job)
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap] at hcost htime
      rw [hcost, htime]
      simpa [harmonicUnfinished] using hold

end

end SchedulingPaper
