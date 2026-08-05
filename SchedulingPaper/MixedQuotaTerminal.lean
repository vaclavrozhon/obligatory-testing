import SchedulingPaper.MixedQuotaFreeze
import SchedulingPaper.HiddenStoppingGlobalExchange
import Mathlib.Tactic

/-!
# Terminal shape of the mixed quota run

This module connects the phase history to the generic lifecycle invariants
of an adaptive run.  Its main result says that a completed post-crossing run
has consumed every positive and zero tail slot and has no live harmonic test
left pending.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Phase-indexed liveness of the positive pending list.  Positivity of the
zero scale is an implication because the pre phase has not selected a scale
yet, and a crossing with empty tail has `Z = 0` and an empty pending list. -/
def MixedPhase.pendingInvariant
    (n : ℕ) (A B : ℕ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post H _ _ _ pending =>
      0 < tailZeroCount A B H →
        pending.Nodup ∧
          ∀ entry ∈ pending,
            config.jobs entry.1 = .tested entry.2

theorem MixedQuotaHistory.pending_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.pendingInvariant n A B config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow history job hjob hbelow ih =>
      trivial
  | preTestCross history job hjob hcross H hH ih =>
      intro hZ
      simp
  | preProcessCap history hjob ih =>
      trivial
  | preRawBelow history job hjob hbelow ih =>
      trivial
  | preRawCross history job hjob hcross H hH ih =>
      intro hZ
      simp
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      let p :=
        harmonicLevel
          (tailZeroCount A B H : ℝ) 0 (L - 1)
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
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        rw [heq, hjob] at hstate
        contradiction
      simpa [Function.update, hne] using hstate
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
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
  | @postProcessZero H L z caps pending config
      history job hjob hvirtualMem ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        have hpZero : entry.2 = 0 := by
          rw [heq, hjob] at hstate
          exact Online.JobState.tested.inj hstate.symm
        have hvirtual :=
          history.post_virtual_history hn hβ
        have hpLower :=
          hvirtual.pending_lower hZ entry hentry
        have hZreal :
            (0 : ℝ) < tailZeroCount A B H := by
          exact_mod_cast hZ
        have hone :
            1 ≤
              harmonicLevel
                (tailZeroCount A B H : ℝ) 0 L :=
          harmonicLevel_one_le hZreal (le_refl 0) L
        rw [hpZero] at hpLower
        linarith
      simpa [Function.update, hne] using hstate
  | @postProcessCap H L z before after pending config
      job history hjob hvirtualMem ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        have hvirtual :=
          history.post_virtual_history hn hβ
        have htest :=
          hvirtual.pending_mem_testResult entry hentry
        have hlabel :
            entry.1 ∈
              (virtualTail n u β
                (tailPositiveCount A B H)
                (tailZeroCount A B H)
                config.transcript).testResults.map Prod.fst :=
          List.mem_map.mpr ⟨entry, htest, rfl⟩
        exact hvirtualMem (heq ▸ hlabel)
      simpa [Function.update, hne] using hstate
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        rw [heq, hjob] at hstate
        contradiction
      simpa [Function.update, hne] using hstate
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      intro hZ
      rcases ih hZ with ⟨hnodup, hlive⟩
      refine ⟨hnodup, ?_⟩
      intro entry hentry
      have hstate := hlive entry hentry
      have hne : entry.1 ≠ job := by
        intro heq
        rw [heq, hjob] at hstate
        contradiction
      simpa [Function.update, hne] using hstate

theorem MixedQuotaHistory.post_pending_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (hZ : 0 < tailZeroCount A B H) :
    pending.Nodup ∧
      ∀ entry ∈ pending,
        config.jobs entry.1 = .tested entry.2 :=
  history.pending_invariant hn hβ hZ

/-- A completed post-crossing run is terminal in the virtual harmonic state
machine as well. -/
theorem MixedQuotaHistory.post_terminal_indices
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    (hB : 0 < B)
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (hprocess : config.ProcessHistoryInvariant)
    (hdone : ∀ job, config.jobs job = .done) :
    L = 0 ∧ z = 0 ∧ pending = [] := by
  have hstartedLength :
      config.transcript.startedLabels.length = n :=
    Online.Config.startedLabels_length_eq_card_of_completed
      history.started_history_invariant hprocess hdone
  have hremaining := history.post_started_add_remaining
  have hLz : L = 0 ∧ z = 0 := by omega
  rcases hLz with ⟨rfl, rfl⟩
  have hpending : pending = [] := by
    by_cases hH : H = 0
    · have hvirtual := history.post_virtual_history hn hβ
      have hcount := hvirtual.test_count
      have hK : tailPositiveCount A B H = 0 := by
        simp [hH, tailPositiveCount]
      have hZ : tailZeroCount A B H = 0 := by
        simp [hH, tailZeroCount, hK]
      have htests :
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry hentry
      have hmem :=
        hvirtual.pending_mem_testResult entry hentry
      rw [htests] at hmem
      simp at hmem
    · have hZ :
          0 < tailZeroCount A B H :=
        tailZeroCount_pos hB (Nat.pos_of_ne_zero hH)
      have hlive :=
        (history.post_pending_invariant hn hβ hZ).2
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry hentry
      have hstate := hlive entry hentry
      rw [hdone entry.1] at hstate
      contradiction
  exact ⟨rfl, rfl, hpending⟩

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
