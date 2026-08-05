import SchedulingPaper.MixedQuotaOracle
import Mathlib.Tactic

/-!
# Reachability for the mixed quota tail

The public quota prefix lives on the original label type, whereas the
harmonic core is determined only after the first crossing.  Consequently
the original `HarmonicHistory K Z` (whose label type is definitionally
`Fin (K+Z)`) cannot be reused directly.  `MixedTailHistory` is the same
finite state machine generalized to an ambient `Fin n`; it records only the
post-crossing virtual transcript.
-/

namespace SchedulingPaper

noncomputable section

open Online

namespace LowerBound
namespace MixedQuotaOracle

abbrev MixedTailPending (n : ℕ) :=
  List (Online.Label n × ℝ)

def MixedTailPending.values
    (pending : MixedTailPending n) : List ℝ :=
  pending.map Prod.snd

/-- Generalized harmonic reachability on the dynamically selected tail. -/
inductive MixedTailHistory (K Z : ℕ) :
    ℕ → ℕ → MixedTailPending n →
      Online.Transcript n → Prop
  | initial :
      MixedTailHistory K Z K Z [] []
  | testPositive
      {L z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history : MixedTailHistory K Z L z pending transcript)
      (hL : 0 < L) (job : Online.Label n) :
      MixedTailHistory K Z (L - 1) z
        (pending ++ [(job,
          harmonicLevel (Z : ℝ) 0 (L - 1))])
        (transcript ++
          [.testResult job
            (harmonicLevel (Z : ℝ) 0 (L - 1))])
  | testZero
      {z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history : MixedTailHistory K Z 0 z pending transcript)
      (hz : 0 < z) (job : Online.Label n) :
      MixedTailHistory K Z 0 (z - 1) pending
        (transcript ++ [.testResult job 0])
  | processPositive
      {L z : ℕ}
      {before after : MixedTailPending n}
      {transcript : Online.Transcript n}
      {job : Online.Label n} {p : ℝ}
      (history :
        MixedTailHistory K Z L z
          (before ++ (job, p) :: after) transcript) :
      MixedTailHistory K Z L z (before ++ after)
        (transcript ++ [.processed job])
  | processZero
      {L z : ℕ} {pending : MixedTailPending n}
      {transcript : Online.Transcript n}
      (history : MixedTailHistory K Z L z pending transcript)
      (job : Online.Label n) :
      MixedTailHistory K Z L z pending
        (transcript ++ [.processed job])

theorem MixedTailHistory.test_count
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
    transcript.testResults.length + L + z = K + Z := by
  induction history with
  | initial =>
      simp
  | testPositive history hL job ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.length_append, List.length_singleton]
      omega
  | testZero history hz job ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.length_append, List.length_singleton]
      omega
  | processPositive history ih =>
      simpa using ih
  | processZero history job ih =>
      simpa using ih

theorem MixedTailHistory.positive_phase
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
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
  | processPositive history ih =>
      exact ih
  | processZero history job ih =>
      exact ih

theorem MixedTailHistory.remaining_bounds
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
    L ≤ K ∧ z ≤ Z := by
  induction history with
  | initial =>
      exact ⟨le_rfl, le_rfl⟩
  | testPositive history hL job ih =>
      exact ⟨(Nat.sub_le _ _).trans ih.1, ih.2⟩
  | testZero history hz job ih =>
      exact ⟨ih.1, (Nat.sub_le _ _).trans ih.2⟩
  | processPositive history ih =>
      exact ih
  | processZero history job ih =>
      exact ih

theorem MixedTailHistory.rank_value_of_positive
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript)
    (hL : 0 < L) :
    harmonicRankValue K Z 0 transcript.testResults.length =
      harmonicLevel (Z : ℝ) 0 (L - 1) := by
  have hzEq : z = Z := by
    rcases history.positive_phase with hzero | hz
    · exact (hL.ne' hzero).elim
    · exact hz
  have hcount := history.test_count
  have hLK := history.remaining_bounds.1
  have hrank :
      transcript.testResults.length = K - L := by
    omega
  have hrankLt : transcript.testResults.length < K := by
    omega
  have hindex : K - 1 - (K - L) = L - 1 := by
    omega
  rw [harmonicRankValue_of_lt hrankLt, hrank, hindex]

theorem MixedTailHistory.rank_value_of_zero
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript)
    (hL : L = 0) :
    harmonicRankValue K Z 0 transcript.testResults.length = 0 := by
  subst L
  have hcount := history.test_count
  have hzZ := history.remaining_bounds.2
  have hrankGe : K ≤ transcript.testResults.length := by
    omega
  exact harmonicRankValue_of_ge hrankGe

theorem MixedTailHistory.pending_mem_testResult
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
    ∀ entry ∈ pending, entry ∈ transcript.testResults := by
  induction history with
  | initial =>
      simp
  | testPositive history hL tested ih =>
      intro entry hentry
      rw [List.mem_append] at hentry
      rw [Online.Transcript.testResults_append]
      rcases hentry with hold | hnew
      · exact List.mem_append.mpr (Or.inl (ih entry hold))
      · simp only [List.mem_singleton] at hnew
        subst entry
        simp
  | testZero history hz tested ih =>
      intro entry hentry
      rw [Online.Transcript.testResults_append]
      exact List.mem_append.mpr (Or.inl (ih entry hentry))
  | @processPositive L z before after transcript job p history ih =>
      intro entry hentry
      rw [Online.Transcript.testResults_append]
      apply List.mem_append.mpr
      left
      apply ih entry
      rw [List.mem_append] at hentry ⊢
      rcases hentry with hbefore | hafter
      · exact Or.inl hbefore
      · exact Or.inr (by simp [hafter])
  | processZero history processed ih =>
      intro entry hentry
      rw [Online.Transcript.testResults_append]
      exact List.mem_append.mpr (Or.inl (ih entry hentry))

/-! ## The two-phase history on the original labels -/

abbrev MixedCapPending (n : ℕ) := List (Online.Label n)

inductive MixedPhase (n : ℕ) where
  | pre (caps : MixedCapPending n)
  | post (H L z : ℕ) (caps : MixedCapPending n)
      (pending : MixedTailPending n)

/-- Reachability of the actual optional run.  The cap prefix is represented
by `pre`; at a first crossing `H` freezes the number of untouched labels and
the post phase begins with the rounded `A:B` harmonic split. -/
inductive MixedQuotaHistory
    (n : ℕ) (u β : ℝ) (A B : ℕ) :
    MixedPhase n → Online.Config n → Prop
  | initial :
      MixedQuotaHistory n u β A B (.pre [])
        (Online.Config.initial n)
  | preTestBelow
      {caps : MixedCapPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B (.pre caps) config)
      (job : Online.Label n)
      (hjob : config.jobs job = .untouched)
      (hbelow :
        ¬ HiddenStoppingOracle.Crossed n u β
          (config.transcript ++ [.testResult job u])) :
      MixedQuotaHistory n u β A B
        (.pre (caps ++ [job]))
        {
          jobs := Function.update config.jobs job (.tested u)
          transcript := config.transcript ++ [.testResult job u]
        }
  | preTestCross
      {caps : MixedCapPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B (.pre caps) config)
      (job : Online.Label n)
      (hjob : config.jobs job = .untouched)
      (hcross :
        HiddenStoppingOracle.Crossed n u β
          (config.transcript ++ [.testResult job u]))
      (H : ℕ)
      (hH :
        H =
          n -
            (config.transcript ++
              [Online.Observation.testResult job u]).startedLabels.length) :
      MixedQuotaHistory n u β A B
        (.post H
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          (caps ++ [job]) [])
        {
          jobs := Function.update config.jobs job (.tested u)
          transcript := config.transcript ++ [.testResult job u]
        }
  | preProcessCap
      {before after : MixedCapPending n}
      {config : Online.Config n}
      {job : Online.Label n}
      (history :
        MixedQuotaHistory n u β A B
          (.pre (before ++ job :: after)) config)
      (hjob : config.jobs job = .tested u) :
      MixedQuotaHistory n u β A B
        (.pre (before ++ after))
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | preRawBelow
      {caps : MixedCapPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B (.pre caps) config)
      (job : Online.Label n)
      (hjob : config.jobs job = .untouched)
      (hbelow :
        ¬ HiddenStoppingOracle.Crossed n u β
          (config.transcript ++ [.rawCompleted job])) :
      MixedQuotaHistory n u β A B (.pre caps)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }
  | preRawCross
      {caps : MixedCapPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B (.pre caps) config)
      (job : Online.Label n)
      (hjob : config.jobs job = .untouched)
      (hcross :
        HiddenStoppingOracle.Crossed n u β
          (config.transcript ++ [.rawCompleted job]))
      (H : ℕ)
      (hH :
        H =
          n -
            (config.transcript ++
              [Online.Observation.rawCompleted job]).startedLabels.length) :
      MixedQuotaHistory n u β A B
        (.post H
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          caps [])
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }
  | postTestPositive
      {H L z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H L z caps pending) config)
      (hL : 0 < L) (job : Online.Label n)
      (hjob : config.jobs job = .untouched) :
      MixedQuotaHistory n u β A B
        (.post H (L - 1) z caps
          (pending ++ [(job,
            harmonicLevel
              (tailZeroCount A B H : ℝ) 0 (L - 1))]))
        {
          jobs := Function.update config.jobs job
            (.tested
              (harmonicLevel
                (tailZeroCount A B H : ℝ) 0 (L - 1)))
          transcript := config.transcript ++
            [.testResult job
              (harmonicLevel
                (tailZeroCount A B H : ℝ) 0 (L - 1))]
        }
  | postTestZero
      {H z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H 0 z caps pending) config)
      (hz : 0 < z) (job : Online.Label n)
      (hjob : config.jobs job = .untouched) :
      MixedQuotaHistory n u β A B
        (.post H 0 (z - 1) caps pending)
        {
          jobs := Function.update config.jobs job (.tested 0)
          transcript := config.transcript ++ [.testResult job 0]
        }
  | postProcessPositive
      {H L z : ℕ} {caps : MixedCapPending n}
      {before after : MixedTailPending n}
      {config : Online.Config n}
      {job : Online.Label n} {p : ℝ}
      (history :
        MixedQuotaHistory n u β A B
          (.post H L z caps
            (before ++ (job, p) :: after)) config)
      (hjob : config.jobs job = .tested p) :
      MixedQuotaHistory n u β A B
        (.post H L z caps (before ++ after))
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | postProcessZero
      {H L z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H L z caps pending) config)
      (job : Online.Label n)
      (hjob : config.jobs job = .tested 0)
      (hvirtual :
        job ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults.map Prod.fst) :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | postProcessCap
      {H L z : ℕ}
      {before after : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      {job : Online.Label n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H L z (before ++ job :: after) pending) config)
      (hjob : config.jobs job = .tested u)
      (hvirtual :
        job ∉
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults.map Prod.fst) :
      MixedQuotaHistory n u β A B
        (.post H L z (before ++ after) pending)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | postRawPositive
      {H L z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H L z caps pending) config)
      (hL : 0 < L) (job : Online.Label n)
      (hjob : config.jobs job = .untouched) :
      MixedQuotaHistory n u β A B
        (.post H (L - 1) z caps pending)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }
  | postRawZero
      {H z : ℕ} {caps : MixedCapPending n}
      {pending : MixedTailPending n}
      {config : Online.Config n}
      (history :
        MixedQuotaHistory n u β A B
          (.post H 0 z caps pending) config)
      (hz : 0 < z) (job : Online.Label n)
      (hjob : config.jobs job = .untouched) :
      MixedQuotaHistory n u β A B
        (.post H 0 (z - 1) caps pending)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }

def MixedPhase.crossingInvariant
    (n : ℕ) (u β : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ =>
      ¬ HiddenStoppingOracle.Crossed n u β config.transcript
  | .post _ _ _ _ _ =>
      HiddenStoppingOracle.Crossed n u β config.transcript

theorem MixedQuotaHistory.crossing_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.crossingInvariant n u β config := by
  induction history with
  | initial =>
      exact HiddenStoppingOracle.not_crossed_nil hn hβ
  | preTestBelow history job hjob hbelow ih =>
      exact hbelow
  | preTestCross history job hjob hcross H hH ih =>
      exact hcross
  | preProcessCap history hjob ih =>
      intro hcross
      apply ih
      unfold HiddenStoppingOracle.Crossed at *
      rwa [HiddenStoppingOracle.surplus_append_processed] at hcross
  | preRawBelow history job hjob hbelow ih =>
      exact hbelow
  | preRawCross history job hjob hcross H hH ih =>
      exact hcross
  | postTestPositive history hL job hjob ih =>
      exact crossed_append_observation ih hβ.le _
  | postTestZero history hz job hjob ih =>
      exact crossed_append_observation ih hβ.le _
  | postProcessPositive history hjob ih =>
      exact crossed_append_observation ih hβ.le _
  | postProcessZero history job hjob hvirtual ih =>
      exact crossed_append_observation ih hβ.le _
  | postProcessCap history hjob hvirtual ih =>
      exact crossed_append_observation ih hβ.le _
  | postRawPositive history hL job hjob ih =>
      exact crossed_append_observation ih hβ.le _
  | postRawZero history hz job hjob ih =>
      exact crossed_append_observation ih hβ.le _

theorem MixedQuotaHistory.pre_not_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config) :
    ¬ HiddenStoppingOracle.Crossed n u β config.transcript :=
  history.crossing_invariant hn hβ

theorem MixedQuotaHistory.post_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {H L z : ℕ} {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    HiddenStoppingOracle.Crossed n u β config.transcript :=
  history.crossing_invariant hn hβ

def MixedPhase.tailSizeInvariant
    (n : ℕ) (u β : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post H _ _ _ _ =>
      (scan n u β config.transcript).tailSize = H

theorem MixedQuotaHistory.tailSize_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.tailSizeInvariant n u β config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow history job hjob hbelow ih =>
      trivial
  | @preTestCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore
              ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.testResult job u) hcross
      simpa [MixedPhase.tailSizeInvariant, hH] using hscan.2.2
  | preProcessCap history hjob ih =>
      trivial
  | preRawBelow history job hjob hbelow ih =>
      trivial
  | @preRawCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore
              ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.rawCompleted job) hcross
      simpa [MixedPhase.tailSizeInvariant, hH] using hscan.2.2
  | postTestPositive history hL job hjob ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postTestZero history hz job hjob ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postProcessPositive history hjob ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postProcessZero history job hjob hvirtual ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postProcessCap history hjob hvirtual ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postRawPositive history hL job hjob ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih
  | postRawZero history hz job hjob ih =>
      exact
        (scan_tailSize_append_of_crossed hn hβ
          (history.post_crossed hn hβ) _).trans ih

theorem MixedQuotaHistory.post_tailSize_eq
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {H L z : ℕ} {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    (scan n u β config.transcript).tailSize = H :=
  history.tailSize_invariant hn hβ

/-! ## Exact virtual tail history -/

/-- The phase-indexed invariant saying that the physical post-crossing
transcript, after expanding raw completions, is exactly a run of the
finite harmonic state machine selected at the crossing. -/
def MixedPhase.virtualHistoryInvariant
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post H L z _ pending =>
      MixedTailHistory
        (tailPositiveCount A B H)
        (tailZeroCount A B H)
        L z pending
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript)

theorem MixedQuotaHistory.virtual_history_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.virtualHistoryInvariant n u β A B config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow history job hjob hbelow ih =>
      trivial
  | @preTestCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore
              ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.testResult job u) hcross
      have hempty :
          virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              (config.transcript ++ [.testResult job u]) =
            [] := by
        simp [virtualTail, hscan.2.1, htail]
      simpa [MixedPhase.virtualHistoryInvariant, hempty] using
        (MixedTailHistory.initial :
          MixedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            ([] : MixedTailPending n) [])
  | preProcessCap history hjob ih =>
      trivial
  | preRawBelow history job hjob hbelow ih =>
      trivial
  | @preRawCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
      have htail :=
        scan_tail_eq_nil_of_not_crossed hn hβ hbefore
      have hstored :
          (scan n u β config.transcript).crossed = false := by
        exact Bool.eq_false_of_not_eq_true
          (fun htrue =>
            hbefore
              ((scan_crossed_iff hn hβ _).mp htrue))
      have hscan :=
        scan_append_firstCrossing hstored
          (Online.Observation.rawCompleted job) hcross
      have hempty :
          virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              (config.transcript ++ [.rawCompleted job]) =
            [] := by
        simp [virtualTail, hscan.2.1, htail]
      simpa [MixedPhase.virtualHistoryInvariant, hempty] using
        (MixedTailHistory.initial :
          MixedTailHistory
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            ([] : MixedTailPending n) [])
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.testResult job
            (harmonicLevel
              (tailZeroCount A B H : ℝ) 0 (L - 1)))
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep] using
        (MixedTailHistory.testPositive ih hL job)
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.testResult job 0)
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep] using
        (MixedTailHistory.testZero ih hz job)
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.processed job)
      have hentry :
          (job, p) ∈
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults :=
        ih.pending_mem_testResult (job, p) (by simp)
      have hlabel :
          job ∈
            (virtualTail n u β
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              config.transcript).testResults.map Prod.fst :=
        List.mem_map.mpr ⟨(job, p), hentry, rfl⟩
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep, hlabel] using
        (MixedTailHistory.processPositive ih)
  | @postProcessZero H L z caps pending config
      history job hjob hvirtualMem ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.processed job)
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep, hvirtualMem] using
        (MixedTailHistory.processZero ih job)
  | @postProcessCap H L z before after pending config
      job history hjob hvirtualMem ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.processed job)
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep, hvirtualMem] using ih
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.rawCompleted job)
      have hrank := ih.rank_value_of_positive hL
      have htested :=
        MixedTailHistory.testPositive ih hL job
      have hprocessed :=
        MixedTailHistory.processPositive
          (before := pending) (after := []) htested
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep, hrank, List.append_assoc] using
        hprocessed
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hvirtual :=
        virtualTail_append_of_crossed hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross (Online.Observation.rawCompleted job)
      have hrank := ih.rank_value_of_zero rfl
      have htested :=
        MixedTailHistory.testZero ih hz job
      have hprocessed :=
        MixedTailHistory.processZero htested job
      simpa [MixedPhase.virtualHistoryInvariant,
        hvirtual, virtualTailStep, hrank, List.append_assoc] using
        hprocessed

theorem MixedQuotaHistory.post_virtual_history
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    MixedTailHistory
      (tailPositiveCount A B H)
      (tailZeroCount A B H)
      L z pending
      (virtualTail n u β
        (tailPositiveCount A B H)
        (tailZeroCount A B H)
        config.transcript) :=
  history.virtual_history_invariant hn hβ

/-! ## Lifecycle and remaining-tail counts -/

/-- Every history generated by the mixed state machine is a legal lifecycle
history: first-touch labels are distinct and an untouched label has not
already appeared. -/
theorem MixedQuotaHistory.started_history_invariant
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    config.StartedHistoryInvariant := by
  induction history with
  | initial =>
      exact Online.Config.initial_startedHistoryInvariant n
  | @preTestBelow caps config history job hjob hbelow ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => u)
        (action := .test job)
      simp [Online.Config.step, hjob]
  | @preTestCross caps config history job hjob hcross H hH ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => u)
        (action := .test job)
      simp [Online.Config.step, hjob]
  | @preProcessCap before after config job history hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => u)
        (action := .process job)
      simp [Online.Config.step, hjob]
  | @preRawBelow caps config history job hjob hbelow ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => u)
        (action := .raw job)
      simp [Online.Config.step, hjob]
  | @preRawCross caps config history job hjob hcross H hH ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => u)
        (action := .raw job)
      simp [Online.Config.step, hjob]
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ =>
          harmonicLevel
            (tailZeroCount A B H : ℝ) 0 (L - 1))
        (action := .test job)
      simp [Online.Config.step, hjob]
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .test job)
      simp [Online.Config.step, hjob]
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .process job)
      simp [Online.Config.step, hjob]
  | @postProcessZero H L z caps pending config
      history job hjob hvirtual ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .process job)
      simp [Online.Config.step, hjob]
  | @postProcessCap H L z before after pending config
      job history hjob hvirtual ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .process job)
      simp [Online.Config.step, hjob]
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .raw job)
      simp [Online.Config.step, hjob]
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      apply Online.Config.startedHistoryInvariant_step ih
        (cap := .finite u)
        (oracle := fun _ _ => 0)
        (action := .raw job)
      simp [Online.Config.step, hjob]

/-- Phase-indexed form of the exact remaining-tail count. -/
def MixedPhase.remainingInvariant
    (n : ℕ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post _ L z _ _ =>
      config.transcript.startedLabels.length + L + z = n

theorem MixedQuotaHistory.remaining_invariant
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.remainingInvariant n config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow history job hjob hbelow ih =>
      trivial
  | @preTestCross caps config previous job hjob hcross H hH ih =>
      have hfull :
          MixedQuotaHistory n u β A B
            (.post H
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              (caps ++ [job]) [])
            {
              jobs := Function.update config.jobs job (.tested u)
              transcript := config.transcript ++ [.testResult job u]
            } :=
        MixedQuotaHistory.preTestCross
          previous job hjob hcross H hH
      have hnodup := hfull.started_history_invariant.nodup
      have hbound :
          (config.transcript ++
            [Online.Observation.testResult job u]).startedLabels.length ≤ n := by
        calc
          _ = (config.transcript ++
                [Online.Observation.testResult job u]).startedLabels.toFinset.card := by
              rw [List.toFinset_card_of_nodup hnodup]
          _ ≤ Fintype.card (Online.Label n) :=
              Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      have hsplit := tail_split A B H
      simp only [MixedPhase.remainingInvariant]
      omega
  | preProcessCap history hjob ih =>
      trivial
  | preRawBelow history job hjob hbelow ih =>
      trivial
  | @preRawCross caps config previous job hjob hcross H hH ih =>
      have hfull :
          MixedQuotaHistory n u β A B
            (.post H
              (tailPositiveCount A B H)
              (tailZeroCount A B H)
              caps [])
            {
              jobs := Function.update config.jobs job .done
              transcript := config.transcript ++ [.rawCompleted job]
            } :=
        MixedQuotaHistory.preRawCross
          previous job hjob hcross H hH
      have hnodup := hfull.started_history_invariant.nodup
      have hbound :
          (config.transcript ++
            [Online.Observation.rawCompleted job]).startedLabels.length ≤ n := by
        calc
          _ = (config.transcript ++
                [Online.Observation.rawCompleted job]).startedLabels.toFinset.card := by
              rw [List.toFinset_card_of_nodup hnodup]
          _ ≤ Fintype.card (Online.Label n) :=
              Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      have hsplit := tail_split A B H
      simp only [MixedPhase.remainingInvariant]
      omega
  | postTestPositive history hL job hjob ih =>
      simp only [MixedPhase.remainingInvariant,
        Online.Transcript.startedLabels_append_testResult,
        List.length_append, List.length_singleton] at ih ⊢
      omega
  | postTestZero history hz job hjob ih =>
      simp only [MixedPhase.remainingInvariant,
        Online.Transcript.startedLabels_append_testResult,
        List.length_append, List.length_singleton] at ih ⊢
      omega
  | postProcessPositive history hjob ih =>
      simpa [MixedPhase.remainingInvariant] using ih
  | postProcessZero history job hjob hvirtual ih =>
      simpa [MixedPhase.remainingInvariant] using ih
  | postProcessCap history hjob hvirtual ih =>
      simpa [MixedPhase.remainingInvariant] using ih
  | postRawPositive history hL job hjob ih =>
      simp only [MixedPhase.remainingInvariant,
        Online.Transcript.startedLabels_append_rawCompleted,
        List.length_append, List.length_singleton] at ih ⊢
      omega
  | postRawZero history hz job hjob ih =>
      simp only [MixedPhase.remainingInvariant,
        Online.Transcript.startedLabels_append_rawCompleted,
        List.length_append, List.length_singleton] at ih ⊢
      omega

/-- Once the scale is frozen, every later first touch consumes exactly one
of the remaining positive/zero tail slots. -/
theorem MixedQuotaHistory.post_started_add_remaining
    {n : ℕ} {u β : ℝ} {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    config.transcript.startedLabels.length + L + z = n :=
  history.remaining_invariant

theorem MixedQuotaHistory.no_untouched_of_tail_finished
    {n : ℕ} {u β : ℝ} {A B H : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps pending) config)
    (job : Online.Label n)
    (hjob : config.jobs job = .untouched) :
    False := by
  have hlength :
      config.transcript.startedLabels.length = n := by
    simpa using history.post_started_add_remaining
  have hstarted := history.started_history_invariant
  have hnot := hstarted.untouched_not_mem job hjob
  have hnotFin :
      job ∉ config.transcript.startedLabels.toFinset := by
    simpa using hnot
  have hcard :
      config.transcript.startedLabels.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hstarted.nodup]
    exact hlength
  have hinsert :
      (config.transcript.startedLabels.toFinset.cons
        job hnotFin).card = n + 1 := by
    rw [Finset.card_cons hnotFin, hcard]
  have hle :
      (config.transcript.startedLabels.toFinset.cons
        job hnotFin).card ≤ n := by
    calc
      _ ≤ Fintype.card (Online.Label n) :=
        Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  omega

/-! The next three identities are the exact public-label effect of a
post-crossing observation on the virtual transcript. -/

theorem virtualTail_testLabels_append_test_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    (K Z : ℕ) {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) (p : ℝ) :
    (virtualTail n u β K Z
      (transcript ++ [.testResult job p])).testResults.map Prod.fst =
      (virtualTail n u β K Z
        transcript).testResults.map Prod.fst ++ [job] := by
  rw [virtualTail_append_of_crossed hn hβ K Z hcross]
  simp [virtualTailStep]

theorem virtualTail_testLabels_append_process_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    (K Z : ℕ) {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) :
    (virtualTail n u β K Z
      (transcript ++ [.processed job])).testResults.map Prod.fst =
      (virtualTail n u β K Z
        transcript).testResults.map Prod.fst := by
  rw [virtualTail_append_of_crossed hn hβ K Z hcross]
  simp only [virtualTailStep]
  split <;> simp

theorem virtualTail_testLabels_append_raw_of_crossed
    {n : ℕ} (hn : 0 < n) {u β : ℝ} (hβ : 0 < β)
    (K Z : ℕ) {transcript : Online.Transcript n}
    (hcross : HiddenStoppingOracle.Crossed n u β transcript)
    (job : Online.Label n) :
    (virtualTail n u β K Z
      (transcript ++ [.rawCompleted job])).testResults.map Prod.fst =
      (virtualTail n u β K Z
        transcript).testResults.map Prod.fst ++ [job] := by
  rw [virtualTail_append_of_crossed hn hβ K Z hcross]
  simp [virtualTailStep]

/-! ## Classification of live tested jobs -/

/-- Every live tested state is represented by exactly one of the data
structures that the mixed transition system knows how to process.  In the
post phase, prefix-cap labels are additionally known not to belong to the
virtual tail. -/
def MixedPhase.testedInvariant
    (n : ℕ) (u β : ℝ) (A B : ℕ)
    (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre caps =>
      ∀ job p, config.jobs job = .tested p →
        p = u ∧ job ∈ caps
  | .post H _ _ caps pending =>
      let virtualLabels :=
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript).testResults.map Prod.fst
      ∀ job p, config.jobs job = .tested p →
        (p = u ∧ job ∈ caps ∧ job ∉ virtualLabels) ∨
        (job, p) ∈ pending ∨
        (p = 0 ∧ job ∈ virtualLabels)

theorem MixedQuotaHistory.tested_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.testedInvariant n u β A B config := by
  induction history with
  | initial =>
      intro job p hjob
      simp [Online.Config.initial] at hjob
  | @preTestBelow caps config history job hjob hbelow ih =>
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      by_cases heq : tested = job
      · subst tested
        simp [Function.update] at htested
        subst p
        exact ⟨rfl, by simp⟩
      · have hold : config.jobs tested = .tested p := by
          simpa [Function.update, heq] using htested
        rcases ih tested p hold with ⟨hp, hmem⟩
        exact ⟨hp, List.mem_append.mpr (Or.inl hmem)⟩
  | @preTestCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
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
      have hempty :
          ((virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (config.transcript ++ [.testResult job u]))).testResults.map
              Prod.fst = [] := by
        simp [virtualTail, hscan.2.1, htail]
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      by_cases heq : tested = job
      · subst tested
        simp [Function.update] at htested
        subst p
        exact Or.inl ⟨rfl, by simp, by simp [hempty]⟩
      · have hold : config.jobs tested = .tested p := by
          simpa [Function.update, heq] using htested
        rcases ih tested p hold with ⟨hp, hmem⟩
        exact Or.inl
          ⟨hp, List.mem_append.mpr (Or.inl hmem),
            by simp [hempty]⟩
  | @preProcessCap before after config job history hjob ih =>
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with ⟨hp, hmem⟩
      rw [List.mem_append] at hmem ⊢
      rcases hmem with hbefore | htail
      · exact ⟨hp, Or.inl hbefore⟩
      · simp only [List.mem_cons] at htail
        rcases htail with heq | hafter
        · exact (hne (congrArg id heq)).elim
        · exact ⟨hp, Or.inr hafter⟩
  | @preRawBelow caps config history job hjob hbelow ih =>
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      apply ih tested p
      simpa [Function.update, hne] using htested
  | @preRawCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
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
      have hempty :
          ((virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            (config.transcript ++ [.rawCompleted job]))).testResults.map
              Prod.fst = [] := by
        simp [virtualTail, hscan.2.1, htail]
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with ⟨hp, hmem⟩
      exact Or.inl ⟨hp, hmem, by simp [hempty]⟩
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_test_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
          (harmonicLevel
            (tailZeroCount A B H : ℝ) 0 (L - 1))
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      by_cases heq : tested = job
      · subst tested
        simp [Function.update] at htested
        subst p
        exact Or.inr (Or.inl (by simp))
      · have hold : config.jobs tested = .tested p := by
          simpa [Function.update, heq] using htested
        rcases ih tested p hold with hcap | hpending | hzero
        · exact Or.inl
            ⟨hcap.1, hcap.2.1, by
              rw [hlabels]
              simp [hcap.2.2, heq]⟩
        · exact Or.inr
            (Or.inl (List.mem_append.mpr (Or.inl hpending)))
        · exact Or.inr (Or.inr
            ⟨hzero.1, by
              rw [hlabels]
              exact List.mem_append.mpr (Or.inl hzero.2)⟩)
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_test_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job 0
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      by_cases heq : tested = job
      · subst tested
        simp [Function.update] at htested
        subst p
        exact Or.inr (Or.inr
          ⟨rfl, by rw [hlabels]; simp⟩)
      · have hold : config.jobs tested = .tested p := by
          simpa [Function.update, heq] using htested
        rcases ih tested p hold with hcap | hpending | hzero
        · exact Or.inl
            ⟨hcap.1, hcap.2.1, by
              rw [hlabels]
              simp [hcap.2.2, heq]⟩
        · exact Or.inr (Or.inl hpending)
        · exact Or.inr (Or.inr
            ⟨hzero.1, by
              rw [hlabels]
              exact List.mem_append.mpr (Or.inl hzero.2)⟩)
  | @postProcessPositive H L z caps before after config
      job q history hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_process_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with hcap | hpending | hzero
      · exact Or.inl
          ⟨hcap.1, hcap.2.1, by simpa [hlabels] using hcap.2.2⟩
      · rw [List.mem_append] at hpending ⊢
        rcases hpending with hbefore | htail
        · exact Or.inr (Or.inl (Or.inl hbefore))
        · simp only [List.mem_cons] at htail
          rcases htail with heq | hafter
          · have hfirst : tested = job :=
              congrArg Prod.fst heq
            exact (hne hfirst).elim
          · exact Or.inr (Or.inl (Or.inr hafter))
      · exact Or.inr (Or.inr
          ⟨hzero.1, by simpa [hlabels] using hzero.2⟩)
  | @postProcessZero H L z caps pending config
      history job hjob hvirtual ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_process_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with hcap | hpending | hzero
      · exact Or.inl
          ⟨hcap.1, hcap.2.1, by simpa [hlabels] using hcap.2.2⟩
      · exact Or.inr (Or.inl hpending)
      · exact Or.inr (Or.inr
          ⟨hzero.1, by simpa [hlabels] using hzero.2⟩)
  | @postProcessCap H L z before after pending config
      job history hjob hvirtual ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_process_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with hcap | hpending | hzero
      · rw [List.mem_append] at hcap ⊢
        rcases hcap.2.1 with hbefore | htail
        · exact Or.inl
            ⟨hcap.1, Or.inl hbefore,
              by simpa [hlabels] using hcap.2.2⟩
        · simp only [List.mem_cons] at htail
          rcases htail with heq | hafter
          · exact (hne heq).elim
          · exact Or.inl
              ⟨hcap.1, Or.inr hafter,
                by simpa [hlabels] using hcap.2.2⟩
      · exact Or.inr (Or.inl hpending)
      · exact Or.inr (Or.inr
          ⟨hzero.1, by simpa [hlabels] using hzero.2⟩)
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_raw_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with hcap | hpending | hzero
      · exact Or.inl
          ⟨hcap.1, hcap.2.1, by
            rw [hlabels]
            simp [hcap.2.2, hne]⟩
      · exact Or.inr (Or.inl hpending)
      · exact Or.inr (Or.inr
          ⟨hzero.1, by
            rw [hlabels]
            exact List.mem_append.mpr (Or.inl hzero.2)⟩)
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      have hcross := history.post_crossed hn hβ
      have hlabels :=
        virtualTail_testLabels_append_raw_of_crossed
          hn hβ
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          hcross job
      simp only [MixedPhase.testedInvariant] at ih ⊢
      intro tested p htested
      have hne : tested ≠ job := by
        intro heq
        subst tested
        simp [Function.update] at htested
      have hold : config.jobs tested = .tested p := by
        simpa [Function.update, hne] using htested
      rcases ih tested p hold with hcap | hpending | hzero
      · exact Or.inl
          ⟨hcap.1, hcap.2.1, by
            rw [hlabels]
            simp [hcap.2.2, hne]⟩
      · exact Or.inr (Or.inl hpending)
      · exact Or.inr (Or.inr
          ⟨hzero.1, by
            rw [hlabels]
            exact List.mem_append.mpr (Or.inl hzero.2)⟩)

/-! ## Preservation by the concrete adaptive oracle -/

theorem transcript_mem_started_of_testResult
    {transcript : Online.Transcript n}
    {job : Online.Label n} {p : ℝ}
    (hmem : (job, p) ∈ transcript.testResults) :
    job ∈ transcript.startedLabels := by
  induction transcript with
  | nil =>
      simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult tested q =>
          simp only [Online.Transcript.testResults_testResult_cons,
            List.mem_cons] at hmem
          simp only [Online.Transcript.startedLabels_testResult_cons,
            List.mem_cons]
          rcases hmem with hhead | htail
          · exact Or.inl (congrArg Prod.fst hhead)
          · exact Or.inr (ih htail)
      | processed processed =>
          exact ih hmem
      | rawCompleted raw =>
          exact List.mem_cons_of_mem raw (ih hmem)

theorem MixedQuotaHistory.adaptiveStep
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    {phase : MixedPhase n}
    {config next : Online.Config n}
    {assignment nextAssignment : Online.PartialAssignment n}
    {action : Online.Action n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        phase config)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hstep :
      Online.adaptiveStep (.finite u)
        (oracle n u M A B)
        config assignment action =
          some (next, nextAssignment)) :
    ∃ nextPhase,
      MixedQuotaHistory n u (quotaFraction M A B) A B
        nextPhase next := by
  let β := quotaFraction M A B
  have hβ : 0 < β := quotaFraction_pos hM
  have hstarted := history.started_history_invariant
  have hunassigned_of_untouched :
      ∀ {job : Online.Label n},
        config.jobs job = .untouched → assignment job = none := by
    intro job hjob
    cases hassigned : assignment job with
    | none => rfl
    | some p =>
        have htested := hsupported job p hassigned
        exact (hstarted.untouched_not_mem job hjob
          (transcript_mem_started_of_testResult htested)).elim
  cases phase with
  | pre caps =>
      cases action with
      | process job =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have hclass :=
                history.tested_invariant hn hβ job p hjob
              obtain ⟨hp, hmem⟩ := hclass
              subst p
              obtain ⟨before, after, hcaps⟩ :=
                List.append_of_mem hmem
              subst caps
              exact ⟨.pre (before ++ after),
                MixedQuotaHistory.preProcessCap history hjob⟩
      | test job =>
          cases hjob : config.jobs job with
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | untouched =>
              have hunassigned := hunassigned_of_untouched hjob
              have hnot := history.pre_not_crossed hn hβ
              have horacle :=
                oracle_eq_cap_of_not_crossed hnot job
              simp [Online.adaptiveStep, Online.Config.step, hjob,
                Online.adaptiveOracle, Online.adaptiveValue,
                hunassigned, horacle] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              by_cases hcross :
                  HiddenStoppingOracle.Crossed n u β
                    (config.transcript ++ [.testResult job u])
              · let H :=
                  n -
                    (config.transcript ++
                      [Online.Observation.testResult job u]).startedLabels.length
                exact
                  ⟨.post H
                      (tailPositiveCount A B H)
                      (tailZeroCount A B H)
                      (caps ++ [job]) [],
                    MixedQuotaHistory.preTestCross
                      history job hjob hcross H rfl⟩
              · exact
                  ⟨.pre (caps ++ [job]),
                    MixedQuotaHistory.preTestBelow
                      history job hjob hcross⟩
      | raw job =>
          cases hjob : config.jobs job with
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | untouched =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              by_cases hcross :
                  HiddenStoppingOracle.Crossed n u β
                    (config.transcript ++ [.rawCompleted job])
              · let H :=
                  n -
                    (config.transcript ++
                      [Online.Observation.rawCompleted job]).startedLabels.length
                exact
                  ⟨.post H
                      (tailPositiveCount A B H)
                      (tailZeroCount A B H)
                      caps [],
                    MixedQuotaHistory.preRawCross
                      history job hjob hcross H rfl⟩
              · exact
                  ⟨.pre caps,
                    MixedQuotaHistory.preRawBelow
                      history job hjob hcross⟩
  | post H L z caps pending =>
      have hcross := history.post_crossed hn hβ
      have htailSize := history.post_tailSize_eq hn hβ
      have hvirtual := history.post_virtual_history hn hβ
      cases action with
      | process job =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              have hclass :=
                history.tested_invariant hn hβ job p hjob
              rcases hclass with hcap | hpending | hzero
              · obtain ⟨hp, hmem, hnotVirtual⟩ := hcap
                subst p
                obtain ⟨before, after, hcaps⟩ :=
                  List.append_of_mem hmem
                subst caps
                exact
                  ⟨.post H L z (before ++ after) pending,
                    MixedQuotaHistory.postProcessCap
                      history hjob hnotVirtual⟩
              · obtain ⟨before, after, hpendingEq⟩ :=
                  List.append_of_mem hpending
                subst pending
                exact
                  ⟨.post H L z caps (before ++ after),
                    MixedQuotaHistory.postProcessPositive
                      history hjob⟩
              · obtain ⟨hp, hmem⟩ := hzero
                subst p
                exact
                  ⟨.post H L z caps pending,
                    MixedQuotaHistory.postProcessZero
                      history job hjob hmem⟩
      | test job =>
          cases hjob : config.jobs job with
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | untouched =>
              have hunassigned := hunassigned_of_untouched hjob
              have horacle :=
                oracle_eq_virtual_rank_of_crossed hcross job
              by_cases hL : 0 < L
              · have hvalue :=
                  hvirtual.rank_value_of_positive hL
                simp [Online.adaptiveStep, Online.Config.step, hjob,
                  Online.adaptiveOracle, Online.adaptiveValue,
                  hunassigned, horacle, β, htailSize, hvalue] at hstep
                rcases hstep with ⟨rfl, rfl⟩
                exact
                  ⟨.post H (L - 1) z caps
                      (pending ++ [(job,
                        harmonicLevel
                          (tailZeroCount A B H : ℝ)
                          0 (L - 1))]),
                    MixedQuotaHistory.postTestPositive
                      history hL job hjob⟩
              · have hLzero : L = 0 :=
                  Nat.eq_zero_of_not_pos hL
                subst L
                by_cases hz : 0 < z
                · have hvalue :=
                    hvirtual.rank_value_of_zero rfl
                  simp [Online.adaptiveStep, Online.Config.step, hjob,
                    Online.adaptiveOracle, Online.adaptiveValue,
                    hunassigned, horacle, β, htailSize, hvalue] at hstep
                  rcases hstep with ⟨rfl, rfl⟩
                  exact
                    ⟨.post H 0 (z - 1) caps pending,
                      MixedQuotaHistory.postTestZero
                        history hz job hjob⟩
                · have hz0 : z = 0 :=
                    Nat.eq_zero_of_not_pos hz
                  subst z
                  exact
                    (history.no_untouched_of_tail_finished
                      job hjob).elim
      | raw job =>
          cases hjob : config.jobs job with
          | tested p =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | done =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          | untouched =>
              simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
              rcases hstep with ⟨rfl, rfl⟩
              by_cases hL : 0 < L
              · exact
                  ⟨.post H (L - 1) z caps pending,
                    MixedQuotaHistory.postRawPositive
                      history hL job hjob⟩
              · have hLzero : L = 0 :=
                  Nat.eq_zero_of_not_pos hL
                subst L
                by_cases hz : 0 < z
                · exact
                    ⟨.post H 0 (z - 1) caps pending,
                      MixedQuotaHistory.postRawZero
                        history hz job hjob⟩
                · have hz0 : z = 0 :=
                    Nat.eq_zero_of_not_pos hz
                  subst z
                  exact
                    (history.no_untouched_of_tail_finished
                      job hjob).elim

theorem runAdaptiveFuel_mixedQuotaHistory
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {phase : MixedPhase n}
    {config : Online.Config n}
    {assignment : Online.PartialAssignment n}
    (history :
      MixedQuotaHistory n u (quotaFraction M A B) A B
        phase config)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript) :
    ∃ finalPhase,
      MixedQuotaHistory n u (quotaFraction M A B) A B
        finalPhase
        (Online.runAdaptiveFuel (.finite u)
          (oracle n u M A B)
          strategy fuel config assignment).result.config := by
  induction fuel generalizing phase config assignment with
  | zero =>
      exact ⟨phase, history⟩
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [Online.runAdaptiveFuel, haction] using
            (show ∃ finalPhase,
              MixedQuotaHistory n u (quotaFraction M A B) A B
                finalPhase config from ⟨phase, history⟩)
      | some action =>
          cases hstep :
              Online.adaptiveStep (.finite u)
                (oracle n u M A B)
                config assignment action with
          | none =>
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                (show ∃ finalPhase,
                  MixedQuotaHistory n u (quotaFraction M A B) A B
                    finalPhase config from ⟨phase, history⟩)
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              obtain ⟨nextPhase, nextHistory⟩ :=
                history.adaptiveStep hn hM hsupported hstep
              have nextSupported :=
                Online.adaptiveStep_supportedByTranscript
                  (.finite u) (oracle n u M A B)
                  config next assignment nextAssignment action
                  hsupported hstep
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                ih nextHistory nextSupported

theorem adaptiveRun_mixedQuotaHistory
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    ∃ finalPhase,
      MixedQuotaHistory n u (quotaFraction M A B) A B
        finalPhase
        (Online.adaptiveRun (.finite u)
          (oracle n u M A B)
          strategy fuel).result.config := by
  unfold Online.adaptiveRun
  apply runAdaptiveFuel_mixedQuotaHistory hn hM
    strategy fuel
    (MixedQuotaHistory.initial
      (n := n) (u := u) (β := quotaFraction M A B)
      (A := A) (B := B))
  simp [Online.SupportedByTranscript,
    Online.Config.initial, Online.emptyAssignment]

/-! ## Literal prefix/tail decomposition -/

def MixedPhase.tailDecompositionInvariant
    (n : ℕ) (u β : ℝ) (phase : MixedPhase n)
    (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => True
  | .post _ _ _ _ _ =>
      ∃ headTranscript : Online.Transcript n,
        config.transcript =
          headTranscript ++ (scan n u β config.transcript).tail

theorem MixedQuotaHistory.tail_decomposition_invariant
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B : ℕ}
    {phase : MixedPhase n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B phase config) :
    phase.tailDecompositionInvariant n u β config := by
  induction history with
  | initial =>
      trivial
  | preTestBelow history job hjob hbelow ih =>
      trivial
  | @preTestCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
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
      simp only [MixedPhase.tailDecompositionInvariant]
      refine ⟨config.transcript ++ [.testResult job u], ?_⟩
      simp [hscan.2.1, htail]
  | preProcessCap history hjob ih =>
      trivial
  | preRawBelow history job hjob hbelow ih =>
      trivial
  | @preRawCross caps config history job hjob hcross H hH ih =>
      have hbefore := history.pre_not_crossed hn hβ
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
      simp only [MixedPhase.tailDecompositionInvariant]
      refine ⟨config.transcript ++ [.rawCompleted job], ?_⟩
      simp [hscan.2.1, htail]
  | @postTestPositive H L z caps pending config
      history hL job hjob ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.testResult job
            (harmonicLevel
              (tailZeroCount A B H : ℝ) 0 (L - 1)))
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++
            [.testResult job
              (harmonicLevel
                (tailZeroCount A B H : ℝ) 0 (L - 1))] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.testResult job
              (harmonicLevel
                (tailZeroCount A B H : ℝ) 0 (L - 1))] :=
            congrArg
              (fun transcript =>
                transcript ++
                  [.testResult job
                    (harmonicLevel
                      (tailZeroCount A B H : ℝ) 0 (L - 1))])
              hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postTestZero H z caps pending config
      history hz job hjob ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.testResult job 0)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.testResult job 0] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.testResult job 0] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.testResult job 0])
                hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postProcessPositive H L z caps before after config
      job p history hjob ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.processed job)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.processed job] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.processed job] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.processed job])
                hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postProcessZero H L z caps pending config
      history job hjob hvirtual ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.processed job)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.processed job] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.processed job] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.processed job])
                hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postProcessCap H L z before after pending config
      job history hjob hvirtual ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.processed job)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.processed job] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.processed job] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.processed job])
                hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postRawPositive H L z caps pending config
      history hL job hjob ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.rawCompleted job)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.rawCompleted job] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.rawCompleted job] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.rawCompleted job])
                hdecomp
        _ = _ := List.append_assoc _ _ _
  | @postRawZero H z caps pending config
      history hz job hjob ih =>
      obtain ⟨headTranscript, hdecomp⟩ := ih
      have hscan :=
        scan_append_of_storedCrossed
          ((scan_crossed_iff hn hβ _).mpr
            (history.post_crossed hn hβ))
          (Online.Observation.rawCompleted job)
      refine ⟨headTranscript, ?_⟩
      rw [hscan.2.1]
      calc
        config.transcript ++ [.rawCompleted job] =
          (headTranscript ++
              (scan n u β config.transcript).tail) ++
            [.rawCompleted job] :=
              congrArg
                (fun transcript =>
                  transcript ++ [.rawCompleted job])
                hdecomp
        _ = _ := List.append_assoc _ _ _

theorem MixedQuotaHistory.post_tail_decomposition
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hβ : 0 < β) {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config) :
    ∃ headTranscript : Online.Transcript n,
      config.transcript =
        headTranscript ++ (scan n u β config.transcript).tail :=
  history.tail_decomposition_invariant hn hβ

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
