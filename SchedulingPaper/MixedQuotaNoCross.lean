import SchedulingPaper.MixedQuotaHistory
import SchedulingPaper.HiddenStoppingGlobalExchange
import Mathlib.Tactic

/-!
# The terminal no-crossing branch of the mixed quota adversary

Before the quota line is crossed every public test returns the cap.  At a
completed configuration, a quota strictly below one therefore forces the
number of tests to be zero: the whole execution used raw first touches.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound
namespace MixedQuotaOracle

/-- Phase-indexed statement that every test before crossing returned the
cap value. -/
def MixedPhase.preTestsInvariant
    (u : ℝ) (phase : MixedPhase n) (config : Online.Config n) : Prop :=
  match phase with
  | .pre _ => config.transcript.AllTestsEqual u
  | .post _ _ _ _ _ => True

theorem MixedQuotaHistory.pre_tests_invariant
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {phase : MixedPhase n} {config : Online.Config n}
    (history : MixedQuotaHistory n u β A B phase config) :
    phase.preTestsInvariant u config := by
  induction history with
  | initial =>
      simp [MixedPhase.preTestsInvariant,
        Online.Transcript.AllTestsEqual, Online.Config.initial]
  | preTestBelow history job hjob hbelow ih =>
      intro tested p hmem
      rw [Online.Transcript.testResults_append] at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ih tested p hmem
      · simp at hmem
        exact hmem.2
  | preProcessCap history hjob ih =>
      intro tested p hmem
      rw [Online.Transcript.testResults_append] at hmem
      exact ih tested p (by simpa using hmem)
  | preRawBelow history job hjob hbelow ih =>
      intro tested p hmem
      rw [Online.Transcript.testResults_append] at hmem
      exact ih tested p (by simpa using hmem)
  | preTestCross => trivial
  | preRawCross => trivial
  | postTestPositive => trivial
  | postTestZero => trivial
  | postProcessPositive => trivial
  | postProcessZero => trivial
  | postProcessCap => trivial
  | postRawPositive => trivial
  | postRawZero => trivial

/-- Every test in a pre-crossing mixed history returned the cap value. -/
theorem MixedQuotaHistory.pre_allTestsEqual
    {n : ℕ} {u β : ℝ} {A B : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config) :
    config.transcript.AllTestsEqual u :=
  history.pre_tests_invariant

/-- A completed pre-crossing history has no tests when the quota lies
strictly between zero and one. -/
theorem MixedQuotaHistory.pre_testResults_length_eq_zero_of_completed
    {n : ℕ} (hn : 0 < n)
    {u β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {A B : ℕ} {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config)
    (hprocess : config.ProcessHistoryInvariant)
    (hdone : ∀ job, config.jobs job = .done) :
    config.transcript.testResults.length = 0 := by
  have hall := history.pre_allTestsEqual
  have hlong :
      HiddenStoppingOracle.longCount u config.transcript =
        config.transcript.testResults.length :=
    HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length hall
  have hstartedLength :
      config.transcript.startedLabels.length = n :=
    Online.Config.startedLabels_length_eq_card_of_completed
      history.started_history_invariant hprocess hdone
  have hstartedCount :
      n =
        HiddenStoppingOracle.rawCount config.transcript +
          config.transcript.testResults.length := by
    have hstructural :=
      config.transcript.startedLabels_length_eq_raw_add_tests
    omega
  have hnotCrossed := history.pre_not_crossed hn hβ
  have hsurplus :
      HiddenStoppingOracle.surplus n u β config.transcript < 0 :=
    lt_of_not_ge hnotCrossed
  have hremaining :
      (n : ℝ) -
          HiddenStoppingOracle.rawCount config.transcript =
        config.transcript.testResults.length := by
    have hcast :
        (n : ℝ) =
          HiddenStoppingOracle.rawCount config.transcript +
            config.transcript.testResults.length := by
      exact_mod_cast hstartedCount
    linarith
  have hstrict :
      (config.transcript.testResults.length : ℝ) -
          β * config.transcript.testResults.length < 0 := by
    simpa [HiddenStoppingOracle.surplus, hlong, hremaining] using
      hsurplus
  have hzero :
      (config.transcript.testResults.length : ℝ) = 0 := by
    have hnonneg :
        0 ≤ (config.transcript.testResults.length : ℝ) := by
      positivity
    nlinarith
  exact_mod_cast hzero

/-- Consequently every first touch in the completed no-crossing branch was
raw. -/
theorem MixedQuotaHistory.pre_rawCount_eq_of_completed
    {n : ℕ} (hn : 0 < n)
    {u β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {A B : ℕ} {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B (.pre caps) config)
    (hprocess : config.ProcessHistoryInvariant)
    (hdone : ∀ job, config.jobs job = .done) :
    HiddenStoppingOracle.rawCount config.transcript = n := by
  have htests :=
    history.pre_testResults_length_eq_zero_of_completed
      hn hβ hβone hprocess hdone
  have hstartedLength :
      config.transcript.startedLabels.length = n :=
    Online.Config.startedLabels_length_eq_card_of_completed
      history.started_history_invariant hprocess hdone
  have hstructural :=
    config.transcript.startedLabels_length_eq_raw_add_tests
  omega

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
