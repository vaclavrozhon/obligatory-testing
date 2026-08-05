import SchedulingPaper.ForcedPrefixUTE

/-!
# Executable Raw policy

The first two finite-cap branches use the policy that executes every job
untested in label order.  Its next label is reconstructed from the public
`rawCompleted` observations, so it is a genuine deterministic online
strategy and never inspects a hidden processing time.
-/

namespace SchedulingPaper.Online

noncomputable section

def Transcript.rawCompletedLabels
    (transcript : Transcript n) : List (Label n) :=
  transcript.filterMap fun
    | .rawCompleted job => some job
    | .testResult _ _ | .processed _ => none

def rawStrategy (n : ℕ) : Strategy n :=
  fun transcript =>
    let completed := transcript.rawCompletedLabels.length
    if h : completed < n then
      some (.raw ⟨completed, h⟩)
    else
      none

theorem rawStrategy_eq_raw_of_lt
    (transcript : Transcript n)
    (h : transcript.rawCompletedLabels.length < n) :
    rawStrategy n transcript =
      some (.raw ⟨transcript.rawCompletedLabels.length, h⟩) := by
  simp [rawStrategy, h]

theorem rawStrategy_eq_none_of_le
    (transcript : Transcript n)
    (h : n ≤ transcript.rawCompletedLabels.length) :
    rawStrategy n transcript = none := by
  simp [rawStrategy, not_lt.mpr h]

theorem rawStrategy_ne_test
    (n : ℕ) (transcript : Transcript n) (job : Label n) :
    rawStrategy n transcript ≠ some (.test job) := by
  simp [rawStrategy]

theorem rawStrategy_ne_process
    (n : ℕ) (transcript : Transcript n) (job : Label n) :
    rawStrategy n transcript ≠ some (.process job) := by
  simp [rawStrategy]

end

end SchedulingPaper.Online
