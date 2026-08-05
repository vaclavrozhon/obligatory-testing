import SchedulingPaper.TimedOnline
import SchedulingPaper.BankPotential

/-!
# An executable transcript-only AdaptiveThreshold strategy

The algorithm in the paper is deterministic and fixes the label order
`0,1,...,n-1`.  All counters below are reconstructed from the public test
results, so the resulting term has exactly the required online type
`Transcript n → Option (Action n)`.
-/

namespace SchedulingPaper.Online

noncomputable section

structure ThresholdCounters where
  tested : ℕ
  positive : ℝ
  deferred : ℝ

def ThresholdCounters.initial : ThresholdCounters :=
  ⟨0, 0, 0⟩

def ThresholdCounters.remaining (n : ℕ) (s : ThresholdCounters) : ℕ :=
  n - s.tested

def ThresholdCounters.y (n : ℕ) (s : ThresholdCounters) : ℝ :=
  (s.deferred - RStar * s.positive) / s.remaining n

def ThresholdCounters.threshold (n : ℕ) (s : ThresholdCounters) : ℝ :=
  adaptiveThreshold (s.y n)

/-- Update after one public test result. -/
def ThresholdCounters.observe
    (n : ℕ) (s : ThresholdCounters) (p : ℝ) : ThresholdCounters :=
  {
    tested := s.tested + 1
    positive := s.positive + if 0 < p then 1 else 0
    deferred := s.deferred + if s.threshold n < p then 1 else 0
  }

def countersFromResults (n : ℕ) :
    List (Label n × ℝ) → ThresholdCounters :=
  List.foldl (fun s result => s.observe n result.2)
    ThresholdCounters.initial

def Transcript.thresholdCounters (n : ℕ)
    (transcript : Transcript n) : ThresholdCounters :=
  countersFromResults n transcript.testResults

/-- The state immediately before the most recent test result. -/
def Transcript.countersBeforeLastTest (n : ℕ)
    (transcript : Transcript n) : ThresholdCounters :=
  countersFromResults n transcript.testResults.dropLast

def Transcript.processedLabels (transcript : Transcript n) : List (Label n) :=
  transcript.filterMap fun
    | .processed job => some job
    | .testResult _ _ | .rawCompleted _ => none

def Transcript.remainingTestResults
    (transcript : Transcript n) : List (Label n × ℝ) :=
  transcript.testResults.filter fun result =>
    result.1 ∉ transcript.processedLabels

def shortestResult? : List (Label n × ℝ) → Option (Label n × ℝ)
  | [] => none
  | result :: rest =>
      some <| rest.foldl
        (fun best candidate =>
          if candidate.2 < best.2 then candidate else best)
        result

def Transcript.shortestRemaining? (transcript : Transcript n) :
    Option (Label n) :=
  (shortestResult? transcript.remainingTestResults).map Prod.fst

/-- If the last public event is a test whose revealed value is at most the
threshold reconstructed from all preceding tests, it must be processed
immediately before another test is started. -/
def Transcript.pendingImmediate? (n : ℕ)
    (transcript : Transcript n) : Option (Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) =>
      if p ≤ (transcript.countersBeforeLastTest n).threshold n
        then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- The paper's endpoint algorithm as an actual deterministic online
strategy.  After all tests, deferred jobs are selected in nondecreasing
revealed processing time. -/
def adaptiveThresholdStrategy (n : ℕ) : Strategy n :=
  fun transcript =>
    match transcript.pendingImmediate? n with
    | some job => some (.process job)
    | none =>
        let tested := transcript.testResults.length
        if h : tested < n then
          some (.test ⟨tested, h⟩)
        else
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none => none

theorem adaptiveThresholdStrategy_ne_raw
    (n : ℕ) (transcript : Transcript n) (job : Label n) :
    adaptiveThresholdStrategy n transcript ≠ some (.raw job) := by
  unfold adaptiveThresholdStrategy
  split
  · simp
  · dsimp only
    split
    · simp
    · split <;> simp

theorem adaptiveThreshold_ge_one_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    1 ≤ adaptiveThreshold y := by
  unfold adaptiveThreshold
  split_ifs with hflat
  · exact le_rfl
  · exact activeThreshold_ge_one (le_of_not_ge hflat) hy

/-- The paper's elementary invariant `D ≤ N` is preserved by one
nonnegative observation, provided a test remains. -/
theorem ThresholdCounters.observe_deferred_le_positive
    {n : ℕ} {s : ThresholdCounters} {p : ℝ}
    (hremaining : s.tested < n)
    (hpositive : 0 ≤ s.positive)
    (hbalance : s.deferred ≤ s.positive) :
    (s.observe n p).deferred ≤ (s.observe n p).positive := by
  have hx : 0 < (s.remaining n : ℝ) := by
    simp [ThresholdCounters.remaining, hremaining]
  have hR : 1 ≤ RStar := one_lt_RStar.le
  have hnum : s.deferred - RStar * s.positive ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hpositive]
  have hy : s.y n ≤ 0 := by
    unfold ThresholdCounters.y
    exact div_nonpos_of_nonpos_of_nonneg hnum hx.le
  have hthreshold := adaptiveThreshold_ge_one_of_nonpos hy
  unfold ThresholdCounters.observe
  dsimp only
  split_ifs with hpPos hdefer
  · linarith
  · have hthresholdPos : 0 < s.threshold n :=
      lt_of_lt_of_le zero_lt_one hthreshold
    exact (hdefer (hthresholdPos.trans hpPos)).elim
  · linarith
  · linarith

end

end SchedulingPaper.Online
