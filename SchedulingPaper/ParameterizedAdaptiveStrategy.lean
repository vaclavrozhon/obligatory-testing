import SchedulingPaper.AdaptiveThreshold
import SchedulingPaper.ParameterizedBank

/-!
# Executable parameterized AdaptiveThreshold

The finite mixed branch uses the same transcript-only algorithm as the
obligatory endpoint, but with a variable coefficient `c`.  This module gives
that algorithm its actual `Online.Strategy` term.  In particular, its state is
reconstructed solely from public test results and it never requests raw
execution.
-/

namespace SchedulingPaper.Online

noncomputable section

structure ParameterizedThresholdCounters where
  tested : ℕ
  positive : ℝ
  deferred : ℝ

def ParameterizedThresholdCounters.initial :
    ParameterizedThresholdCounters :=
  ⟨0, 0, 0⟩

def ParameterizedThresholdCounters.remaining
    (n : ℕ) (s : ParameterizedThresholdCounters) : ℕ :=
  n - s.tested

def ParameterizedThresholdCounters.y
    (n : ℕ) (c : ℝ) (s : ParameterizedThresholdCounters) : ℝ :=
  (s.deferred - (1 + c) * s.positive) / s.remaining n

def ParameterizedThresholdCounters.threshold
    (n : ℕ) (c : ℝ) (s : ParameterizedThresholdCounters) : ℝ :=
  parameterizedAdaptiveThreshold c (s.y n c)

def ParameterizedThresholdCounters.observe
    (n : ℕ) (c : ℝ) (s : ParameterizedThresholdCounters)
    (p : ℝ) : ParameterizedThresholdCounters :=
  {
    tested := s.tested + 1
    positive := s.positive + if 0 < p then 1 else 0
    deferred := s.deferred + if s.threshold n c < p then 1 else 0
  }

def parameterizedCountersFromResults (n : ℕ) (c : ℝ) :
    List (Label n × ℝ) → ParameterizedThresholdCounters :=
  List.foldl (fun state result => state.observe n c result.2)
    ParameterizedThresholdCounters.initial

def Transcript.parameterizedThresholdCounters
    (n : ℕ) (c : ℝ) (transcript : Transcript n) :
    ParameterizedThresholdCounters :=
  parameterizedCountersFromResults n c transcript.testResults

def Transcript.parameterizedCountersBeforeLastTest
    (n : ℕ) (c : ℝ) (transcript : Transcript n) :
    ParameterizedThresholdCounters :=
  parameterizedCountersFromResults n c transcript.testResults.dropLast

def Transcript.parameterizedPendingImmediate?
    (n : ℕ) (c : ℝ) (transcript : Transcript n) : Option (Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) =>
      if p ≤
          (transcript.parameterizedCountersBeforeLastTest n c).threshold n c
        then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- The paper's `AdaptiveThreshold(J,c)` as a deterministic public-transcript
strategy. -/
def parameterizedAdaptiveThresholdStrategy
    (n : ℕ) (c : ℝ) : Strategy n :=
  fun transcript =>
    match transcript.parameterizedPendingImmediate? n c with
    | some job => some (.process job)
    | none =>
        let tested := transcript.testResults.length
        if h : tested < n then
          some (.test ⟨tested, h⟩)
        else
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none => none

theorem parameterizedAdaptiveThresholdStrategy_ne_raw
    (n : ℕ) (c : ℝ) (transcript : Transcript n) (job : Label n) :
    parameterizedAdaptiveThresholdStrategy n c transcript ≠
      some (.raw job) := by
  unfold parameterizedAdaptiveThresholdStrategy
  split
  · simp
  · dsimp only
    split
    · simp
    · split <;> simp

theorem parameterizedAdaptiveThreshold_ge_one_of_nonpos
    {c y : ℝ} (hc : 0 < c) (hy : y ≤ 0) :
    1 ≤ parameterizedAdaptiveThreshold c y := by
  unfold parameterizedAdaptiveThreshold
  split_ifs with hflat
  · exact le_rfl
  · exact parameterizedThreshold_ge_one hc
      (le_of_not_ge hflat) hy

/-- The invariant `D ≤ N` is preserved by one nonnegative observation. -/
theorem ParameterizedThresholdCounters.observe_deferred_le_positive
    {n : ℕ} {c : ℝ} {s : ParameterizedThresholdCounters} {p : ℝ}
    (hc : 0 < c)
    (hremaining : s.tested < n)
    (hpositive : 0 ≤ s.positive)
    (hbalance : s.deferred ≤ s.positive) :
    (s.observe n c p).deferred ≤ (s.observe n c p).positive := by
  have hx : 0 < (s.remaining n : ℝ) := by
    simp [ParameterizedThresholdCounters.remaining, hremaining]
  have hC : 1 ≤ 1 + c := by linarith
  have hnum :
      s.deferred - (1 + c) * s.positive ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) hpositive]
  have hy : s.y n c ≤ 0 := by
    unfold ParameterizedThresholdCounters.y
    exact div_nonpos_of_nonpos_of_nonneg hnum hx.le
  have hthreshold :=
    parameterizedAdaptiveThreshold_ge_one_of_nonpos hc hy
  unfold ParameterizedThresholdCounters.observe
  dsimp only
  split_ifs with hpPos hdefer
  · linarith
  · have hthresholdPos : 0 < s.threshold n c :=
      lt_of_lt_of_le zero_lt_one hthreshold
    exact (hdefer (hthresholdPos.trans hpPos)).elim
  · linarith
  · linarith

theorem parameterizedAdaptiveThreshold_rhoStar (y : ℝ) :
    parameterizedAdaptiveThreshold rhoStar y = adaptiveThreshold y := by
  rfl

theorem ParameterizedThresholdCounters.threshold_rhoStar
    (n : ℕ) (s : ParameterizedThresholdCounters) :
    s.threshold n rhoStar =
      adaptiveThreshold
        ((s.deferred - RStar * s.positive) / s.remaining n) := by
  rfl

end

end SchedulingPaper.Online
