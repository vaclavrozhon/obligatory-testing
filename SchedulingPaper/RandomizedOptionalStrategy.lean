import SchedulingPaper.RandomizedOptionalOperational
import SchedulingPaper.RandomizedOperationalStrategy
import Mathlib.Tactic

/-!
# Optional testing: the canonical four-block strategy

This is the literal transcript-only policy corresponding to the fluid
template.  It tests a fixed prefix of virtual labels, immediately drains
newly revealed low jobs, processes known medium jobs by SPT, runs every
untouched job blind, and finally drains the remaining tested tail by SPT.
Random relabelling turns the virtual label order into a private uniform
permutation against every fixed oblivious input.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Online

noncomputable section

def classRemainingResults
    (category : ℝ → Bool) (transcript : Transcript n) :
    List (Label n × ℝ) :=
  transcript.remainingTestResults.filter fun result => category result.2

def shortestClassPending?
    (category : ℝ → Bool) (transcript : Transcript n) : Option (Label n) :=
  (shortestResult? (classRemainingResults category transcript)).map Prod.fst

/-- The just-revealed low result has priority over every subsequent touch. -/
def lastLowPending?
    (low : ℝ → Bool) (transcript : Transcript n) : Option (Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) => if low p then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- Next virtual label in first-touch order. -/
def nextCanonicalTouch? (n : ℕ) (transcript : Transcript n) :
    Option (Label n) :=
  if h : transcript.startedLabels.length < n then
    some ⟨transcript.startedLabels.length, h⟩
  else none

/-- Literal four-block policy for an integral test quota `q`.

`low` is the selected discovery module and `medium` is the residual class
placed before the blind block.  Every tested result not in those two classes
is processed in the final SPT tail. -/
def canonicalOptionalStrategy
    (n q : ℕ) (low medium : ℝ → Bool) : Strategy n :=
  fun transcript =>
    match lastLowPending? low transcript with
    | some job => some (.process job)
    | none =>
        if transcript.testResults.length < q then
          (nextCanonicalTouch? n transcript).map Action.test
        else
          match shortestClassPending? medium transcript with
          | some job => some (.process job)
          | none =>
              match nextCanonicalTouch? n transcript with
              | some job => some (.raw job)
              | none =>
                  transcript.shortestRemaining?.map Action.process

/-- Randomized operational policy obtained by conjugating the virtual
canonical order by a private permutation. -/
def randomizedCanonicalOptionalStrategy
    (n q : ℕ) (low medium : ℝ → Bool) :
    Equiv.Perm (Label n) → Strategy n :=
  fun order => (canonicalOptionalStrategy n q low medium).relabel order

theorem canonicalOptionalStrategy_test_implies_below_quota
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction :
      canonicalOptionalStrategy n q low medium transcript = some (.test job)) :
    transcript.testResults.length < q := by
  unfold canonicalOptionalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · assumption
    · split at haction
      · simp at haction
      · cases hnext : nextCanonicalTouch? n transcript with
        | some next => simp [hnext] at haction
        | none =>
            cases htail : transcript.shortestRemaining? with
            | some tail => simp [hnext, htail] at haction
            | none => simp [hnext, htail] at haction

theorem canonicalOptionalStrategy_raw_implies_quota_reached
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction :
      canonicalOptionalStrategy n q low medium transcript = some (.raw job)) :
    q ≤ transcript.testResults.length := by
  unfold canonicalOptionalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · cases hnext : nextCanonicalTouch? n transcript <;>
        simp [hnext] at haction
    · have hquota : q ≤ transcript.testResults.length :=
        Nat.le_of_not_gt ‹¬ transcript.testResults.length < q›
      split at haction
      · simp at haction
      · cases hnext : nextCanonicalTouch? n transcript with
        | some next => exact hquota
        | none =>
            cases htail : transcript.shortestRemaining? <;>
              simp [hnext, htail] at haction

theorem canonicalOptionalStrategy_test_or_process_before_quota
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n}
    (hquota : transcript.testResults.length < q) :
    (∃ job, canonicalOptionalStrategy n q low medium transcript =
        some (.process job)) ∨
      canonicalOptionalStrategy n q low medium transcript =
        (nextCanonicalTouch? n transcript).map Action.test := by
  unfold canonicalOptionalStrategy
  split
  · exact Or.inl ⟨_, rfl⟩
  · rw [if_pos hquota]
    exact Or.inr rfl

end

end RandomizedOptional
end SchedulingPaper
