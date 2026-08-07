import SchedulingPaper.RandomizedOptionalOnline
import SchedulingPaper.AdaptiveThreshold
import Mathlib.Tactic

/-!
# Optional testing: four-block policy in the observed-blind model

This is the canonical transcript-only policy in the information model where a
completed blind job publishes its elapsed processing time.  The policy does
not use that extra value, but arbitrary comparison policies in the lower bound
may use it.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section

def shortestResult? : List (Label n × ℝ) → Option (Label n × ℝ)
  | [] => none
  | result :: rest =>
      some <| rest.foldl
        (fun best candidate =>
          if candidate.2 < best.2 then candidate else best)
        result

def Transcript.remainingTestResults (transcript : Transcript n) :
    List (Label n × ℝ) :=
  transcript.testResults.filter fun result =>
    result.1 ∉ transcript.processedLabels

def classRemainingResults
    (category : ℝ → Bool) (transcript : Transcript n) :
    List (Label n × ℝ) :=
  transcript.remainingTestResults.filter fun result => category result.2

def shortestClassPending?
    (category : ℝ → Bool) (transcript : Transcript n) : Option (Label n) :=
  (shortestResult? (classRemainingResults category transcript)).map Prod.fst

def lastLowPending?
    (low : ℝ → Bool) (transcript : Transcript n) : Option (Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) => if low p then some job else none
  | some (.processed _) | some (.blindCompleted _ _) | none => none

def nextCanonicalTouch? (n : ℕ) (transcript : Transcript n) :
    Option (Label n) :=
  if h : transcript.startedLabels.length < n then
    some ⟨transcript.startedLabels.length, h⟩
  else none

def canonicalStrategy
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
              | some job => some (.blind job)
              | none =>
                  (shortestResult? transcript.remainingTestResults).map
                    (Action.process ∘ Prod.fst)

def randomizedCanonicalStrategy
    (n q : ℕ) (low medium : ℝ → Bool) :
    Equiv.Perm (Label n) → Strategy n :=
  fun order => (canonicalStrategy n q low medium).relabel order

theorem canonicalStrategy_test_implies_below_quota
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.test job)) :
    transcript.testResults.length < q := by
  unfold canonicalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · assumption
    · split at haction
      · simp at haction
      · cases hnext : nextCanonicalTouch? n transcript with
        | some next => simp [hnext] at haction
        | none =>
            cases htail : shortestResult? transcript.remainingTestResults <;>
              simp [hnext, htail] at haction

theorem canonicalStrategy_blind_implies_quota_reached
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.blind job)) :
    q ≤ transcript.testResults.length := by
  unfold canonicalStrategy at haction
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
            cases htail : shortestResult? transcript.remainingTestResults <;>
              simp [hnext, htail] at haction

theorem canonicalStrategy_processes_last_low
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (hlow : lastLowPending? low transcript = some job) :
    canonicalStrategy n q low medium transcript = some (.process job) := by
  simp [canonicalStrategy, hlow]

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
