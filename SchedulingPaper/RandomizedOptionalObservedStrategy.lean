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

theorem canonicalStrategy_test_implies_nextTouch
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.test job)) :
    nextCanonicalTouch? n transcript = some job := by
  unfold canonicalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · cases hnext : nextCanonicalTouch? n transcript <;>
        simp [hnext] at haction ⊢
      exact haction
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

theorem canonicalStrategy_blind_implies_nextTouch
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.blind job)) :
    nextCanonicalTouch? n transcript = some job := by
  unfold canonicalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · cases hnext : nextCanonicalTouch? n transcript <;>
        simp [hnext] at haction
    · split at haction
      · simp at haction
      · cases hnext : nextCanonicalTouch? n transcript with
        | some next =>
            simp [hnext] at haction
            exact congrArg some haction
        | none =>
            cases htail : shortestResult? transcript.remainingTestResults <;>
              simp [hnext, htail] at haction

theorem canonicalStrategy_processes_last_low
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (hlow : lastLowPending? low transcript = some job) :
    canonicalStrategy n q low medium transcript = some (.process job) := by
  simp [canonicalStrategy, hlow]

/-- A blind execution starts only after the known medium stock has been
drained.  This is the operational separation between the medium and YOLO
blocks. -/
theorem canonicalStrategy_blind_implies_no_medium
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.blind job)) :
    shortestClassPending? medium transcript = none := by
  unfold canonicalStrategy at haction
  split at haction
  · simp at haction
  · split at haction
    · cases hnext : nextCanonicalTouch? n transcript <;>
        simp [hnext] at haction
    · split at haction
      · simp at haction
      · assumption

/-- Every processing action belongs to exactly one of the three processing
branches of the four-block strategy: immediate low, known medium, or final
SPT tail. -/
theorem canonicalStrategy_process_cases
    {n q : ℕ} {low medium : ℝ → Bool}
    {transcript : Transcript n} {job : Label n}
    (haction : canonicalStrategy n q low medium transcript =
      some (.process job)) :
    lastLowPending? low transcript = some job ∨
      (lastLowPending? low transcript = none ∧
        q ≤ transcript.testResults.length ∧
        shortestClassPending? medium transcript = some job) ∨
      (lastLowPending? low transcript = none ∧
        q ≤ transcript.testResults.length ∧
        shortestClassPending? medium transcript = none ∧
        nextCanonicalTouch? n transcript = none ∧
        ∃ value, shortestResult? transcript.remainingTestResults =
          some (job, value)) := by
  unfold canonicalStrategy at haction
  cases hlow : lastLowPending? low transcript with
  | some lowJob =>
      simp only [hlow] at haction
      have hjob : lowJob = job := Action.process.inj
        (Option.some.inj haction)
      subst lowJob
      exact Or.inl rfl
  | none =>
      simp only [hlow] at haction
      by_cases htest : transcript.testResults.length < q
      · simp [htest] at haction
      · have hreached : q ≤ transcript.testResults.length :=
          Nat.le_of_not_gt htest
        simp only [if_neg htest] at haction
        cases hmedium : shortestClassPending? medium transcript with
        | some mediumJob =>
            simp only [hmedium] at haction
            have hjob : mediumJob = job := Action.process.inj
              (Option.some.inj haction)
            subst mediumJob
            exact Or.inr (Or.inl ⟨rfl, hreached, rfl⟩)
        | none =>
            simp only [hmedium] at haction
            cases hnext : nextCanonicalTouch? n transcript with
            | some next => simp [hnext] at haction
            | none =>
                simp only [hnext] at haction
                cases htail : shortestResult?
                    transcript.remainingTestResults with
                | none => simp [htail] at haction
                | some result =>
                    simp only [htail, Option.map_some,
                      Option.some.injEq, Action.process.injEq] at haction
                    rcases result with ⟨tailJob, value⟩
                    have hjob : tailJob = job :=
                      Action.process.inj haction
                    subst tailJob
                    refine Or.inr (Or.inr
                      ⟨rfl, hreached, rfl, rfl, ?_⟩)
                    exact ⟨value, rfl⟩

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
