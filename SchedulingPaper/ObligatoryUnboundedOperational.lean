import SchedulingPaper.ObligatoryUnbounded
import SchedulingPaper.HiddenStoppingGlobalExchange
import SchedulingPaper.OnlineTestingInvariant
import SchedulingPaper.RandomizedOptionalObservedTrace
import Mathlib.Tactic

/-!
# Operational extraction for unbounded obligatory testing

This file connects the finite averaging theorem in `ObligatoryUnbounded`
to literal `Online.Strategy` runs.  The first layer is a purely transcript
level decomposition of an all-`H` run into processing area and test area.
-/

namespace SchedulingPaper
namespace ObligatoryUnboundedOperational

open Randomized
open Online

noncomputable section

def allHighProcessing (H : ℝ) : Online.Label n → ℝ := fun _ => H

def oneZeroProcessing (H : ℝ) (zero : Online.Label n) :
    Online.Label n → ℝ := fun job => if job = zero then 0 else H

def testLabels (transcript : Online.Transcript n) : List (Online.Label n) :=
  transcript.testResults.map Prod.fst

def processedCount : Online.Transcript n → ℕ
  | [] => 0
  | .processed _ :: rest => processedCount rest + 1
  | _ :: rest => processedCount rest

def testCount : Online.Transcript n → ℕ
  | [] => 0
  | .testResult _ _ :: rest => testCount rest + 1
  | _ :: rest => testCount rest

/-- Test-duration area when the only completion observations are process
operations: a test is charged once for every process completion in its
current suffix. -/
def testSuffixProcessArea : Online.Transcript n → ℝ
  | [] => 0
  | .testResult _ _ :: rest =>
      processedCount rest + testSuffixProcessArea rest
  | _ :: rest => testSuffixProcessArea rest

/-- Processing-duration suffix weights, without the common factor `H`. -/
def processSuffixRankArea : Online.Transcript n → ℝ
  | [] => 0
  | .processed _ :: rest =>
      (processedCount rest + 1 : ℕ) + processSuffixRankArea rest
  | _ :: rest => processSuffixRankArea rest

/-- Numbers of earlier process observations at successive tests. -/
def processedBeforeTestsAux : Online.Transcript n → ℕ → List ℕ
  | [], _ => []
  | .testResult _ _ :: rest, completed =>
      completed :: processedBeforeTestsAux rest completed
  | .processed _ :: rest, completed =>
      processedBeforeTestsAux rest (completed + 1)
  | .rawCompleted _ :: rest, completed =>
      processedBeforeTestsAux rest completed

def processedBeforeTests (transcript : Online.Transcript n) : List ℕ :=
  processedBeforeTestsAux transcript 0

def NoRaw (transcript : Online.Transcript n) : Prop :=
  ∀ job, .rawCompleted job ∉ transcript

def TestsHaveValue (H : ℝ) (transcript : Online.Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults → p = H

@[simp] theorem processedCount_eq_processedLabels_length
    (transcript : Online.Transcript n) :
    processedCount transcript = transcript.processedLabels.length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [processedCount, Online.Transcript.processedLabels, ih]

@[simp] theorem testCount_eq_testResults_length
    (transcript : Online.Transcript n) :
    testCount transcript = transcript.testResults.length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [testCount, Online.Transcript.testResults,
          Online.Observation.testResult?, ih]

@[simp] theorem processedBeforeTestsAux_length
    (transcript : Online.Transcript n) (completed : ℕ) :
    (processedBeforeTestsAux transcript completed).length =
      testCount transcript := by
  induction transcript generalizing completed with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [processedBeforeTestsAux, testCount, ih]

theorem processSuffixRankArea_eq
    (transcript : Online.Transcript n) :
    processSuffixRankArea transcript =
      (processedCount transcript : ℝ) * (processedCount transcript + 1) / 2 := by
  induction transcript with
  | nil => simp [processSuffixRankArea, processedCount]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [processSuffixRankArea, processedCount] using ih
      | rawCompleted job =>
          simpa [processSuffixRankArea, processedCount] using ih
      | processed job =>
          simp only [processSuffixRankArea, processedCount]
          rw [ih]
          push_cast
          ring

/-- Prefix and suffix process counts partition the total process count at
each test. -/
theorem testArea_add_processedBefore_sum
    (transcript : Online.Transcript n) (completed : ℕ) :
    testSuffixProcessArea transcript +
        ((processedBeforeTestsAux transcript completed).map
          (fun x => (x : ℝ))).sum =
      testCount transcript * (completed + processedCount transcript) := by
  induction transcript generalizing completed with
  | nil => simp [testSuffixProcessArea, processedBeforeTestsAux,
      testCount, processedCount]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simp only [testSuffixProcessArea, processedBeforeTestsAux,
            testCount, processedCount]
          change (processedCount rest : ℝ) + testSuffixProcessArea rest +
              ((completed : ℝ) +
                ((processedBeforeTestsAux rest completed).map
                  (fun x => (x : ℝ))).sum) = _
          calc
            _ = (processedCount rest : ℝ) + completed +
                (testSuffixProcessArea rest +
                  ((processedBeforeTestsAux rest completed).map
                    (fun x => (x : ℝ))).sum) := by ring
            _ = (processedCount rest : ℝ) + completed +
                testCount rest * (completed + processedCount rest) := by
              rw [ih completed]
            _ = (testCount rest + 1 : ℕ) *
                (completed + processedCount rest) := by
              push_cast
              ring
      | processed job =>
          simp only [testSuffixProcessArea, processedBeforeTestsAux,
            testCount, processedCount]
          rw [ih (completed + 1)]
          push_cast
          ring
      | rawCompleted job =>
          simpa [testSuffixProcessArea, processedBeforeTestsAux,
            testCount, processedCount] using ih completed

theorem completionCount_allHigh_eq_processedCount
    {H : ℝ} (hH : H ≠ 0) (transcript : Online.Transcript n)
    (hnoraw : NoRaw transcript) (htests : TestsHaveValue H transcript) :
    Online.completionCount (allHighProcessing H) transcript =
      processedCount transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hnorawRest : NoRaw rest := by
        intro job hmem
        exact hnoraw job (by simp [hmem])
      have htestsRest : TestsHaveValue H rest := by
        intro job p hmem
        apply htests job p
        cases observation with
        | testResult touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
        | processed touched => exact hmem
        | rawCompleted touched => exact hmem
      cases observation with
      | testResult job p =>
          have hp : p = H := htests job p (by simp)
          simp [Online.completionCount, Online.Observation.completionLabel,
            processedCount, hp, hH, ih hnorawRest htestsRest]
      | processed job =>
          simp [Online.completionCount, Online.Observation.completionLabel,
            allHighProcessing, processedCount, hH,
            ih hnorawRest htestsRest]
          omega
      | rawCompleted job =>
          exact (hnoraw job (by simp)).elim

/-- Exact all-`H` transcript cost decomposition. -/
theorem allHigh_completionCost_eq_areas
    {H : ℝ} (hH : H ≠ 0) (transcript : Online.Transcript n)
    (hnoraw : NoRaw transcript) (htests : TestsHaveValue H transcript) :
    Online.completionCost .infinite (allHighProcessing H) transcript =
      H * processSuffixRankArea transcript + testSuffixProcessArea transcript := by
  rw [Online.completionCost_eq_suffixWeightedDuration]
  induction transcript with
  | nil => simp [Online.suffixWeightedDuration, processSuffixRankArea,
      testSuffixProcessArea]
  | cons observation rest ih =>
      have hnorawRest : NoRaw rest := by
        intro job hmem
        exact hnoraw job (by simp [hmem])
      have htestsRest : TestsHaveValue H rest := by
        intro job p hmem
        apply htests job p
        cases observation with
        | testResult touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
        | processed touched => exact hmem
        | rawCompleted touched => exact hmem
      have ih' := ih hnorawRest htestsRest
      cases observation with
      | testResult job p =>
          rw [Online.suffixWeightedDuration_cons,
            completionCount_allHigh_eq_processedCount hH _ hnoraw htests,
            ih']
          simp [Online.Observation.duration, processSuffixRankArea,
            testSuffixProcessArea, processedCount]
          ring
      | processed job =>
          rw [Online.suffixWeightedDuration_cons,
            completionCount_allHigh_eq_processedCount hH _ hnoraw htests,
            ih']
          simp [Online.Observation.duration, allHighProcessing,
            processSuffixRankArea, testSuffixProcessArea, processedCount]
          ring
      | rawCompleted job =>
          exact (hnoraw job (by simp)).elim

end

end ObligatoryUnboundedOperational
end SchedulingPaper
