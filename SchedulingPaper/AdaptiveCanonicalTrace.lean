import SchedulingPaper.FixedTestProcessCompletion
import SchedulingPaper.ObligatorySymbolicEndpoint

/-!
# Canonical trace shape of AdaptiveThreshold

This module follows the concrete parameterized strategy through its two
operational phases.  During the first phase labels are tested in order and a
nondeferred result is processed immediately.  During the second phase the
deferred labels are processed by the strategy's shortest-remaining selector.

The main invariant is stated as a decomposition of the public transcript.
It is designed to expose the two-label projections used by the generic
completion-pair decomposition.
-/

namespace SchedulingPaper.Online

noncomputable section

open SchedulingPaper

structure AdaptiveRuntimeJob (n : ℕ) where
  label : Label n
  processing : ℝ
  threshold : ℝ
  symbol : ObligatoryRuntimeClass

def classifyAdaptive
    (threshold processing : ℝ) : ObligatoryRuntimeClass :=
  if processing = 0 then .zero
  else if processing ≤ threshold then .immediate else .deferred

def buildAdaptiveJobs :
    AnalysisState → List (Label n × ℝ) → List (AdaptiveRuntimeJob n)
  | _, [] => []
  | s, result :: results =>
      let symbol := classifyAdaptive s.threshold result.2
      {
        label := result.1
        processing := result.2
        threshold := s.threshold
        symbol := symbol
      } :: buildAdaptiveJobs (s.step symbol.outcome) results

@[simp] theorem buildAdaptiveJobs_length
    (s : AnalysisState) (results : List (Label n × ℝ)) :
    (buildAdaptiveJobs s results).length = results.length := by
  induction results generalizing s with
  | nil => rfl
  | cons result results ih =>
      simp [buildAdaptiveJobs, ih]

def fixedTestResults (processingTime : Label n → ℝ) :
    List (Label n × ℝ) :=
  List.ofFn fun job => (job, processingTime job)

@[simp] theorem fixedTestResults_length
    (processingTime : Label n → ℝ) :
    (fixedTestResults processingTime).length = n := by
  simp [fixedTestResults]

@[simp] theorem fixedTestResults_get
    (processingTime : Label n → ℝ) (job : Label n) :
    (fixedTestResults processingTime).get
        ⟨job.1, by simpa using job.2⟩ =
      (job, processingTime job) := by
  simp [fixedTestResults]

def adaptiveRuntimeJobs (processingTime : Label n → ℝ) :
    List (AdaptiveRuntimeJob n) :=
  buildAdaptiveJobs (initialAnalysisState n)
    (fixedTestResults processingTime)

@[simp] theorem adaptiveRuntimeJobs_length
    (processingTime : Label n → ℝ) :
    (adaptiveRuntimeJobs processingTime).length = n := by
  simp [adaptiveRuntimeJobs]

def AdaptiveRuntimeJob.block
    (job : AdaptiveRuntimeJob n) : Transcript n :=
  [.testResult job.label job.processing] ++
    if job.symbol = .deferred then []
    else [.processed job.label]

def adaptiveTestPhasePrefix
    (jobs : List (AdaptiveRuntimeJob n)) (k : ℕ) : Transcript n :=
  (jobs.take k).flatMap AdaptiveRuntimeJob.block

def adaptiveTestPhase
    (jobs : List (AdaptiveRuntimeJob n)) : Transcript n :=
  jobs.flatMap AdaptiveRuntimeJob.block

theorem adaptiveTestPhasePrefix_length
    (jobs : List (AdaptiveRuntimeJob n)) :
    adaptiveTestPhasePrefix jobs jobs.length =
      adaptiveTestPhase jobs := by
  simp [adaptiveTestPhasePrefix, adaptiveTestPhase]

theorem adaptiveTestPhasePrefix_succ
    (jobs : List (AdaptiveRuntimeJob n))
    {k : ℕ} (hk : k < jobs.length) :
    adaptiveTestPhasePrefix jobs (k + 1) =
      adaptiveTestPhasePrefix jobs k ++ (jobs.get ⟨k, hk⟩).block := by
  unfold adaptiveTestPhasePrefix
  have htake :
      jobs.take (k + 1) = jobs.take k ++ [jobs[k]] :=
    List.take_succ_eq_append_getElem hk
  rw [htake, List.flatMap_append]
  simp

@[simp] theorem AdaptiveRuntimeJob.block_testResults
    (job : AdaptiveRuntimeJob n) :
    job.block.testResults = [(job.label, job.processing)] := by
  simp [AdaptiveRuntimeJob.block]
  split_ifs <;> simp

@[simp] theorem AdaptiveRuntimeJob.block_processedLabels
    (job : AdaptiveRuntimeJob n) :
    job.block.processedLabels =
      if job.symbol = .deferred then [] else [job.label] := by
  simp [AdaptiveRuntimeJob.block, Transcript.processedLabels]
  split_ifs <;> simp_all

@[simp] theorem adaptiveTestPhasePrefix_testResults
    (jobs : List (AdaptiveRuntimeJob n)) (k : ℕ) :
    (adaptiveTestPhasePrefix jobs k).testResults =
      (jobs.take k).map fun job => (job.label, job.processing) := by
  unfold adaptiveTestPhasePrefix
  induction jobs.take k with
  | nil => rfl
  | cons job rest ih =>
      simp [ih]

@[simp] theorem adaptiveTestPhase_testResults
    (jobs : List (AdaptiveRuntimeJob n)) :
    (adaptiveTestPhase jobs).testResults =
      jobs.map fun job => (job.label, job.processing) := by
  unfold adaptiveTestPhase
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      simp [ih]

@[simp] theorem adaptiveTestPhasePrefix_processedLabels
    (jobs : List (AdaptiveRuntimeJob n)) (k : ℕ) :
    (adaptiveTestPhasePrefix jobs k).processedLabels =
      (jobs.take k).filterMap fun job =>
        if job.symbol = .deferred then none else some job.label := by
  unfold adaptiveTestPhasePrefix
  induction jobs.take k with
  | nil => rfl
  | cons job rest ih =>
      simp only [List.flatMap_cons]
      rw [show
        Transcript.processedLabels
            (job.block ++ List.flatMap AdaptiveRuntimeJob.block rest) =
          job.block.processedLabels ++
            Transcript.processedLabels
              (List.flatMap AdaptiveRuntimeJob.block rest) by
              simp [Transcript.processedLabels, List.filterMap_append],
        ih]
      by_cases hsymbol : job.symbol = .deferred <;>
        simp [AdaptiveRuntimeJob.block_processedLabels, hsymbol]

@[simp] theorem adaptiveTestPhase_processedLabels
    (jobs : List (AdaptiveRuntimeJob n)) :
    (adaptiveTestPhase jobs).processedLabels =
      jobs.filterMap fun job =>
        if job.symbol = .deferred then none else some job.label := by
  unfold adaptiveTestPhase
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      simp only [List.flatMap_cons]
      rw [show
        Transcript.processedLabels
            (job.block ++ List.flatMap AdaptiveRuntimeJob.block jobs) =
          job.block.processedLabels ++
            Transcript.processedLabels
              (List.flatMap AdaptiveRuntimeJob.block jobs) by
              simp [Transcript.processedLabels, List.filterMap_append],
        ih]
      by_cases hsymbol : job.symbol = .deferred <;>
        simp [AdaptiveRuntimeJob.block_processedLabels, hsymbol]

end

end SchedulingPaper.Online
