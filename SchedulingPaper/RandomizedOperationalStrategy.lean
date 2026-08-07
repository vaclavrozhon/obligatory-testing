import SchedulingPaper.RandomizedDensityOptimizer
import SchedulingPaper.RandomizedQuantization
import SchedulingPaper.FixedTestProcessCompletion
import Mathlib.Tactic

/-!
# The sampled obligatory-testing strategy as a transcript-only policy

This module gives the algorithm used by the `4/3` proof an operational
meaning.  The learner is computed solely from the first `k` public test
results.  A positive learned maximum-density subset determines a threshold;
thresholds above sixteen select fallback mode.  In learned mode the sampled
early jobs are drained in SPT order, later early jobs are processed
immediately, and the final deferred tail is processed in SPT order.

The termination theorem is deliberately independent of the statistical
analysis: every pending selector that chooses an unprocessed tested job fits
the common `2n+1` work-rank argument.
-/

namespace SchedulingPaper
namespace Online

open RandomizedObligatory

noncomputable section

/-- Empirical mass of one quantization category in a finite list of public
test results. -/
def resultCategoryFraction
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (b : QuantizedCategory d) : ℝ :=
  ((results.filter fun result =>
      quantizedCategory d η result.2 hη = b).length : ℝ) /
    results.length

/-- A chosen maximum-density subset of the empirical quantized histogram. -/
def resultMaximumDensitySet
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) : Finset (QuantizedCategory d) :=
  chosenMaximumDensitySubset
    (resultCategoryFraction d η hη results)
    (quantizedRepresentative d η)

theorem resultMaximumDensitySet_isMaximum
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) :
    IsMaximumDensitySubset
      (resultCategoryFraction d η hη results)
      (quantizedRepresentative d η)
      (resultMaximumDensitySet d η hη results) :=
  chosenMaximumDensitySubset_isMaximum
    (resultCategoryFraction d η hη results)
    (quantizedRepresentative d η)

/-- The learned inverse density, restricted to the learned branch
`thetaHat <= 16`.  `none` is fallback mode. -/
def learnedThresholdFromResults?
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) : Option ℝ :=
  let μ := resultCategoryFraction d η hη results
  let q := quantizedRepresentative d η
  let selected := resultMaximumDensitySet d η hη results
  let a := subsetMass μ selected
  let m := subsetMoment μ q selected
  if _ha : 0 < a then
    let θ := (1 + m) / a
    if θ ≤ 16 then some θ else none
  else none

theorem resultCategoryFraction_nonneg
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (b : QuantizedCategory d) :
    0 ≤ resultCategoryFraction d η hη results b := by
  unfold resultCategoryFraction
  positivity

theorem learnedThresholdFromResults_some
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) {θ : ℝ}
    (hlearn : learnedThresholdFromResults? d η hη results = some θ) :
    let μ := resultCategoryFraction d η hη results
    let q := quantizedRepresentative d η
    let selected := resultMaximumDensitySet d η hη results
    0 < subsetMass μ selected ∧
      θ = (1 + subsetMoment μ q selected) / subsetMass μ selected ∧
      θ ≤ 16 := by
  unfold learnedThresholdFromResults? at hlearn
  dsimp only at hlearn ⊢
  split at hlearn
  next ha =>
    split at hlearn
    next hθ =>
      simp only [Option.some.injEq] at hlearn
      subst θ
      exact ⟨ha, rfl, hθ⟩
    next => simp at hlearn
  next => simp at hlearn

/-- Every successful learned branch automatically supplies all sample-side
hypotheses of the good-learned certificate: nonnegative threshold, cutoff,
mass lower bound, and the density identity for the complete threshold
closure. -/
theorem learnedThresholdFromResults_closure_certificate
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) {θ : ℝ}
    (hlearn : learnedThresholdFromResults? d η hη results = some θ) :
    let μ := resultCategoryFraction d η hη results
    let q := quantizedRepresentative d η
    0 ≤ θ ∧ θ ≤ 16 ∧
      1 / 16 ≤ selectedMass μ (thresholdClosure q θ) ∧
      1 + selectedMoment μ q (thresholdClosure q θ) =
        selectedMass μ (thresholdClosure q θ) * θ := by
  dsimp only
  let μ := resultCategoryFraction d η hη results
  let q := quantizedRepresentative d η
  let selected := resultMaximumDensitySet d η hη results
  obtain ⟨ha, hθeq, hθ16⟩ :=
    learnedThresholdFromResults_some d η hη results hlearn
  have hμ : ∀ b, 0 ≤ μ b := by
    intro b
    exact resultCategoryFraction_nonneg d η hη results b
  have hq : ∀ b, 0 ≤ q b := by
    intro b
    exact quantizedRepresentative_nonneg d hη.le b
  have hmax : IsMaximumDensitySubset μ q selected := by
    exact resultMaximumDensitySet_isMaximum d η hη results
  have hdensitySelected :
      1 + subsetMoment μ q selected = subsetMass μ selected * θ := by
    rw [hθeq]
    exact inverseDensity_identity ha
  have hθpos : 0 < θ := by
    rw [hθeq]
    exact inverseDensity_pos hμ hq ha
  have hdensityClosure :
      1 + selectedMoment μ q (thresholdClosure q θ) =
        θ * selectedMass μ (thresholdClosure q θ) :=
    maximumDensity_thresholdClosure_preserves hμ hq hmax ha
      hdensitySelected
  have hmClosure :
      0 ≤ selectedMoment μ q (thresholdClosure q θ) := by
    unfold selectedMoment
    exact Finset.sum_nonneg fun b _ => by
      exact mul_nonneg (mul_nonneg (hμ b) (hq b)) (by positivity)
  have haClosure :
      1 / 16 ≤ selectedMass μ (thresholdClosure q θ) := by
    apply inverseDensity_le_sixteen_mass_lower hmClosure hθpos.le hθ16
    nlinarith [hdensityClosure]
  exact ⟨hθpos.le, hθ16, haClosure, by nlinarith [hdensityClosure]⟩

/-- Complete threshold closure, so even a category absent from the sample is
classified canonically. -/
def learnedClassifiesEarly
    {n : ℕ} (d : ℕ) (η : ℝ) (hη : 0 < η)
    (results : List (Label n × ℝ)) (p : ℝ) : Bool :=
  match learnedThresholdFromResults? d η hη results with
  | none => false
  | some θ => decide <|
      thresholdClosure (quantizedRepresentative d η) θ
        (quantizedCategory d η p hη)

/-- Remaining positive sampled jobs classified early by the learned
threshold.  They are drained before testing resumes. -/
def Transcript.learnedSampleRemainingResults
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : List (Label n × ℝ) :=
  let sample := transcript.testResults.take k
  transcript.remainingTestResults.filter fun result =>
    result.1.val < k && decide (0 < result.2) &&
      learnedClassifiesEarly d η hη sample result.2

/-- SPT selector for the learned early part of the sample. -/
def Transcript.learnedSamplePending?
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : Option (Label n) :=
  (shortestResult? <|
    transcript.learnedSampleRemainingResults n k d η hη).map Prod.fst

/-- Pending processing action of the sampled algorithm.

After the sample is complete, sampled early jobs have priority.  Once that
batch is empty, a newly tested nonsample job is processed immediately iff it
belongs to the same threshold closure. -/
def Transcript.sampledObligatoryPending?
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (transcript : Transcript n) : Option (Label n) :=
  let tested := transcript.testResults.length
  if tested < k then none
  else
    match transcript.learnedSamplePending? n k d η hη with
    | some job => some job
    | none =>
        match transcript.getLast? with
        | some (.testResult job p) =>
            if k < tested &&
                learnedClassifiesEarly d η hη
                  (transcript.testResults.take k) p
              then some job else none
        | some (.processed _) | some (.rawCompleted _) | none => none

/-- The literal deterministic policy for one fixed label order.  A random
permutation seed is equivalently applied by relabelling the instance/order.
-/
def sampledObligatoryStrategy
    (n k d : ℕ) (η : ℝ) (hη : 0 < η) : Strategy n :=
  testProcessStrategy fun transcript =>
    transcript.sampledObligatoryPending? n k d η hη

/-- Relabel one public observation. -/
def Observation.relabel (order : Equiv.Perm (Label n)) :
    Observation n → Observation n
  | .testResult job p => .testResult (order job) p
  | .processed job => .processed (order job)
  | .rawCompleted job => .rawCompleted (order job)

/-- Relabel one requested operation. -/
def Action.relabel (order : Equiv.Perm (Label n)) : Action n → Action n
  | .test job => .test (order job)
  | .process job => .process (order job)
  | .raw job => .raw (order job)

/-- Conjugate a transcript-only strategy by a label permutation.  The
strategy sees virtual labels in canonical order while its actions address
the corresponding physical labels. -/
def Strategy.relabel
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) : Strategy n :=
  fun transcript =>
    (strategy <| transcript.map (Observation.relabel order.symm)).map
      (Action.relabel order)

/-- The finite random-seed family used against an oblivious fixed input. -/
def randomizedSampledObligatoryStrategy
    (n k d : ℕ) (η : ℝ) (hη : 0 < η) :
    Equiv.Perm (Label n) → Strategy n :=
  fun order => (sampledObligatoryStrategy n k d η hη).relabel order

/-- A selector suitable for a test/process policy may choose any test result
that has not yet received its administrative processing action. -/
def SelectsRemainingTest
    (pending : Transcript n → Option (Label n)) : Prop :=
  ∀ transcript job, pending transcript = some job →
    (∃ p, (job, p) ∈ transcript.testResults ∧
      job ∉ transcript.processedLabels) ∨
    ∃ p, transcript.getLast? = some (.testResult job p)

theorem Config.TestProcessInvariant.tested_of_selectsRemaining
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending)
    {config : Config n} (hgood : config.TestProcessInvariant)
    {job : Label n} (hselected : pending config.transcript = some job) :
    ∃ p, config.jobs job = .tested p := by
  rcases hpending config.transcript job hselected with
    ⟨p, hresult, hnotProcessed⟩ | ⟨p, hlast⟩
  · exact ⟨p, (hgood.tested_iff job p).2 ⟨hresult, hnotProcessed⟩⟩
  · exact ⟨p, hgood.lastTest job p hlast⟩

theorem testProcessStrategy_stop_of_zero_of_selectsRemaining
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending)
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hzero : config.remainingWork = 0) :
    testProcessStrategy pending config.transcript = none := by
  have hdone : ∀ job, config.jobs job = .done :=
    (Config.remainingWork_eq_zero_iff config).mp hzero
  unfold testProcessStrategy
  cases hp : pending config.transcript with
  | some job =>
      obtain ⟨p, htested⟩ := hgood.tested_of_selectsRemaining hpending hp
      rw [hdone job] at htested
      contradiction
  | none =>
      simp only
      split
      next hlt =>
        let job : Label n := ⟨config.transcript.testResults.length, hlt⟩
        have huntouched : config.jobs job = .untouched :=
          hgood.labelAtTestCount_untouched rfl
        rw [hdone job] at huntouched
        contradiction
      next _ =>
        split
        next job hshort =>
          obtain ⟨p, htested⟩ := hgood.shortestRemaining_tested hshort
          rw [hdone job] at htested
          contradiction
        next => rfl

theorem testProcessStrategy_progress_of_selectsRemaining
    (cap : Cap) (oracle : Oracle n)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending)
    {config : Config n} (hgood : config.TestProcessInvariant)
    (hpos : 0 < config.remainingWork) :
    WorkStep cap oracle (testProcessStrategy pending)
      Config.TestProcessInvariant config := by
  unfold WorkStep testProcessStrategy
  cases hp : pending config.transcript with
  | some job =>
      obtain ⟨p, hjob⟩ := hgood.tested_of_selectsRemaining hpending hp
      let next : Config n := {
        jobs := Function.update config.jobs job .done
        transcript := config.transcript ++ [.processed job]
      }
      refine ⟨.process job, next, by simp, ?_, ?_, ?_⟩
      · simp [Config.step, hjob, next]
      · exact hgood.afterProcess job p hjob
      · exact remainingWork_update_process config.jobs job p hjob
  | none =>
      simp only
      split
      next hlt =>
        let job : Label n := ⟨config.transcript.testResults.length, hlt⟩
        let p := oracle config.transcript job
        have hjob : config.jobs job = .untouched :=
          hgood.labelAtTestCount_untouched rfl
        let next : Config n := {
          jobs := Function.update config.jobs job (.tested p)
          transcript := config.transcript ++ [.testResult job p]
        }
        refine ⟨.test job, next, rfl, ?_, ?_, ?_⟩
        · simp [Config.step, hjob, next, p]
        · exact hgood.afterTest job rfl p
        · exact remainingWork_update_test config.jobs job p hjob
      next hnotlt =>
        have hall : config.transcript.testResults.length = n := by
          have hbound := hgood.testBound
          omega
        split
        next job hshort =>
          obtain ⟨p, hjob⟩ := hgood.shortestRemaining_tested hshort
          let next : Config n := {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.processed job]
          }
          refine ⟨.process job, next, rfl, ?_, ?_, ?_⟩
          · simp [Config.step, hjob, next]
          · exact hgood.afterProcess job p hjob
          · exact remainingWork_update_process config.jobs job p hjob
        next hnone =>
          have hdone :=
            hgood.done_of_allTests_of_noRemaining hall hnone
          have hworkZero :=
            (Config.remainingWork_eq_zero_iff config).mpr hdone
          omega

theorem runFuel_testProcessStrategy_completed_of_selectsRemaining
    (cap : Cap) (oracle : Oracle n)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending) (extra : ℕ) :
    let result :=
      runFuel cap oracle (testProcessStrategy pending)
        (2 * n + 1 + extra) (Config.initial n)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  have hrun :=
    runFuel_completedNormally_of_workRank cap oracle
      (testProcessStrategy pending) Config.TestProcessInvariant
      (fun _ hgood hzero =>
        testProcessStrategy_stop_of_zero_of_selectsRemaining hpending hgood hzero)
      (fun _ hgood hpos =>
        testProcessStrategy_progress_of_selectsRemaining
          cap oracle hpending hgood hpos)
      (Config.initial n) (Config.initial_testProcessInvariant n) extra
  rw [Config.initial_remainingWork] at hrun
  exact ⟨hrun.1, hrun.2.2⟩

/-- The same work-rank run while retaining the fixed-input test and
completion-label invariants.  Unlike the older immediate-processing lemma,
the pending selector may drain any previously tested, still-unprocessed job;
this is needed for the sampled batch. -/
theorem runFuel_testProcessStrategy_completed_with_completionInvariant_of_selectsRemaining
    (cap : Cap) (processingTime : Label n → ℝ)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsRemainingTest pending) (extra : ℕ) :
    let result :=
      runFuel cap (fixedOracle processingTime)
        (testProcessStrategy pending)
        (2 * n + 1 + extra) (Config.initial n)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      result.config.transcript.TestsMatch processingTime ∧
      result.config.FixedCompletionInvariant processingTime ∧
      ∀ job, result.config.jobs job = .done := by
  let Good : Config n → Prop :=
    fun config =>
      config.TestProcessInvariant ∧
        config.transcript.TestsMatch processingTime ∧
        config.FixedCompletionInvariant processingTime
  have hstop :
      ∀ config, Good config → config.remainingWork = 0 →
        testProcessStrategy pending config.transcript = none := by
    intro config hgood hzero
    exact testProcessStrategy_stop_of_zero_of_selectsRemaining
      hpending hgood.1 hzero
  have hprogress :
      ∀ config, Good config → 0 < config.remainingWork →
        WorkStep cap (fixedOracle processingTime)
          (testProcessStrategy pending) Good config := by
    intro config hgood hpos
    obtain ⟨action, next, haction, hstep, hnext, hwork⟩ :=
      testProcessStrategy_progress_of_selectsRemaining
        cap (fixedOracle processingTime) hpending hgood.1 hpos
    refine
      ⟨action, next, haction, hstep,
        ⟨hnext,
          Config.step_preserves_testsMatch cap processingTime
            hgood.2.1 hstep,
          Config.fixedCompletionInvariant_step
            cap processingTime hgood.1 hgood.2.1 hgood.2.2 hstep⟩,
        hwork⟩
  have hrun :=
    runFuel_completedNormally_of_workRank cap
      (fixedOracle processingTime) (testProcessStrategy pending)
      Good hstop hprogress (Config.initial n)
      ⟨Config.initial_testProcessInvariant n,
        Transcript.testsMatch_nil processingTime,
        Config.initial_fixedCompletionInvariant processingTime⟩ extra
  rw [Config.initial_remainingWork] at hrun
  exact
    ⟨hrun.1, hrun.2.1.1, hrun.2.1.2.1,
      hrun.2.1.2.2, hrun.2.2⟩

theorem learnedSamplePending_selectsRemaining
    (n k d : ℕ) (η : ℝ) (hη : 0 < η) :
    SelectsRemainingTest fun transcript =>
      transcript.learnedSamplePending? n k d η hη := by
  intro transcript job hpending
  unfold Transcript.learnedSamplePending? at hpending
  cases hshort : shortestResult?
      (transcript.learnedSampleRemainingResults n k d η hη) with
  | none => simp [hshort] at hpending
  | some result =>
      have hjob : result.1 = job := by simpa [hshort] using hpending
      have hmem := shortestResult?_mem hshort
      unfold Transcript.learnedSampleRemainingResults at hmem
      simp only at hmem
      have hfiltered := List.mem_filter.mp hmem
      unfold Transcript.remainingTestResults at hfiltered
      have hremaining := List.mem_filter.mp hfiltered.1
      subst job
      left
      refine ⟨result.2, hremaining.1, ?_⟩
      simpa using hremaining.2

theorem sampledObligatoryPending_selectsRemaining
    (n k d : ℕ) (η : ℝ) (hη : 0 < η) :
    SelectsRemainingTest fun transcript =>
      transcript.sampledObligatoryPending? n k d η hη := by
  intro transcript job hpending
  by_cases hsample : transcript.testResults.length < k
  · simp [Transcript.sampledObligatoryPending?, hsample] at hpending
  · cases hselected : transcript.learnedSamplePending? n k d η hη with
    | some selectedJob =>
      have hremaining := learnedSamplePending_selectsRemaining n k d η hη
        transcript selectedJob hselected
      simp [Transcript.sampledObligatoryPending?, hsample, hselected] at hpending
      subst job
      exact hremaining
    | none =>
      cases hlast : transcript.getLast? with
      | none =>
          simp [Transcript.sampledObligatoryPending?, hsample,
            hselected, hlast] at hpending
      | some observation =>
          cases observation with
          | processed processedJob =>
              simp [Transcript.sampledObligatoryPending?, hsample,
                hselected, hlast] at hpending
          | rawCompleted rawJob =>
              simp [Transcript.sampledObligatoryPending?, hsample,
                hselected, hlast] at hpending
          | testResult testedJob p =>
              by_cases htake : k < transcript.testResults.length &&
                  learnedClassifiesEarly d η hη
                    (transcript.testResults.take k) p
              · simp [Transcript.sampledObligatoryPending?, hsample,
                    hselected, hlast, htake] at hpending
                subst job
                exact Or.inr ⟨p, rfl⟩
              · simp [Transcript.sampledObligatoryPending?, hsample,
                  hselected, hlast, htake] at hpending

/-- The sampled strategy is a legal terminating obligatory-testing policy.
It uses exactly the public transcript and stops normally with every job done
within the universal `2n+1` fuel bound. -/
theorem run_sampledObligatoryStrategy_completed
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (oracle : Oracle n) :
    let result := run .infinite oracle
      (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
    result.reason = .strategyStopped ∧
      ∀ job, result.config.jobs job = .done := by
  unfold run sampledObligatoryStrategy
  simpa using
    runFuel_testProcessStrategy_completed_of_selectsRemaining
      (.infinite) oracle
      (sampledObligatoryPending_selectsRemaining n k d η hη) 0

/-- On every fixed input, the completed sampled run records each job's
completion exactly once.  In particular its operational completion cost may
be rewritten by the generic suffix/pair accounting theorems. -/
theorem run_sampledObligatoryStrategy_completionLabels_perm
    (n k d : ℕ) (η : ℝ) (hη : 0 < η)
    (processingTime : Label n → ℝ) :
    let result := run .infinite (fixedOracle processingTime)
      (sampledObligatoryStrategy n k d η hη) (2 * n + 1)
    (result.config.transcript.completionLabels processingTime).Perm
      (List.ofFn id) := by
  unfold run sampledObligatoryStrategy
  have hrun :=
    runFuel_testProcessStrategy_completed_with_completionInvariant_of_selectsRemaining
      (.infinite) processingTime
      (sampledObligatoryPending_selectsRemaining n k d η hη) 0
  let result :=
    runFuel (.infinite) (fixedOracle processingTime)
      (testProcessStrategy fun transcript =>
        transcript.sampledObligatoryPending? n k d η hη)
      (2 * n + 1) (Config.initial n)
  have hnodup :
      (result.config.transcript.completionLabels processingTime).Nodup :=
    hrun.2.2.2.1.nodup
  have hmem :
      ∀ job,
        job ∈ result.config.transcript.completionLabels processingTime := by
    intro job
    rw [hrun.2.2.2.1.mem_iff]
    simp [hrun.2.2.2.2 job, JobState.completionRecorded]
  apply
    (List.perm_ext_iff_of_nodup hnodup
      (List.nodup_ofFn.mpr Function.injective_id)).mpr
  intro job
  simp [hmem job]

end

end Online
end SchedulingPaper
