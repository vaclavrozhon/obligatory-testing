import SchedulingPaper.RandomizedOptionalFluid
import SchedulingPaper.RandomizedOptionalPermutationUrn
import SchedulingPaper.HiddenStoppingGlobalExchange
import SchedulingPaper.RandomizedRelabelRun
import Mathlib.Tactic

/-!
# Optional testing: operational accounting

The repository's older finite-cap model charges a blind operation the
declared cap.  The optional-information theorem instead runs a blind job for
its actual hidden processing time.  This file therefore reuses the same
legal transcript semantics but gives it the timing required by the optional
model.

It also proves the deterministic bridge needed by the fluid lower bound:
for every reachable prefix, processed tested jobs from any processing-time
class are no more numerous than tests revealing that class.  The statement
is uniform in the class predicate and is ready to be combined with the
predictable-urn concentration lemmas.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Online

noncomputable section

/-! ## Actual-processing-time timing for blind execution -/

def optionalDuration (processing : Label n → ℝ) : Observation n → ℝ
  | .testResult _ _ => 1
  | .processed job => processing job
  | .rawCompleted job => processing job

def optionalElapsed (processing : Label n → ℝ) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      optionalDuration processing observation + optionalElapsed processing rest

def optionalCompletionCostFrom
    (processing : Label n → ℝ) : ℝ → Transcript n → ℝ
  | _, [] => 0
  | time, observation :: rest =>
      let finish := time + optionalDuration processing observation
      (if (observation.completionLabel processing).isSome then finish else 0) +
        optionalCompletionCostFrom processing finish rest

def optionalCompletionCost
    (processing : Label n → ℝ) (transcript : Transcript n) : ℝ :=
  optionalCompletionCostFrom processing 0 transcript

def optionalSuffixWeightedDuration
    (processing : Label n → ℝ) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      optionalDuration processing observation *
          Online.completionCount processing (observation :: rest) +
        optionalSuffixWeightedDuration processing rest

@[simp] theorem optionalElapsed_nil (processing : Label n → ℝ) :
    optionalElapsed processing [] = 0 := rfl

@[simp] theorem optionalElapsed_cons
    (processing : Label n → ℝ) (observation : Observation n)
    (rest : Transcript n) :
    optionalElapsed processing (observation :: rest) =
      optionalDuration processing observation + optionalElapsed processing rest :=
  rfl

@[simp] theorem optionalSuffixWeightedDuration_nil
    (processing : Label n → ℝ) :
    optionalSuffixWeightedDuration processing [] = 0 := rfl

@[simp] theorem optionalSuffixWeightedDuration_cons
    (processing : Label n → ℝ) (observation : Observation n)
    (rest : Transcript n) :
    optionalSuffixWeightedDuration processing (observation :: rest) =
      optionalDuration processing observation *
          Online.completionCount processing (observation :: rest) +
        optionalSuffixWeightedDuration processing rest := rfl

/-- Optional total completion cost is the exact area under the number of
unfinished jobs, expressed as a suffix-weighted operation sum. -/
theorem optionalCompletionCostFrom_eq_count_mul_add_suffixWeighted
    (processing : Label n → ℝ) (time : ℝ) (transcript : Transcript n) :
    optionalCompletionCostFrom processing time transcript =
      Online.completionCount processing transcript * time +
        optionalSuffixWeightedDuration processing transcript := by
  induction transcript generalizing time with
  | nil => simp [optionalCompletionCostFrom]
  | cons observation rest ih =>
      simp only [optionalCompletionCostFrom, Online.completionCount_cons,
        optionalSuffixWeightedDuration_cons]
      rw [ih]
      by_cases hcompletion :
          (observation.completionLabel processing).isSome
      · simp only [if_pos hcompletion, Nat.cast_add, Nat.cast_one]
        ring
      · simp only [if_neg hcompletion, zero_add]
        ring

theorem optionalCompletionCost_eq_suffixWeightedDuration
    (processing : Label n → ℝ) (transcript : Transcript n) :
    optionalCompletionCost processing transcript =
      optionalSuffixWeightedDuration processing transcript := by
  unfold optionalCompletionCost
  rw [optionalCompletionCostFrom_eq_count_mul_add_suffixWeighted]
  ring

/-- Optional timing commutes with the existing operational relabelling. -/
@[simp] theorem optionalDuration_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    optionalDuration physicalProcessing (observation.relabel order) =
      optionalDuration (fun virtual => physicalProcessing (order virtual))
        observation := by
  cases observation <;> simp [optionalDuration, Observation.relabel]

theorem optionalCompletionCostFrom_map_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (time : ℝ)
    (transcript : Transcript n) :
    optionalCompletionCostFrom physicalProcessing time
        (transcript.map (Observation.relabel order)) =
      optionalCompletionCostFrom
        (fun virtual => physicalProcessing (order virtual)) time transcript := by
  induction transcript generalizing time with
  | nil => rfl
  | cons observation rest ih =>
      simp only [List.map_cons, optionalCompletionCostFrom,
        optionalDuration_relabel, Observation.completionLabel_relabel]
      rw [ih]
      cases hcompletion : observation.completionLabel
          (fun virtual => physicalProcessing (order virtual)) <;>
        simp [hcompletion]

theorem optionalCompletionCost_map_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (transcript : Transcript n) :
    optionalCompletionCost physicalProcessing
        (transcript.map (Observation.relabel order)) =
      optionalCompletionCost
        (fun virtual => physicalProcessing (order virtual)) transcript := by
  unfold optionalCompletionCost
  exact optionalCompletionCostFrom_map_relabel
    physicalProcessing order 0 transcript

/-- Cost of a randomly relabelled physical run equals the cost of the
virtual canonical run on the permuted processing vector. -/
theorem optionalRunCost_relabel
    (u : ℝ) (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) (fuel : ℕ) :
    optionalCompletionCost physicalProcessing
        (run (.finite u) (fixedOracle physicalProcessing)
          (strategy.relabel order) fuel).config.transcript =
      optionalCompletionCost
        (fun virtual => physicalProcessing (order virtual))
        (run (.finite u)
          (fixedOracle fun virtual => physicalProcessing (order virtual))
          strategy fuel).config.transcript := by
  rw [run_relabel_config]
  exact optionalCompletionCost_map_relabel
    physicalProcessing order _

/-- Finite-seed expected cost in the actual-processing-time blind model. -/
def expectedOptionalCompletionCost
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : ℝ) (processing : Label n → ℝ)
    (strategy : Ω → Strategy n) (fuel : ℕ) : ℝ :=
  Randomized.uniformAverage fun seed =>
    optionalCompletionCost processing
      (run (.finite u) (fixedOracle processing) (strategy seed) fuel).config.transcript

/-- A private uniform relabelling is exactly a uniform permutation of the
processing vector as seen by the fixed virtual policy. -/
theorem expectedOptionalCompletionCost_relabel
    (u : ℝ) (processing : Label n → ℝ)
    (strategy : Strategy n) (fuel : ℕ) :
    expectedOptionalCompletionCost u processing
        (fun order : Equiv.Perm (Label n) => strategy.relabel order) fuel =
      Randomized.uniformAverage (fun order : Equiv.Perm (Label n) =>
        optionalCompletionCost (fun virtual => processing (order virtual))
          (run (.finite u)
            (fixedOracle fun virtual => processing (order virtual))
            strategy fuel).config.transcript) := by
  unfold expectedOptionalCompletionCost
  apply congrArg Randomized.uniformAverage
  funext order
  exact optionalRunCost_relabel u processing order strategy fuel

/-! ## Exact operation counts and work -/

def optionalRawLabels : Transcript n → List (Label n)
  | [] => []
  | .rawCompleted job :: rest => job :: optionalRawLabels rest
  | _ :: rest => optionalRawLabels rest

def optionalZeroTestCount : Transcript n → ℕ
  | [] => 0
  | .testResult _ p :: rest =>
      (if p = 0 then 1 else 0) + optionalZeroTestCount rest
  | _ :: rest => optionalZeroTestCount rest

def optionalPositiveProcessedCount
    (processing : Label n → ℝ) : Transcript n → ℕ
  | [] => 0
  | .processed job :: rest =>
      (if processing job = 0 then 0 else 1) +
        optionalPositiveProcessedCount processing rest
  | _ :: rest => optionalPositiveProcessedCount processing rest

def optionalProcessedWork
    (processing : Label n → ℝ) (transcript : Transcript n) : ℝ :=
  (transcript.processedLabels.map processing).sum

def optionalRawWork
    (processing : Label n → ℝ) (transcript : Transcript n) : ℝ :=
  ((optionalRawLabels transcript).map processing).sum

@[simp] theorem optionalRawLabels_testResult_cons
    (job : Label n) (p : ℝ) (rest : Transcript n) :
    optionalRawLabels (.testResult job p :: rest) = optionalRawLabels rest := rfl

@[simp] theorem optionalRawLabels_processed_cons
    (job : Label n) (rest : Transcript n) :
    optionalRawLabels (.processed job :: rest) = optionalRawLabels rest := rfl

@[simp] theorem optionalRawLabels_rawCompleted_cons
    (job : Label n) (rest : Transcript n) :
    optionalRawLabels (.rawCompleted job :: rest) =
      job :: optionalRawLabels rest := rfl

/-- Structural completion-count identity.  It does not require reachability:
zero tests, positive tested processing operations, and blind completions are
exactly the three completion observations. -/
theorem completionCount_eq_optional_counts
    (processing : Label n → ℝ) (transcript : Transcript n) :
    Online.completionCount processing transcript =
      optionalZeroTestCount transcript +
        optionalPositiveProcessedCount processing transcript +
        (optionalRawLabels transcript).length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = 0 <;>
            simp [Online.completionCount, Observation.completionLabel,
              optionalZeroTestCount,
              optionalPositiveProcessedCount, hp, ih] <;> omega
      | processed job =>
          by_cases hp : processing job = 0 <;>
            simp [Online.completionCount, Observation.completionLabel,
              optionalZeroTestCount,
              optionalPositiveProcessedCount, hp, ih] <;> omega
      | rawCompleted job =>
          simp [Online.completionCount, Observation.completionLabel,
            optionalZeroTestCount,
            optionalPositiveProcessedCount, ih]
          omega

/-- Exact work decomposition in the optional model. -/
theorem optionalElapsed_eq_test_add_processed_add_raw
    (processing : Label n → ℝ) (transcript : Transcript n) :
    optionalElapsed processing transcript =
      transcript.testResults.length + optionalProcessedWork processing transcript +
        optionalRawWork processing transcript := by
  induction transcript with
  | nil => simp [optionalElapsed, optionalProcessedWork,
      optionalRawWork, optionalRawLabels, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation <;>
        simp [optionalElapsed, optionalDuration, optionalProcessedWork,
          optionalRawWork, optionalRawLabels, Transcript.processedLabels,
          ih, add_assoc, add_left_comm, add_comm]

/-! ## Reachability and classwise revelation capacity -/

/-- Every public test result in a fixed-input run carries the corresponding
fixed processing time. -/
def AllTestsMatch
    (processing : Label n → ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults → p = processing job

theorem AllTestsMatch_nil (processing : Label n → ℝ) :
    AllTestsMatch processing [] := by
  simp [AllTestsMatch]

theorem AllTestsMatch_append_test
    {processing : Label n → ℝ} {transcript : Transcript n}
    (hmatch : AllTestsMatch processing transcript) (job : Label n) :
    AllTestsMatch processing
      (transcript ++ [Observation.testResult job (processing job)]) := by
  intro other p hmem
  rw [Transcript.testResults_append_testResult] at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact hmatch other p hold
  · have hpair : (other, p) = (job, processing job) := by simpa using hnew
    have hfirst : other = job := congrArg Prod.fst hpair
    have hsecond : p = processing job := congrArg Prod.snd hpair
    subst other
    exact hsecond

/-- `AllTestsMatch` is preserved by every successful fixed-input step. -/
theorem allTestsMatch_step
    {processing : Label n → ℝ} {u : ℝ}
    {config next : Config n} {action : Action n}
    (hmatch : AllTestsMatch processing config.transcript)
    (hstep : config.step (.finite u) (fixedOracle processing) action = some next) :
    AllTestsMatch processing next.transcript := by
  cases action with
  | test job =>
      cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      simpa [fixedOracle] using AllTestsMatch_append_test hmatch job
  | process job =>
      cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      simpa [AllTestsMatch] using hmatch
  | raw job =>
      cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      simpa [AllTestsMatch] using hmatch

/-- Every fuel-truncated fixed-input run simultaneously has unique first
touches, the process-history invariant, and truthful test results.  Varying
the fuel exposes every operational prefix needed by the completion-envelope
argument. -/
theorem runFuel_optional_prefix_invariants
    (u : ℝ) (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hstarted : config.StartedHistoryInvariant)
    (hprocess : config.ProcessHistoryInvariant)
    (hmatch : AllTestsMatch processing config.transcript) :
    let final :=
      (runFuel (.finite u) (fixedOracle processing) strategy fuel config).config
    final.StartedHistoryInvariant ∧
      final.ProcessHistoryInvariant ∧
      AllTestsMatch processing final.transcript := by
  induction fuel generalizing config with
  | zero =>
      simpa [runFuel] using And.intro hstarted (And.intro hprocess hmatch)
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simp [haction, hstarted, hprocess, hmatch]
      | some action =>
          simp only [haction]
          cases hstep : config.step (.finite u) (fixedOracle processing) action with
          | none =>
              simp [hstep, hstarted, hprocess, hmatch]
          | some next =>
              simp only [hstep]
              exact ih next
                (Config.startedHistoryInvariant_step hstarted hstep)
                (Config.processHistoryInvariant_step hprocess hstarted hstep)
                (allTestsMatch_step hmatch hstep)

theorem run_optional_prefix_invariants
    (u : ℝ) (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) :
    let final :=
      (run (.finite u) (fixedOracle processing) strategy fuel).config
    final.StartedHistoryInvariant ∧
      final.ProcessHistoryInvariant ∧
      AllTestsMatch processing final.transcript := by
  unfold run
  exact runFuel_optional_prefix_invariants u processing strategy fuel
    (Config.initial n) (Config.initial_startedHistoryInvariant n)
    (Config.initial_processHistoryInvariant n) (AllTestsMatch_nil processing)

/-- Count observations whose revealed/actual processing time lies in one
Boolean class. -/
def testClassCount
    (category : ℝ → Bool) (transcript : Transcript n) : ℕ :=
  (transcript.testResults.filter fun result => category result.2).length

def processedClassCount
    (processing : Label n → ℝ) (category : ℝ → Bool)
    (transcript : Transcript n) : ℕ :=
  (transcript.processedLabels.filter fun job => category (processing job)).length

/-- Classwise revelation constraint for every reachable prefix.  A known
processed job injects into a previous matching test result of the same
class. -/
theorem processedClassCount_le_testClassCount
    {processing : Label n → ℝ} {config : Config n}
    (hprocess : config.ProcessHistoryInvariant)
    (hmatch : AllTestsMatch processing config.transcript)
    (category : ℝ → Bool) :
    processedClassCount processing category config.transcript ≤
      testClassCount category config.transcript := by
  let processed := config.transcript.processedLabels.filter fun job =>
    category (processing job)
  let tested := config.transcript.testResults.filter fun result => category result.2
  have hprocessedNodup : processed.Nodup := by
    exact hprocess.processedNodup.filter _
  have hsubset : processed.toFinset ⊆ (tested.map Prod.fst).toFinset := by
    intro job hjob
    have hprocessed : job ∈ config.transcript.processedLabels := by
      have := List.mem_filter.mp (List.mem_toFinset.mp hjob)
      exact this.1
    have hclass : category (processing job) = true := by
      have := List.mem_filter.mp (List.mem_toFinset.mp hjob)
      simpa using this.2
    have hrecorded := hprocess.processedRecorded job hprocessed
    rcases List.mem_map.mp hrecorded with ⟨result, hresult, hlabel⟩
    have hvalue : result.2 = processing job := by
      rw [← hlabel]
      exact hmatch result.1 result.2 hresult
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨result, List.mem_filter.mpr ⟨hresult, ?_⟩, hlabel⟩
    simpa [hvalue, ← hlabel] using hclass
  calc
    processedClassCount processing category config.transcript = processed.length := rfl
    _ = processed.toFinset.card := by
      rw [List.toFinset_card_of_nodup hprocessedNodup]
    _ ≤ (tested.map Prod.fst).toFinset.card := Finset.card_le_card hsubset
    _ ≤ (tested.map Prod.fst).length := List.toFinset_card_le _
    _ = testClassCount category config.transcript := by
      simp [testClassCount, tested]

/-- Normalized revelation constraint obtained by combining operational
reachability with one class-count discrepancy estimate. -/
theorem normalized_processedClass_revelation
    {n : ℕ} (hn : 0 < n)
    {processing : Label n → ℝ} {config : Config n}
    (hprocess : config.ProcessHistoryInvariant)
    (hmatch : AllTestsMatch processing config.transcript)
    (category : ℝ → Bool) {mass error : ℝ}
    (hdiscrepancy :
      (testClassCount category config.transcript : ℝ) ≤
        mass * config.transcript.testResults.length + error) :
    (processedClassCount processing category config.transcript : ℝ) / n ≤
      mass * ((config.transcript.testResults.length : ℝ) / n) + error / n := by
  have hoperational :
      (processedClassCount processing category config.transcript : ℝ) ≤
        testClassCount category config.transcript := by
    exact_mod_cast processedClassCount_le_testClassCount
      hprocess hmatch category
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  calc
    (processedClassCount processing category config.transcript : ℝ) ≤
        testClassCount category config.transcript := hoperational
    _ ≤ mass * config.transcript.testResults.length + error := hdiscrepancy
    _ = (mass * ((config.transcript.testResults.length : ℝ) / n) +
          error / n) * n := by
      field_simp [hnR.ne']

end

end RandomizedOptional
end SchedulingPaper
