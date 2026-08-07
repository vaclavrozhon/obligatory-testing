import SchedulingPaper.RandomizedOptionalOperational
import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Optional testing: operational model with observed blind durations

Unlike the older finite-cap oracle model, a blind execution here lasts its
actual processing time and that elapsed duration is observable when the job
finishes.  This is the information model used by the announced-urn proof:
both a test and a blind first touch reveal the touched value to subsequent
decisions, although only a test leaves a pending known job.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section

abbrev Label (n : ℕ) := Fin n

inductive JobState where
  | untouched
  | tested (processingTime : ℝ)
  | done
  deriving DecidableEq

inductive Action (n : ℕ) where
  | test (job : Label n)
  | process (job : Label n)
  | blind (job : Label n)
  deriving DecidableEq

inductive Observation (n : ℕ) where
  | testResult (job : Label n) (processingTime : ℝ)
  | processed (job : Label n)
  | blindCompleted (job : Label n) (processingTime : ℝ)
  deriving DecidableEq

abbrev Transcript (n : ℕ) := List (Observation n)
abbrev Strategy (n : ℕ) := Transcript n → Option (Action n)

structure Config (n : ℕ) where
  jobs : Label n → JobState
  transcript : Transcript n

def Config.initial (n : ℕ) : Config n where
  jobs := fun _ => .untouched
  transcript := []

def Config.step (processing : Label n → ℝ) (config : Config n) :
    Action n → Option (Config n)
  | .test job =>
      match config.jobs job with
      | .untouched =>
          some {
            jobs := Function.update config.jobs job (.tested (processing job))
            transcript := config.transcript ++
              [.testResult job (processing job)]
          }
      | .tested _ | .done => none
  | .process job =>
      match config.jobs job with
      | .tested _ =>
          some {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.processed job]
          }
      | .untouched | .done => none
  | .blind job =>
      match config.jobs job with
      | .untouched =>
          some {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++
              [.blindCompleted job (processing job)]
          }
      | .tested _ | .done => none

inductive StopReason where
  | strategyStopped
  | invalidAction
  | outOfFuel
  deriving DecidableEq

structure RunResult (n : ℕ) where
  config : Config n
  reason : StopReason

def runFuel (processing : Label n → ℝ) (strategy : Strategy n) :
    ℕ → Config n → RunResult n
  | 0, config => ⟨config, .outOfFuel⟩
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => ⟨config, .strategyStopped⟩
      | some action =>
          match config.step processing action with
          | none => ⟨config, .invalidAction⟩
          | some next => runFuel processing strategy fuel next

def run (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    RunResult n := runFuel processing strategy fuel (Config.initial n)

def Observation.duration : Observation n → ℝ
  | .testResult _ _ => 1
  | .processed _ => 0
  | .blindCompleted _ p => p

/-- Processing observations obtain their duration from the truthful tested
stock; this version is used for cost accounting. -/
def Observation.actualDuration
    (processing : Label n → ℝ) : Observation n → ℝ
  | .testResult _ _ => 1
  | .processed job => processing job
  | .blindCompleted _ p => p

def Observation.completionLabel
    (processing : Label n → ℝ) : Observation n → Option (Label n)
  | .testResult job p => if p = 0 then some job else none
  | .processed job => if processing job = 0 then none else some job
  | .blindCompleted job _ => some job

def elapsed (processing : Label n → ℝ) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.actualDuration processing + elapsed processing rest

def completionCostFrom
    (processing : Label n → ℝ) : ℝ → Transcript n → ℝ
  | _, [] => 0
  | time, observation :: rest =>
      let finish := time + observation.actualDuration processing
      (if (observation.completionLabel processing).isSome then finish else 0) +
        completionCostFrom processing finish rest

def completionCost (processing : Label n → ℝ) (transcript : Transcript n) : ℝ :=
  completionCostFrom processing 0 transcript

def completionCount (processing : Label n → ℝ) : Transcript n → ℕ
  | [] => 0
  | observation :: rest =>
      (if (observation.completionLabel processing).isSome then 1 else 0) +
        completionCount processing rest

def suffixWeightedDuration
    (processing : Label n → ℝ) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.actualDuration processing *
          completionCount processing (observation :: rest) +
        suffixWeightedDuration processing rest

def zeroTestCount : Transcript n → ℕ
  | [] => 0
  | .testResult _ p :: rest =>
      (if p = 0 then 1 else 0) + zeroTestCount rest
  | _ :: rest => zeroTestCount rest

def positiveProcessedCount
    (processing : Label n → ℝ) : Transcript n → ℕ
  | [] => 0
  | .processed job :: rest =>
      (if processing job = 0 then 0 else 1) +
        positiveProcessedCount processing rest
  | _ :: rest => positiveProcessedCount processing rest

def blindCount : Transcript n → ℕ
  | [] => 0
  | .blindCompleted _ _ :: rest => 1 + blindCount rest
  | _ :: rest => blindCount rest

def processedWork
    (processing : Label n → ℝ) : Transcript n → ℝ
  | [] => 0
  | .processed job :: rest =>
      processing job + processedWork processing rest
  | _ :: rest => processedWork processing rest

def blindWork : Transcript n → ℝ
  | [] => 0
  | .blindCompleted _ p :: rest => p + blindWork rest
  | _ :: rest => blindWork rest

theorem completionCount_eq_operation_counts
    (processing : Label n → ℝ) (transcript : Transcript n) :
    completionCount processing transcript =
      zeroTestCount transcript + positiveProcessedCount processing transcript +
        blindCount transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = 0 <;>
            simp [completionCount, Observation.completionLabel,
              zeroTestCount, positiveProcessedCount, blindCount, hp, ih] <;>
            omega
      | processed job =>
          by_cases hp : processing job = 0 <;>
            simp [completionCount, Observation.completionLabel,
              zeroTestCount, positiveProcessedCount, blindCount, hp, ih] <;>
            omega
      | blindCompleted job p =>
          simp [completionCount, Observation.completionLabel,
            zeroTestCount, positiveProcessedCount, blindCount, ih]
          omega

theorem completionCostFrom_eq_count_mul_add_suffixWeighted
    (processing : Label n → ℝ) (time : ℝ) (transcript : Transcript n) :
    completionCostFrom processing time transcript =
      completionCount processing transcript * time +
        suffixWeightedDuration processing transcript := by
  induction transcript generalizing time with
  | nil => simp [completionCostFrom, completionCount, suffixWeightedDuration]
  | cons observation rest ih =>
      simp only [completionCostFrom, completionCount, suffixWeightedDuration]
      rw [ih]
      by_cases hcompletion :
          (observation.completionLabel processing).isSome
      · simp only [if_pos hcompletion, Nat.cast_add, Nat.cast_one]
        ring
      · simp only [if_neg hcompletion, zero_add]
        ring

theorem completionCost_eq_suffixWeightedDuration
    (processing : Label n → ℝ) (transcript : Transcript n) :
    completionCost processing transcript =
      suffixWeightedDuration processing transcript := by
  unfold completionCost
  rw [completionCostFrom_eq_count_mul_add_suffixWeighted]
  ring

/-! ## Publicly revealed first-touch sequence -/

def Transcript.revealedResults : Transcript n → List (Label n × ℝ)
  | [] => []
  | .testResult job p :: rest => (job, p) :: revealedResults rest
  | .processed _ :: rest => revealedResults rest
  | .blindCompleted job p :: rest => (job, p) :: revealedResults rest

def Transcript.testResults : Transcript n → List (Label n × ℝ)
  | [] => []
  | .testResult job p :: rest => (job, p) :: testResults rest
  | _ :: rest => testResults rest

def Transcript.blindResults : Transcript n → List (Label n × ℝ)
  | [] => []
  | .blindCompleted job p :: rest => (job, p) :: blindResults rest
  | _ :: rest => blindResults rest

def Transcript.processedLabels : Transcript n → List (Label n)
  | [] => []
  | .processed job :: rest => job :: processedLabels rest
  | _ :: rest => processedLabels rest

def Transcript.startedLabels (transcript : Transcript n) : List (Label n) :=
  transcript.revealedResults.map Prod.fst

theorem elapsed_eq_test_add_processed_add_blind
    (processing : Label n → ℝ) (transcript : Transcript n) :
    elapsed processing transcript =
      transcript.testResults.length + processedWork processing transcript +
        blindWork transcript := by
  induction transcript with
  | nil => simp [elapsed, Transcript.testResults, processedWork, blindWork]
  | cons observation rest ih =>
      cases observation <;>
        simp [elapsed, Observation.actualDuration, Transcript.testResults,
          processedWork, blindWork, ih, add_assoc, add_left_comm, add_comm]

@[simp] theorem Transcript.revealedResults_append_test
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).revealedResults =
      transcript.revealedResults ++ [(job, p)] := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.revealedResults, ih]

@[simp] theorem Transcript.revealedResults_append_process
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.processed job]).revealedResults =
      transcript.revealedResults := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.revealedResults, ih]

@[simp] theorem Transcript.revealedResults_append_blind
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.blindCompleted job p]).revealedResults =
      transcript.revealedResults ++ [(job, p)] := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.revealedResults, ih]

@[simp] theorem Transcript.testResults_append_test
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).testResults =
      transcript.testResults ++ [(job, p)] := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.testResults, ih]

@[simp] theorem Transcript.testResults_append_process
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.processed job]).testResults =
      transcript.testResults := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.testResults, ih]

@[simp] theorem Transcript.testResults_append_blind
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.blindCompleted job p]).testResults =
      transcript.testResults := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.testResults, ih]

@[simp] theorem Transcript.processedLabels_append_test
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).processedLabels =
      transcript.processedLabels := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.processedLabels, ih]

@[simp] theorem Transcript.processedLabels_append_process
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.processed job]).processedLabels =
      transcript.processedLabels ++ [job] := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.processedLabels, ih]

@[simp] theorem Transcript.processedLabels_append_blind
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.blindCompleted job p]).processedLabels =
      transcript.processedLabels := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [Transcript.processedLabels, ih]

@[simp] theorem Transcript.startedLabels_append_test
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.testResult job p]).startedLabels =
      transcript.startedLabels ++ [job] := by
  simp [Transcript.startedLabels]

@[simp] theorem Transcript.startedLabels_append_process
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.processed job]).startedLabels =
      transcript.startedLabels := by
  simp [Transcript.startedLabels]

@[simp] theorem Transcript.startedLabels_append_blind
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (transcript ++ [Observation.blindCompleted job p]).startedLabels =
      transcript.startedLabels ++ [job] := by
  simp [Transcript.startedLabels]

/-! ## Reachable-prefix invariants -/

def AllRevealsMatch
    (processing : Label n → ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.revealedResults → p = processing job

structure HistoryInvariant
    (processing : Label n → ℝ) (config : Config n) : Prop where
  startedNodup : config.transcript.startedLabels.Nodup
  untouchedNotStarted : ∀ job, config.jobs job = .untouched →
    job ∉ config.transcript.startedLabels
  processedNodup : config.transcript.processedLabels.Nodup
  testedRecorded : ∀ job p, config.jobs job = .tested p →
    (job, p) ∈ config.transcript.testResults
  processedRecorded : ∀ job,
    job ∈ config.transcript.processedLabels →
      job ∈ config.transcript.testResults.map Prod.fst
  processedDone : ∀ job,
    job ∈ config.transcript.processedLabels → config.jobs job = .done
  revealsMatch : AllRevealsMatch processing config.transcript

theorem Config.initial_historyInvariant
    (processing : Label n → ℝ) :
    HistoryInvariant processing (Config.initial n) := by
  constructor <;>
    simp [Config.initial, Transcript.startedLabels,
      Transcript.revealedResults, Transcript.processedLabels,
      Transcript.testResults, AllRevealsMatch]

theorem HistoryInvariant.step
    {processing : Label n → ℝ} {config next : Config n}
    (hgood : HistoryInvariant processing config) {action : Action n}
    (hstep : config.step processing action = some next) :
    HistoryInvariant processing next := by
  cases action with
  | test testedJob =>
      cases hstate : config.jobs testedJob with
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotStarted := hgood.untouchedNotStarted testedJob hstate
          constructor
          · simpa only [Transcript.startedLabels_append_test,
                List.concat_eq_append] using
              List.Nodup.concat hnotStarted hgood.startedNodup
          · intro job hjob
            by_cases heq : job = testedJob
            · subst job
              simp [Function.update] at hjob
            · have hold := hgood.untouchedNotStarted job
                (by simpa [Function.update, heq] using hjob)
              simpa [heq] using hold
          · simpa using hgood.processedNodup
          · intro job p hjob
            by_cases heq : job = testedJob
            · subst job
              have hp : p = processing testedJob := by
                simpa [Function.update] using hjob.symm
              subst p
              simp
            · have hold := hgood.testedRecorded job p
                (by simpa [Function.update, heq] using hjob)
              simpa only [Transcript.testResults_append_test] using
                List.mem_append_left [(testedJob, processing testedJob)] hold
          · intro job hmem
            rw [Transcript.processedLabels_append_test] at hmem
            rw [Transcript.testResults_append_test, List.map_append,
              List.map_singleton]
            exact List.mem_append_left _ (hgood.processedRecorded job hmem)
          · intro job hmem
            rw [Transcript.processedLabels_append_test] at hmem
            have hdone := hgood.processedDone job hmem
            by_cases heq : job = testedJob
            · subst job
              rw [hstate] at hdone
              contradiction
            · simpa [Function.update, heq] using hdone
          · intro job p hmem
            rw [Transcript.revealedResults_append_test] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · exact hgood.revealsMatch job p hold
            · have heq : (job, p) = (testedJob, processing testedJob) := by
                simpa using hnew
              have hfirst : job = testedJob := congrArg Prod.fst heq
              have hsecond : p = processing testedJob := congrArg Prod.snd heq
              subst job
              exact hsecond
  | process processedJob =>
      cases hstate : config.jobs processedJob with
      | untouched => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          have hrecord := hgood.testedRecorded processedJob p hstate
          have hnotProcessed :
              processedJob ∉ config.transcript.processedLabels := by
            intro hmem
            have hdone := hgood.processedDone processedJob hmem
            rw [hstate] at hdone
            contradiction
          constructor
          · simpa using hgood.startedNodup
          · intro job hjob
            have hold := hgood.untouchedNotStarted job
            by_cases heq : job = processedJob
            · subst job
              simp [Function.update] at hjob
            · simpa only [Transcript.startedLabels_append_process] using
                hold (by simpa [Function.update, heq] using hjob)
          · simpa only [Transcript.processedLabels_append_process,
                List.concat_eq_append] using
              List.Nodup.concat hnotProcessed hgood.processedNodup
          · intro job q hjob
            by_cases heq : job = processedJob
            · subst job
              simp [Function.update] at hjob
            · simpa only [Transcript.testResults_append_process] using
                hgood.testedRecorded job q
                  (by simpa [Function.update, heq] using hjob)
          · intro job hmem
            rw [Transcript.processedLabels_append_process] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · rw [Transcript.testResults_append_process]
              exact hgood.processedRecorded job hold
            · have : job = processedJob := by simpa using hnew
              subst job
              rw [Transcript.testResults_append_process]
              exact List.mem_map.mpr ⟨(processedJob, p), hrecord, rfl⟩
          · intro job hmem
            rw [Transcript.processedLabels_append_process] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · have hdone := hgood.processedDone job hold
              by_cases heq : job = processedJob
              · subst job
                exact (hnotProcessed hold).elim
              · simpa [Function.update, heq] using hdone
            · have : job = processedJob := by simpa using hnew
              subst job
              simp [Function.update]
          · simpa [AllRevealsMatch] using hgood.revealsMatch
  | blind blindJob =>
      cases hstate : config.jobs blindJob with
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotStarted := hgood.untouchedNotStarted blindJob hstate
          constructor
          · simpa only [Transcript.startedLabels_append_blind,
                List.concat_eq_append] using
              List.Nodup.concat hnotStarted hgood.startedNodup
          · intro job hjob
            by_cases heq : job = blindJob
            · subst job
              simp [Function.update] at hjob
            · have hold := hgood.untouchedNotStarted job
                (by simpa [Function.update, heq] using hjob)
              simpa [heq] using hold
          · simpa using hgood.processedNodup
          · intro job p hjob
            by_cases heq : job = blindJob
            · subst job
              simp [Function.update] at hjob
            · simpa only [Transcript.testResults_append_blind] using
                hgood.testedRecorded job p
                  (by simpa [Function.update, heq] using hjob)
          · intro job hmem
            rw [Transcript.processedLabels_append_blind] at hmem
            rw [Transcript.testResults_append_blind]
            exact hgood.processedRecorded job hmem
          · intro job hmem
            rw [Transcript.processedLabels_append_blind] at hmem
            have hdone := hgood.processedDone job hmem
            by_cases heq : job = blindJob
            · subst job
              rw [hstate] at hdone
              contradiction
            · simpa [Function.update, heq] using hdone
          · intro job p hmem
            rw [Transcript.revealedResults_append_blind] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · exact hgood.revealsMatch job p hold
            · have heq : (job, p) = (blindJob, processing blindJob) := by
                simpa using hnew
              have hfirst : job = blindJob := congrArg Prod.fst heq
              have hsecond : p = processing blindJob := congrArg Prod.snd heq
              subst job
              exact hsecond

theorem runFuel_historyInvariant
    (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hgood : HistoryInvariant processing config) :
    HistoryInvariant processing
      (runFuel processing strategy fuel config).config := by
  induction fuel generalizing config with
  | zero => exact hgood
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none => simp [haction, hgood]
      | some action =>
          cases hstep : config.step processing action with
          | none => simp [haction, hstep, hgood]
          | some next =>
              simp only [haction, hstep]
              exact ih next (hgood.step hstep)

theorem run_historyInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    HistoryInvariant processing (run processing strategy fuel).config := by
  unfold run
  exact runFuel_historyInvariant processing strategy fuel (Config.initial n)
    (Config.initial_historyInvariant processing)

/-! Every successful optional action strictly consumes a finite lifecycle
rank.  Thus `2n+1` fuel always settles, independently of processing times and
of the strategy's adaptive use of observed blind durations. -/

def JobState.work : JobState → ℕ
  | .untouched => 2
  | .tested _ => 1
  | .done => 0

def Config.remainingWork (config : Config n) : ℕ :=
  ∑ job, (config.jobs job).work

private theorem remainingWork_update_test
    (jobs : Label n → JobState) (job : Label n) (p : ℝ)
    (hjob : jobs job = .untouched) :
    (∑ i, (Function.update jobs job (.tested p) i).work) + 1 =
      ∑ i, (jobs i).work := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ job)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Label n))
    (fun i => (Function.update jobs job (.tested p) i).work)
    (Finset.mem_univ job)]
  have hrest :
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
        (Function.update jobs job (.tested p) i).work) =
      ∑ i ∈ (Finset.univ : Finset (Label n)).erase job, (jobs i).work := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Function.update, (Finset.mem_erase.mp hi).1]
  rw [hrest]
  simp [Function.update, hjob, JobState.work]

private theorem remainingWork_update_process
    (jobs : Label n → JobState) (job : Label n) (p : ℝ)
    (hjob : jobs job = .tested p) :
    (∑ i, (Function.update jobs job .done i).work) + 1 =
      ∑ i, (jobs i).work := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ job)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Label n))
    (fun i => (Function.update jobs job .done i).work)
    (Finset.mem_univ job)]
  have hrest :
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
        (Function.update jobs job .done i).work) =
      ∑ i ∈ (Finset.univ : Finset (Label n)).erase job, (jobs i).work := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Function.update, (Finset.mem_erase.mp hi).1]
  rw [hrest]
  simp [Function.update, hjob, JobState.work]

private theorem remainingWork_update_blind
    (jobs : Label n → JobState) (job : Label n)
    (hjob : jobs job = .untouched) :
    (∑ i, (Function.update jobs job .done i).work) + 2 =
      ∑ i, (jobs i).work := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ job)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Label n))
    (fun i => (Function.update jobs job .done i).work)
    (Finset.mem_univ job)]
  have hrest :
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
        (Function.update jobs job .done i).work) =
      ∑ i ∈ (Finset.univ : Finset (Label n)).erase job, (jobs i).work := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Function.update, (Finset.mem_erase.mp hi).1]
  rw [hrest]
  simp [Function.update, hjob, JobState.work]

theorem Config.remainingWork_step_lt
    {processing : Label n → ℝ} {config next : Config n} {action : Action n}
    (hstep : config.step processing action = some next) :
    next.remainingWork < config.remainingWork := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
          subst next
          have hdrop := remainingWork_update_test config.jobs job
            (processing job) hjob
          unfold Config.remainingWork
          omega
      | tested p => simp [Config.step, hjob] at hstep
      | done => simp [Config.step, hjob] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched => simp [Config.step, hjob] at hstep
      | tested p =>
          simp [Config.step, hjob] at hstep
          subst next
          have hdrop := remainingWork_update_process config.jobs job p hjob
          unfold Config.remainingWork
          omega
      | done => simp [Config.step, hjob] at hstep
  | blind job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
          subst next
          have hdrop := remainingWork_update_blind config.jobs job hjob
          unfold Config.remainingWork
          omega
      | tested p => simp [Config.step, hjob] at hstep
      | done => simp [Config.step, hjob] at hstep

theorem runFuel_reason_ne_outOfFuel_of_remainingWork_lt
    (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hfuel : config.remainingWork < fuel) :
    (runFuel processing strategy fuel config).reason ≠ .outOfFuel := by
  induction fuel generalizing config with
  | zero => omega
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          cases hstep : config.step processing action with
          | none => simp
          | some next =>
              have hdrop := Config.remainingWork_step_lt hstep
              apply ih next
              omega

@[simp] theorem Config.initial_remainingWork (n : ℕ) :
    (Config.initial n).remainingWork = 2 * n := by
  simp [Config.remainingWork, Config.initial, JobState.work]
  omega

theorem run_reason_ne_outOfFuel
    (processing : Label n → ℝ) (strategy : Strategy n) :
    (run processing strategy (2 * n + 1)).reason ≠ .outOfFuel := by
  unfold run
  apply runFuel_reason_ne_outOfFuel_of_remainingWork_lt
  simp

def testClassCount
    (category : ℝ → Bool) (transcript : Transcript n) : ℕ :=
  (transcript.testResults.filter fun result => category result.2).length

def processedClassCount
    (processing : Label n → ℝ) (category : ℝ → Bool)
    (transcript : Transcript n) : ℕ :=
  (transcript.processedLabels.filter fun job =>
    category (processing job)).length

theorem Transcript.mem_revealedResults_of_mem_testResults
    {transcript : Transcript n} {result : Label n × ℝ}
    (hresult : result ∈ transcript.testResults) :
    result ∈ transcript.revealedResults := by
  induction transcript with
  | nil => simp [Transcript.testResults] at hresult
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simp only [Transcript.testResults, Transcript.revealedResults,
            List.mem_cons] at hresult ⊢
          exact hresult.elim Or.inl (fun h => Or.inr (ih h))
      | processed job =>
          exact ih hresult
      | blindCompleted job p =>
          exact List.mem_cons_of_mem _ (ih hresult)

theorem processedClassCount_le_testClassCount
    {processing : Label n → ℝ} {config : Config n}
    (hgood : HistoryInvariant processing config)
    (category : ℝ → Bool) :
    processedClassCount processing category config.transcript ≤
      testClassCount category config.transcript := by
  let processed := config.transcript.processedLabels.filter fun job =>
    category (processing job)
  let tested := config.transcript.testResults.filter fun result =>
    category result.2
  have hprocessedNodup : processed.Nodup := hgood.processedNodup.filter _
  have hsubset : processed.toFinset ⊆ (tested.map Prod.fst).toFinset := by
    intro job hjob
    have hfiltered := List.mem_filter.mp (List.mem_toFinset.mp hjob)
    have hrecorded := hgood.processedRecorded job hfiltered.1
    rcases List.mem_map.mp hrecorded with ⟨result, hresult, hlabel⟩
    have hvalue : result.2 = processing job := by
      have := hgood.revealsMatch result.1 result.2
        (Transcript.mem_revealedResults_of_mem_testResults hresult)
      simpa [hlabel] using this
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨result, List.mem_filter.mpr ⟨hresult, ?_⟩, hlabel⟩
    simpa [hvalue] using hfiltered.2
  calc
    processedClassCount processing category config.transcript =
        processed.length := rfl
    _ = processed.toFinset.card := by
      rw [List.toFinset_card_of_nodup hprocessedNodup]
    _ ≤ (tested.map Prod.fst).toFinset.card := Finset.card_le_card hsubset
    _ ≤ (tested.map Prod.fst).length := List.toFinset_card_le _
    _ = testClassCount category config.transcript := by
      simp [testClassCount, tested]

/-! ## Relabelling -/

def Observation.relabel (order : Equiv.Perm (Label n)) :
    Observation n → Observation n
  | .testResult job p => .testResult (order job) p
  | .processed job => .processed (order job)
  | .blindCompleted job p => .blindCompleted (order job) p

def Action.relabel (order : Equiv.Perm (Label n)) : Action n → Action n
  | .test job => .test (order job)
  | .process job => .process (order job)
  | .blind job => .blind (order job)

def Strategy.relabel (order : Equiv.Perm (Label n))
    (strategy : Strategy n) : Strategy n :=
  fun transcript =>
    (strategy (transcript.map (Observation.relabel order.symm))).map
      (Action.relabel order)

@[simp] theorem Observation.relabel_symm_relabel
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).relabel order.symm = observation := by
  cases observation <;> simp [Observation.relabel]

@[simp] theorem Action.relabel_symm_relabel
    (order : Equiv.Perm (Label n)) (action : Action n) :
    (action.relabel order).relabel order.symm = action := by
  cases action <;> simp [Action.relabel]

def Config.relabel (order : Equiv.Perm (Label n))
    (config : Config n) : Config n where
  jobs := fun physical => config.jobs (order.symm physical)
  transcript := config.transcript.map (Observation.relabel order)

@[simp] theorem Config.relabel_initial
    (order : Equiv.Perm (Label n)) :
    (Config.initial n).relabel order = Config.initial n := by
  rw [Config.mk.injEq]
  exact ⟨by funext job; rfl, rfl⟩

@[simp] theorem Config.relabel_transcript_map_symm
    (order : Equiv.Perm (Label n)) (config : Config n) :
    (config.relabel order).transcript.map (Observation.relabel order.symm) =
      config.transcript := by
  simp [Config.relabel, List.map_map, Function.comp_def]

theorem Config.step_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (config : Config n)
    (action : Action n) :
    (config.relabel order).step physicalProcessing (action.relabel order) =
      (config.step (fun virtual => physicalProcessing (order virtual)) action).map
        (Config.relabel order) := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Action.relabel, Config.step, Config.relabel,
            Equiv.symm_apply_apply, hstate, Option.map_some]
          apply congrArg some
          rw [Config.mk.injEq]
          constructor
          · funext physical
            by_cases hphysical : physical = order job
            · subst physical
              simp [Function.update]
            · have hvirtual : order.symm physical ≠ job := by
                intro h
                apply hphysical
                simpa using congrArg order h
              simp [Function.update, hphysical, hvirtual]
          · simp [List.map_append, Observation.relabel]
      | tested p =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
      | done =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
  | process job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
      | tested p =>
          simp only [Action.relabel, Config.step, Config.relabel,
            Equiv.symm_apply_apply, hstate, Option.map_some]
          apply congrArg some
          rw [Config.mk.injEq]
          constructor
          · funext physical
            by_cases hphysical : physical = order job
            · subst physical
              simp [Function.update]
            · have hvirtual : order.symm physical ≠ job := by
                intro h
                apply hphysical
                simpa using congrArg order h
              simp [Function.update, hphysical, hvirtual]
          · simp [List.map_append, Observation.relabel]
      | done =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
  | blind job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Action.relabel, Config.step, Config.relabel,
            Equiv.symm_apply_apply, hstate, Option.map_some]
          apply congrArg some
          rw [Config.mk.injEq]
          constructor
          · funext physical
            by_cases hphysical : physical = order job
            · subst physical
              simp [Function.update]
            · have hvirtual : order.symm physical ≠ job := by
                intro h
                apply hphysical
                simpa using congrArg order h
              simp [Function.update, hphysical, hvirtual]
          · simp [List.map_append, Observation.relabel]
      | tested p =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]
      | done =>
          simp [Action.relabel, Config.step, Config.relabel, hstate]

theorem runFuel_relabel_config
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) :
    (runFuel physicalProcessing (strategy.relabel order) fuel
        (config.relabel order)).config =
      (runFuel (fun virtual => physicalProcessing (order virtual))
        strategy fuel config).config.relabel order := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFuel, Strategy.relabel,
        Config.relabel_transcript_map_symm]
      cases haction : strategy config.transcript with
      | none => simp [haction]
      | some action =>
          simp only [haction, Option.map_some]
          rw [Config.step_relabel]
          cases hstep : config.step
              (fun virtual => physicalProcessing (order virtual)) action with
          | none => simp [hstep]
          | some next =>
              simp only [hstep, Option.map_some]
              exact ih next

theorem run_relabel_config
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) (fuel : ℕ) :
    (run physicalProcessing (strategy.relabel order) fuel).config =
      (run (fun virtual => physicalProcessing (order virtual))
        strategy fuel).config.relabel order := by
  unfold run
  rw [← Config.relabel_initial order]
  exact runFuel_relabel_config physicalProcessing order strategy fuel
    (Config.initial n)

@[simp] theorem Observation.actualDuration_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).actualDuration physicalProcessing =
      observation.actualDuration
        (fun virtual => physicalProcessing (order virtual)) := by
  cases observation <;> simp [Observation.relabel, Observation.actualDuration]

@[simp] theorem Observation.completionLabel_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (observation : Observation n) :
    (observation.relabel order).completionLabel physicalProcessing =
      (observation.completionLabel
        (fun virtual => physicalProcessing (order virtual))).map order := by
  cases observation with
  | testResult job p =>
      by_cases hp : p = 0 <;>
        simp [Observation.relabel, Observation.completionLabel, hp]
  | processed job =>
      by_cases hp : physicalProcessing (order job) = 0 <;>
        simp [Observation.relabel, Observation.completionLabel, hp]
  | blindCompleted job p =>
      simp [Observation.relabel, Observation.completionLabel]

theorem completionCostFrom_map_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (time : ℝ)
    (transcript : Transcript n) :
    completionCostFrom physicalProcessing time
        (transcript.map (Observation.relabel order)) =
      completionCostFrom
        (fun virtual => physicalProcessing (order virtual)) time transcript := by
  induction transcript generalizing time with
  | nil => rfl
  | cons observation rest ih =>
      simp only [List.map_cons, completionCostFrom,
        Observation.actualDuration_relabel,
        Observation.completionLabel_relabel, Option.isSome_map]
      rw [ih]

theorem completionCost_map_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (transcript : Transcript n) :
    completionCost physicalProcessing
        (transcript.map (Observation.relabel order)) =
      completionCost
        (fun virtual => physicalProcessing (order virtual)) transcript := by
  unfold completionCost
  exact completionCostFrom_map_relabel physicalProcessing order 0 transcript

theorem runCompletionCost_relabel
    (physicalProcessing : Label n → ℝ)
    (order : Equiv.Perm (Label n)) (strategy : Strategy n) (fuel : ℕ) :
    completionCost physicalProcessing
        (run physicalProcessing (strategy.relabel order) fuel).config.transcript =
      completionCost (fun virtual => physicalProcessing (order virtual))
        (run (fun virtual => physicalProcessing (order virtual))
          strategy fuel).config.transcript := by
  rw [run_relabel_config]
  exact completionCost_map_relabel physicalProcessing order _

end


end ObservedOnline
end RandomizedOptional
end SchedulingPaper
