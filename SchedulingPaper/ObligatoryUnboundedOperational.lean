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

theorem runFuel_testsMatch (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ) (config : Online.Config n)
    (hmatch : config.transcript.TestsMatch processing) :
    (Online.runFuel .infinite (Online.fixedOracle processing) strategy fuel
      config).config.transcript.TestsMatch processing := by
  induction fuel generalizing config with
  | zero => simpa [Online.runFuel] using hmatch
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [Online.runFuel, haction] using hmatch
      | some action =>
          cases hstep : config.step .infinite
              (Online.fixedOracle processing) action with
          | none => simpa [Online.runFuel, haction, hstep] using hmatch
          | some next =>
              have hnext := Online.Config.step_preserves_testsMatch
                .infinite processing hmatch hstep
              simpa [Online.runFuel, haction, hstep] using ih next hnext

theorem run_testsMatch (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    Online.Transcript.TestsMatch processing
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript := by
  unfold Online.run
  exact runFuel_testsMatch processing strategy fuel (Online.Config.initial n)
    (Online.Transcript.testsMatch_nil processing)

theorem runFuel_processHistoryInvariant (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) (config : Online.Config n)
    (hprocess : config.ProcessHistoryInvariant)
    (hstarted : config.StartedHistoryInvariant) :
    (Online.runFuel .infinite oracle strategy fuel config).config.ProcessHistoryInvariant := by
  induction fuel generalizing config with
  | zero => simpa [Online.runFuel] using hprocess
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [Online.runFuel, haction] using hprocess
      | some action =>
          cases hstep : config.step .infinite oracle action with
          | none => simpa [Online.runFuel, haction, hstep] using hprocess
          | some next =>
              have hprocessNext := Online.Config.processHistoryInvariant_step
                hprocess hstarted hstep
              have hstartedNext := Online.Config.startedHistoryInvariant_step
                hstarted hstep
              simpa [Online.runFuel, haction, hstep] using
                ih next hprocessNext hstartedNext

theorem run_processHistoryInvariant (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    (Online.run .infinite oracle strategy fuel).config.ProcessHistoryInvariant := by
  unfold Online.run
  exact runFuel_processHistoryInvariant oracle strategy fuel
    (Online.Config.initial n) (Online.Config.initial_processHistoryInvariant n)
    (Online.Config.initial_startedHistoryInvariant n)

theorem NoRaw.step_infinite {oracle : Online.Oracle n}
    {config next : Online.Config n} {action : Online.Action n}
    (hnoraw : NoRaw config.transcript)
    (hstep : config.step .infinite oracle action = some next) :
    NoRaw next.transcript := by
  cases action with
  | test job =>
      cases hstate : config.jobs job <;>
        simp [Online.Config.step, hstate] at hstep
      subst next
      intro other hmem
      exact hnoraw other (by
        simpa [Online.Transcript.testResults] using hmem)
  | process job =>
      cases hstate : config.jobs job <;>
        simp [Online.Config.step, hstate] at hstep
      subst next
      intro other hmem
      exact hnoraw other (by
        simpa [Online.Transcript.testResults] using hmem)
  | raw job => simp [Online.Config.step] at hstep

theorem runFuel_noRaw (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) (config : Online.Config n)
    (hnoraw : NoRaw config.transcript) :
    NoRaw (Online.runFuel .infinite oracle strategy fuel config).config.transcript := by
  induction fuel generalizing config with
  | zero => simpa [Online.runFuel] using hnoraw
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [Online.runFuel, haction] using hnoraw
      | some action =>
          cases hstep : config.step .infinite oracle action with
          | none => simpa [Online.runFuel, haction, hstep] using hnoraw
          | some next =>
              simpa [Online.runFuel, haction, hstep] using
                ih next (hnoraw.step_infinite hstep)

theorem run_noRaw (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    NoRaw (Online.run .infinite oracle strategy fuel).config.transcript := by
  unfold Online.run
  exact runFuel_noRaw oracle strategy fuel (Online.Config.initial n) (by
    intro job
    simp [NoRaw, Online.Config.initial])

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

/-- A completed obligatory run has exactly one process observation per job.
The point is not merely cardinality: the lifecycle invariant rules out a
tested-but-unprocessed job in a terminal configuration. -/
theorem processedLabels_perm_of_all_done
    (processing : Online.Label n → ℝ) (strategy : Online.Strategy n)
    (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) :
    (Online.Transcript.processedLabels
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript).Perm
      (List.ofFn fun job : Fin n => job) := by
  let result := Online.run .infinite (Online.fixedOracle processing) strategy fuel
  have hprocess := run_processHistoryInvariant
    (Online.fixedOracle processing) strategy fuel
  have htesting := Online.run_testingInvariant
    (Online.fixedOracle processing) strategy fuel
  have hall : ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    have htestedLabel :
        job ∈ result.config.transcript.testResults.map Prod.fst := by
      by_contra hnot
      have huntouched := (htesting.untouched_iff job).mpr hnot
      have hdoneJob := hdone job
      change result.config.jobs job = .untouched at huntouched
      change result.config.jobs job = .done at hdoneJob
      rw [hdoneJob] at huntouched
      contradiction
    rcases List.mem_map.mp htestedLabel with ⟨⟨other, p⟩, hpair, hother⟩
    simp only at hother
    subst other
    by_contra hnotProcessed
    have hstate := hprocess.recordedUnprocessedTested job p hpair hnotProcessed
    have hdoneJob := hdone job
    change result.config.jobs job = .done at hdoneJob
    rw [hdoneJob] at hstate
    contradiction
  apply (List.perm_ext_iff_of_nodup hprocess.processedNodup
    (List.nodup_ofFn.mpr fun _ _ hij => hij)).2
  intro job
  constructor
  · intro _
    simp
  · intro _
    exact hall job

theorem processedCount_eq_n_of_all_done
    (processing : Online.Label n → ℝ) (strategy : Online.Strategy n)
    (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) :
    processedCount
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript = n := by
  rw [processedCount_eq_processedLabels_length]
  simpa using
    (processedLabels_perm_of_all_done processing strategy fuel hdone).length_eq

def testOrder (transcript : Online.Transcript n)
    (hlength : (testLabels transcript).length = n)
    (hnodup : (testLabels transcript).Nodup) : Equiv.Perm (Fin n) :=
  RandomizedOptional.ObservedTrace.listOrderPerm
    (testLabels transcript) hlength hnodup

def completedBeforeAt (transcript : Online.Transcript n)
    (hlength : (processedBeforeTests transcript).length = n) : Fin n → ℕ :=
  fun rank => (processedBeforeTests transcript).get
    (Fin.cast hlength.symm rank)

theorem sum_completedBeforeAt (transcript : Online.Transcript n)
    (hlength : (processedBeforeTests transcript).length = n) :
    (∑ rank, (completedBeforeAt transcript hlength rank : ℝ)) =
      ((processedBeforeTests transcript).map (fun x : ℕ => (x : ℝ))).sum := by
  rw [← List.sum_ofFn]
  change
    (List.ofFn (fun rank : Fin n =>
      ((processedBeforeTests transcript).get
        (Fin.cast hlength.symm rank) : ℝ))).sum = _
  have hitems :=
    RandomizedOptional.ObservedTrace.list_ofFn_cast_get
      (processedBeforeTests transcript) hlength
  have hmap := congrArg (List.map fun x : ℕ => (x : ℝ)) hitems
  simpa [List.map_ofFn, Function.comp_def] using congrArg List.sum hmap

def runTestOrder (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) : Equiv.Perm (Fin n) :=
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  testOrder transcript
    (by
      simpa [transcript, testLabels] using
        Online.testResults_length_eq_n_of_all_done
          (Online.fixedOracle processing) strategy fuel hdone)
    (by
      simpa [transcript, testLabels] using
        (Online.run_testingInvariant
          (Online.fixedOracle processing) strategy fuel).testNodup)

def runCompletedBefore (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) : Fin n → ℕ :=
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  completedBeforeAt transcript
    (by
      simpa [transcript, processedBeforeTests] using
        Online.testResults_length_eq_n_of_all_done
          (Online.fixedOracle processing) strategy fuel hdone)

def actionObservation (processing : Online.Label n → ℝ) :
    Online.Action n → Online.Observation n
  | .test job => .testResult job (processing job)
  | .process job => .processed job
  | .raw job => .rawCompleted job

/-- Fresh observations produced after a current configuration.  This mirrors
`Online.runFuel` and is used only for the lockstep theorem below. -/
def runWord (processing : Online.Label n → ℝ) (strategy : Online.Strategy n) :
    ℕ → Online.Config n → Online.Transcript n
  | 0, _ => []
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => []
      | some action =>
          match config.step .infinite (Online.fixedOracle processing) action with
          | none => []
          | some next => actionObservation processing action ::
              runWord processing strategy fuel next

theorem step_transcript_eq_append_observation
    {processing : Online.Label n → ℝ} {config next : Online.Config n}
    {action : Online.Action n}
    (hstep : config.step .infinite (Online.fixedOracle processing) action =
      some next) :
    next.transcript = config.transcript ++ [actionObservation processing action] := by
  cases action with
  | test job =>
      cases hstate : config.jobs job <;>
        simp [Online.Config.step, Online.fixedOracle, hstate] at hstep
      subst next
      rfl
  | process job =>
      cases hstate : config.jobs job <;>
        simp [Online.Config.step, hstate] at hstep
      subst next
      rfl
  | raw job => simp [Online.Config.step] at hstep

theorem runFuel_transcript_eq_append_runWord
    (processing : Online.Label n → ℝ) (strategy : Online.Strategy n)
    (fuel : ℕ) (config : Online.Config n) :
    (Online.runFuel .infinite (Online.fixedOracle processing) strategy fuel
      config).config.transcript =
      config.transcript ++ runWord processing strategy fuel config := by
  induction fuel generalizing config with
  | zero => simp [Online.runFuel, runWord]
  | succ fuel ih =>
      simp only [Online.runFuel, runWord]
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only
          cases hstep : config.step .infinite
              (Online.fixedOracle processing) action with
          | none => simp
          | some next =>
              simp only
              rw [ih next, step_transcript_eq_append_observation hstep]
              simp

theorem run_transcript_eq_runWord
    (processing : Online.Label n → ℝ) (strategy : Online.Strategy n)
    (fuel : ℕ) :
    (Online.run .infinite
      (Online.fixedOracle processing) strategy fuel).config.transcript =
      runWord processing strategy fuel (Online.Config.initial n) := by
  unfold Online.run
  simpa [Online.Config.initial] using
    runFuel_transcript_eq_append_runWord processing strategy fuel
      (Online.Config.initial n)

def testValues (transcript : Online.Transcript n) : List ℝ :=
  transcript.testResults.map Prod.snd

def testEventsAux : Online.Transcript n → ℕ → List (Online.Label n × ℕ)
  | [], _ => []
  | .testResult job _ :: rest, completed =>
      (job, completed) :: testEventsAux rest completed
  | .processed _ :: rest, completed => testEventsAux rest (completed + 1)
  | .rawCompleted _ :: rest, completed => testEventsAux rest completed

def testEvents (transcript : Online.Transcript n) :
    List (Online.Label n × ℕ) :=
  testEventsAux transcript 0

theorem testEvents_map_fst (transcript : Online.Transcript n)
    (completed : ℕ) :
    (testEventsAux transcript completed).map Prod.fst = testLabels transcript := by
  induction transcript generalizing completed with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [testEventsAux, testLabels, Online.Transcript.testResults,
          Online.Observation.testResult?, ih]

theorem testEvents_map_snd (transcript : Online.Transcript n)
    (completed : ℕ) :
    (testEventsAux transcript completed).map Prod.snd =
      processedBeforeTestsAux transcript completed := by
  induction transcript generalizing completed with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [testEventsAux, processedBeforeTestsAux, ih]

@[simp] theorem testEventsAux_length (transcript : Online.Transcript n)
    (completed : ℕ) :
    (testEventsAux transcript completed).length = testCount transcript := by
  induction transcript generalizing completed with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [testEventsAux, testCount, ih]

def testEventAt (transcript : Online.Transcript n)
    (hlength : (testEvents transcript).length = n) (rank : Fin n) :
    Online.Label n × ℕ :=
  (testEvents transcript).get (Fin.cast hlength.symm rank)

theorem testEventAt_fst (transcript : Online.Transcript n)
    (hevents : (testEvents transcript).length = n)
    (hlabels : (testLabels transcript).length = n)
    (hnodup : (testLabels transcript).Nodup) (rank : Fin n) :
    (testEventAt transcript hevents rank).1 =
      testOrder transcript hlabels hnodup rank := by
  let eventIndex : Fin (testEvents transcript).length :=
    Fin.cast hevents.symm rank
  let labelIndex : Fin (testLabels transcript).length :=
    Fin.cast hlabels.symm rank
  have hmap : (testEvents transcript).map Prod.fst = testLabels transcript := by
    simpa [testEvents] using testEvents_map_fst transcript 0
  calc
    (testEventAt transcript hevents rank).1 =
        ((testEvents transcript).map Prod.fst).get
          ⟨rank.val, by simpa [eventIndex] using eventIndex.isLt⟩ := by
      simp [testEventAt, eventIndex]
    _ = (testLabels transcript).get
          ⟨rank.val, by simpa [labelIndex] using labelIndex.isLt⟩ := by
      simpa using List.get_of_eq hmap
        ⟨rank.val, by simpa [eventIndex] using eventIndex.isLt⟩
    _ = testOrder transcript hlabels hnodup rank := by
      rfl

theorem testEventAt_snd (transcript : Online.Transcript n)
    (hevents : (testEvents transcript).length = n)
    (hbefore : (processedBeforeTests transcript).length = n)
    (rank : Fin n) :
    (testEventAt transcript hevents rank).2 =
      completedBeforeAt transcript hbefore rank := by
  let eventIndex : Fin (testEvents transcript).length :=
    Fin.cast hevents.symm rank
  let beforeIndex : Fin (processedBeforeTests transcript).length :=
    Fin.cast hbefore.symm rank
  have hmap : (testEvents transcript).map Prod.snd =
      processedBeforeTests transcript := by
    simpa [testEvents, processedBeforeTests] using
      testEvents_map_snd transcript 0
  calc
    (testEventAt transcript hevents rank).2 =
        ((testEvents transcript).map Prod.snd).get
          ⟨rank.val, by simpa [eventIndex] using eventIndex.isLt⟩ := by
      simp [testEventAt, eventIndex]
    _ = (processedBeforeTests transcript).get
          ⟨rank.val, by simpa [beforeIndex] using beforeIndex.isLt⟩ := by
      simpa using List.get_of_eq hmap
        ⟨rank.val, by simpa [eventIndex] using eventIndex.isLt⟩
    _ = completedBeforeAt transcript hbefore rank := by
      rfl

theorem testValues_eq_testLabels_map
    (processing : Online.Label n → ℝ) (transcript : Online.Transcript n)
    (hmatch : transcript.TestsMatch processing) :
    testValues transcript = (testLabels transcript).map processing := by
  unfold testValues testLabels
  rw [List.map_map]
  apply List.map_congr_left
  intro pair hmem
  rcases pair with ⟨job, p⟩
  simp [hmatch job p hmem]

/-- If the first `k` published test values agree, then the first `k+1`
test labels and their numbers of earlier process completions agree.  Process
actions expose no new value, while a test chooses its label before reading
the oracle answer. -/
theorem runWord_testEvents_causal
    (processing processing' : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel k : ℕ) (config : Online.Config n)
    (completed : ℕ)
    (hvalues :
      (testValues (runWord processing strategy fuel config)).take k =
        (testValues (runWord processing' strategy fuel config)).take k) :
    (testEventsAux (runWord processing strategy fuel config) completed).take (k + 1) =
      (testEventsAux (runWord processing' strategy fuel config) completed).take
        (k + 1) := by
  induction fuel generalizing config k completed with
  | zero => simp [runWord, testEventsAux]
  | succ fuel ih =>
      simp only [runWord] at hvalues ⊢
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only [haction] at hvalues ⊢
          cases action with
          | raw job => simp [Online.Config.step]
          | process job =>
              cases hstate : config.jobs job with
              | untouched => simp [Online.Config.step, hstate]
              | done => simp [Online.Config.step, hstate]
              | tested p =>
                  simp only [Online.Config.step, hstate, actionObservation,
                    testValues, Online.Transcript.testResults_processed_cons,
                    List.map, testEventsAux] at hvalues ⊢
                  exact ih k _ (completed + 1) hvalues
          | test job =>
              cases hstate : config.jobs job with
              | tested p => simp [Online.Config.step, hstate]
              | done => simp [Online.Config.step, hstate]
              | untouched =>
                  cases k with
                  | zero =>
                      simp [Online.Config.step, Online.fixedOracle, hstate,
                        actionObservation, testValues, testEventsAux]
                  | succ k =>
                      simp only [Online.Config.step, Online.fixedOracle, hstate,
                        actionObservation, testValues,
                        Online.Transcript.testResults_testResult_cons,
                        List.map, List.take_succ_cons, List.cons.injEq] at hvalues
                      have hp : processing job = processing' job := hvalues.1
                      simp only [Online.Config.step, Online.fixedOracle, hstate,
                        actionObservation, testEventsAux,
                        List.take_succ_cons, List.cons.injEq]
                      rw [← hp] at hvalues ⊢
                      exact ⟨True.intro, ih k _ completed hvalues.2⟩

theorem run_testEvents_causal
    (processing processing' : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel k : ℕ)
    (hvalues :
      (testValues (Online.run .infinite (Online.fixedOracle processing)
        strategy fuel).config.transcript).take k =
      (testValues (Online.run .infinite (Online.fixedOracle processing')
        strategy fuel).config.transcript).take k) :
    (testEvents (Online.run .infinite (Online.fixedOracle processing)
        strategy fuel).config.transcript).take (k + 1) =
      (testEvents (Online.run .infinite (Online.fixedOracle processing')
        strategy fuel).config.transcript).take (k + 1) := by
  rw [run_transcript_eq_runWord, run_transcript_eq_runWord] at hvalues ⊢
  simpa [testEvents] using
    runWord_testEvents_causal processing processing' strategy fuel k
      (Online.Config.initial n) 0 hvalues

def runTestEvent (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) (rank : Fin n) : Online.Label n × ℕ :=
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  testEventAt transcript
    (by
      simpa [transcript, testEvents] using
        Online.testResults_length_eq_n_of_all_done
          (Online.fixedOracle processing) strategy fuel hdone)
    rank

theorem runTestEvent_fst (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) (rank : Fin n) :
    (runTestEvent processing strategy fuel hdone rank).1 =
      runTestOrder processing strategy fuel hdone rank := by
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  have hevents : (testEvents transcript).length = n := by
    simpa [transcript, testEvents] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle processing) strategy fuel hdone
  have hlabels : (testLabels transcript).length = n := by
    simpa [transcript, testLabels] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle processing) strategy fuel hdone
  have hnodup : (testLabels transcript).Nodup := by
    simpa [transcript, testLabels] using
      (Online.run_testingInvariant
        (Online.fixedOracle processing) strategy fuel).testNodup
  simpa [runTestEvent, runTestOrder, transcript] using
    testEventAt_fst transcript hevents hlabels hnodup rank

theorem runTestEvent_snd (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) (rank : Fin n) :
    (runTestEvent processing strategy fuel hdone rank).2 =
      runCompletedBefore processing strategy fuel hdone rank := by
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  have hevents : (testEvents transcript).length = n := by
    simpa [transcript, testEvents] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle processing) strategy fuel hdone
  have hbefore : (processedBeforeTests transcript).length = n := by
    simpa [transcript, processedBeforeTests] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle processing) strategy fuel hdone
  simpa [runTestEvent, runCompletedBefore, transcript] using
    testEventAt_snd transcript hevents hbefore rank

theorem run_testValues_eq_ofFn (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.jobs job =
        .done) :
    testValues
        (Online.run .infinite
          (Online.fixedOracle processing) strategy fuel).config.transcript =
      List.ofFn (fun rank : Fin n =>
        processing (runTestOrder processing strategy fuel hdone rank)) := by
  let transcript :=
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel).config.transcript
  have hmatch : transcript.TestsMatch processing := by
    simpa [transcript] using run_testsMatch processing strategy fuel
  have hlabels : (testLabels transcript).length = n := by
    simpa [transcript, testLabels] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle processing) strategy fuel hdone
  have hnodup : (testLabels transcript).Nodup := by
    simpa [transcript, testLabels] using
      (Online.run_testingInvariant
        (Online.fixedOracle processing) strategy fuel).testNodup
  have horder := RandomizedOptional.ObservedTrace.listOrderPerm_ofFn
    (testLabels transcript) hlabels hnodup
  calc
    testValues
        (Online.run .infinite
          (Online.fixedOracle processing) strategy fuel).config.transcript =
          (testLabels transcript).map processing := by
      simpa [transcript] using
        testValues_eq_testLabels_map processing transcript hmatch
    _ = (List.ofFn
          (testOrder transcript hlabels hnodup)).map processing := by
      simpa [testOrder] using congrArg (List.map processing) horder.symm
    _ = List.ofFn (fun rank : Fin n =>
          processing (runTestOrder processing strategy fuel hdone rank)) := by
      rw [List.map_ofFn]
      rfl

/-- Replacing one all-`H` label by zero is unobservable before that label's
test.  Consequently its test rank and the number of long jobs processed
before that test are identical in the two literal fixed-input runs. -/
theorem allHigh_oneZero_same_rank_completed {H : ℝ}
    (strategy : Online.Strategy n) (fuel : ℕ) (label : Fin n)
    (hdoneHigh : ∀ job,
      (Online.run .infinite
        (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.jobs job =
          .done)
    (hdoneZero : ∀ job,
      (Online.run .infinite
        (Online.fixedOracle (oneZeroProcessing H label)) strategy fuel).config.jobs job =
          .done) :
    let highOrder :=
      runTestOrder (allHighProcessing H) strategy fuel hdoneHigh
    let zeroOrder :=
      runTestOrder (oneZeroProcessing H label) strategy fuel hdoneZero
    let highRank := highOrder.symm label
    let zeroRank := zeroOrder.symm label
    highRank = zeroRank ∧
      runCompletedBefore (allHighProcessing H) strategy fuel hdoneHigh highRank =
        runCompletedBefore (oneZeroProcessing H label) strategy fuel
          hdoneZero zeroRank := by
  dsimp
  let highOrder :=
    runTestOrder (allHighProcessing H) strategy fuel hdoneHigh
  let zeroOrder :=
    runTestOrder (oneZeroProcessing H label) strategy fuel hdoneZero
  let highRank := highOrder.symm label
  let zeroRank := zeroOrder.symm label
  let kNat := min highRank.val zeroRank.val
  have hklt : kNat < n :=
    lt_of_le_of_lt (min_le_left _ _) highRank.isLt
  let k : Fin n := ⟨kNat, hklt⟩
  have hvalues :
      (testValues
        (Online.run .infinite
          (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.transcript).take
            kNat =
      (testValues
        (Online.run .infinite
          (Online.fixedOracle (oneZeroProcessing H label)) strategy fuel).config.transcript).take
            kNat := by
    rw [run_testValues_eq_ofFn (allHighProcessing H) strategy fuel hdoneHigh,
      run_testValues_eq_ofFn (oneZeroProcessing H label) strategy fuel hdoneZero]
    apply RandomizedOptional.TraceBijection.take_ofFn_eq_of_prefix
    intro rank hrank
    have hrankZero : rank.val < zeroRank.val :=
      lt_of_lt_of_le hrank (min_le_right _ _)
    have hnotLabel : zeroOrder rank ≠ label := by
      intro heq
      have hrankEq : rank = zeroRank := by
        apply zeroOrder.injective
        simpa [zeroRank] using heq
      rw [hrankEq] at hrankZero
      exact (Nat.lt_irrefl _ hrankZero)
    simp [allHighProcessing, oneZeroProcessing, highOrder, zeroOrder,
      hnotLabel]
  have hevents := run_testEvents_causal
    (allHighProcessing H) (oneZeroProcessing H label) strategy fuel kNat hvalues
  let highEvents := testEvents
    (Online.run .infinite
      (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.transcript
  let zeroEvents := testEvents
    (Online.run .infinite
      (Online.fixedOracle (oneZeroProcessing H label)) strategy fuel).config.transcript
  have hhighLength : highEvents.length = n := by
    simpa [highEvents, testEvents] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle (allHighProcessing H)) strategy fuel hdoneHigh
  have hzeroLength : zeroEvents.length = n := by
    simpa [zeroEvents, testEvents] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle (oneZeroProcessing H label)) strategy fuel hdoneZero
  have hget :
      highEvents.get ⟨kNat, by simpa [hhighLength] using hklt⟩ =
        zeroEvents.get ⟨kNat, by simpa [hzeroLength] using hklt⟩ := by
    apply RandomizedOptional.TraceBijection.get_eq_of_take_succ_eq
    simpa [highEvents, zeroEvents] using hevents
  have hpair :
      runTestEvent (allHighProcessing H) strategy fuel hdoneHigh k =
        runTestEvent (oneZeroProcessing H label) strategy fuel hdoneZero k := by
    simpa [runTestEvent, testEventAt, highEvents, zeroEvents, k] using hget
  have hpairLabel := congrArg Prod.fst hpair
  rw [runTestEvent_fst, runTestEvent_fst] at hpairLabel
  have hpairCompleted := congrArg Prod.snd hpair
  rw [runTestEvent_snd, runTestEvent_snd] at hpairCompleted
  have hranks : highRank = zeroRank := by
    rcases le_total highRank.val zeroRank.val with hle | hle
    · have hkhigh : k = highRank := by
        apply Fin.ext
        exact min_eq_left hle
      have hzeroLabel : zeroOrder k = label := by
        rw [← hpairLabel, hkhigh]
        simp [highRank, highOrder]
      have hkzero : k = zeroRank := by
        apply zeroOrder.injective
        simpa [zeroRank] using hzeroLabel
      exact hkhigh.symm.trans hkzero
    · have hkzero : k = zeroRank := by
        apply Fin.ext
        exact min_eq_right hle
      have hhighLabel : highOrder k = label := by
        rw [hpairLabel, hkzero]
        simp [zeroRank, zeroOrder]
      have hkhigh : k = highRank := by
        apply highOrder.injective
        simpa [highRank] using hhighLabel
      exact hkhigh.symm.trans hkzero
  refine ⟨hranks, ?_⟩
  change runCompletedBefore (allHighProcessing H) strategy fuel hdoneHigh highRank =
    runCompletedBefore (oneZeroProcessing H label) strategy fuel hdoneZero zeroRank
  have hkhigh : k = highRank := by
    apply Fin.ext
    dsimp [k, kNat]
    rw [hranks]
    simp
  have hcompleted := hpairCompleted
  rw [hkhigh] at hcompleted
  simpa [hranks] using hcompleted

def highProcessedCount (zero : Online.Label n) : Online.Transcript n → ℕ
  | [] => 0
  | .processed job :: rest =>
      (if job = zero then 0 else 1) + highProcessedCount zero rest
  | _ :: rest => highProcessedCount zero rest

def zeroTestCount (zero : Online.Label n) : Online.Transcript n → ℕ
  | [] => 0
  | .testResult job _ :: rest =>
      (if job = zero then 1 else 0) + zeroTestCount zero rest
  | _ :: rest => zeroTestCount zero rest

/-- Sum of the completion-suffix multiplicities of the nonzero process
observations.  Multiplication by `H` is exactly their contribution to the
suffix-weighted cost. -/
def highCompletionArea (H : ℝ) (zero : Online.Label n) :
    Online.Transcript n → ℕ
  | [] => 0
  | .processed job :: rest =>
      (if job = zero then 0
        else Online.completionCount (oneZeroProcessing H zero)
          (.processed job :: rest)) +
        highCompletionArea H zero rest
  | _ :: rest => highCompletionArea H zero rest

/-- Extra suffix multiplicity supplied by the exceptional zero completion
to long processes lying before its test. -/
def zeroCarry (zero : Online.Label n) : Online.Transcript n → ℕ
  | [] => 0
  | .processed job :: rest =>
      (if job = zero then 0 else zeroTestCount zero rest) + zeroCarry zero rest
  | _ :: rest => zeroCarry zero rest

def processesBeforeTestAux (zero : Online.Label n) :
    Online.Transcript n → ℕ → ℕ
  | [], completed => completed
  | .testResult job _ :: rest, completed =>
      if job = zero then completed
      else processesBeforeTestAux zero rest completed
  | .processed _ :: rest, completed =>
      processesBeforeTestAux zero rest (completed + 1)
  | .rawCompleted _ :: rest, completed =>
      processesBeforeTestAux zero rest completed

def processesBeforeTest (zero : Online.Label n)
    (transcript : Online.Transcript n) : ℕ :=
  processesBeforeTestAux zero transcript 0

def zeroProcessesBeforeTestAux (zero : Online.Label n) :
    Online.Transcript n → ℕ
  | [] => 0
  | .testResult job _ :: rest =>
      if job = zero then 0 else zeroProcessesBeforeTestAux zero rest
  | .processed job :: rest =>
      (if job = zero then 1 else 0) + zeroProcessesBeforeTestAux zero rest
  | .rawCompleted _ :: rest => zeroProcessesBeforeTestAux zero rest

def zeroProcessesBeforeTest (zero : Online.Label n)
    (transcript : Online.Transcript n) : ℕ :=
  zeroProcessesBeforeTestAux zero transcript

theorem triangle_succ (m : ℕ) :
    (m + 1) * (m + 1 + 1) / 2 =
      m * (m + 1) / 2 + (m + 1) := by
  have h := Nat.triangle_succ (m + 1)
  simpa [Nat.add_sub_cancel, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Nat.mul_comm] using h

theorem completionCount_oneZero_eq
    {H : ℝ} (hH : H ≠ 0) (zero : Online.Label n)
    (transcript : Online.Transcript n) (hnoraw : NoRaw transcript)
    (hmatch : transcript.TestsMatch (oneZeroProcessing H zero)) :
    Online.completionCount (oneZeroProcessing H zero) transcript =
      highProcessedCount zero transcript + zeroTestCount zero transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hnorawRest : NoRaw rest := by
        intro job hmem
        exact hnoraw job (by simp [hmem])
      have hmatchRest : Online.Transcript.TestsMatch
          (oneZeroProcessing H zero) rest := by
        intro job p hmem
        apply hmatch job p
        cases observation with
        | testResult touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
        | processed touched => exact hmem
        | rawCompleted touched => exact hmem
      cases observation with
      | testResult job p =>
          have hp := hmatch job p (by simp)
          by_cases hjob : job = zero
          · subst job
            simp [Online.completionCount, Online.Observation.completionLabel,
              oneZeroProcessing, highProcessedCount, zeroTestCount,
              hH, ih hnorawRest hmatchRest] at hp ⊢
            simp [hp]
            omega
          · have hp' : p = H := by
              simpa [oneZeroProcessing, hjob] using hp
            simp [Online.completionCount, Online.Observation.completionLabel,
              highProcessedCount, zeroTestCount, hjob, hp', hH,
              ih hnorawRest hmatchRest]
      | processed job =>
          by_cases hjob : job = zero
          · subst job
            simp [Online.completionCount, Online.Observation.completionLabel,
              oneZeroProcessing, highProcessedCount, zeroTestCount,
              ih hnorawRest hmatchRest]
          · simp [Online.completionCount, Online.Observation.completionLabel,
              oneZeroProcessing, highProcessedCount, zeroTestCount, hjob, hH,
              ih hnorawRest hmatchRest]
            omega
      | rawCompleted job => exact (hnoraw job (by simp)).elim

theorem highCompletionArea_eq_rank_add_carry
    {H : ℝ} (hH : H ≠ 0) (zero : Online.Label n)
    (transcript : Online.Transcript n) (hnoraw : NoRaw transcript)
    (hmatch : transcript.TestsMatch (oneZeroProcessing H zero)) :
    highCompletionArea H zero transcript =
      highProcessedCount zero transcript *
          (highProcessedCount zero transcript + 1) / 2 +
        zeroCarry zero transcript := by
  induction transcript with
  | nil => simp [highCompletionArea, highProcessedCount, zeroCarry]
  | cons observation rest ih =>
      have hnorawRest : NoRaw rest := by
        intro job hmem
        exact hnoraw job (by simp [hmem])
      have hmatchRest : Online.Transcript.TestsMatch
          (oneZeroProcessing H zero) rest := by
        intro job p hmem
        apply hmatch job p
        cases observation with
        | testResult touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
        | processed touched => exact hmem
        | rawCompleted touched => exact hmem
      cases observation with
      | testResult job p =>
          simpa [highCompletionArea, highProcessedCount, zeroCarry] using
            ih hnorawRest hmatchRest
      | rawCompleted job => exact (hnoraw job (by simp)).elim
      | processed job =>
          by_cases hjob : job = zero
          · subst job
            simpa [highCompletionArea, highProcessedCount, zeroCarry] using
              ih hnorawRest hmatchRest
          · rw [highCompletionArea, if_neg hjob,
              completionCount_oneZero_eq hH zero
                (.processed job :: rest) hnoraw hmatch,
              ih hnorawRest hmatchRest]
            simp [highProcessedCount, zeroTestCount, zeroCarry, hjob]
            simp only [Nat.one_add]
            rw [triangle_succ]
            omega

theorem oneZero_completionCost_ge_highArea
    {H : ℝ} (hH : 0 ≤ H) (zero : Online.Label n)
    (transcript : Online.Transcript n) (hnoraw : NoRaw transcript) :
    H * highCompletionArea H zero transcript ≤
      Online.completionCost .infinite (oneZeroProcessing H zero) transcript := by
  rw [Online.completionCost_eq_suffixWeightedDuration]
  induction transcript with
  | nil => simp [Online.suffixWeightedDuration, highCompletionArea]
  | cons observation rest ih =>
      have hnorawRest : NoRaw rest := by
        intro job hmem
        exact hnoraw job (by simp [hmem])
      cases observation with
      | testResult job p =>
          simp only [Online.suffixWeightedDuration,
            Online.Observation.duration, highCompletionArea]
          have hcount : 0 ≤
              (Online.completionCount (oneZeroProcessing H zero)
                (.testResult job p :: rest) : ℝ) := by positivity
          linarith [ih hnorawRest]
      | processed job =>
          by_cases hjob : job = zero
          · subst job
            simp [Online.suffixWeightedDuration, Online.Observation.duration,
              oneZeroProcessing, highCompletionArea, ih hnorawRest]
          · simp only [Online.suffixWeightedDuration,
              Online.Observation.duration, oneZeroProcessing, hjob,
              if_false, highCompletionArea]
            push_cast
            nlinarith [ih hnorawRest]
      | rawCompleted job => exact (hnoraw job (by simp)).elim

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
          (fun x : ℕ => (x : ℝ))).sum =
      (testCount transcript : ℝ) *
        ((completed : ℝ) + processedCount transcript) := by
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
                  (fun x : ℕ => (x : ℝ))).sum) = _
          calc
            _ = (processedCount rest : ℝ) + completed +
                (testSuffixProcessArea rest +
                  ((processedBeforeTestsAux rest completed).map
                    (fun x : ℕ => (x : ℝ))).sum) := by ring
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

/-- On a literal completed all-`H` run, subtracting the immediate
test--process comparison schedule leaves exactly the rank-gap statistic used
by the finite averaging lower bound. -/
theorem allHigh_operational_gap_eq_rankGaps
    {H : ℝ} (hH : 0 < H) (strategy : Online.Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (Online.run .infinite
        (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.jobs job =
          .done) :
    Online.completionCost .infinite (allHighProcessing H)
        (Online.run .infinite
          (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.transcript -
        (H + 1) * (n : ℝ) * (n + 1) / 2 =
      ∑ rank, ObligatoryUnbounded.rankGap
        (runCompletedBefore (allHighProcessing H) strategy fuel hdone) rank := by
  let transcript :=
    (Online.run .infinite
      (Online.fixedOracle (allHighProcessing H)) strategy fuel).config.transcript
  have hHne : H ≠ 0 := ne_of_gt hH
  have hnoraw : NoRaw transcript := by
    simpa [transcript] using
      run_noRaw (Online.fixedOracle (allHighProcessing H)) strategy fuel
  have hmatch := run_testsMatch (allHighProcessing H) strategy fuel
  have htests : TestsHaveValue H transcript := by
    intro job p hmem
    have hp := hmatch job p (by simpa [transcript] using hmem)
    simpa [allHighProcessing] using hp
  have hprocessed : processedCount transcript = n := by
    simpa [transcript] using
      processedCount_eq_n_of_all_done
        (allHighProcessing H) strategy fuel hdone
  have htestedLength : transcript.testResults.length = n := by
    simpa [transcript] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle (allHighProcessing H)) strategy fuel hdone
  have htested : testCount transcript = n := by
    simpa using htestedLength
  have hbeforeLength : (processedBeforeTests transcript).length = n := by
    simpa [processedBeforeTests] using htestedLength
  have hsumBefore :
      (∑ rank,
        (runCompletedBefore (allHighProcessing H) strategy fuel hdone rank : ℝ)) =
        ((processedBeforeTests transcript).map (fun x : ℕ => (x : ℝ))).sum := by
    simpa [runCompletedBefore, transcript] using
      sum_completedBeforeAt transcript hbeforeLength
  have hareaRaw := testArea_add_processedBefore_sum transcript 0
  have harea : testSuffixProcessArea transcript +
      ((processedBeforeTests transcript).map (fun x : ℕ => (x : ℝ))).sum =
      (testCount transcript : ℝ) * (processedCount transcript : ℝ) := by
    simpa [processedBeforeTests] using hareaRaw
  rw [htested, hprocessed] at harea
  have hprocessArea := processSuffixRankArea_eq transcript
  rw [hprocessed] at hprocessArea
  have hcost := allHigh_completionCost_eq_areas
    hHne transcript hnoraw htests
  change Online.completionCost .infinite (allHighProcessing H) transcript -
      (H + 1) * (n : ℝ) * (n + 1) / 2 = _
  simp only [ObligatoryUnbounded.rankGap]
  rw [Finset.sum_sub_distrib]
  rw [ObligatoryUnbounded.sum_rankValues, hsumBefore]
  rw [hcost, hprocessArea]
  push_cast at harea hprocessArea ⊢
  nlinarith

theorem zeroTestCount_eq_count (zero : Online.Label n)
    (transcript : Online.Transcript n) :
    zeroTestCount zero transcript = (testLabels transcript).count zero := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hjob : job = zero <;>
            simp [zeroTestCount, testLabels, Online.Transcript.testResults,
              Online.Observation.testResult?, hjob, ih] <;> omega
      | processed job =>
          simpa [zeroTestCount, testLabels, Online.Transcript.testResults,
            Online.Observation.testResult?] using ih
      | rawCompleted job =>
          simpa [zeroTestCount, testLabels, Online.Transcript.testResults,
            Online.Observation.testResult?] using ih

theorem zeroCarry_eq_zero_of_zeroTestCount_eq_zero
    (zero : Online.Label n) (transcript : Online.Transcript n)
    (hzero : zeroTestCount zero transcript = 0) :
    zeroCarry zero transcript = 0 := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          have hrest : zeroTestCount zero rest = 0 := by
            by_cases hjob : job = zero <;>
              simp [zeroTestCount, hjob] at hzero ⊢ <;> assumption
          simpa [zeroCarry] using ih hrest
      | processed job =>
          have hrest : zeroTestCount zero rest = 0 := by
            simpa [zeroTestCount] using hzero
          by_cases hjob : job = zero <;>
            simp [zeroCarry, hjob, hrest, ih hrest]
      | rawCompleted job =>
          have hrest : zeroTestCount zero rest = 0 := by
            simpa [zeroTestCount] using hzero
          simpa [zeroCarry] using ih hrest

theorem carry_add_zeroProcesses_eq_processesBefore
    (zero : Online.Label n) (transcript : Online.Transcript n)
    (completed : ℕ) (hone : zeroTestCount zero transcript = 1) :
    zeroCarry zero transcript + zeroProcessesBeforeTestAux zero transcript +
        completed =
      processesBeforeTestAux zero transcript completed := by
  induction transcript generalizing completed with
  | nil => simp [zeroTestCount] at hone
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hjob : job = zero
          · subst job
            have hrest : zeroTestCount zero rest = 0 := by
              simp [zeroTestCount] at hone
              omega
            have hcarry := zeroCarry_eq_zero_of_zeroTestCount_eq_zero
              zero rest hrest
            simp [zeroCarry, zeroProcessesBeforeTestAux,
              processesBeforeTestAux, hcarry]
          · have hrest : zeroTestCount zero rest = 1 := by
              simpa [zeroTestCount, hjob] using hone
            simpa [zeroCarry, zeroProcessesBeforeTestAux,
              processesBeforeTestAux, hjob] using ih completed hrest
      | processed job =>
          have hrest : zeroTestCount zero rest = 1 := by
            simpa [zeroTestCount] using hone
          have hrec := ih (completed + 1) hrest
          by_cases hjob : job = zero <;>
            simp [zeroCarry, zeroProcessesBeforeTestAux,
              processesBeforeTestAux, hjob, hrest] at hrec ⊢ <;> omega
      | rawCompleted job =>
          have hrest : zeroTestCount zero rest = 1 := by
            simpa [zeroTestCount] using hone
          simpa [zeroCarry, zeroProcessesBeforeTestAux,
            processesBeforeTestAux] using ih completed hrest

theorem zeroProcessesBeforeTest_le_count (zero : Online.Label n)
    (transcript : Online.Transcript n) :
    zeroProcessesBeforeTest zero transcript ≤
      transcript.processedLabels.count zero := by
  unfold zeroProcessesBeforeTest
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hjob : job = zero
          · simp [zeroProcessesBeforeTestAux,
              Online.Transcript.processedLabels, hjob]
          · simpa [zeroProcessesBeforeTestAux,
              Online.Transcript.processedLabels, hjob] using ih
      | processed job =>
          by_cases hjob : job = zero
          · subst job
            have h := Nat.add_le_add_left ih 1
            simpa [zeroProcessesBeforeTestAux,
              Online.Transcript.processedLabels, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using h
          · simpa [zeroProcessesBeforeTestAux,
              Online.Transcript.processedLabels, hjob] using ih
      | rawCompleted job =>
          simpa [zeroProcessesBeforeTestAux,
            Online.Transcript.processedLabels] using ih

theorem processesBeforeTestAux_eq_of_event_mem
    (zero : Online.Label n) (transcript : Online.Transcript n)
    (completed X : ℕ) (hnodup : (testLabels transcript).Nodup)
    (hmem : (zero, X) ∈ testEventsAux transcript completed) :
    processesBeforeTestAux zero transcript completed = X := by
  induction transcript generalizing completed with
  | nil => simp [testEventsAux] at hmem
  | cons observation rest ih =>
      cases observation with
      | processed job =>
          apply ih (completed + 1)
          · simpa [testLabels, Online.Transcript.testResults,
              Online.Observation.testResult?] using hnodup
          · simpa [testEventsAux] using hmem
      | rawCompleted job =>
          apply ih completed
          · simpa [testLabels, Online.Transcript.testResults,
              Online.Observation.testResult?] using hnodup
          · simpa [testEventsAux] using hmem
      | testResult job p =>
          have hcons : (job :: testLabels rest).Nodup := by
            simpa [testLabels, Online.Transcript.testResults,
              Online.Observation.testResult?] using hnodup
          by_cases hjob : job = zero
          · subst job
            have hnot : zero ∉ testLabels rest :=
              (List.nodup_cons.mp hcons).1
            have hnotEvent : (zero, X) ∉ testEventsAux rest completed := by
              intro hevent
              apply hnot
              rw [← testEvents_map_fst rest completed]
              exact List.mem_map.mpr ⟨(zero, X), hevent, rfl⟩
            have hcases : (zero, X) = (zero, completed) ∨
                (zero, X) ∈ testEventsAux rest completed := by
              simpa [testEventsAux] using hmem
            rcases hcases with hhead | htail
            · have hX : completed = X := (congrArg Prod.snd hhead).symm
              simpa [processesBeforeTestAux, hX]
            · exact (hnotEvent htail).elim
          · have hrestNodup : (testLabels rest).Nodup := by
              exact (List.nodup_cons.mp hcons).2
            have hmemRest : (zero, X) ∈ testEventsAux rest completed := by
              have hcases : (zero, X) = (job, completed) ∨
                  (zero, X) ∈ testEventsAux rest completed := by
                simpa [testEventsAux] using hmem
              rcases hcases with hhead | htail
              · have heq : zero = job := congrArg Prod.fst hhead
                exact (hjob heq.symm).elim
              · exact htail
            simpa [processesBeforeTestAux, hjob] using
              ih completed hrestNodup hmemRest

theorem highProcessedCount_add_zero_count (zero : Online.Label n)
    (transcript : Online.Transcript n) :
    highProcessedCount zero transcript +
        transcript.processedLabels.count zero = processedCount transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [highProcessedCount, processedCount,
            Online.Transcript.processedLabels] using ih
      | rawCompleted job =>
          simpa [highProcessedCount, processedCount,
            Online.Transcript.processedLabels] using ih
      | processed job =>
          by_cases hjob : job = zero
          · subst job
            rw [highProcessedCount, processedCount,
              Online.Transcript.processedLabels]
            simp only [List.filterMap_cons]
            simp
            change highProcessedCount zero rest +
                (Online.Transcript.processedLabels rest).count zero + 1 =
              (Online.Transcript.processedLabels rest).length + 1
            rw [← processedCount_eq_processedLabels_length]
            omega
          · rw [highProcessedCount, processedCount,
              Online.Transcript.processedLabels]
            simp only [List.filterMap_cons]
            simp [hjob]
            change 1 + highProcessedCount zero rest +
                (Online.Transcript.processedLabels rest).count zero =
              (Online.Transcript.processedLabels rest).length + 1
            rw [← processedCount_eq_processedLabels_length]
            omega

theorem cast_triangle (m : ℕ) :
    ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [triangle_succ]
      push_cast
      rw [ih]
      ring

/-- Literal one-zero cost lower bound.  The harmless `-H` remainder allows
for one administrative zero-process observation in the prefix; lifecycle
uniqueness shows there can be no more than one. -/
theorem oneZero_operational_cost_ge
    {H : ℝ} (hH : 0 ≤ H) (hHne : H ≠ 0)
    (strategy : Online.Strategy n) (fuel : ℕ) (zero : Fin n)
    (hn : 0 < n)
    (hdone : ∀ job,
      (Online.run .infinite
        (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel).config.jobs job =
          .done) :
    let zeroRank :=
      (runTestOrder (oneZeroProcessing H zero) strategy fuel hdone).symm zero
    let X := runCompletedBefore (oneZeroProcessing H zero) strategy fuel
      hdone zeroRank
    H * ((n : ℝ) * (n - 1) / 2 + X - 1) ≤
      Online.completionCost .infinite (oneZeroProcessing H zero)
        (Online.run .infinite
          (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel).config.transcript := by
  dsimp
  let transcript :=
    (Online.run .infinite
      (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel).config.transcript
  let order := runTestOrder (oneZeroProcessing H zero) strategy fuel hdone
  let rank := order.symm zero
  let X := runCompletedBefore (oneZeroProcessing H zero) strategy fuel hdone rank
  have hnoraw : NoRaw transcript := by
    simpa [transcript] using
      run_noRaw (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel
  have hmatch : transcript.TestsMatch (oneZeroProcessing H zero) := by
    simpa [transcript] using
      run_testsMatch (oneZeroProcessing H zero) strategy fuel
  have htesting := Online.run_testingInvariant
    (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel
  have hlabelsNodup : (testLabels transcript).Nodup := by
    simpa [transcript, testLabels] using htesting.testNodup
  have hlabelsLength : (testLabels transcript).length = n := by
    simpa [transcript, testLabels] using
      Online.testResults_length_eq_n_of_all_done
        (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel hdone
  have hzeroMem : zero ∈ testLabels transcript := by
    have horder := RandomizedOptional.ObservedTrace.listOrderPerm_ofFn
      (testLabels transcript) hlabelsLength hlabelsNodup
    rw [← horder]
    exact List.mem_ofFn.mpr ⟨
      (RandomizedOptional.ObservedTrace.listOrderPerm
        (testLabels transcript) hlabelsLength hlabelsNodup).symm zero,
      by simp⟩
  have honeTest : zeroTestCount zero transcript = 1 := by
    rw [zeroTestCount_eq_count]
    simpa [hzeroMem] using hlabelsNodup.count (a := zero)
  have hprocess := run_processHistoryInvariant
    (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel
  have hprocessedPerm :=
    processedLabels_perm_of_all_done
      (oneZeroProcessing H zero) strategy fuel hdone
  have hprocessedMem : zero ∈ transcript.processedLabels := by
    exact hprocessedPerm.mem_iff.mpr (by simp)
  have honeProcessed : transcript.processedLabels.count zero = 1 := by
    have hnodupProcessed : transcript.processedLabels.Nodup := by
      simpa [transcript] using hprocess.processedNodup
    rw [hnodupProcessed.count, if_pos hprocessedMem]
  have hprocessedCount : processedCount transcript = n := by
    simpa [transcript] using processedCount_eq_n_of_all_done
      (oneZeroProcessing H zero) strategy fuel hdone
  have hhighCount : highProcessedCount zero transcript = n - 1 := by
    have hpartition := highProcessedCount_add_zero_count zero transcript
    rw [honeProcessed, hprocessedCount] at hpartition
    omega
  have hfst := runTestEvent_fst
    (oneZeroProcessing H zero) strategy fuel hdone rank
  have hsnd := runTestEvent_snd
    (oneZeroProcessing H zero) strategy fuel hdone rank
  have heventEq :
      runTestEvent (oneZeroProcessing H zero) strategy fuel hdone rank =
        (zero, X) := by
    apply Prod.ext
    · simpa [order, rank] using hfst
    · simpa [X] using hsnd
  have heventMem : (zero, X) ∈ testEvents transcript := by
    have heventsLength : (testEvents transcript).length = n := by
      simpa [transcript, testEvents] using
        Online.testResults_length_eq_n_of_all_done
          (Online.fixedOracle (oneZeroProcessing H zero)) strategy fuel hdone
    let eventRank : Fin (testEvents transcript).length :=
      Fin.cast heventsLength.symm rank
    rw [← heventEq]
    simpa [runTestEvent, testEventAt, transcript] using
      List.get_mem (testEvents transcript) eventRank
  have hbefore : processesBeforeTest zero transcript = X := by
    unfold processesBeforeTest
    apply processesBeforeTestAux_eq_of_event_mem zero transcript 0 X
      hlabelsNodup
    simpa [testEvents] using heventMem
  have hzeroProcesses : zeroProcessesBeforeTest zero transcript ≤ 1 := by
    exact (zeroProcessesBeforeTest_le_count zero transcript).trans_eq
      honeProcessed
  have hcarryIdentity :=
    carry_add_zeroProcesses_eq_processesBefore zero transcript 0 honeTest
  have hcarry : (X : ℝ) - 1 ≤ zeroCarry zero transcript := by
    change zeroCarry zero transcript + zeroProcessesBeforeTest zero transcript =
      processesBeforeTest zero transcript at hcarryIdentity
    rw [hbefore] at hcarryIdentity
    have hx : (X : ℝ) ≤ zeroCarry zero transcript + 1 := by
      exact_mod_cast (show X ≤ zeroCarry zero transcript + 1 by omega)
    linarith
  have harea := highCompletionArea_eq_rank_add_carry
    hHne zero transcript hnoraw hmatch
  have hcost := oneZero_completionCost_ge_highArea
    hH zero transcript hnoraw
  rw [hhighCount] at harea
  have hcast := cast_triangle (n - 1)
  have hareaR : (highCompletionArea H zero transcript : ℝ) =
      (((n - 1) * (n - 1 + 1) / 2 : ℕ) : ℝ) +
        (zeroCarry zero transcript : ℝ) := by
    exact_mod_cast harea
  rw [hcast] at hareaR
  rw [Nat.cast_sub (by omega : 1 ≤ n)] at hareaR
  change H * ((n : ℝ) * (n - 1) / 2 + X - 1) ≤ _
  rw [hareaR] at hcost
  have hbase :
      (n - 1 : ℝ) * n / 2 + (X - 1) ≤
        (n - 1 : ℝ) * n / 2 + zeroCarry zero transcript := by
    linarith
  nlinarith

/-! ## End-to-end finite-seed impossibility theorem -/

/-- Completion cost of one literal fixed-input run. -/
def operationalCost (processing : Online.Label n → ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ) : ℝ :=
  Online.runCompletionCost .infinite processing
    (Online.run .infinite (Online.fixedOracle processing) strategy fuel)

/-- Cost of the announced policy that tests and immediately processes every
job on the all-long input. -/
def allHighImmediateComparisonCost (n : ℕ) (H : ℝ) : ℝ :=
  (H + 1) * n * (n + 1) / 2

/-- The random-test-order announced comparator on a one-zero input has at
most this cost.  The first term is its SPT processing area; `n²` is the
worst possible displacement cost of its unit tests. -/
def oneZeroRandomOrderComparisonUpper (n : ℕ) (H : ℝ) : ℝ :=
  H * n * (n - 1) / 2 + n ^ 2

theorem uniformAverage_sub_const
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (c : ℝ) :
    Randomized.uniformAverage (fun seed ↦ f seed - c) =
      Randomized.uniformAverage f - c := by
  calc
    Randomized.uniformAverage (fun seed ↦ f seed - c) =
        Randomized.uniformAverage (fun seed ↦ f seed + (-c)) := rfl
    _ = Randomized.uniformAverage f +
        Randomized.uniformAverage (fun _seed : Ω ↦ -c) :=
      Randomized.uniformAverage_add _ _
    _ = Randomized.uniformAverage f - c := by
      rw [Randomized.uniformAverage_const]
      ring

/-- Every completing finite-private-seed obligatory-testing policy loses by
`n²/8` on one fixed input in `[0,n²]`, relative to the corresponding
announced comparison schedule.  The input is either all `n²`, or has one
fixed oblivious zero label and all other jobs equal to `n²`.

This theorem closes the operational bridge: `strategy seed` is a literal
transcript-only `Online.Strategy`, both alternatives use its actual run cost,
and the exceptional label is selected only after averaging over the finite
private seed. -/
theorem finiteSeed_exists_operational_quadratic_gap
    {n : ℕ} (hn : 7 ≤ n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (strategy : Ω → Online.Strategy n) (fuel : ℕ)
    (hdoneHigh : ∀ seed job,
      (Online.run .infinite
        (Online.fixedOracle (allHighProcessing ((n : ℝ) ^ 2)))
        (strategy seed) fuel).config.jobs job = .done)
    (hdoneZero : ∀ seed label job,
      (Online.run .infinite
        (Online.fixedOracle
          (oneZeroProcessing ((n : ℝ) ^ 2) label))
        (strategy seed) fuel).config.jobs job = .done) :
    (n : ℝ) ^ 2 / 8 ≤
        Randomized.uniformAverage (fun seed ↦
          operationalCost (allHighProcessing ((n : ℝ) ^ 2))
            (strategy seed) fuel) -
          allHighImmediateComparisonCost n ((n : ℝ) ^ 2) ∨
      ∃ label,
        (n : ℝ) ^ 2 / 8 <
          Randomized.uniformAverage (fun seed ↦
            operationalCost (oneZeroProcessing ((n : ℝ) ^ 2) label)
              (strategy seed) fuel) -
            oneZeroRandomOrderComparisonUpper n ((n : ℝ) ^ 2) := by
  let H : ℝ := (n : ℝ) ^ 2
  let order : Ω → Equiv.Perm (Fin n) := fun seed ↦
    runTestOrder (allHighProcessing H) (strategy seed) fuel
      (by simpa [H] using hdoneHigh seed)
  let completedBefore : Ω → Fin n → ℕ := fun seed ↦
    runCompletedBefore (allHighProcessing H) (strategy seed) fuel
      (by simpa [H] using hdoneHigh seed)
  let oneZeroGap : Fin n → ℝ := fun label ↦
    Randomized.uniformAverage (fun seed ↦
      operationalCost (oneZeroProcessing H label) (strategy seed) fuel) -
        oneZeroRandomOrderComparisonUpper n H
  have hH : 0 < H := by
    dsimp [H]
    positivity
  have hone : ∀ label,
      Randomized.uniformAverage (fun seed ↦
        ObligatoryUnbounded.exceptionalZeroCharge (order seed)
          (completedBefore seed) H label) - 2 * n ^ 2 ≤
        oneZeroGap label := by
    intro label
    have hpoint : ∀ seed,
        ObligatoryUnbounded.exceptionalZeroCharge (order seed)
            (completedBefore seed) H label - 2 * n ^ 2 ≤
          operationalCost (oneZeroProcessing H label) (strategy seed) fuel -
            oneZeroRandomOrderComparisonUpper n H := by
      intro seed
      have hsame := allHigh_oneZero_same_rank_completed
        (strategy seed) fuel label
        (by simpa [H] using hdoneHigh seed)
        (by simpa [H] using hdoneZero seed label)
      have hcost := oneZero_operational_cost_ge
        (le_of_lt hH) (ne_of_gt hH) (strategy seed) fuel label
        (by omega)
        (by simpa [H] using hdoneZero seed label)
      dsimp at hsame hcost
      dsimp [ObligatoryUnbounded.exceptionalZeroCharge, order,
        completedBefore, operationalCost,
        oneZeroRandomOrderComparisonUpper]
      rw [hsame.2]
      dsimp [H, Online.runCompletionCost] at hcost ⊢
      nlinarith
    calc
      Randomized.uniformAverage (fun seed ↦
          ObligatoryUnbounded.exceptionalZeroCharge (order seed)
            (completedBefore seed) H label) - 2 * n ^ 2 =
          Randomized.uniformAverage (fun seed ↦
            ObligatoryUnbounded.exceptionalZeroCharge (order seed)
              (completedBefore seed) H label - 2 * n ^ 2) := by
            rw [uniformAverage_sub_const]
      _ ≤ Randomized.uniformAverage (fun seed ↦
            operationalCost (oneZeroProcessing H label) (strategy seed) fuel -
              oneZeroRandomOrderComparisonUpper n H) :=
        Randomized.uniformAverage_mono hpoint
      _ = oneZeroGap label := by
        rw [uniformAverage_sub_const]
  have hdichotomy :=
    ObligatoryUnbounded.exists_quadratic_instance_gap_two_remainders
      hn order completedBefore oneZeroGap (by simpa [H] using hone)
  have hhighEq :
      Randomized.uniformAverage (fun seed ↦
          operationalCost (allHighProcessing H) (strategy seed) fuel) -
          allHighImmediateComparisonCost n H =
        ObligatoryUnbounded.allHighExcess completedBefore := by
    rw [← uniformAverage_sub_const]
    unfold ObligatoryUnbounded.allHighExcess
    apply congrArg Randomized.uniformAverage
    funext seed
    simpa [operationalCost, allHighImmediateComparisonCost, completedBefore]
      using allHigh_operational_gap_eq_rankGaps hH (strategy seed) fuel
        (by simpa [H] using hdoneHigh seed)
  rcases hdichotomy with hhigh | ⟨label, hlabel⟩
  · left
    simpa [H, hhighEq] using hhigh
  · right
    refine ⟨label, ?_⟩
    simpa [H, oneZeroGap] using hlabel

end

end ObligatoryUnboundedOperational
end SchedulingPaper
