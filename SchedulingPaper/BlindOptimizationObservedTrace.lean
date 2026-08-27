import SchedulingPaper.BlindOptimizationModel
import SchedulingPaper.RandomizedOptionalObservedTrace

/-!
# First-touch traces for blind optimization

This file connects the literal blind-optimization runtime to the generic
causal-trace bijection.  Raw completions deliberately contain no processing
time.  The auxiliary `analysisValues` list exposes those hidden values only
to the proof, after the corresponding scheduling decision has already been
made.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace ObservedTrace

open Randomized
open RandomizedOptional
open RandomizedOptional.TraceBijection
open Online

noncomputable section

abbrev Placement (n : ℕ) := Equiv.Perm (Fin n)

def placedProcessing {n : ℕ} (p : Fin n → ℝ)
    (placement : Placement n) : Fin n → ℝ :=
  fun label ↦ p (placement label)

def actionObservation {n : ℕ} (processing : Fin n → ℝ) :
    Online.Action n → Online.Observation n
  | ⟨job, .raw⟩ => .rawCompleted job
  | ⟨job, .optimized⟩ => .optimizedCompleted job (processing job)

def observationKind {n : ℕ} :
    Online.Observation n → RandomizedOptional.TraceBijection.TouchKind
  | .rawCompleted _ => .blind
  | .optimizedCompleted _ _ => .test

def touchChoices {n : ℕ} (transcript : Online.Transcript n) :
    List (Fin n × RandomizedOptional.TraceBijection.TouchKind) :=
  transcript.map fun observation ↦ (observation.job, observationKind observation)

def analysisValues {n : ℕ} (processing : Fin n → ℝ)
    (transcript : Online.Transcript n) : List ℝ :=
  transcript.map fun observation ↦ processing observation.job

def runWord {n : ℕ} (processing : Fin n → ℝ)
    (strategy : Online.Strategy n) :
    ℕ → Online.Config n → Online.Transcript n
  | 0, _ => []
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => []
      | some action =>
          match config.step processing action with
          | none => []
          | some next => actionObservation processing action ::
              runWord processing strategy fuel next

theorem step_transcript_eq_append_observation {n : ℕ}
    {processing : Fin n → ℝ} {config next : Online.Config n}
    {action : Online.Action n}
    (hstep : config.step processing action = some next) :
    next.transcript = config.transcript ++ [actionObservation processing action] := by
  cases action with
  | mk job mode =>
      cases mode <;> simp [Online.Config.step, actionObservation] at hstep ⊢
      all_goals rcases hstep with ⟨_, rfl⟩
      all_goals rfl

theorem runFuel_transcript_eq_append_runWord {n : ℕ}
    (processing : Fin n → ℝ) (strategy : Online.Strategy n)
    (fuel : ℕ) (config : Online.Config n) :
    (Online.runFuel processing strategy fuel config).config.transcript =
      config.transcript ++ runWord processing strategy fuel config := by
  induction fuel generalizing config with
  | zero => simp [Online.runFuel, runWord]
  | succ fuel ih =>
      simp only [Online.runFuel, runWord]
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none => simp
          | some next =>
              simp only
              rw [ih next, step_transcript_eq_append_observation hstep]
              simp

theorem run_transcript_eq_runWord {n : ℕ}
    (processing : Fin n → ℝ) (strategy : Online.Strategy n) (fuel : ℕ) :
    (Online.run processing strategy fuel).config.transcript =
      runWord processing strategy fuel (Online.Config.initial n) := by
  unfold Online.run
  simpa [Online.Config.initial] using
    runFuel_transcript_eq_append_runWord processing strategy fuel
      (Online.Config.initial n)

/-! Equal analytically exposed values force equal scheduling choices.  This
is stronger than operational observability for raw jobs and is therefore a
valid hypothesis for the trace-bijection compiler. -/
theorem runWord_touchChoices_causal {n : ℕ}
    (processing processing' : Fin n → ℝ)
    (strategy : Online.Strategy n) (fuel k : ℕ)
    (config : Online.Config n)
    (hvalues :
      (analysisValues processing
        (runWord processing strategy fuel config)).take k =
      (analysisValues processing'
        (runWord processing' strategy fuel config)).take k) :
    (touchChoices (runWord processing strategy fuel config)).take (k + 1) =
      (touchChoices (runWord processing' strategy fuel config)).take (k + 1) := by
  induction fuel generalizing config k with
  | zero => simp [runWord, touchChoices]
  | succ fuel ih =>
      simp only [runWord] at hvalues ⊢
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only [haction] at hvalues ⊢
          cases action with
          | mk job mode =>
              cases mode with
              | raw =>
                  by_cases hfresh : job ∈ config.touched
                  · simp [Online.Config.step, hfresh]
                  · let next : Online.Config n :=
                      ⟨insert job config.touched,
                        config.transcript ++ [.rawCompleted job]⟩
                    have hstep : config.step processing ⟨job, .raw⟩ = some next := by
                      simp [Online.Config.step, hfresh, next]
                    have hstep' : config.step processing' ⟨job, .raw⟩ = some next := by
                      simp [Online.Config.step, hfresh, next]
                    simp only [hstep, hstep', actionObservation] at hvalues ⊢
                    cases k with
                    | zero => simp [touchChoices, observationKind]
                    | succ k =>
                        simp only [analysisValues, List.map_cons,
                          List.take_succ_cons, List.cons.injEq] at hvalues
                        simp only [touchChoices, List.map_cons,
                          observationKind, List.take_succ_cons, List.cons.injEq]
                        exact ⟨True.intro, ih k next hvalues.2⟩
              | optimized =>
                  by_cases hfresh : job ∈ config.touched
                  · simp [Online.Config.step, hfresh]
                  · let next : Online.Config n :=
                      ⟨insert job config.touched,
                        config.transcript ++
                          [.optimizedCompleted job (processing job)]⟩
                    have hstep :
                        config.step processing ⟨job, .optimized⟩ = some next := by
                      simp [Online.Config.step, hfresh, next]
                    let next' : Online.Config n :=
                      ⟨insert job config.touched,
                        config.transcript ++
                          [.optimizedCompleted job (processing' job)]⟩
                    have hstep' :
                        config.step processing' ⟨job, .optimized⟩ = some next' := by
                      simp [Online.Config.step, hfresh, next']
                    simp only [hstep, hstep', actionObservation] at hvalues ⊢
                    cases k with
                    | zero =>
                        simp [touchChoices, observationKind,
                          Online.Observation.job]
                    | succ k =>
                        simp only [analysisValues, List.map_cons,
                          List.take_succ_cons, List.cons.injEq] at hvalues
                        have hp : processing job = processing' job := hvalues.1
                        have hnext : next' = next := by
                          simp [next, next', hp]
                        rw [hnext] at hvalues
                        rw [hnext]
                        simp only [touchChoices, List.map_cons,
                          observationKind, List.take_succ_cons, List.cons.injEq]
                        exact ⟨rfl, ih k next hvalues.2⟩

structure CompletePolicy {n : ℕ} (p : Fin n → ℝ) where
  strategy : Online.Strategy n
  completes : ∀ placement, Online.Completes (placedProcessing p placement) strategy

def settledRun {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) : Online.RunResult n :=
  Online.run (placedProcessing p placement) policy.strategy n

theorem settled_length {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) :
    (settledRun p policy placement).config.transcript.length = n := by
  exact Online.transcript_length_eq_n_of_completes (policy.completes placement)

theorem settled_nodup {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) :
    ((settledRun p policy placement).config.transcript.map
      Online.Observation.job).Nodup := by
  exact (Online.run_historyInvariant (placedProcessing p placement)
    policy.strategy n).nodup

def touchLabelOrder {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) : Equiv.Perm (Fin n) :=
  let transcript := (settledRun p policy placement).config.transcript
  RandomizedOptional.ObservedTrace.listOrderPerm
    (transcript.map Online.Observation.job)
    (by simpa using settled_length p policy placement)
    (settled_nodup p policy placement)

def touchTrace {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) :
    RandomizedOptional.TraceBijection.TouchTrace n where
  label := touchLabelOrder p policy placement
  kind := fun k ↦
    observationKind <|
      (settledRun p policy placement).config.transcript.get
        (Fin.cast (settled_length p policy placement).symm k)

@[simp] theorem touchLabelOrder_apply {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) (k : Fin n) :
    touchLabelOrder p policy placement k =
      ((settledRun p policy placement).config.transcript.get
        (Fin.cast (settled_length p policy placement).symm k)).job := by
  unfold touchLabelOrder
  rw [RandomizedOptional.ObservedTrace.listOrderPerm_apply]
  simp

theorem touchTrace_choice {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) (k : Fin n) :
    ((touchTrace p policy placement).label k,
      (touchTrace p policy placement).kind k) =
      let observation :=
        (settledRun p policy placement).config.transcript.get
          (Fin.cast (settled_length p policy placement).symm k)
      (observation.job, observationKind observation) := by
  change
    (touchLabelOrder p policy placement k,
      observationKind ((settledRun p policy placement).config.transcript.get
        (Fin.cast (settled_length p policy placement).symm k))) = _
  rw [touchLabelOrder_apply]

theorem settled_analysisValues_eq_ofFn {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : Placement n) :
    analysisValues (placedProcessing p placement)
        (settledRun p policy placement).config.transcript =
      List.ofFn fun k ↦
        p (RandomizedOptional.TraceBijection.revealOrder
          (touchTrace p policy) placement k) := by
  let transcript := (settledRun p policy placement).config.transcript
  have horder : List.ofFn (touchLabelOrder p policy placement) =
      transcript.map Online.Observation.job := by
    unfold touchLabelOrder
    exact RandomizedOptional.ObservedTrace.listOrderPerm_ofFn _ _ _
  unfold analysisValues placedProcessing
  change
    List.map (fun observation ↦ p (placement observation.job)) transcript = _
  rw [show List.map (fun observation ↦ p (placement observation.job)) transcript =
      List.map (fun job ↦ p (placement job))
        (transcript.map Online.Observation.job) by simp [List.map_map]]
  rw [← horder, List.map_ofFn]
  rfl

theorem touchTrace_causal {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    RandomizedOptional.TraceBijection.Causal p (touchTrace p policy) := by
  intro placement placement' k hprefix
  let processing := placedProcessing p placement
  let processing' := placedProcessing p placement'
  let initial := Online.Config.initial n
  have htakeOfFn :
      (List.ofFn fun j ↦ p (RandomizedOptional.TraceBijection.revealOrder
        (touchTrace p policy) placement j)).take k.val =
      (List.ofFn fun j ↦ p (RandomizedOptional.TraceBijection.revealOrder
        (touchTrace p policy) placement' j)).take k.val :=
    RandomizedOptional.TraceBijection.take_ofFn_eq_of_prefix _ _ hprefix
  have hvalues := runWord_touchChoices_causal processing processing'
    policy.strategy n k.val initial (by
      rw [← run_transcript_eq_runWord, ← run_transcript_eq_runWord]
      change
        (analysisValues (placedProcessing p placement)
          (settledRun p policy placement).config.transcript).take k.val =
        (analysisValues (placedProcessing p placement')
          (settledRun p policy placement').config.transcript).take k.val
      rw [settled_analysisValues_eq_ofFn p policy placement,
          settled_analysisValues_eq_ofFn p policy placement']
      exact htakeOfFn)
  have hchoices :
      (touchChoices (settledRun p policy placement).config.transcript).take
          (k.val + 1) =
      (touchChoices (settledRun p policy placement').config.transcript).take
          (k.val + 1) := by
    unfold settledRun
    rw [run_transcript_eq_runWord, run_transcript_eq_runWord]
    exact hvalues
  let left := (settledRun p policy placement).config.transcript
  let right := (settledRun p policy placement').config.transcript
  have hkLeft : k.val < left.length := by
    dsimp [left]
    rw [settled_length p policy placement]
    exact k.isLt
  have hkRight : k.val < right.length := by
    dsimp [right]
    rw [settled_length p policy placement']
    exact k.isLt
  have hget :
      (touchChoices left).get ⟨k.val, by simpa [touchChoices] using hkLeft⟩ =
      (touchChoices right).get ⟨k.val, by simpa [touchChoices] using hkRight⟩ :=
    RandomizedOptional.TraceBijection.get_eq_of_take_succ_eq
      (by simpa [touchChoices] using hkLeft)
      (by simpa [touchChoices] using hkRight) (by simpa [left, right] using hchoices)
  have hpair :
      ((touchTrace p policy placement).label k,
        (touchTrace p policy placement).kind k) =
      ((touchTrace p policy placement').label k,
        (touchTrace p policy placement').kind k) := by
    rw [touchTrace_choice p policy placement k,
      touchTrace_choice p policy placement' k]
    simpa [touchChoices, left, right] using hget
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

def compiledOptimizeSelector {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) : Fin n → Placement n → ℝ :=
  RandomizedOptional.TraceBijection.compiledTestSelector p
    (touchTrace p policy) (touchTrace_causal p policy)

theorem compiledOptimizeSelector_predictable {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    RandomizedOptional.PredictableSelector
      (compiledOptimizeSelector p policy) :=
  RandomizedOptional.TraceBijection.compiledTestSelector_predictable p
    (touchTrace p policy) (touchTrace_causal p policy)

theorem compiledOptimizeSelector_zero_one {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (k : Fin n) (reveal : Placement n) :
    compiledOptimizeSelector p policy k reveal = 0 ∨
      compiledOptimizeSelector p policy k reveal = 1 :=
  RandomizedOptional.TraceBijection.compiledTestSelector_zero_one p
    (touchTrace p policy) (touchTrace_causal p policy) k reveal

end
end ObservedTrace
end BlindOptimization
end SchedulingPaper
