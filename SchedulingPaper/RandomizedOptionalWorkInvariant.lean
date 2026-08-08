import SchedulingPaper.RandomizedOptionalOnline
import Mathlib.Tactic

/-!
# Exact processing-work accounting for optional testing

A legal transcript may process a tested job or complete an untouched job
blindly.  This file proves that these two kinds of processing work equal the
processing-time mass of the lifecycle states marked `done`.  Consequently a
completed run uses every job's processing time exactly once, including the
zero-length bookkeeping operation after a zero test.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section

def doneContribution (processing : Label n → ℝ) : JobState → Label n → ℝ
  | .done, job => processing job
  | _, _ => 0

def doneProcessingWork (processing : Label n → ℝ)
    (jobs : Label n → JobState) : ℝ :=
  ∑ job, doneContribution processing (jobs job) job

@[simp] theorem processedWork_append
    (processing : Label n → ℝ) (left right : Transcript n) :
    processedWork processing (left ++ right) =
      processedWork processing left + processedWork processing right := by
  induction left with
  | nil => simp [processedWork]
  | cons observation rest ih =>
      cases observation <;> simp [processedWork, ih] <;> ring

@[simp] theorem blindWork_append (left right : Transcript n) :
    blindWork (left ++ right) = blindWork left + blindWork right := by
  induction left with
  | nil => simp [blindWork]
  | cons observation rest ih =>
      cases observation <;> simp [blindWork, ih] <;> ring

private theorem doneProcessingWork_eq_erase_add
    (processing : Label n → ℝ) (jobs : Label n → JobState)
    (job : Label n) :
    doneProcessingWork processing jobs =
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
        doneContribution processing (jobs i) i) +
      doneContribution processing (jobs job) job := by
  unfold doneProcessingWork
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ job)]

private theorem doneProcessingWork_update
    (processing : Label n → ℝ) (jobs : Label n → JobState)
    (job : Label n) (state : JobState) :
    doneProcessingWork processing (Function.update jobs job state) =
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
        doneContribution processing (jobs i) i) +
      doneContribution processing state job := by
  classical
  rw [doneProcessingWork_eq_erase_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ job := (Finset.mem_erase.mp hi).1
    simp [Function.update, hne]
  · simp [Function.update]

structure ProcessingWorkInvariant
    (processing : Label n → ℝ) (config : Config n) : Prop where
  work_eq : processedWork processing config.transcript +
      blindWork config.transcript = doneProcessingWork processing config.jobs

theorem Config.initial_processingWorkInvariant
    (processing : Label n → ℝ) :
    ProcessingWorkInvariant processing (Config.initial n) := by
  constructor
  simp [Config.initial, processedWork, blindWork, doneProcessingWork,
    doneContribution]

theorem ProcessingWorkInvariant.step
    {processing : Label n → ℝ} {config next : Config n}
    (hinv : ProcessingWorkInvariant processing config)
    {action : Action n} (hstep : config.step processing action = some next) :
    ProcessingWorkInvariant processing next := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hold := hinv.work_eq
          constructor
          dsimp
          rw [doneProcessingWork_eq_erase_add processing config.jobs job] at hold
          rw [processedWork_append, blindWork_append,
            doneProcessingWork_update]
          simp [processedWork, blindWork, doneContribution, hstate] at hold ⊢
          exact hold
  | process job =>
      cases hstate : config.jobs job with
      | untouched => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | tested value =>
          simp [Config.step, hstate] at hstep
          subst next
          have hold := hinv.work_eq
          constructor
          dsimp
          rw [doneProcessingWork_eq_erase_add processing config.jobs job] at hold
          rw [processedWork_append, blindWork_append,
            doneProcessingWork_update]
          simp [processedWork, blindWork, doneContribution, hstate] at hold ⊢
          linarith
  | blind job =>
      cases hstate : config.jobs job with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hold := hinv.work_eq
          constructor
          dsimp
          rw [doneProcessingWork_eq_erase_add processing config.jobs job] at hold
          rw [processedWork_append, blindWork_append,
            doneProcessingWork_update]
          simp [processedWork, blindWork, doneContribution, hstate] at hold ⊢
          linarith

theorem runFuel_processingWorkInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (hinv : ProcessingWorkInvariant processing config) :
    ProcessingWorkInvariant processing
      (runFuel processing strategy fuel config).config := by
  induction fuel generalizing config with
  | zero => exact hinv
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none => exact hinv
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none => exact hinv
          | some next => exact ih next (hinv.step hstep)

theorem run_processingWorkInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    ProcessingWorkInvariant processing (run processing strategy fuel).config := by
  unfold run
  exact runFuel_processingWorkInvariant processing strategy fuel (Config.initial n)
    (Config.initial_processingWorkInvariant processing)

theorem processingWork_eq_sum_of_done
    {processing : Label n → ℝ} {config : Config n}
    (hinv : ProcessingWorkInvariant processing config)
    (hdone : ∀ job, config.jobs job = .done) :
    processedWork processing config.transcript + blindWork config.transcript =
      ∑ job, processing job := by
  rw [hinv.work_eq]
  unfold doneProcessingWork
  apply Finset.sum_congr rfl
  intro job hjob
  simp [hdone job, doneContribution]

theorem run_processingWork_eq_sum_of_done
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ job, (run processing strategy fuel).config.jobs job = .done) :
    processedWork processing (run processing strategy fuel).config.transcript +
        blindWork (run processing strategy fuel).config.transcript =
      ∑ job, processing job :=
  processingWork_eq_sum_of_done
    (run_processingWorkInvariant processing strategy fuel) hdone

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
