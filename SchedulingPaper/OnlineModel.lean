import SchedulingPaper.Model
import Mathlib.Data.Fin.Basic

/-!
# Finite deterministic online semantics

The processing-time oracle is separated from the public transcript.  A test
queries the oracle and publishes its answer.  Raw execution neither queries
nor publishes the hidden processing time.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Job labels for an instance with `n` jobs. -/
abbrev Label (n : ℕ) := Fin n

/-- The local lifecycle of a job.  A processing time is stored only between
its test and its processing operation. -/
inductive JobState where
  | untouched
  | tested (processingTime : ℝ)
  | done
  deriving DecidableEq

/-- Operations that an online strategy may request. -/
inductive Action (n : ℕ) where
  | test (job : Label n)
  | process (job : Label n)
  | raw (job : Label n)
  deriving DecidableEq

/-- Public feedback after a successful operation.

Only `testResult` contains a processing time.  In particular, `rawCompleted`
does not reveal the processing time of its job. -/
inductive Observation (n : ℕ) where
  | testResult (job : Label n) (processingTime : ℝ)
  | processed (job : Label n)
  | rawCompleted (job : Label n)
  deriving DecidableEq

abbrev Transcript (n : ℕ) := List (Observation n)

/-- The machine configuration.  The strategy below receives only its public
`transcript`, not this entire structure. -/
structure Config (n : ℕ) where
  jobs : Label n → JobState
  transcript : Transcript n

def Config.initial (n : ℕ) : Config n where
  jobs := fun _ => .untouched
  transcript := []

/-- An oracle may depend on the complete public transcript so far. -/
abbrev Oracle (n : ℕ) := Transcript n → Label n → ℝ

/-- A fixed input instance is the transcript-independent special case. -/
def fixedOracle (processingTime : Label n → ℝ) : Oracle n :=
  fun _ job => processingTime job

/-- Values admissible for a cap. -/
def ValueAdmissible : Cap → ℝ → Prop
  | .finite u, p => 0 ≤ p ∧ p ≤ u
  | .infinite, p => 0 ≤ p

def Oracle.Admissible (cap : Cap) (oracle : Oracle n) : Prop :=
  ∀ transcript job, ValueAdmissible cap (oracle transcript job)

/-- Preconditions for online operations.

Testing and raw execution require an untouched job.  Processing requires a
previous test.  Raw execution is unavailable at the obligatory endpoint. -/
def Action.Enabled (cap : Cap) (config : Config n) : Action n → Prop
  | .test job => config.jobs job = .untouched
  | .process job => ∃ p, config.jobs job = .tested p
  | .raw job =>
      config.jobs job = .untouched ∧ ∃ u, cap = .finite u

/-- Execute one requested operation.  `none` means that its precondition
failed. -/
def Config.step (cap : Cap) (oracle : Oracle n) (config : Config n) :
    Action n → Option (Config n)
  | .test job =>
      match config.jobs job with
      | .untouched =>
          let p := oracle config.transcript job
          some {
            jobs := Function.update config.jobs job (.tested p)
            transcript := config.transcript ++ [.testResult job p]
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
  | .raw job =>
      match cap, config.jobs job with
      | .finite _, .untouched =>
          some {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.rawCompleted job]
          }
      | _, _ => none

theorem Config.step_some_iff_enabled (cap : Cap) (oracle : Oracle n)
    (config : Config n) (action : Action n) :
    (∃ next, config.step cap oracle action = some next) ↔
      action.Enabled cap config := by
  cases action with
  | test job =>
      cases h : config.jobs job <;>
        simp [Config.step, Action.Enabled, h]
  | process job =>
      cases h : config.jobs job <;>
        simp [Config.step, Action.Enabled, h]
  | raw job =>
      cases cap <;> cases h : config.jobs job <;>
        simp [Config.step, Action.Enabled, h]

/-- Whether an action is invalid is independent of all hidden processing
times. -/
theorem Config.step_eq_none_oracle_independent (cap : Cap)
    (left right : Oracle n) (config : Config n) (action : Action n) :
    config.step cap left action = none ↔
      config.step cap right action = none := by
  cases action with
  | test job =>
      cases hjob : config.jobs job <;>
        simp [Config.step, hjob]
  | process job =>
      cases hjob : config.jobs job <;>
        simp [Config.step, hjob]
  | raw job =>
      cases cap <;> cases hjob : config.jobs job <;>
        simp [Config.step, hjob]

@[simp] theorem Config.step_test_of_untouched (cap : Cap)
    (oracle : Oracle n) (config : Config n) (job : Label n)
    (hjob : config.jobs job = .untouched) :
    config.step cap oracle (.test job) =
      some {
        jobs := Function.update config.jobs job
          (.tested (oracle config.transcript job))
        transcript := config.transcript ++
          [.testResult job (oracle config.transcript job)]
      } := by
  simp [Config.step, hjob]

/-- Raw execution is observationally independent of every processing-time
oracle. -/
theorem Config.step_raw_oracle_independent (cap : Cap)
    (left right : Oracle n) (config : Config n) (job : Label n) :
    config.step cap left (.raw job) = config.step cap right (.raw job) := by
  cases cap <;> cases h : config.jobs job <;>
    simp [Config.step, h]

/-- A deterministic online strategy is a function of the public transcript
only.  Returning `none` stops the execution. -/
abbrev Strategy (n : ℕ) := Transcript n → Option (Action n)

inductive StopReason (n : ℕ) where
  | outOfFuel
  | strategyStopped
  | invalidAction (action : Action n)
  deriving DecidableEq

structure RunResult (n : ℕ) where
  config : Config n
  reason : StopReason n

/-- Fuelled big-step evaluation.  Recursive consumption of `fuel` is the
termination argument; invalid actions and an explicit strategy stop are
reported separately. -/
def runFuel (cap : Cap) (oracle : Oracle n) (strategy : Strategy n) :
    ℕ → Config n → RunResult n
  | 0, config => ⟨config, .outOfFuel⟩
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => ⟨config, .strategyStopped⟩
      | some action =>
          match config.step cap oracle action with
          | none => ⟨config, .invalidAction action⟩
          | some next => runFuel cap oracle strategy fuel next

def run (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) : RunResult n :=
  runFuel cap oracle strategy fuel (Config.initial n)

end

end SchedulingPaper.Online
