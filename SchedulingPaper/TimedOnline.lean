import SchedulingPaper.Replay

/-!
# Time and total completion cost of an online transcript

`OnlineModel` is intentionally operational.  This file gives its public
transcript the scheduling interpretation needed by the competitive analysis.
Tests last one unit, a tested processing operation lasts its fixed processing
time, and raw execution lasts the finite cap.  A zero job completes at the
end of its test; its later zero-duration administrative `process` action is
not counted a second time.
-/

namespace SchedulingPaper.Online

noncomputable section

def rawDuration : Cap → ℝ
  | .finite u => u
  | .infinite => 0

/-- Machine time consumed by one successful public operation. -/
def Observation.duration (cap : Cap) (processingTime : Label n → ℝ) :
    Observation n → ℝ
  | .testResult _ _ => 1
  | .processed job => processingTime job
  | .rawCompleted _ => rawDuration cap

/-- The job completed by an observation, if any.  The fixed processing map
is used to avoid counting the administrative process action of a zero job
twice. -/
def Observation.completionLabel
    (processingTime : Label n → ℝ) : Observation n → Option (Label n)
  | .testResult job p => if p = 0 then some job else none
  | .processed job => if processingTime job = 0 then none else some job
  | .rawCompleted job => some job

def Observation.isCompletion
    (processingTime : Label n → ℝ) (observation : Observation n) : Bool :=
  (observation.completionLabel processingTime).isSome

/-- Absolute machine time after executing a transcript. -/
def transcriptElapsed
    (cap : Cap) (processingTime : Label n → ℝ) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.duration cap processingTime +
        transcriptElapsed cap processingTime rest

/-- Sum of completion times, carrying the elapsed time at the start of the
current suffix. -/
def completionCostFrom
    (cap : Cap) (processingTime : Label n → ℝ) :
    ℝ → Transcript n → ℝ
  | _, [] => 0
  | time, observation :: rest =>
      let finish := time + observation.duration cap processingTime
      (if observation.completionLabel processingTime |>.isSome
        then finish else 0) +
      completionCostFrom cap processingTime finish rest

def completionCost
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) : ℝ :=
  completionCostFrom cap processingTime 0 transcript

def runCompletionCost
    (cap : Cap) (processingTime : Label n → ℝ)
    (result : RunResult n) : ℝ :=
  completionCost cap processingTime result.config.transcript

@[simp] theorem transcriptElapsed_nil
    (cap : Cap) (processingTime : Label n → ℝ) :
    transcriptElapsed cap processingTime [] = 0 := rfl

@[simp] theorem transcriptElapsed_cons
    (cap : Cap) (processingTime : Label n → ℝ)
    (observation : Observation n) (rest : Transcript n) :
    transcriptElapsed cap processingTime (observation :: rest) =
      observation.duration cap processingTime +
        transcriptElapsed cap processingTime rest := rfl

theorem Observation.duration_nonneg
    {cap : Cap} {processingTime : Label n → ℝ}
    (hcap : cap.Valid)
    (hp : ∀ job, ValueAdmissible cap (processingTime job))
    (observation : Observation n) :
    0 ≤ observation.duration cap processingTime := by
  cases observation with
  | testResult job p => simp [Observation.duration]
  | processed job =>
      cases cap with
      | finite u => exact (hp job).1
      | infinite => exact hp job
  | rawCompleted job =>
      cases cap with
      | finite u => exact hcap.le
      | infinite => simp [Observation.duration, rawDuration]

theorem transcriptElapsed_nonneg
    {cap : Cap} {processingTime : Label n → ℝ}
    (hcap : cap.Valid)
    (hp : ∀ job, ValueAdmissible cap (processingTime job))
    (transcript : Transcript n) :
    0 ≤ transcriptElapsed cap processingTime transcript := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      rw [transcriptElapsed_cons]
      exact add_nonneg
        (Observation.duration_nonneg hcap hp observation) ih

theorem completionCostFrom_nonneg
    {cap : Cap} {processingTime : Label n → ℝ}
    (hcap : cap.Valid)
    (hp : ∀ job, ValueAdmissible cap (processingTime job))
    {time : ℝ} (htime : 0 ≤ time)
    (transcript : Transcript n) :
    0 ≤ completionCostFrom cap processingTime time transcript := by
  induction transcript generalizing time with
  | nil => simp [completionCostFrom]
  | cons observation rest ih =>
      have hduration :=
        Observation.duration_nonneg hcap hp observation
      have hfinish : 0 ≤
          time + observation.duration cap processingTime :=
        add_nonneg htime hduration
      simp only [completionCostFrom]
      split_ifs
      · exact add_nonneg hfinish (ih hfinish)
      · simpa using ih hfinish

theorem completionCost_nonneg
    {cap : Cap} {processingTime : Label n → ℝ}
    (hcap : cap.Valid)
    (hp : ∀ job, ValueAdmissible cap (processingTime job))
    (transcript : Transcript n) :
    0 ≤ completionCost cap processingTime transcript := by
  exact completionCostFrom_nonneg hcap hp (le_refl 0) transcript

/-- Replay preserves not only the public operations but their full timing and
total completion cost on the frozen instance. -/
theorem replay_preserves_completionCost
    (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (default : Label n → ℝ) (fuel : ℕ) :
    let frozen :=
      frozenProcessingTimes cap adversary strategy default fuel
    runCompletionCost cap frozen
        (run cap (fixedOracle frozen) strategy fuel) =
      runCompletionCost cap frozen
        (adaptiveRun cap adversary strategy fuel).result := by
  dsimp only
  rw [replay]

end

end SchedulingPaper.Online
