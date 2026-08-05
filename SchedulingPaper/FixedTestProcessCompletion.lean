import SchedulingPaper.CompletionPairDecomposition
import SchedulingPaper.UTERuntimeAccounting
import Mathlib.Tactic

/-!
# Exact completion-label invariant for fixed test/process runs

Zero processing times complete at their test observation, while positive
processing times complete at the later administrative process observation.
This module tracks that distinction and proves that every completed
test/process run has exactly one completion observation for every label.
-/

namespace SchedulingPaper.Online

noncomputable section

def JobState.completionRecorded : JobState → Prop
  | .untouched => False
  | .tested p => p = 0
  | .done => True

/-- The public completion-label history agrees exactly with the local job
states and contains no duplicate label. -/
structure Config.FixedCompletionInvariant
    (processingTime : Label n → ℝ) (config : Config n) : Prop where
  nodup :
    (config.transcript.completionLabels processingTime).Nodup
  mem_iff :
    ∀ job,
      job ∈ config.transcript.completionLabels processingTime ↔
        (config.jobs job).completionRecorded

theorem Config.initial_fixedCompletionInvariant
    (processingTime : Label n → ℝ) :
    (Config.initial n).FixedCompletionInvariant processingTime := by
  constructor <;> simp [Config.initial, JobState.completionRecorded]

theorem Config.TestProcessInvariant.tested_value_eq_fixed
    {processingTime : Label n → ℝ} {config : Config n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    {job : Label n} {p : ℝ}
    (hjob : config.jobs job = .tested p) :
    p = processingTime job := by
  have hmem := (hstruct.tested_iff job p).mp hjob |>.1
  exact hmatch job p hmem

theorem Config.fixedCompletionInvariant_step
    (cap : Cap) (processingTime : Label n → ℝ)
    {config next : Config n} {action : Action n}
    (hstruct : config.TestProcessInvariant)
    (hmatch : config.transcript.TestsMatch processingTime)
    (hcompletion : config.FixedCompletionInvariant processingTime)
    (hstep :
      config.step cap (fixedOracle processingTime) action = some next) :
    next.FixedCompletionInvariant processingTime := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp only [Config.step, hjob, fixedOracle,
            Option.some.injEq] at hstep
          subst next
          have hnotmem :
              job ∉
                config.transcript.completionLabels processingTime := by
            intro hmem
            have :=
              (hcompletion.mem_iff job).mp hmem
            simp [hjob, JobState.completionRecorded] at this
          constructor
          · by_cases hp : processingTime job = 0
            · simp [Observation.completionLabel, hp,
                List.nodup_append_comm,
                hcompletion.nodup, hnotmem]
            · simpa [Observation.completionLabel, hp] using
                hcompletion.nodup
          · intro other
            by_cases hp : processingTime job = 0
            · by_cases heq : other = job
              · subst other
                simp [Observation.completionLabel, hp, Function.update,
                  JobState.completionRecorded]
              · simp [hp, heq, Function.update,
                  Observation.completionLabel,
                  hcompletion.mem_iff other,
                  JobState.completionRecorded]
            · by_cases heq : other = job
              · subst other
                simp [Observation.completionLabel, hp, Function.update,
                  hnotmem, JobState.completionRecorded]
              · simp [hp, heq, Function.update,
                  Observation.completionLabel,
                  hcompletion.mem_iff other,
                  JobState.completionRecorded]
      | tested old =>
          simp [Config.step, hjob] at hstep
      | done =>
          simp [Config.step, hjob] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
      | tested p =>
          simp only [Config.step, hjob, Option.some.injEq] at hstep
          subst next
          have hp :
              p = processingTime job :=
            hstruct.tested_value_eq_fixed hmatch hjob
          by_cases hzero : processingTime job = 0
          · have hmem :
                job ∈
                  config.transcript.completionLabels processingTime := by
              rw [hcompletion.mem_iff]
              simp [hjob, hp, hzero,
                JobState.completionRecorded]
            constructor
            · simpa [Observation.completionLabel, hzero] using
                hcompletion.nodup
            · intro other
              by_cases heq : other = job
              · subst other
                simp [Observation.completionLabel, hzero,
                  Function.update, hmem,
                  JobState.completionRecorded]
              · simp [hzero, heq, Function.update,
                  Observation.completionLabel,
                  hcompletion.mem_iff other,
                  JobState.completionRecorded]
          · have hnotmem :
                job ∉
                  config.transcript.completionLabels processingTime := by
              intro hmem
              have hrecorded :=
                (hcompletion.mem_iff job).mp hmem
              simp [hjob, hp, hzero,
                JobState.completionRecorded] at hrecorded
            constructor
            · simp [Observation.completionLabel, hzero,
                List.nodup_append_comm,
                hcompletion.nodup, hnotmem]
            · intro other
              by_cases heq : other = job
              · subst other
                simp [Observation.completionLabel, hzero,
                  Function.update,
                  JobState.completionRecorded]
              · simp [hzero, heq, Function.update,
                  Observation.completionLabel,
                  hcompletion.mem_iff other,
                  JobState.completionRecorded]
      | done =>
          simp [Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp only [Config.step, hjob,
                Option.some.injEq] at hstep
              subst next
              have hnotmem :
                  job ∉
                    config.transcript.completionLabels processingTime := by
                intro hmem
                have hrecorded :=
                  (hcompletion.mem_iff job).mp hmem
                simp [hjob, JobState.completionRecorded] at hrecorded
              constructor
              · rw [Transcript.completionLabels_append]
                change
                  (config.transcript.completionLabels processingTime ++
                    [job]).Nodup
                simp [List.nodup_append_comm,
                  hcompletion.nodup, hnotmem]
              · intro other
                rw [Transcript.completionLabels_append]
                simp only [Transcript.completionLabels,
                  Observation.completionLabel, List.filterMap_cons,
                  List.filterMap_nil]
                by_cases heq : other = job
                · subst other
                  change
                    job ∈
                        config.transcript.completionLabels processingTime ++
                          [job] ↔
                      JobState.completionRecorded
                        (Function.update config.jobs job .done job)
                  simp [Function.update, JobState.completionRecorded]
                · change
                    other ∈
                        config.transcript.completionLabels processingTime ++
                          [job] ↔
                      JobState.completionRecorded
                        (Function.update config.jobs job .done other)
                  simp [heq, Function.update,
                    hcompletion.mem_iff other,
                    JobState.completionRecorded]
          | tested p =>
              simp [Config.step, hjob] at hstep
          | done =>
              simp [Config.step, hjob] at hstep

/-- Work-rank termination while retaining exact completion labels. -/
theorem runFuel_testProcessStrategy_completed_with_completionInvariant
    (cap : Cap) (processingTime : Label n → ℝ)
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending) (extra : ℕ) :
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
    exact testProcessStrategy_stop_of_zero hpending hgood.1 hzero
  have hprogress :
      ∀ config, Good config → 0 < config.remainingWork →
        WorkStep cap (fixedOracle processingTime)
          (testProcessStrategy pending) Good config := by
    intro config hgood hpos
    obtain ⟨action, next, haction, hstep, hnext, hwork⟩ :=
      testProcessStrategy_progress cap (fixedOracle processingTime)
        hpending hgood.1 hpos
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

/-- The concrete ForcedPrefixUTE run has one completion label per job. -/
theorem run_forcedPrefixUTEStrategy_completionLabels_perm
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    (result.config.transcript.completionLabels processingTime).Perm
      (List.ofFn id) := by
  unfold run
  rw [forcedPrefixUTEStrategy_eq_testProcessStrategy]
  have hrun :=
    runFuel_testProcessStrategy_completed_with_completionInvariant
      cap processingTime
      (forcedPrefixPendingImmediate_selectsLastTest n
        (forcedPrefixCount n b) (uteThreshold u)) 0
  let result :=
    runFuel cap (fixedOracle processingTime)
      (testProcessStrategy
        (fun transcript =>
          transcript.forcedPrefixPendingImmediate?
            n (forcedPrefixCount n b) (uteThreshold u)))
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

end SchedulingPaper.Online
