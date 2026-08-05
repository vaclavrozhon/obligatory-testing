import SchedulingPaper.HiddenStoppingExchange

/-!
# Operational completion of the hidden-stopping exchange

This file connects the exact trace law and analytic remainder to the actual
completed adaptive run.
-/

namespace SchedulingPaper

noncomputable section

namespace Online

@[simp] theorem Transcript.processedLabels_append_rawCompleted
    (transcript : Transcript n) (job : Label n) :
    (transcript ++ [Observation.rawCompleted job]).processedLabels =
      transcript.processedLabels := by
  simp [Transcript.processedLabels]

/-- The small lifecycle invariant needed at the crossing configuration:
processed labels are unique, every one was tested, and every currently
tested state is represented by its public test result. -/
structure Config.ProcessHistoryInvariant (config : Config n) : Prop where
  processedNodup : config.transcript.processedLabels.Nodup
  testedRecorded :
    ∀ job p, config.jobs job = .tested p →
      (job, p) ∈ config.transcript.testResults
  processedRecorded :
    ∀ job, job ∈ config.transcript.processedLabels →
      job ∈ config.transcript.testResults.map Prod.fst
  processedDone :
    ∀ job, job ∈ config.transcript.processedLabels →
      config.jobs job = .done
  nonuntouchedStarted :
    ∀ job, config.jobs job ≠ .untouched →
      job ∈ Transcript.startedLabels config.transcript
  recordedUnprocessedTested :
    ∀ job p, (job, p) ∈ config.transcript.testResults →
      job ∉ config.transcript.processedLabels →
      config.jobs job = .tested p

theorem Config.initial_processHistoryInvariant (n : ℕ) :
    (Config.initial n).ProcessHistoryInvariant := by
  constructor <;> simp [Config.initial, Transcript.processedLabels]

theorem Config.processHistoryInvariant_step
    {cap : Cap} {oracle : Oracle n} {config next : Config n}
    {action : Action n}
    (hgood : config.ProcessHistoryInvariant)
    (hstarted : config.StartedHistoryInvariant)
    (hstep : config.step cap oracle action = some next) :
    next.ProcessHistoryInvariant := by
  cases action with
  | test testedJob =>
      cases hstate : config.jobs testedJob with
      | tested p =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotProcessed :
              testedJob ∉ config.transcript.processedLabels := by
            intro hmem
            have := hgood.processedDone testedJob hmem
            rw [hstate] at this
            contradiction
          constructor
          · simpa using hgood.processedNodup
          · intro job p hjob
            by_cases heq : job = testedJob
            · subst job
              have hp : oracle config.transcript testedJob = p := by
                simpa [Function.update] using hjob
              subst p
              simp
            · have hold := hgood.testedRecorded job p
                (by simpa [Function.update, heq] using hjob)
              simpa [Transcript.testResults_append] using
                (List.mem_append_left
                  [(testedJob, oracle config.transcript testedJob)] hold)
          · intro job hmem
            rw [Transcript.processedLabels_append_testResult] at hmem
            rw [Transcript.testResults_append_testResult,
              List.map_append, List.map_singleton]
            exact List.mem_append_left _ (hgood.processedRecorded job hmem)
          · intro job hmem
            rw [Transcript.processedLabels_append_testResult] at hmem
            have hdone := hgood.processedDone job hmem
            by_cases heq : job = testedJob
            · subst job
              exact (hnotProcessed hmem).elim
            · simpa [Function.update, heq] using hdone
          · intro job hjob
            by_cases heq : job = testedJob
            · subst job
              simp
            · rw [Transcript.startedLabels_append_testResult]
              exact List.mem_append_left _
                (hgood.nonuntouchedStarted job
                    (by
                      intro hold
                      apply hjob
                      simpa [Function.update, heq] using hold))
          · intro job p hmem hnot
            rw [Transcript.testResults_append_testResult] at hmem
            by_cases heq : job = testedJob
            · subst job
              rcases List.mem_append.mp hmem with hold | hnew
              · exact
                  (hstarted.untouched_not_mem testedJob hstate
                    (HiddenStoppingOracle.Transcript.mem_startedLabels_of_mem_testResults
                      hold)).elim
              · have hp :
                    p = oracle config.transcript testedJob := by
                  have hpair :
                      (testedJob, p) =
                        (testedJob, oracle config.transcript testedJob) := by
                    simpa using hnew
                  exact congrArg Prod.snd hpair
                subst p
                simp [Function.update]
            · have hold :
                  (job, p) ∈ config.transcript.testResults := by
                rcases List.mem_append.mp hmem with hold | hnew
                · exact hold
                · have : job = testedJob := by
                    have hpair :
                        (job, p) =
                          (testedJob,
                            oracle config.transcript testedJob) := by
                      simpa using hnew
                    exact congrArg Prod.fst hpair
                  exact (heq this).elim
              have holdNot :
                  job ∉ config.transcript.processedLabels := by
                simpa using hnot
              simpa [Function.update, heq] using
                hgood.recordedUnprocessedTested job p hold holdNot
  | process processedJob =>
      cases hstate : config.jobs processedJob with
      | untouched =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotProcessed :
              processedJob ∉ config.transcript.processedLabels := by
            intro hmem
            have hdone := hgood.processedDone processedJob hmem
            rw [hstate] at hdone
            contradiction
          have htested := hgood.testedRecorded processedJob p hstate
          constructor
          · rw [Transcript.processedLabels_append_processed,
              List.nodup_append_comm]
            simp [hgood.processedNodup, hnotProcessed]
          · intro job q hjob
            by_cases heq : job = processedJob
            · subst job
              simp [Function.update] at hjob
            · have hold := hgood.testedRecorded job q
                (by simpa [Function.update, heq] using hjob)
              simpa [Transcript.testResults_append] using hold
          · intro job hmem
            rw [Transcript.processedLabels_append_processed] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · simpa [Transcript.testResults_append] using
                hgood.processedRecorded job hold
            · have heq : job = processedJob := by simpa using hnew
              subst job
              simp only [Transcript.testResults_append, List.mem_map]
              exact ⟨(processedJob, p),
                List.mem_append_left _ htested, rfl⟩
          · intro job hmem
            rw [Transcript.processedLabels_append_processed] at hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · have hdone := hgood.processedDone job hold
              by_cases heq : job = processedJob
              · subst job
                exact (hnotProcessed hold).elim
              · simpa [Function.update, heq] using hdone
            · have heq : job = processedJob := by simpa using hnew
              subst job
              simp [Function.update]
          · intro job hjob
            rw [Transcript.startedLabels_append_processed]
            by_cases heq : job = processedJob
            · subst job
              apply hgood.nonuntouchedStarted processedJob
              rw [hstate]
              simp
            · apply hgood.nonuntouchedStarted job
              intro hold
              apply hjob
              simpa [Function.update, heq] using hold
          · intro job q htest hnot
            rw [Transcript.testResults_append] at htest
            have htestOld :
                (job, q) ∈ config.transcript.testResults := by
              simpa using htest
            rw [Transcript.processedLabels_append_processed] at hnot
            have hnotOld :
                job ∉ config.transcript.processedLabels := by
              intro hmem
              exact hnot (List.mem_append_left _ hmem)
            by_cases heq : job = processedJob
            · subst job
              exact (hnot (by simp)).elim
            · simpa [Function.update, heq] using
                hgood.recordedUnprocessedTested
                  job q htestOld hnotOld
  | raw rawJob =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hstate : config.jobs rawJob with
          | tested p =>
              simp [Config.step, hstate] at hstep
          | done =>
              simp [Config.step, hstate] at hstep
          | untouched =>
              simp [Config.step, hstate] at hstep
              subst next
              have hnotProcessed :
                  rawJob ∉ config.transcript.processedLabels := by
                intro hmem
                have hdone := hgood.processedDone rawJob hmem
                rw [hstate] at hdone
                contradiction
              constructor
              · simpa using hgood.processedNodup
              · intro job p hjob
                by_cases heq : job = rawJob
                · subst job
                  simp [Function.update] at hjob
                · have hold := hgood.testedRecorded job p
                    (by simpa [Function.update, heq] using hjob)
                  simpa [Transcript.testResults_append] using hold
              · intro job hmem
                rw [Transcript.processedLabels_append_rawCompleted] at hmem
                simpa [Transcript.testResults_append] using
                  hgood.processedRecorded job hmem
              · intro job hmem
                rw [Transcript.processedLabels_append_rawCompleted] at hmem
                have hdone := hgood.processedDone job hmem
                by_cases heq : job = rawJob
                · subst job
                  exact (hnotProcessed hmem).elim
                · simpa [Function.update, heq] using hdone
              · intro job hjob
                by_cases heq : job = rawJob
                · subst job
                  simp
                · rw [Transcript.startedLabels_append_rawCompleted]
                  exact List.mem_append_left _
                    (hgood.nonuntouchedStarted job
                      (by
                        intro hold
                        apply hjob
                        simpa [Function.update, heq] using hold))
              · intro job p htest hnot
                rw [Transcript.testResults_append] at htest
                have htestOld :
                    (job, p) ∈ config.transcript.testResults := by
                  simpa using htest
                rw [Transcript.processedLabels_append_rawCompleted] at hnot
                by_cases heq : job = rawJob
                · subst job
                  exact
                    (hstarted.untouched_not_mem rawJob hstate
                      (HiddenStoppingOracle.Transcript.mem_startedLabels_of_mem_testResults
                        htestOld)).elim
                · simpa [Function.update, heq] using
                    hgood.recordedUnprocessedTested
                      job p htestOld hnot

theorem Config.ProcessHistoryInvariant.processed_length_le_tests
    {config : Config n} (hgood : config.ProcessHistoryInvariant) :
    config.transcript.processedLabels.length ≤
      config.transcript.testResults.length := by
  let processed := config.transcript.processedLabels
  let tested := config.transcript.testResults.map Prod.fst
  have hsubset : processed.toFinset ⊆ tested.toFinset := by
    intro job hjob
    have hmem : job ∈ processed := by
      simpa [processed] using hjob
    have htested := hgood.processedRecorded job (by
      simpa [processed] using hmem)
    simpa [tested] using htested
  calc
    config.transcript.processedLabels.length =
        processed.toFinset.card := by
      rw [List.toFinset_card_of_nodup]
      simpa [processed] using hgood.processedNodup
    _ ≤ tested.toFinset.card := Finset.card_le_card hsubset
    _ ≤ tested.length := List.toFinset_card_le tested
    _ = config.transcript.testResults.length := by
      simp [tested]

theorem Config.ProcessHistoryInvariant.processed_length_add_one_le_tests
    {config : Config n} (hgood : config.ProcessHistoryInvariant)
    {job : Label n} {p : ℝ}
    (hstate : config.jobs job = .tested p) :
    config.transcript.processedLabels.length + 1 ≤
      config.transcript.testResults.length := by
  let processed := config.transcript.processedLabels
  let tested := config.transcript.testResults.map Prod.fst
  have hnot : job ∉ processed := by
    intro hmem
    have hdone := hgood.processedDone job (by
      simpa [processed] using hmem)
    rw [hstate] at hdone
    contradiction
  have hnodup : (job :: processed).Nodup := by
    simpa [hnot, processed] using hgood.processedNodup
  have hsubset : (job :: processed).toFinset ⊆ tested.toFinset := by
    intro other hother
    have hcases : other = job ∨ other ∈ processed := by
      simpa using hother
    rcases hcases with heq | hold
    · subst other
      have htest := hgood.testedRecorded job p hstate
      exact List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨(job, p), htest, rfl⟩)
    · exact List.mem_toFinset.mpr
        (hgood.processedRecorded other (by
          simpa [processed] using hold))
  calc
    config.transcript.processedLabels.length + 1 =
        (job :: processed).toFinset.card := by
      rw [List.toFinset_card_of_nodup hnodup]
      simp [processed]
    _ ≤ tested.toFinset.card := Finset.card_le_card hsubset
    _ ≤ tested.length := List.toFinset_card_le tested
    _ = config.transcript.testResults.length := by
      simp [tested]

/-! ## Abstract completion workloads before the stopping time -/

/-- Before the stopping time, a raw completion has workload `u`, while a
completed tested-long job has already consumed its unit test and its `u`
units of processing. -/
def Transcript.preCompletionWeights (u : ℝ) : Transcript n → List ℝ
  | [] => []
  | .testResult _ _ :: rest => preCompletionWeights u rest
  | .processed _ :: rest => (1 + u) :: preCompletionWeights u rest
  | .rawCompleted _ :: rest => u :: preCompletionWeights u rest

@[simp] theorem Transcript.preCompletionWeights_nil (u : ℝ) :
    preCompletionWeights u ([] : Transcript n) = [] := rfl

@[simp] theorem Transcript.preCompletionWeights_append
    (u : ℝ) (left right : Transcript n) :
    preCompletionWeights u (left ++ right) =
      preCompletionWeights u left ++ preCompletionWeights u right := by
  induction left with
  | nil => simp
  | cons observation rest ih =>
      cases observation <;> simp [preCompletionWeights, ih]

@[simp] theorem Transcript.preCompletionWeights_append_test
    (u p : ℝ) (transcript : Transcript n) (job : Label n) :
    preCompletionWeights u (transcript ++ [.testResult job p]) =
      preCompletionWeights u transcript := by
  simp [preCompletionWeights]

@[simp] theorem Transcript.preCompletionWeights_append_processed
    (u : ℝ) (transcript : Transcript n) (job : Label n) :
    preCompletionWeights u (transcript ++ [.processed job]) =
      preCompletionWeights u transcript ++ [1 + u] := by
  simp [preCompletionWeights]

@[simp] theorem Transcript.preCompletionWeights_append_raw
    (u : ℝ) (transcript : Transcript n) (job : Label n) :
    preCompletionWeights u (transcript ++ [.rawCompleted job]) =
      preCompletionWeights u transcript ++ [u] := by
  simp [preCompletionWeights]

theorem Transcript.preCompletionWeights_sum
    (u : ℝ) (transcript : Transcript n) :
    (preCompletionWeights u transcript).sum =
      (1 + u) * transcript.processedLabels.length +
        u * HiddenStoppingOracle.rawCount transcript := by
  induction transcript with
  | nil =>
      simp [preCompletionWeights, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation <;>
        simp [preCompletionWeights, Transcript.processedLabels,
          HiddenStoppingOracle.rawCount, ih] <;> ring

theorem Transcript.preCompletionWeights_length
    (u : ℝ) (transcript : Transcript n) :
    (preCompletionWeights u transcript).length =
      HiddenStoppingOracle.rawCount transcript +
        transcript.processedLabels.length := by
  induction transcript with
  | nil =>
      simp [preCompletionWeights, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation <;>
        simp [preCompletionWeights, Transcript.processedLabels,
          HiddenStoppingOracle.rawCount, ih] <;> omega

theorem Transcript.startedLabels_length_eq_raw_add_tests
    (transcript : Transcript n) :
    transcript.startedLabels.length =
      HiddenStoppingOracle.rawCount transcript +
        transcript.testResults.length := by
  induction transcript with
  | nil =>
      simp [Transcript.startedLabels, Transcript.testResults,
        HiddenStoppingOracle.rawCount]
  | cons observation rest ih =>
      cases observation <;> simp [ih] <;> omega

theorem Transcript.preCompletionWeights_perm_blocks
    (u : ℝ) (transcript : Transcript n) :
    (preCompletionWeights u transcript).Perm
      (List.replicate (HiddenStoppingOracle.rawCount transcript) u ++
        List.replicate transcript.processedLabels.length (1 + u)) := by
  induction transcript with
  | nil =>
      simp [preCompletionWeights, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [preCompletionWeights, Transcript.processedLabels,
            HiddenStoppingOracle.rawCount] using ih
      | rawCompleted job =>
          simpa [preCompletionWeights, Transcript.processedLabels,
            HiddenStoppingOracle.rawCount, List.replicate_succ] using
            ih.cons u
      | processed job =>
          have hmove :
              ((1 + u) ::
                (List.replicate
                    (HiddenStoppingOracle.rawCount rest) u ++
                  List.replicate
                    (Transcript.processedLabels rest).length (1 + u))).Perm
                (List.replicate
                    (HiddenStoppingOracle.rawCount rest) u ++
                  (1 + u) ::
                    List.replicate
                      (Transcript.processedLabels rest).length (1 + u)) :=
            List.perm_middle.symm
          simpa [preCompletionWeights, Transcript.processedLabels,
            HiddenStoppingOracle.rawCount, List.replicate_succ] using
            (ih.cons (1 + u)).trans hmove

theorem preCompletionWeights_blocks_le
    {u : ℝ} (hu : 0 ≤ u) (transcript : Transcript n) :
    prefixCost
        (List.replicate (HiddenStoppingOracle.rawCount transcript) u ++
          List.replicate transcript.processedLabels.length (1 + u)) ≤
      prefixCost (Transcript.preCompletionWeights u transcript) := by
  apply pairwise_prefixCost_minimal
  · simp [List.pairwise_append]
  · exact (transcript.preCompletionWeights_perm_blocks u).symm

theorem Transcript.elapsed_const_long_exact
    (u : ℝ) (transcript : Transcript n) :
    transcriptElapsed (.finite u) (fun _ => u) transcript =
      transcript.testResults.length +
        u * transcript.processedLabels.length +
        u * HiddenStoppingOracle.rawCount transcript := by
  induction transcript with
  | nil =>
      simp [transcriptElapsed, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation <;>
        simp [transcriptElapsed, Observation.duration,
          rawDuration, Transcript.processedLabels,
          HiddenStoppingOracle.rawCount, ih] <;> ring

/-- Every public test in the trace returned the same long value. -/
def Transcript.AllTestsEqual (u : ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults → p = u

theorem Transcript.AllTestsEqual.of_append_left
    {u : ℝ} {left right : Transcript n}
    (hall : AllTestsEqual u (left ++ right)) :
    AllTestsEqual u left := by
  intro job p hmem
  apply hall job p
  rw [Transcript.testResults_append]
  exact List.mem_append_left _ hmem

def Config.PreCostInvariant (u : ℝ) (config : Config n) : Prop :=
  prefixCost (config.transcript.preCompletionWeights u) ≤
    suffixWeightedDuration (.finite u) (fun _ => u)
      config.transcript

theorem Config.initial_preCostInvariant (n : ℕ) (u : ℝ) :
    (Config.initial n).PreCostInvariant u := by
  simp [PreCostInvariant, Config.initial]

theorem Transcript.preCompletionWeights_sum_le_elapsed
    {u : ℝ} {config : Config n}
    (hgood : config.ProcessHistoryInvariant) :
    (config.transcript.preCompletionWeights u).sum ≤
      transcriptElapsed (.finite u) (fun _ => u)
        config.transcript := by
  have hcount :
      (config.transcript.processedLabels.length : ℝ) ≤
        config.transcript.testResults.length := by
    exact_mod_cast hgood.processed_length_le_tests
  rw [Transcript.preCompletionWeights_sum,
    Transcript.elapsed_const_long_exact]
  linarith

theorem Transcript.preCompletionWeights_sum_add_one_le_elapsed
    {u : ℝ} {config : Config n} {job : Label n} {p : ℝ}
    (hgood : config.ProcessHistoryInvariant)
    (hstate : config.jobs job = .tested p) :
    (config.transcript.preCompletionWeights u).sum + 1 ≤
      transcriptElapsed (.finite u) (fun _ => u)
        config.transcript := by
  have hcount :
      (config.transcript.processedLabels.length : ℝ) + 1 ≤
        config.transcript.testResults.length := by
    exact_mod_cast
      hgood.processed_length_add_one_le_tests hstate
  rw [Transcript.preCompletionWeights_sum,
    Transcript.elapsed_const_long_exact]
  linarith

theorem Config.preCostInvariant_step_of_allTestsEqual
    {u : ℝ} (hu : 0 < u)
    {oracle : Oracle n} {config next : Config n} {action : Action n}
    (hprocess : config.ProcessHistoryInvariant)
    (hcost : config.PreCostInvariant u)
    (hstep : config.step (.finite u) oracle action = some next)
    (hall : next.transcript.AllTestsEqual u) :
    next.PreCostInvariant u := by
  have huNe : u ≠ 0 := hu.ne'
  cases action with
  | test testedJob =>
      cases hstate : config.jobs testedJob with
      | tested p =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hp :
              oracle config.transcript testedJob = u := by
            apply hall testedJob
              (oracle config.transcript testedJob)
            simp
          rw [hp]
          simpa [PreCostInvariant,
            Transcript.preCompletionWeights,
            suffixWeightedDuration_append_singleton,
            Observation.completionLabel, huNe] using hcost
  | process processedJob =>
      cases hstate : config.jobs processedJob with
      | untouched =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          have hp : p = u := by
            apply hall processedJob p
            rw [Transcript.testResults_append]
            exact List.mem_append_left _
              (hprocess.testedRecorded processedJob p hstate)
          subst p
          have hsum :=
            Transcript.preCompletionWeights_sum_add_one_le_elapsed
              (u := u) hprocess hstate
          have happend :
              prefixCost
                  (config.transcript.preCompletionWeights u ++ [1 + u]) =
                prefixCost
                    (config.transcript.preCompletionWeights u) +
                  (config.transcript.preCompletionWeights u).sum +
                  (1 + u) := by
            rw [prefixCost_append]
            simp
          unfold PreCostInvariant at hcost ⊢
          rw [Transcript.preCompletionWeights_append_processed,
            happend,
            suffixWeightedDuration_append_singleton]
          simp [Observation.completionLabel, huNe,
            Observation.duration]
          linarith
  | raw rawJob =>
      cases hstate : config.jobs rawJob with
      | tested p =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hsum :=
            Transcript.preCompletionWeights_sum_le_elapsed hprocess
              (u := u)
          have happend :
              prefixCost
                  (config.transcript.preCompletionWeights u ++ [u]) =
                prefixCost
                    (config.transcript.preCompletionWeights u) +
                  (config.transcript.preCompletionWeights u).sum + u := by
            rw [prefixCost_append]
            simp
          unfold PreCostInvariant at hcost ⊢
          rw [Transcript.preCompletionWeights_append_raw,
            happend,
            suffixWeightedDuration_append_singleton]
          simp [Observation.completionLabel, Observation.duration,
            rawDuration]
          linarith

theorem Config.transcript_eq_append_singleton_of_step
    {cap : Cap} {oracle : Oracle n} {config next : Config n}
    {action : Action n}
    (hstep : config.step cap oracle action = some next) :
    ∃ observation,
      next.transcript = config.transcript ++ [observation] := by
  cases action with
  | test job =>
      cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      exact ⟨.testResult job (oracle config.transcript job), rfl⟩
  | process job =>
      cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      exact ⟨.processed job, rfl⟩
  | raw job =>
      cases cap <;> cases hstate : config.jobs job <;>
        simp [Config.step, hstate] at hstep
      subst next
      exact ⟨.rawCompleted job, rfl⟩

/-- A configuration/partial assignment pair obtained by finitely many
successful adaptive steps from the initial state. -/
inductive AdaptiveReachable
    (cap : Cap) (adversary : Oracle n) :
    Config n → PartialAssignment n → Prop
  | initial :
      AdaptiveReachable cap adversary
        (Config.initial n) emptyAssignment
  | step {config next : Config n}
      {assignment nextAssignment : PartialAssignment n}
      {action : Action n}
      (hreachable :
        AdaptiveReachable cap adversary config assignment)
      (hstep :
        adaptiveStep cap adversary config assignment action =
          some (next, nextAssignment)) :
      AdaptiveReachable cap adversary next nextAssignment

/-- A finite successful adaptive continuation from one reachable state to a
later state. -/
inductive AdaptiveExtension
    (cap : Cap) (adversary : Oracle n)
    (start : Config n) (startAssignment : PartialAssignment n) :
    Config n → PartialAssignment n → Prop
  | refl :
      AdaptiveExtension cap adversary start startAssignment
        start startAssignment
  | step {config next : Config n}
      {assignment nextAssignment : PartialAssignment n}
      {action : Action n}
      (hextension :
        AdaptiveExtension cap adversary start startAssignment
          config assignment)
      (hstep :
        adaptiveStep cap adversary config assignment action =
          some (next, nextAssignment)) :
      AdaptiveExtension cap adversary start startAssignment
        next nextAssignment

theorem AdaptiveExtension.reachable
    {cap : Cap} {adversary : Oracle n}
    {start config : Config n}
    {startAssignment assignment : PartialAssignment n}
    (hstart :
      AdaptiveReachable cap adversary start startAssignment)
    (hext :
      AdaptiveExtension cap adversary start startAssignment
        config assignment) :
    AdaptiveReachable cap adversary config assignment := by
  induction hext with
  | refl => exact hstart
  | step hext hstep ih =>
      exact AdaptiveReachable.step ih hstep

theorem AdaptiveReachable.startedHistoryInvariant
    {cap : Cap} {adversary : Oracle n}
    {config : Config n} {assignment : PartialAssignment n}
    (hreach : AdaptiveReachable cap adversary config assignment) :
    config.StartedHistoryInvariant := by
  induction hreach with
  | initial =>
      exact Config.initial_startedHistoryInvariant n
  | step hreach hstep ih =>
      exact Config.startedHistoryInvariant_step ih
        (HiddenStoppingOracle.adaptiveStep_configStep hstep)

theorem AdaptiveReachable.processHistoryInvariant
    {cap : Cap} {adversary : Oracle n}
    {config : Config n} {assignment : PartialAssignment n}
    (hreach : AdaptiveReachable cap adversary config assignment) :
    config.ProcessHistoryInvariant := by
  induction hreach with
  | initial =>
      exact Config.initial_processHistoryInvariant n
  | step hreach hstep ih =>
      exact Config.processHistoryInvariant_step ih
        hreach.startedHistoryInvariant
        (HiddenStoppingOracle.adaptiveStep_configStep hstep)

theorem AdaptiveReachable.supportedByTranscript
    {cap : Cap} {adversary : Oracle n}
    {config : Config n} {assignment : PartialAssignment n}
    (hreach : AdaptiveReachable cap adversary config assignment) :
    SupportedByTranscript assignment config.transcript := by
  induction hreach with
  | initial =>
      simp [SupportedByTranscript, Config.initial, emptyAssignment]
  | step hreach hstep ih =>
      exact adaptiveStep_supportedByTranscript
        cap adversary _ _ _ _ _ ih hstep

theorem runAdaptiveFuel_reachable
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n)
    (hreach : AdaptiveReachable cap adversary config assignment) :
    AdaptiveReachable cap adversary
      (runAdaptiveFuel cap adversary strategy fuel
        config assignment).result.config
      (runAdaptiveFuel cap adversary strategy fuel
        config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hreach
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hreach
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hreach
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                AdaptiveReachable.step hreach hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem adaptiveRun_reachable
    (cap : Cap) (adversary : Oracle n)
    (strategy : Strategy n) (fuel : ℕ) :
    AdaptiveReachable cap adversary
      (adaptiveRun cap adversary strategy fuel).result.config
      (adaptiveRun cap adversary strategy fuel).assigned := by
  exact runAdaptiveFuel_reachable cap adversary strategy fuel
    (Config.initial n) emptyAssignment AdaptiveReachable.initial

theorem AdaptiveReachable.preCostInvariant_of_allTestsEqual
    {u : ℝ} (hu : 0 < u) {adversary : Oracle n}
    {config : Config n} {assignment : PartialAssignment n}
    (hreach :
      AdaptiveReachable (.finite u) adversary config assignment)
    (hall : config.transcript.AllTestsEqual u) :
    config.PreCostInvariant u := by
  induction hreach with
  | initial =>
      exact Config.initial_preCostInvariant n u
  | @step previous next previousAssignment nextAssignment action
      hreach hstep ih =>
      have hbase :=
        HiddenStoppingOracle.adaptiveStep_configStep hstep
      obtain ⟨observation, happend⟩ :=
        Config.transcript_eq_append_singleton_of_step hbase
      have hallPrevious : previous.transcript.AllTestsEqual u := by
        apply Transcript.AllTestsEqual.of_append_left
          (right := [observation])
        simpa [happend] using hall
      exact Config.preCostInvariant_step_of_allTestsEqual
        hu hreach.processHistoryInvariant
          (ih hallPrevious) hbase hall

end Online

namespace HiddenStoppingOracle

open Online

theorem adaptiveReachable_lawfulTrace
    {n : ℕ} {u α : ℝ}
    {config : Config n} {assignment : PartialAssignment n}
    (hreach :
      AdaptiveReachable (.finite u) (oracle n u α)
        config assignment) :
    LawfulTrace n u α config.transcript := by
  induction hreach with
  | initial =>
      exact LawfulTrace.nil
  | step hreach hstep ih =>
      exact adaptiveStep_lawful
        hreach.startedHistoryInvariant
        hreach.supportedByTranscript ih hstep

theorem LawfulTrace.allTestsEqual_of_not_crossed
    {n : ℕ} {u α : ℝ} (hu : u ≠ 0) (hα : 0 ≤ α)
    {transcript : Transcript n}
    (hlawful : LawfulTrace n u α transcript)
    (hbelow : ¬ Crossed n u α transcript) :
    transcript.AllTestsEqual u := by
  induction hlawful with
  | nil =>
      simp [Transcript.AllTestsEqual]
  | testLong previous job hlawful hprevious ih =>
      have hall := ih hprevious
      intro other p hmem
      rw [Transcript.testResults_append] at hmem
      rcases List.mem_append.mp hmem with hold | hlast
      · exact hall other p hold
      · have hpair : (other, p) = (job, u) := by
          simpa using hlast
        simpa using congrArg Prod.snd hpair
  | testZero previous job hlawful hcrossed ih =>
      exact
        (hbelow
          (hcrossed.append_zero_test hu job)).elim
  | processed previous job hlawful ih =>
      have hprevious : ¬ Crossed n u α previous := by
        intro hcrossed
        exact hbelow (hcrossed.append_processed job)
      have hall := ih hprevious
      simpa [Transcript.AllTestsEqual,
        Transcript.testResults_append] using hall
  | rawCompleted previous job hlawful ih =>
      have hprevious : ¬ Crossed n u α previous := by
        intro hcrossed
        exact hbelow (hcrossed.append_raw hα job)
      have hall := ih hprevious
      simpa [Transcript.AllTestsEqual,
        Transcript.testResults_append] using hall

theorem allTestsEqual_longCount_eq_testResults_length
    {n : ℕ} {u : ℝ} {transcript : Transcript n}
    (hall : transcript.AllTestsEqual u) :
    longCount u transcript = transcript.testResults.length := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      have htail : Transcript.AllTestsEqual u rest := by
        intro job p hmem
        apply hall job p
        cases observation <;> simp [hmem]
      cases observation with
      | testResult job p =>
          have hp : p = u := hall job p (by simp)
          subst p
          simp [ih htail]
      | processed job =>
          simp [ih htail]
      | rawCompleted job =>
          simp [ih htail]

theorem TestResultsBinary.of_append_right
    {n : ℕ} {u : ℝ} {left right : Transcript n}
    (hbinary : TestResultsBinary u (left ++ right)) :
    TestResultsBinary u right := by
  intro job p hmem
  apply hbinary job p
  rw [Transcript.testResults_append]
  exact List.mem_append_right _ hmem

theorem allTestsEqual_zero_of_binary_longCount_zero
    {n : ℕ} {u : ℝ} (hu : u ≠ 0)
    {transcript : Transcript n}
    (hbinary : TestResultsBinary u transcript)
    (hlong : longCount u transcript = 0) :
    transcript.AllTestsEqual 0 := by
  induction transcript with
  | nil =>
      simp [Transcript.AllTestsEqual]
  | cons observation rest ih =>
      have hbinaryTail : TestResultsBinary u rest := by
        intro job p hmem
        exact hbinary job p (by
          cases observation <;> simp_all)
      cases observation with
      | testResult job p =>
          have hp := hbinary job p (by simp)
          rcases hp with rfl | rfl
          · have hlongTail : longCount u rest = 0 := by
              simpa [longCount, Ne.symm hu] using hlong
            have htail := ih hbinaryTail hlongTail
            intro other q hmem
            simp only [Transcript.testResults_testResult_cons,
              List.mem_cons] at hmem
            rcases hmem with hnew | hold
            · have hpair : (other, q) = (job, 0) := hnew
              simpa using congrArg Prod.snd hpair
            · exact htail other q hold
          · simp [longCount] at hlong
      | processed job =>
          have htail := ih hbinaryTail (by simpa using hlong)
          simpa [Transcript.AllTestsEqual] using htail
      | rawCompleted job =>
          have htail := ih hbinaryTail (by simpa using hlong)
          simpa [Transcript.AllTestsEqual] using htail

theorem adaptiveStep_preserves_crossed_and_longCount
    {n : ℕ} {u α : ℝ} (hu : u ≠ 0) (hα : 0 ≤ α)
    {config next : Config n}
    {assignment nextAssignment : PartialAssignment n}
    {action : Action n}
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      SupportedByTranscript assignment config.transcript)
    (hcross : Crossed n u α config.transcript)
    (hstep :
      adaptiveStep (.finite u) (oracle n u α)
        config assignment action = some (next, nextAssignment)) :
    Crossed n u α next.transcript ∧
      longCount u next.transcript =
        longCount u config.transcript := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          have hnone :=
            assignment_eq_none_of_untouched
              hstarted hsupported hjob
          have horacle := oracle_eq_zero_of_crossed hcross job
          simp [adaptiveStep, Config.step, hjob,
            adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          constructor
          · exact hcross.append_zero_test hu job
          · exact longCount_append_testResult_ne
              u config.transcript job 0 (Ne.symm hu)
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          exact ⟨hcross.append_processed job, by simp⟩
  | raw job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          exact ⟨hcross.append_raw hα job, by simp⟩

/-- The concrete successful step which first reaches the stopping line. -/
def FirstCrossingReachable
    (n : ℕ) (u α : ℝ)
    (config : Config n) (assignment : PartialAssignment n) : Prop :=
  (∃ before beforeAssignment job,
      AdaptiveReachable (.finite u) (oracle n u α)
        before beforeAssignment ∧
      adaptiveStep (.finite u) (oracle n u α)
          before beforeAssignment (.test job) =
        some (config, assignment) ∧
      FirstCrossingAt n u α before.transcript
        (.testResult job u)) ∨
  (∃ before beforeAssignment job,
      AdaptiveReachable (.finite u) (oracle n u α)
        before beforeAssignment ∧
      adaptiveStep (.finite u) (oracle n u α)
          before beforeAssignment (.raw job) =
        some (config, assignment) ∧
      FirstCrossingAt n u α before.transcript
        (.rawCompleted job))

theorem firstCrossingReachable_of_step
    {n : ℕ} {u α : ℝ}
    {config next : Config n}
    {assignment nextAssignment : PartialAssignment n}
    {action : Action n}
    (hreach :
      AdaptiveReachable (.finite u) (oracle n u α)
        config assignment)
    (hbelow : ¬ Crossed n u α config.transcript)
    (hcross : Crossed n u α next.transcript)
    (hstep :
      adaptiveStep (.finite u) (oracle n u α)
        config assignment action = some (next, nextAssignment)) :
    FirstCrossingReachable n u α next nextAssignment := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          have hnone :=
            assignment_eq_none_of_untouched
              hreach.startedHistoryInvariant
              hreach.supportedByTranscript hjob
          have horacle := oracle_eq_long_of_not_crossed hbelow job
          simp [adaptiveStep, Config.step, hjob,
            adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          left
          exact ⟨config, assignment, job, hreach,
            by
              simpa [adaptiveStep, Config.step, hjob,
                adaptiveOracle, adaptiveValue, hnone, horacle] using
                hassignment,
            hbelow, hcross⟩
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          exact (hbelow (by
            unfold Crossed at *
            rwa [surplus_append_processed] at hcross)).elim
  | raw job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          right
          exact ⟨config, assignment, job, hreach,
            by
              simpa [adaptiveStep, Config.step, hjob] using
                hassignment,
            hbelow, hcross⟩

theorem FirstCrossingReachable.allTestsEqual
    {n : ℕ} {u α : ℝ} (hu : u ≠ 0) (hα : 0 ≤ α)
    {config : Config n} {assignment : PartialAssignment n}
    (hfirst :
      FirstCrossingReachable n u α config assignment) :
    config.transcript.AllTestsEqual u := by
  rcases hfirst with
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩ |
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩
  · have hall :=
      (adaptiveReachable_lawfulTrace hreach).allTestsEqual_of_not_crossed
        hu hα hcross.1
    have hbase := adaptiveStep_configStep hstep
    have hstate : before.jobs job = .untouched := by
      have henabled :=
        (Config.step_some_iff_enabled (.finite u)
          (adaptiveOracle (oracle n u α) beforeAssignment)
          before (.test job)).mp ⟨config, hbase⟩
      simpa [Action.Enabled] using henabled
    have hnone :=
      assignment_eq_none_of_untouched
        hreach.startedHistoryInvariant
        hreach.supportedByTranscript
        hstate
    have horacle := oracle_eq_long_of_not_crossed hcross.1 job
    simp [adaptiveStep, Config.step, hstate,
      adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
    rcases hstep with ⟨hconfig, hassignment⟩
    subst config
    intro other p hmem
    rw [Transcript.testResults_append] at hmem
    rcases List.mem_append.mp hmem with hold | hlast
    · exact hall other p hold
    · have hpair : (other, p) = (job, u) := by
        simpa using hlast
      simpa using congrArg Prod.snd hpair
  · have hall :=
      (adaptiveReachable_lawfulTrace hreach).allTestsEqual_of_not_crossed
        hu hα hcross.1
    cases hstate : before.jobs job with
    | tested p =>
        simp [adaptiveStep, Config.step, hstate] at hstep
    | done =>
        simp [adaptiveStep, Config.step, hstate] at hstep
    | untouched =>
        simp [adaptiveStep, Config.step, hstate] at hstep
        rcases hstep with ⟨hconfig, hassignment⟩
        subst config
        simpa [Transcript.AllTestsEqual,
          Transcript.testResults_append] using hall

theorem FirstCrossingReachable.reachable
    {n : ℕ} {u α : ℝ}
    {config : Config n} {assignment : PartialAssignment n}
    (hfirst :
      FirstCrossingReachable n u α config assignment) :
    AdaptiveReachable (.finite u) (oracle n u α)
      config assignment := by
  rcases hfirst with
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩ |
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩
  · exact AdaptiveReachable.step hreach hstep
  · exact AdaptiveReachable.step hreach hstep

theorem FirstCrossingReachable.countShape
    {n : ℕ} {u α : ℝ}
    {config : Config n} {assignment : PartialAssignment n}
    (hfirst :
      FirstCrossingReachable n u α config assignment) :
    (∃ (before : Config n) (job : Label n),
      FirstCrossingAt n u α before.transcript
          (.testResult job u) ∧
      rawCount config.transcript =
        rawCount before.transcript ∧
      longCount u config.transcript =
        longCount u before.transcript + 1) ∨
    (∃ (before : Config n) (job : Label n),
      FirstCrossingAt n u α before.transcript
          (.rawCompleted job) ∧
      rawCount config.transcript =
        rawCount before.transcript + 1 ∧
      longCount u config.transcript =
        longCount u before.transcript) := by
  rcases hfirst with
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩ |
      ⟨before, beforeAssignment, job, hreach, hstep, hcross⟩
  · have hbase := adaptiveStep_configStep hstep
    have hstate : before.jobs job = .untouched := by
      have henabled :=
        (Config.step_some_iff_enabled (.finite u)
          (adaptiveOracle (oracle n u α) beforeAssignment)
          before (.test job)).mp ⟨config, hbase⟩
      simpa [Action.Enabled] using henabled
    have hnone :=
      assignment_eq_none_of_untouched
        hreach.startedHistoryInvariant
        hreach.supportedByTranscript hstate
    have horacle := oracle_eq_long_of_not_crossed hcross.1 job
    simp [adaptiveStep, Config.step, hstate,
      adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
    rcases hstep with ⟨hconfig, hassignment⟩
    subst config
    left
    exact ⟨before, job, hcross, by simp, by simp⟩
  · cases hstate : before.jobs job with
    | tested p =>
        simp [adaptiveStep, Config.step, hstate] at hstep
    | done =>
        simp [adaptiveStep, Config.step, hstate] at hstep
    | untouched =>
        simp [adaptiveStep, Config.step, hstate] at hstep
        rcases hstep with ⟨hconfig, hassignment⟩
        subst config
        right
        exact ⟨before, job, hcross, by simp, by simp⟩

/-- A crossed reachable configuration contains a reachable first crossing
prefix.  Every later legal oracle step preserves both crossing and the
number of long revelations. -/
theorem adaptiveReachable_exists_firstCrossingPrefix
    {n : ℕ} {u α : ℝ} (hn : 0 < n) (hu : u ≠ 0)
    (hα0 : 0 ≤ α) (hα : 0 < α)
    {config : Config n} {assignment : PartialAssignment n}
    (hreach :
      AdaptiveReachable (.finite u) (oracle n u α)
        config assignment)
    (hcross : Crossed n u α config.transcript) :
    ∃ crossing crossingAssignment,
      FirstCrossingReachable n u α crossing crossingAssignment ∧
      AdaptiveExtension (.finite u) (oracle n u α)
        crossing crossingAssignment config assignment ∧
      ∃ tail,
        config.transcript = crossing.transcript ++ tail ∧
        longCount u config.transcript =
          longCount u crossing.transcript := by
  induction hreach with
  | initial =>
      exact
        (not_crossed_nil hn hα hcross).elim
  | @step previous next previousAssignment nextAssignment action
      hprevious hstep ih =>
      by_cases hpreviousCross :
          Crossed n u α previous.transcript
      · obtain ⟨crossing, crossingAssignment, hfirst,
          hextension, tail, htranscript, hlong⟩ :=
          ih hpreviousCross
        have hpreserve :=
          adaptiveStep_preserves_crossed_and_longCount
            hu hα0 hprevious.startedHistoryInvariant
              hprevious.supportedByTranscript hpreviousCross hstep
        have hbase := adaptiveStep_configStep hstep
        obtain ⟨observation, happend⟩ :=
          Config.transcript_eq_append_singleton_of_step hbase
        refine ⟨crossing, crossingAssignment, hfirst,
          AdaptiveExtension.step hextension hstep,
          tail ++ [observation], ?_, ?_⟩
        · rw [happend, htranscript, List.append_assoc]
        · rw [hpreserve.2, hlong]
      · have hfirst :=
          firstCrossingReachable_of_step
            hprevious hpreviousCross hcross hstep
        exact ⟨next, nextAssignment, hfirst,
          AdaptiveExtension.refl, [],
          by simp, rfl⟩

end HiddenStoppingOracle

namespace Online

def Transcript.extractedWeights
    (weight : Observation n → Option ℝ)
    (transcript : Transcript n) : List ℝ :=
  transcript.filterMap weight

@[simp] theorem Transcript.processedLabels_append
    (left right : Transcript n) :
    (left ++ right).processedLabels =
      left.processedLabels ++ right.processedLabels := by
  simp [Transcript.processedLabels]

theorem Transcript.testLabels_sublist_startedLabels
    (transcript : Transcript n) :
    (transcript.testResults.map Prod.fst).Sublist
      transcript.startedLabels := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          exact ih.cons₂ job
      | processed job =>
          exact ih
      | rawCompleted job =>
          exact ih.cons job

theorem Config.startedLabels_length_eq_card_of_completed
    {config : Config n}
    (hstarted : config.StartedHistoryInvariant)
    (hprocess : config.ProcessHistoryInvariant)
    (hcompleted : ∀ job, config.jobs job = .done) :
    config.transcript.startedLabels.length = n := by
  have hall :
      ∀ job : Label n,
        job ∈ config.transcript.startedLabels := by
    intro job
    apply hprocess.nonuntouchedStarted job
    rw [hcompleted job]
    simp
  have hfinset :
      config.transcript.startedLabels.toFinset =
        (Finset.univ : Finset (Label n)) := by
    ext job
    simp [hall job]
  calc
    config.transcript.startedLabels.length =
        config.transcript.startedLabels.toFinset.card := by
      rw [List.toFinset_card_of_nodup hstarted.nodup]
    _ = (Finset.univ : Finset (Label n)).card := by
      rw [hfinset]
    _ = n := by simp

/-- Processing observations in `tail` whose test already appears in the
crossing prefix. -/
def Transcript.selectedProcessedLabels
    (testedBefore : List (Label n)) (tail : Transcript n) :
    List (Label n) :=
  tail.processedLabels.filter (fun job => job ∈ testedBefore)

/-- The abstract completion workload after crossing.  Every new first touch
is safely charged one unit; processing a job tested before the crossing is
charged its remaining `u` units. -/
def Transcript.postWeight
    (testedBefore : List (Label n)) (u : ℝ) :
    Observation n → Option ℝ
  | .testResult _ _ => some 1
  | .rawCompleted _ => some 1
  | .processed job =>
      if job ∈ testedBefore then some u else none

theorem Transcript.postWeights_perm_blocks
    (testedBefore : List (Label n)) (u : ℝ)
    (tail : Transcript n) :
    (tail.extractedWeights (postWeight testedBefore u)).Perm
      (List.replicate tail.startedLabels.length 1 ++
        List.replicate
          (tail.selectedProcessedLabels testedBefore).length u) := by
  induction tail with
  | nil =>
      simp [Transcript.extractedWeights, postWeight,
        selectedProcessedLabels, Transcript.processedLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simpa [Transcript.extractedWeights, postWeight,
            selectedProcessedLabels, Transcript.processedLabels,
            List.replicate_succ] using ih.cons 1
      | rawCompleted job =>
          simpa [Transcript.extractedWeights, postWeight,
            selectedProcessedLabels, Transcript.processedLabels,
            List.replicate_succ] using ih.cons 1
      | processed job =>
          by_cases hselected : job ∈ testedBefore
          · have hmove :
                (u ::
                  (List.replicate
                      (Transcript.startedLabels rest).length 1 ++
                    List.replicate
                      (Transcript.selectedProcessedLabels
                        testedBefore rest).length
                      u)).Perm
                  (List.replicate
                      (Transcript.startedLabels rest).length 1 ++
                    u ::
                      List.replicate
                        (Transcript.selectedProcessedLabels
                          testedBefore rest).length u) :=
              List.perm_middle.symm
            simpa [Transcript.extractedWeights, postWeight,
              selectedProcessedLabels, Transcript.processedLabels,
              hselected, List.replicate_succ] using
              (ih.cons u).trans hmove
          · simpa [Transcript.extractedWeights, postWeight,
              selectedProcessedLabels, Transcript.processedLabels,
              hselected] using ih

theorem postWeights_blocks_le
    {u : ℝ} (hu : 1 ≤ u)
    (testedBefore : List (Label n)) (tail : Transcript n) :
    prefixCost
        (List.replicate tail.startedLabels.length 1 ++
          List.replicate
            (tail.selectedProcessedLabels testedBefore).length u) ≤
      prefixCost
        (tail.extractedWeights (Transcript.postWeight testedBefore u)) := by
  apply pairwise_prefixCost_minimal
  · simp [List.pairwise_append, hu]
  · exact (tail.postWeights_perm_blocks testedBefore u).symm

/-- In a completed extension, the tests present at the crossing split
exactly into already processed labels and selected later processings. -/
theorem selectedProcessedLabels_count_exact
    {start final : Config n} {tail : Transcript n}
    (happend :
      final.transcript = start.transcript ++ tail)
    (hstartStarted : start.StartedHistoryInvariant)
    (hstartProcess : start.ProcessHistoryInvariant)
    (hfinalProcess : final.ProcessHistoryInvariant)
    (hcompleted : ∀ job, final.jobs job = .done) :
    start.transcript.processedLabels.length +
        (tail.selectedProcessedLabels
          (start.transcript.testResults.map Prod.fst)).length =
      start.transcript.testResults.length := by
  classical
  let tested := start.transcript.testResults.map Prod.fst
  let processed := start.transcript.processedLabels
  let selected := tail.selectedProcessedLabels tested
  have htestedNodup : tested.Nodup := by
    exact List.Nodup.sublist
      start.transcript.testLabels_sublist_startedLabels
      hstartStarted.nodup
  have hprocessedNodup : processed.Nodup := by
    simpa [processed] using hstartProcess.processedNodup
  have hfinalProcessed :
      final.transcript.processedLabels =
        processed ++ tail.processedLabels := by
    simpa [happend, processed]
  have happendNodup :
      (processed ++ tail.processedLabels).Nodup := by
    rw [← hfinalProcessed]
    exact hfinalProcess.processedNodup
  have htailNodup : tail.processedLabels.Nodup :=
    (List.nodup_append.mp happendNodup).2.1
  have hselectedNodup : selected.Nodup := by
    exact htailNodup.filter _
  have hseparate :
      ∀ a ∈ processed, ∀ b ∈ tail.processedLabels, a ≠ b :=
    (List.nodup_append.mp happendNodup).2.2
  have hunion :
      tested.toFinset = processed.toFinset ∪ selected.toFinset := by
    ext job
    constructor
    · intro htestSet
      have htest : job ∈ tested := by simpa using htestSet
      by_cases hprocessed : job ∈ processed
      · simp [hprocessed]
      · have hpair :
            ∃ p, (job, p) ∈ start.transcript.testResults := by
          rcases List.mem_map.mp htest with
            ⟨pair, hpair, hfst⟩
          rcases pair with ⟨testedJob, p⟩
          change testedJob = job at hfst
          subst job
          exact ⟨p, hpair⟩
        rcases hpair with ⟨p, hp⟩
        have hpFinal :
            (job, p) ∈ final.transcript.testResults := by
          rw [happend, Transcript.testResults_append]
          exact List.mem_append_left _ hp
        have htailProcessed : job ∈ tail.processedLabels := by
          by_contra hnotTail
          have hnotFinal :
              job ∉ final.transcript.processedLabels := by
            rw [hfinalProcessed]
            simp [hprocessed, hnotTail]
          have htestedState :=
            hfinalProcess.recordedUnprocessedTested
              job p hpFinal hnotFinal
          rw [hcompleted job] at htestedState
          contradiction
        have hselected : job ∈ selected := by
          simp [selected, Transcript.selectedProcessedLabels,
            htailProcessed, htest]
        simp [hselected]
    · intro hmem
      simp only [Finset.mem_union, List.mem_toFinset] at hmem ⊢
      rcases hmem with hprocessed | hselected
      · exact hstartProcess.processedRecorded job
          (by simpa [processed] using hprocessed)
      · have hfilter :
            job ∈ tail.processedLabels ∧ job ∈ tested := by
          simpa [selected, Transcript.selectedProcessedLabels] using
            hselected
        exact hfilter.2
  have hdisjoint :
      Disjoint processed.toFinset selected.toFinset := by
    apply Finset.disjoint_left.mpr
    intro job hprocessed hselected
    have hp : job ∈ processed := by simpa using hprocessed
    have hs :
        job ∈ tail.processedLabels ∧ job ∈ tested := by
      simpa [selected, Transcript.selectedProcessedLabels] using
        hselected
    exact hseparate job hp job hs.1 rfl
  have hcard :=
    Finset.card_union_of_disjoint hdisjoint
  calc
    start.transcript.processedLabels.length +
        (tail.selectedProcessedLabels
          (start.transcript.testResults.map Prod.fst)).length =
        processed.toFinset.card + selected.toFinset.card := by
      rw [List.toFinset_card_of_nodup hprocessedNodup,
        List.toFinset_card_of_nodup hselectedNodup]
    _ = (processed.toFinset ∪ selected.toFinset).card := hcard.symm
    _ = tested.toFinset.card := by rw [hunion]
    _ = tested.length := List.toFinset_card_of_nodup htestedNodup
    _ = start.transcript.testResults.length := by
      simp [tested]

theorem completionCount_append
    (processingTime : Label n → ℝ)
    (left right : Transcript n) :
    completionCount processingTime (left ++ right) =
      completionCount processingTime left +
        completionCount processingTime right := by
  induction left with
  | nil => simp
  | cons observation rest ih =>
      simp only [List.cons_append, completionCount_cons, ih]
      split_ifs <;> omega

theorem transcriptElapsed_append
    (cap : Cap) (processingTime : Label n → ℝ)
    (left right : Transcript n) :
    transcriptElapsed cap processingTime (left ++ right) =
      transcriptElapsed cap processingTime left +
        transcriptElapsed cap processingTime right := by
  induction left with
  | nil => simp
  | cons observation rest ih =>
      simp [ih]
      ring

theorem suffixWeightedDuration_append
    (cap : Cap) (processingTime : Label n → ℝ)
    (left right : Transcript n) :
    suffixWeightedDuration cap processingTime (left ++ right) =
      suffixWeightedDuration cap processingTime left +
        completionCount processingTime right *
          transcriptElapsed cap processingTime left +
        suffixWeightedDuration cap processingTime right := by
  induction left with
  | nil => simp
  | cons observation rest ih =>
      simp only [List.cons_append, suffixWeightedDuration_cons,
        completionCount_cons, completionCount_append,
        transcriptElapsed_cons]
      rw [ih]
      split_ifs <;> push_cast <;> ring

theorem completionCount_congr
    {left right : Label n → ℝ} {transcript : Transcript n}
    (hcompletion :
      ∀ observation ∈ transcript,
        observation.completionLabel left =
          observation.completionLabel right) :
    completionCount left transcript =
      completionCount right transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hhead := hcompletion observation (by simp)
      have htail :
          ∀ observed ∈ rest,
            observed.completionLabel left =
              observed.completionLabel right :=
        fun observed hobserved =>
          hcompletion observed (by simp [hobserved])
      simp only [completionCount_cons, hhead, ih htail]

theorem suffixWeightedDuration_congr
    (cap : Cap) {left right : Label n → ℝ}
    {transcript : Transcript n}
    (hduration :
      ∀ observation ∈ transcript,
        observation.duration cap left =
          observation.duration cap right)
    (hcompletion :
      ∀ observation ∈ transcript,
        observation.completionLabel left =
          observation.completionLabel right) :
    suffixWeightedDuration cap left transcript =
      suffixWeightedDuration cap right transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hdurationHead := hduration observation (by simp)
      have hcompletionHead := hcompletion observation (by simp)
      have hdurationTail :
          ∀ observed ∈ rest,
            observed.duration cap left =
              observed.duration cap right :=
        fun observed hobserved =>
          hduration observed (by simp [hobserved])
      have hcompletionTail :
          ∀ observed ∈ rest,
            observed.completionLabel left =
              observed.completionLabel right :=
        fun observed hobserved =>
          hcompletion observed (by simp [hobserved])
      rw [suffixWeightedDuration_cons,
        suffixWeightedDuration_cons, hdurationHead,
        completionCount_congr hcompletion, ih hdurationTail hcompletionTail]

theorem transcriptElapsed_congr
    (cap : Cap) {left right : Label n → ℝ}
    {transcript : Transcript n}
    (hduration :
      ∀ observation ∈ transcript,
        observation.duration cap left =
          observation.duration cap right) :
    transcriptElapsed cap left transcript =
      transcriptElapsed cap right transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      rw [transcriptElapsed_cons, transcriptElapsed_cons,
        hduration observation (by simp)]
      apply congrArg (fun z =>
        observation.duration cap right + z)
      exact ih (fun observed hobserved =>
        hduration observed (by simp [hobserved]))

theorem suffixWeightedDuration_eq_const_of_processed
    {u : ℝ} {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (hprocessed :
      ∀ job ∈ transcript.processedLabels,
        processingTime job = u) :
    suffixWeightedDuration (.finite u) processingTime transcript =
      suffixWeightedDuration (.finite u) (fun _ => u) transcript := by
  apply suffixWeightedDuration_congr
  · intro observation hmem
    cases observation with
    | testResult job p => rfl
    | rawCompleted job => rfl
    | processed job =>
        simp only [Observation.duration]
        apply hprocessed job
        unfold Transcript.processedLabels
        simp only [List.mem_filterMap]
        exact ⟨.processed job, hmem, by simp⟩
  · intro observation hmem
    cases observation with
    | testResult job p => rfl
    | rawCompleted job => rfl
    | processed job =>
        simp only [Observation.completionLabel]
        have hp : processingTime job = u := by
          apply hprocessed job
          unfold Transcript.processedLabels
          simp only [List.mem_filterMap]
          exact ⟨.processed job, hmem, by simp⟩
        rw [hp]

theorem transcriptElapsed_eq_const_of_processed
    {u : ℝ} {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (hprocessed :
      ∀ job ∈ transcript.processedLabels,
        processingTime job = u) :
    transcriptElapsed (.finite u) processingTime transcript =
      transcriptElapsed (.finite u) (fun _ => u) transcript := by
  apply transcriptElapsed_congr
  intro observation hmem
  cases observation with
  | testResult job p => rfl
  | rawCompleted job => rfl
  | processed job =>
      simp only [Observation.duration]
      apply hprocessed job
      unfold Transcript.processedLabels
      simp only [List.mem_filterMap]
      exact ⟨.processed job, hmem, by simp⟩

/-! ## Generic lower bound for extracted completion workloads -/

theorem Transcript.extractedWeights_length_le_completionCount
    (processingTime : Label n → ℝ)
    (weight : Observation n → Option ℝ)
    (transcript : Transcript n)
    (hemits :
      ∀ (observation : Observation n), observation ∈ transcript → ∀ w,
        weight observation = some w →
        (observation.completionLabel processingTime).isSome) :
    (transcript.extractedWeights weight).length ≤
      completionCount processingTime transcript := by
  induction transcript with
  | nil =>
      simp [Transcript.extractedWeights]
  | cons observation rest ih =>
      have ih' :
          (Transcript.extractedWeights weight rest).length ≤
            completionCount processingTime rest :=
        ih (fun observed hobserved value hvalue =>
          hemits observed (by simp [hobserved]) value hvalue)
      cases hweight : weight observation with
      | none =>
          by_cases hcompletion :
              (observation.completionLabel processingTime).isSome
          · simp [Transcript.extractedWeights, hweight,
              completionCount, hcompletion] at ih' ⊢
            omega
          · simp [Transcript.extractedWeights, hweight,
              completionCount, hcompletion] at ih' ⊢
            exact ih'
      | some w =>
          have hcompletion :=
            hemits observation (by simp) w hweight
          simp [Transcript.extractedWeights, hweight,
            completionCount, hcompletion] at ih' ⊢
          omega

theorem Transcript.prefixCost_extractedWeights_le_suffixWeighted
    (cap : Cap) (processingTime : Label n → ℝ)
    (weight : Observation n → Option ℝ)
    (transcript : Transcript n)
    (hduration :
      ∀ (observation : Observation n), observation ∈ transcript →
        0 ≤ observation.duration cap processingTime)
    (hemits :
      ∀ (observation : Observation n), observation ∈ transcript → ∀ w,
        weight observation = some w →
        0 ≤ w ∧
        w ≤ observation.duration cap processingTime ∧
        (observation.completionLabel processingTime).isSome) :
    prefixCost (transcript.extractedWeights weight) ≤
      suffixWeightedDuration cap processingTime transcript := by
  induction transcript with
  | nil =>
      simp [Transcript.extractedWeights]
  | cons observation rest ih =>
      have ih' :
          prefixCost
              (Transcript.extractedWeights weight rest) ≤
            suffixWeightedDuration cap processingTime rest :=
        ih
          (fun observed hobserved =>
            hduration observed (by simp [hobserved]))
          (fun observed hobserved value hvalue =>
            hemits observed (by simp [hobserved])
              value hvalue)
      cases hweight : weight observation with
      | none =>
          have hweights :
              Transcript.extractedWeights weight
                  (observation :: rest) =
                Transcript.extractedWeights weight rest := by
            simp [Transcript.extractedWeights, hweight]
          have hterm :
              0 ≤ observation.duration cap processingTime *
                completionCount processingTime
                  (observation :: rest) := by
            exact mul_nonneg
              (hduration observation (by simp)) (by positivity)
          rw [hweights, suffixWeightedDuration_cons]
          linarith
      | some w =>
          obtain ⟨hw0, hwDuration, hcompletion⟩ :=
            hemits observation (by simp) w hweight
          have hcountNat :
              (Transcript.extractedWeights weight rest).length + 1 ≤
                completionCount processingTime
                  (observation :: rest) := by
            rw [completionCount_cons, if_pos hcompletion]
            have hrest :=
              Transcript.extractedWeights_length_le_completionCount
                processingTime weight rest
                (fun observed hobserved value hvalue =>
                  (hemits observed (by simp [hobserved])
                    value hvalue).2.2)
            omega
          have hcount :
              ((Transcript.extractedWeights weight rest).length + 1 : ℝ) ≤
                completionCount processingTime
                  (observation :: rest) := by
            exact_mod_cast hcountNat
          have hleft :
              ((Transcript.extractedWeights weight rest).length + 1 : ℝ) * w ≤
                completionCount processingTime
                    (observation :: rest) * w :=
            mul_le_mul_of_nonneg_right hcount hw0
          have hright :
              completionCount processingTime
                    (observation :: rest) * w ≤
                completionCount processingTime
                    (observation :: rest) *
                  observation.duration cap processingTime :=
            mul_le_mul_of_nonneg_left hwDuration (by positivity)
          have hweights :
              Transcript.extractedWeights weight
                  (observation :: rest) =
                w :: Transcript.extractedWeights weight rest := by
            simp [Transcript.extractedWeights, hweight]
          rw [hweights, prefixCost_cons,
            suffixWeightedDuration_cons]
          have hterm := hleft.trans hright
          calc
            ((Transcript.extractedWeights weight rest).length + 1 : ℝ) *
                  w +
                prefixCost (Transcript.extractedWeights weight rest) ≤
                completionCount processingTime
                    (observation :: rest) *
                    observation.duration cap processingTime +
                  suffixWeightedDuration cap processingTime rest :=
              add_le_add hterm ih'
            _ =
                observation.duration cap processingTime *
                    completionCount processingTime
                      (observation :: rest) +
                  suffixWeightedDuration cap processingTime rest := by
              ring

theorem postCross_suffix_block_lower
    {u : ℝ} (hu : 1 < u)
    (processingTime : Label n → ℝ)
    (start tail : Transcript n)
    (hvalid :
      ∀ job, ValueAdmissible (.finite u) (processingTime job))
    (hzero : tail.AllTestsEqual 0)
    (hlong :
      ∀ job ∈ start.testResults.map Prod.fst,
        processingTime job = u) :
    prefixCost
        (List.replicate tail.startedLabels.length 1 ++
          List.replicate
            (tail.selectedProcessedLabels
              (start.testResults.map Prod.fst)).length u) ≤
      suffixWeightedDuration (.finite u) processingTime tail := by
  let tested := start.testResults.map Prod.fst
  let weight := Transcript.postWeight tested u
  have hblocks :=
    postWeights_blocks_le hu.le tested tail
  have hweighted :
      prefixCost (tail.extractedWeights weight) ≤
        suffixWeightedDuration (.finite u) processingTime tail := by
    apply Transcript.prefixCost_extractedWeights_le_suffixWeighted
      (.finite u) processingTime weight tail
    · intro observation hobservation
      exact Observation.duration_nonneg
        (by simpa [Cap.Valid] using (by linarith : 0 < u))
        hvalid observation
    · intro observation hobservation w hweight
      cases observation with
      | testResult job p =>
          have hp : p = 0 := by
            apply hzero job p
            unfold Transcript.testResults
            simp only [List.mem_filterMap]
            exact ⟨.testResult job p, hobservation, rfl⟩
          subst p
          simp [weight, Transcript.postWeight,
            Observation.duration, Observation.completionLabel] at hweight ⊢
          subst w
          norm_num
      | rawCompleted job =>
          simp [weight, Transcript.postWeight,
            Observation.duration, rawDuration,
            Observation.completionLabel] at hweight ⊢
          subst w
          exact ⟨by norm_num, hu.le⟩
      | processed job =>
          by_cases hselected : job ∈ tested
          · have hp : processingTime job = u := by
              exact hlong job (by simpa [tested] using hselected)
            simp [weight, Transcript.postWeight, hselected,
              Observation.duration, Observation.completionLabel,
              hp] at hweight ⊢
            subst w
            exact ⟨by linarith, ⟨le_rfl, by linarith⟩⟩
          · simp [weight, Transcript.postWeight, hselected] at hweight
  simpa [tested, weight] using hblocks.trans hweighted

theorem postCross_extractedWeights_length_le_completionCount
    {u : ℝ} (hu : 1 < u)
    (processingTime : Label n → ℝ)
    (start tail : Transcript n)
    (hzero : tail.AllTestsEqual 0)
    (hlong :
      ∀ job ∈ start.testResults.map Prod.fst,
        processingTime job = u) :
    (tail.extractedWeights
        (Transcript.postWeight
          (start.testResults.map Prod.fst) u)).length ≤
      completionCount processingTime tail := by
  let tested := start.testResults.map Prod.fst
  let weight := Transcript.postWeight tested u
  apply Transcript.extractedWeights_length_le_completionCount
    processingTime weight tail
  intro observation hobservation w hweight
  cases observation with
  | testResult job p =>
      have hp : p = 0 := by
        apply hzero job p
        unfold Transcript.testResults
        simp only [List.mem_filterMap]
        exact ⟨.testResult job p, hobservation, rfl⟩
      subst p
      simp [weight, Transcript.postWeight,
        Observation.completionLabel] at hweight ⊢
  | rawCompleted job =>
      simp [weight, Transcript.postWeight,
        Observation.completionLabel] at hweight ⊢
  | processed job =>
      by_cases hselected : job ∈ tested
      · have hp : processingTime job = u :=
          hlong job (by simpa [tested] using hselected)
        simp [weight, Transcript.postWeight, hselected,
          Observation.completionLabel, hp] at hweight ⊢
        exact (by linarith : u ≠ 0)
      · simp [weight, Transcript.postWeight, hselected] at hweight

end Online

namespace Online

def Transcript.longTestLabels (u : ℝ) : Transcript n → List (Label n)
  | [] => []
  | .testResult job p :: rest =>
      (if p = u then [job] else []) ++ longTestLabels u rest
  | .processed _ :: rest => longTestLabels u rest
  | .rawCompleted _ :: rest => longTestLabels u rest

theorem Transcript.longTestLabels_length
    (u : ℝ) (transcript : Transcript n) :
    (transcript.longTestLabels u).length =
      HiddenStoppingOracle.longCount u transcript := by
  induction transcript with
  | nil => simp [Transcript.longTestLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = u <;>
            simp [Transcript.longTestLabels,
              HiddenStoppingOracle.longCount, hp, ih] <;> omega
      | processed job =>
          simp [Transcript.longTestLabels,
            HiddenStoppingOracle.longCount, ih]
      | rawCompleted job =>
          simp [Transcript.longTestLabels,
            HiddenStoppingOracle.longCount, ih]

theorem Transcript.mem_longTestLabels_iff
    {u : ℝ} {transcript : Transcript n} {job : Label n} :
    job ∈ transcript.longTestLabels u ↔
      (job, u) ∈ transcript.testResults := by
  induction transcript with
  | nil => simp [Transcript.longTestLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult tested p =>
          by_cases hp : p = u
          · subst p
            simp [Transcript.longTestLabels, ih]
          · simp [Transcript.longTestLabels, hp, Ne.symm hp, ih]
      | processed processed =>
          simpa [Transcript.longTestLabels] using ih
      | rawCompleted raw =>
          simpa [Transcript.longTestLabels] using ih

theorem Transcript.longTestLabels_sublist_startedLabels
    (u : ℝ) (transcript : Transcript n) :
    (transcript.longTestLabels u).Sublist
      transcript.startedLabels := by
  induction transcript with
  | nil => simp [Transcript.longTestLabels]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = u
          · simpa [Transcript.longTestLabels, hp] using
              ih.cons₂ job
          · simpa [Transcript.longTestLabels, hp] using
              ih.cons job
      | processed job =>
          simpa [Transcript.longTestLabels] using ih
      | rawCompleted job =>
          simpa [Transcript.longTestLabels] using ih.cons job

end Online

namespace LowerBound

/-! ## Exact identification of the two canonical blocks -/

theorem stoppingAlgExact_eq_block_prefixCosts
    (u : ℝ) (v e d x : ℕ) :
    stoppingAlgExact u (v + e + d + x) v e d =
      prefixCost
          (List.replicate v u ++
            List.replicate e (1 + u)) +
        (x + d : ℕ) *
          ((List.replicate v u ++
              List.replicate e (1 + u)).sum + d) +
        prefixCost
          (List.replicate x 1 ++
            List.replicate d u) := by
  rw [prefixCost_append, prefixCost_append,
    prefixCost_replicate, prefixCost_replicate,
    prefixCost_replicate, prefixCost_replicate]
  simp [stoppingAlgExact, triangular, List.sum_replicate]
  push_cast
  ring

theorem stoppingOptExact_eq_binary_triangular
    (u : ℝ) (n e d : ℕ) :
    stoppingOptExact u n e d =
      triangular n +
        (u - 1) * triangular (e + d) := by
  simp [stoppingOptExact, triangular]
  push_cast
  ring

theorem binaryLongCount_ofFn_eq_filter_card
    (u : ℝ) (n : ℕ) (f : Fin n → ℝ) :
    binaryLongCount u (List.ofFn f) =
      ((Finset.univ : Finset (Fin n)).filter
        (fun job => f job = u)).card := by
  have hsum :
      binaryLongCount u (List.ofFn f) =
        ∑ job : Fin n, if f job = u then 1 else 0 := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [List.ofFn_succ, binaryLongCount_cons,
          Fin.sum_univ_succ, ih]
  rw [hsum]
  simp

theorem effectiveLength_eq_long_iff
    {u p : ℝ} (hu : 1 < u) (hbinary : p = 0 ∨ p = u) :
    effectiveLength (.finite u) p = u ↔ p = u := by
  rcases hbinary with rfl | rfl
  · have hu0 : (0 : ℝ) ≠ u := by linarith
    have hu1 : (1 : ℝ) ≠ u := ne_of_lt hu
    simp [effectiveLength, min_eq_right hu.le, hu0, hu1]
  · rw [effectiveLength_finite,
      min_eq_left (by linarith)]

theorem hiddenStopping_frozen_binaryLongCount_eq_longCount
    {n : ℕ} {u : ℝ} (hu : 1 < u) (α : ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (HiddenStoppingOracle.oracle n u α)
        strategy (fun _ => 0) fuel
    let effective := vectorEffectiveLengths (.finite u) frozen
    binaryLongCount u effective =
      HiddenStoppingOracle.longCount u
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u α)
          strategy fuel).result.config.transcript := by
  dsimp only
  let result :=
    (Online.adaptiveRun (.finite u)
      (HiddenStoppingOracle.oracle n u α)
      strategy fuel).result
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (HiddenStoppingOracle.oracle n u α)
      strategy (fun _ => 0) fuel
  let effective := vectorEffectiveLengths (.finite u) frozen
  have hstarted :=
    Online.hiddenStopping_adaptiveRun_startedHistoryInvariant
      u α strategy fuel
  have hlongNodup :
      (result.config.transcript.longTestLabels u).Nodup := by
    exact List.Nodup.sublist
      (result.config.transcript.longTestLabels_sublist_startedLabels u)
      hstarted.nodup
  have hsets :
      ((Finset.univ : Finset (Online.Label n)).filter
          (fun job =>
            effectiveLength (.finite u) (frozen job) = u)) =
        (result.config.transcript.longTestLabels u).toFinset := by
    ext job
    constructor
    · intro hmem
      have heffective :
          effectiveLength (.finite u) (frozen job) = u := by
        simpa [effective, vectorEffectiveLengths] using hmem
      have hfrozen : frozen job = u := by
        apply (effectiveLength_eq_long_iff hu
          (HiddenStoppingOracle.frozenProcessingTimes_binary
            n u α strategy fuel job)).mp
        exact heffective
      by_cases htested :
          ∃ p, (job, p) ∈ result.config.transcript.testResults
      · rcases htested with ⟨p, hp⟩
        have hpFrozen :
            frozen job = p := by
          exact Online.frozenProcessingTimes_eq_of_testResult
            (.finite u) (HiddenStoppingOracle.oracle n u α)
            strategy (fun _ => 0) fuel hp
        have hpLong : p = u := by linarith
        rw [hpLong] at hp
        exact List.mem_toFinset.mpr
          (result.config.transcript.mem_longTestLabels_iff.mpr hp)
      · have hzero :
            frozen job = 0 := by
          exact Online.frozenProcessingTimes_eq_default_of_not_tested
            (.finite u) (HiddenStoppingOracle.oracle n u α)
            strategy (fun _ => 0) fuel job htested
        linarith
    · intro hmem
      have hlong :
          (job, u) ∈ result.config.transcript.testResults :=
        result.config.transcript.mem_longTestLabels_iff.mp
          (List.mem_toFinset.mp hmem)
      have hfrozen :
          frozen job = u :=
        Online.frozenProcessingTimes_eq_of_testResult
          (.finite u) (HiddenStoppingOracle.oracle n u α)
          strategy (fun _ => 0) fuel hlong
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ job, ?_⟩
      rw [hfrozen, effectiveLength_finite,
        min_eq_left (by linarith)]
  calc
    binaryLongCount u effective =
        ((Finset.univ : Finset (Online.Label n)).filter
          (fun job =>
            effectiveLength (.finite u) (frozen job) = u)).card := by
      exact binaryLongCount_ofFn_eq_filter_card u n
        (fun job =>
          effectiveLength (.finite u) (frozen job))
    _ = (result.config.transcript.longTestLabels u).toFinset.card := by
      rw [hsets]
    _ = (result.config.transcript.longTestLabels u).length :=
      List.toFinset_card_of_nodup hlongNodup
    _ = HiddenStoppingOracle.longCount u
        result.config.transcript :=
      result.config.transcript.longTestLabels_length u

/-- The completed operational run dominates the four-block canonical
schedule attached to its reachable first crossing. -/
theorem hiddenStopping_canonical_lower_of_firstCrossing
    {n : ℕ} {u α : ℝ} (hu : 1 < u) (hα0 : 0 ≤ α)
    (strategy : Online.Strategy n) (fuel : ℕ)
    {crossing : Online.Config n}
    {crossingAssignment : Online.PartialAssignment n}
    {tail : Online.Transcript n}
    (hfirst :
      HiddenStoppingOracle.FirstCrossingReachable
        n u α crossing crossingAssignment)
    (happend :
      (Online.adaptiveRun (.finite u)
        (HiddenStoppingOracle.oracle n u α)
        strategy fuel).result.config.transcript =
          crossing.transcript ++ tail)
    (hlong :
      HiddenStoppingOracle.longCount u
          (Online.adaptiveRun (.finite u)
            (HiddenStoppingOracle.oracle n u α)
            strategy fuel).result.config.transcript =
        HiddenStoppingOracle.longCount u crossing.transcript)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u α)
          strategy fuel).result) :
    ∃ v e d x : ℕ,
      n = v + e + d + x ∧
      v = HiddenStoppingOracle.rawCount crossing.transcript ∧
      e = crossing.transcript.processedLabels.length ∧
      e + d =
        HiddenStoppingOracle.longCount u crossing.transcript ∧
      stoppingAlgExact u n v e d ≤
        Online.suffixWeightedDuration (.finite u)
          (Online.frozenProcessingTimes (.finite u)
            (HiddenStoppingOracle.oracle n u α)
            strategy (fun _ => 0) fuel)
          (Online.adaptiveRun (.finite u)
            (HiddenStoppingOracle.oracle n u α)
            strategy fuel).result.config.transcript := by
  let result :=
    (Online.adaptiveRun (.finite u)
      (HiddenStoppingOracle.oracle n u α)
      strategy fuel).result
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (HiddenStoppingOracle.oracle n u α)
      strategy (fun _ => 0) fuel
  change result.config.transcript =
    crossing.transcript ++ tail at happend
  change HiddenStoppingOracle.longCount u result.config.transcript =
    HiddenStoppingOracle.longCount u crossing.transcript at hlong
  change resultCompleted result at hcompleted
  let v := HiddenStoppingOracle.rawCount crossing.transcript
  let e := crossing.transcript.processedLabels.length
  let d :=
    (tail.selectedProcessedLabels
      (crossing.transcript.testResults.map Prod.fst)).length
  let x := tail.startedLabels.length
  let preBlock :=
    List.replicate v u ++ List.replicate e (1 + u)
  let postBlock :=
    List.replicate x 1 ++ List.replicate d u
  have hcrossReach := hfirst.reachable
  have hcrossStarted := hcrossReach.startedHistoryInvariant
  have hcrossProcess := hcrossReach.processHistoryInvariant
  have hfinalReach :
      Online.AdaptiveReachable (.finite u)
        (HiddenStoppingOracle.oracle n u α)
        result.config
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u α)
          strategy fuel).assigned := by
    simpa [result] using
      Online.adaptiveRun_reachable (.finite u)
        (HiddenStoppingOracle.oracle n u α)
        strategy fuel
  have hfinalStarted := hfinalReach.startedHistoryInvariant
  have hfinalProcess := hfinalReach.processHistoryInvariant
  have hall :=
    hfirst.allTestsEqual (by linarith : u ≠ 0) hα0
  have hfrozenValid :
      ∀ job, Online.ValueAdmissible (.finite u) (frozen job) := by
    dsimp [frozen]
    apply Online.frozenProcessingTimes_admissible
    · exact HiddenStoppingOracle.oracle_admissible (by linarith)
    · exact HiddenStoppingOracle.zero_default_admissible (by linarith)
  have hfrozenTest :
      ∀ job ∈ crossing.transcript.testResults.map Prod.fst,
        frozen job = u := by
    intro job hjob
    rcases List.mem_map.mp hjob with ⟨pair, hpair, hfst⟩
    rcases pair with ⟨testedJob, p⟩
    change testedJob = job at hfst
    subst testedJob
    have hp : p = u := hall job p hpair
    rw [hp] at hpair
    have hpairFinal :
        (job, u) ∈ result.config.transcript.testResults := by
      rw [happend, Online.Transcript.testResults_append]
      exact List.mem_append_left _ hpair
    simpa [frozen, result] using
      Online.frozenProcessingTimes_eq_of_testResult
        (.finite u) (HiddenStoppingOracle.oracle n u α)
        strategy (fun _ => 0) fuel hpairFinal
  have hfrozenProcessed :
      ∀ job ∈ crossing.transcript.processedLabels,
        frozen job = u := by
    intro job hjob
    exact hfrozenTest job
      (hcrossProcess.processedRecorded job hjob)
  have hselected :
      e + d = crossing.transcript.testResults.length := by
    simpa [e, d] using
      Online.selectedProcessedLabels_count_exact
        happend hcrossStarted hcrossProcess hfinalProcess hcompleted
  have htestsLong :
      HiddenStoppingOracle.longCount u crossing.transcript =
        crossing.transcript.testResults.length :=
    HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
      hall
  have hedLong :
      e + d =
        HiddenStoppingOracle.longCount u crossing.transcript := by
    omega
  have hfinalStartedLength :
      result.config.transcript.startedLabels.length = n :=
    Online.Config.startedLabels_length_eq_card_of_completed
      hfinalStarted hfinalProcess hcompleted
  have hcrossStartedLength :
      crossing.transcript.startedLabels.length =
        v + crossing.transcript.testResults.length := by
    simpa [v] using
      crossing.transcript.startedLabels_length_eq_raw_add_tests
  have hsize : n = v + e + d + x := by
    have happendStarted :
        result.config.transcript.startedLabels =
          crossing.transcript.startedLabels ++
            tail.startedLabels := by
      rw [happend, Online.Transcript.startedLabels_append]
    have hlength := congrArg List.length happendStarted
    simp only [List.length_append] at hlength
    dsimp [x]
    omega
  have hbinaryFull :
      HiddenStoppingOracle.TestResultsBinary u
        result.config.transcript := by
    simpa [result] using
      HiddenStoppingOracle.adaptiveRun_testResultsBinary
        u α strategy fuel
  have hbinaryTail :
      HiddenStoppingOracle.TestResultsBinary u tail := by
    apply HiddenStoppingOracle.TestResultsBinary.of_append_right
    rw [← happend]
    exact hbinaryFull
  have hlongTail :
      HiddenStoppingOracle.longCount u tail = 0 := by
    rw [happend,
      HiddenStoppingOracle.longCount_append] at hlong
    omega
  have hzero : tail.AllTestsEqual 0 :=
    HiddenStoppingOracle.allTestsEqual_zero_of_binary_longCount_zero
      (by linarith : u ≠ 0) hbinaryTail hlongTail
  have hpreInvariant :
      crossing.PreCostInvariant u :=
    hcrossReach.preCostInvariant_of_allTestsEqual
      (by linarith) hall
  have hpreBlock :
      prefixCost preBlock ≤
        Online.suffixWeightedDuration (.finite u)
          frozen crossing.transcript := by
    calc
      prefixCost preBlock ≤
          prefixCost
            (crossing.transcript.preCompletionWeights u) := by
        simpa [preBlock, v, e] using
          Online.preCompletionWeights_blocks_le
            (by linarith : 0 ≤ u) crossing.transcript
      _ ≤ Online.suffixWeightedDuration (.finite u)
          (fun _ => u) crossing.transcript :=
        hpreInvariant
      _ = Online.suffixWeightedDuration (.finite u)
          frozen crossing.transcript := by
        symm
        exact
          Online.suffixWeightedDuration_eq_const_of_processed
            hfrozenProcessed
  have hpreSum :
      preBlock.sum =
        (crossing.transcript.preCompletionWeights u).sum := by
    have hperm :=
      crossing.transcript.preCompletionWeights_perm_blocks u
    simpa [preBlock, v, e] using hperm.sum_eq.symm
  have hcountReal :
      (crossing.transcript.testResults.length : ℝ) =
        (crossing.transcript.processedLabels.length : ℝ) +
          (d : ℝ) := by
    exact_mod_cast hselected.symm
  have helapsed :
      Online.transcriptElapsed (.finite u) frozen
          crossing.transcript =
        preBlock.sum + d := by
    calc
      Online.transcriptElapsed (.finite u) frozen
          crossing.transcript =
          Online.transcriptElapsed (.finite u) (fun _ => u)
            crossing.transcript :=
        Online.transcriptElapsed_eq_const_of_processed
          hfrozenProcessed
      _ =
          crossing.transcript.testResults.length +
            u * crossing.transcript.processedLabels.length +
            u * HiddenStoppingOracle.rawCount
              crossing.transcript :=
        crossing.transcript.elapsed_const_long_exact u
      _ =
          (crossing.transcript.preCompletionWeights u).sum + d := by
        rw [crossing.transcript.preCompletionWeights_sum]
        nlinarith
      _ = preBlock.sum + d := by rw [hpreSum]
  have hpostBlock :
      prefixCost postBlock ≤
        Online.suffixWeightedDuration (.finite u) frozen tail := by
    simpa [postBlock, x, d] using
      Online.postCross_suffix_block_lower
        hu frozen crossing.transcript tail
          hfrozenValid hzero hfrozenTest
  have hpostPerm :=
    tail.postWeights_perm_blocks
      (crossing.transcript.testResults.map Prod.fst) u
  have hpostLength :
      (tail.extractedWeights
        (Online.Transcript.postWeight
          (crossing.transcript.testResults.map Prod.fst) u)).length =
        x + d := by
    have := hpostPerm.length_eq
    simpa [x, d, List.length_append] using this
  have hcompletionExtracted :=
    Online.postCross_extractedWeights_length_le_completionCount
      hu frozen crossing.transcript tail hzero hfrozenTest
  have hcompletionNat :
      x + d ≤ Online.completionCount frozen tail := by
    rw [← hpostLength]
    exact hcompletionExtracted
  have hcompletionReal :
      ((x + d : ℕ) : ℝ) ≤
        (Online.completionCount frozen tail : ℝ) := by
    exact_mod_cast hcompletionNat
  have helapsedNonneg :
      0 ≤ Online.transcriptElapsed (.finite u) frozen
        crossing.transcript :=
    Online.transcriptElapsed_nonneg
      (by simp [Cap.Valid]; linarith) hfrozenValid _
  have hpreElapsedNonneg :
      0 ≤ preBlock.sum + (d : ℝ) := by
    rw [← helapsed]
    exact helapsedNonneg
  have hcarry :
      (x + d : ℕ) * (preBlock.sum + d) ≤
        Online.completionCount frozen tail *
          Online.transcriptElapsed (.finite u) frozen
            crossing.transcript := by
    rw [helapsed]
    exact mul_le_mul_of_nonneg_right
      hcompletionReal hpreElapsedNonneg
  have hsplit :
      Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript =
        Online.suffixWeightedDuration (.finite u) frozen
            crossing.transcript +
          Online.completionCount frozen tail *
            Online.transcriptElapsed (.finite u) frozen
              crossing.transcript +
          Online.suffixWeightedDuration (.finite u) frozen tail := by
    rw [happend,
      Online.suffixWeightedDuration_append]
  have hcanonicalLower :
      prefixCost preBlock +
          (x + d : ℕ) * (preBlock.sum + d) +
          prefixCost postBlock ≤
        Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript := by
    rw [hsplit]
    linarith
  refine ⟨v, e, d, x, hsize, rfl, rfl, hedLong, ?_⟩
  have hcanonicalIdentity :
      stoppingAlgExact u n v e d =
        prefixCost preBlock +
          (x + d : ℕ) * (preBlock.sum + d) +
          prefixCost postBlock := by
    calc
      stoppingAlgExact u n v e d =
          stoppingAlgExact u
            ((v : ℝ) + e + d + x) v e d := by
        congr 2
        exact_mod_cast hsize
      _ =
          prefixCost preBlock +
            (x + d : ℕ) * (preBlock.sum + d) +
            prefixCost postBlock := by
        simpa [preBlock, postBlock] using
          stoppingAlgExact_eq_block_prefixCosts u v e d x
  rw [hcanonicalIdentity]
  simpa [result, frozen] using hcanonicalLower

/-- If a completed hidden-stopping run never reaches the stopping line, then
every test was long.  Since `alpha < 1`, completion forces there to have
been no tests at all; the run is therefore the all-raw schedule. -/
theorem hiddenStopping_noCross_lower
    {n : ℕ} {u ratio : ℝ} (hu : 1 < u)
    (certificate : BinaryStoppingCertificate u ratio)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u certificate.alpha)
          strategy fuel).result)
    (hnotCrossed :
      ¬ HiddenStoppingOracle.Crossed n u certificate.alpha
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u certificate.alpha)
          strategy fuel).result.config.transcript) :
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (HiddenStoppingOracle.oracle n u certificate.alpha)
        strategy (fun _ => 0) fuel
    let effective := vectorEffectiveLengths (.finite u) frozen
    ratio *
        (triangular n +
          (u - 1) * triangular (binaryLongCount u effective)) ≤
      Online.suffixWeightedDuration (.finite u) frozen
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u certificate.alpha)
          strategy fuel).result.config.transcript := by
  dsimp only
  let result :=
    (Online.adaptiveRun (.finite u)
      (HiddenStoppingOracle.oracle n u certificate.alpha)
      strategy fuel).result
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (HiddenStoppingOracle.oracle n u certificate.alpha)
      strategy (fun _ => 0) fuel
  let effective := vectorEffectiveLengths (.finite u) frozen
  change resultCompleted result at hcompleted
  change
    ¬ HiddenStoppingOracle.Crossed n u certificate.alpha
      result.config.transcript at hnotCrossed
  change
    ratio *
        (triangular n +
          (u - 1) * triangular (binaryLongCount u effective)) ≤
      Online.suffixWeightedDuration (.finite u) frozen
        result.config.transcript
  have hreach :
      Online.AdaptiveReachable (.finite u)
        (HiddenStoppingOracle.oracle n u certificate.alpha)
        result.config
        (Online.adaptiveRun (.finite u)
          (HiddenStoppingOracle.oracle n u certificate.alpha)
          strategy fuel).assigned := by
    simpa [result] using
      Online.adaptiveRun_reachable (.finite u)
        (HiddenStoppingOracle.oracle n u certificate.alpha)
        strategy fuel
  have hall :
      result.config.transcript.AllTestsEqual u :=
    HiddenStoppingOracle.LawfulTrace.allTestsEqual_of_not_crossed
      (by linarith : u ≠ 0) certificate.alpha_pos.le
      (HiddenStoppingOracle.adaptiveReachable_lawfulTrace hreach)
      hnotCrossed
  have hlongTests :
      HiddenStoppingOracle.longCount u result.config.transcript =
        result.config.transcript.testResults.length :=
    HiddenStoppingOracle.allTestsEqual_longCount_eq_testResults_length
      hall
  have hstartedLength :
      result.config.transcript.startedLabels.length = n :=
    Online.Config.startedLabels_length_eq_card_of_completed
      hreach.startedHistoryInvariant hreach.processHistoryInvariant
      hcompleted
  have hstartedCount :
      n =
        HiddenStoppingOracle.rawCount result.config.transcript +
          result.config.transcript.testResults.length := by
    have :=
      result.config.transcript.startedLabels_length_eq_raw_add_tests
    omega
  have hsurplusLt :
      HiddenStoppingOracle.surplus n u certificate.alpha
        result.config.transcript < 0 :=
    lt_of_not_ge hnotCrossed
  have hremainingCount :
      (n : ℝ) -
          HiddenStoppingOracle.rawCount result.config.transcript =
        result.config.transcript.testResults.length := by
    have hstartedCountReal :
        (n : ℝ) =
          HiddenStoppingOracle.rawCount result.config.transcript +
            result.config.transcript.testResults.length := by
      exact_mod_cast hstartedCount
    linarith
  have htestsZero :
      result.config.transcript.testResults.length = 0 := by
    have htestsNonneg :
        0 ≤
          (result.config.transcript.testResults.length : ℝ) := by
      positivity
    have hstrict :
        (result.config.transcript.testResults.length : ℝ) -
            certificate.alpha *
              result.config.transcript.testResults.length <
          0 := by
      simpa [HiddenStoppingOracle.surplus, hlongTests,
        hremainingCount] using hsurplusLt
    have htestsReal :
        (result.config.transcript.testResults.length : ℝ) = 0 := by
      nlinarith [certificate.alpha_lt_one]
    exact_mod_cast htestsReal
  have hlongZero :
      HiddenStoppingOracle.longCount u
        result.config.transcript = 0 := by
    omega
  have hrawCount :
      HiddenStoppingOracle.rawCount
        result.config.transcript = n := by
    omega
  have hprocessedLength :
      result.config.transcript.processedLabels.length = 0 := by
    have hle :=
      hreach.processHistoryInvariant.processed_length_le_tests
    omega
  have hfrozenProcessed :
      ∀ job ∈ result.config.transcript.processedLabels,
        frozen job = u := by
    intro job hjob
    have hrecorded :=
      hreach.processHistoryInvariant.processedRecorded job hjob
    have hpositive :
        0 < result.config.transcript.testResults.length :=
      by
        simpa using List.length_pos_of_mem hrecorded
    omega
  have hpreInvariant :
      result.config.PreCostInvariant u :=
    hreach.preCostInvariant_of_allTestsEqual
      (by linarith) hall
  have hrawPrefix :
      prefixCost (List.replicate n u) ≤
        prefixCost
          (result.config.transcript.preCompletionWeights u) := by
    simpa [hrawCount, hprocessedLength] using
      Online.preCompletionWeights_blocks_le
        (by linarith : 0 ≤ u) result.config.transcript
  have honlineLower :
      u * triangular n ≤
        Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript := by
    calc
      u * triangular n =
          prefixCost (List.replicate n u) :=
        (prefixCost_replicate n u).symm
      _ ≤ prefixCost
          (result.config.transcript.preCompletionWeights u) :=
        hrawPrefix
      _ ≤ Online.suffixWeightedDuration (.finite u)
          (fun _ => u) result.config.transcript :=
        hpreInvariant
      _ = Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript := by
        symm
        exact
          Online.suffixWeightedDuration_eq_const_of_processed
            hfrozenProcessed
  have hbinaryLong :
      binaryLongCount u effective =
        HiddenStoppingOracle.longCount u
          result.config.transcript := by
    simpa [effective, frozen, result] using
      hiddenStopping_frozen_binaryLongCount_eq_longCount
        hu certificate.alpha strategy fuel
  have heffectiveZero :
      binaryLongCount u effective = 0 := by
    rw [hbinaryLong, hlongZero]
  have htriangularNonneg : 0 ≤ triangular n := by
    unfold triangular
    positivity
  have hratioLower :
      ratio * triangular n ≤ u * triangular n :=
    mul_le_mul_of_nonneg_right
      certificate.ratio_le_cap htriangularNonneg
  rw [heffectiveZero, triangular_zero, mul_zero, add_zero]
  exact hratioLower.trans honlineLower

/-- Both possible first-crossing observations give the same normalized
one-remaining-job overshoot estimate. -/
theorem hiddenStopping_firstCrossing_normalized_overshoot
    {n v k : ℕ} {u α : ℝ}
    {crossing : Online.Config n}
    {crossingAssignment : Online.PartialAssignment n}
    (hfirst :
      HiddenStoppingOracle.FirstCrossingReachable
        n u α crossing crossingAssignment)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hv :
      v = HiddenStoppingOracle.rawCount crossing.transcript)
    (hk :
      k = HiddenStoppingOracle.longCount u crossing.transcript)
    (hvn : v < n) :
    α ≤ (k : ℝ) / ((n : ℝ) - (v : ℝ)) ∧
      (k : ℝ) / ((n : ℝ) - (v : ℝ)) - α ≤
        1 / ((n : ℝ) - (v : ℝ)) := by
  rcases hfirst.countShape with
      ⟨before, job, hcross, hraw, hlong⟩ |
      ⟨before, job, hcross, hraw, hlong⟩
  · have hvBefore :
        v = HiddenStoppingOracle.rawCount before.transcript :=
      hv.trans hraw
    have hkBefore :
        k =
          HiddenStoppingOracle.longCount u before.transcript + 1 :=
      hk.trans hlong
    have hremainingNat :
        HiddenStoppingOracle.rawCount before.transcript < n := by
      omega
    have hremaining :
        0 <
          (n : ℝ) -
            (HiddenStoppingOracle.rawCount before.transcript : ℝ) := by
      have hcast :
          (HiddenStoppingOracle.rawCount before.transcript : ℝ) <
            (n : ℝ) := by
        exact_mod_cast hremainingNat
      linarith
    have hover :=
      HiddenStoppingOracle.firstCrossing_long_overshoot
        hcross hremaining
    dsimp only at hover
    have hy :
        (k : ℝ) / ((n : ℝ) - (v : ℝ)) =
          ((HiddenStoppingOracle.longCount u
                before.transcript : ℝ) + 1) /
            ((n : ℝ) -
              HiddenStoppingOracle.rawCount before.transcript) := by
      rw [hvBefore, hkBefore]
      norm_num
    constructor
    · rw [hy]
      linarith [hover.1]
    · rw [hy]
      simpa [hvBefore] using le_of_lt hover.2
  · have hvBefore :
        v =
          HiddenStoppingOracle.rawCount before.transcript + 1 :=
      hv.trans hraw
    have hkBefore :
        k =
          HiddenStoppingOracle.longCount u before.transcript :=
      hk.trans hlong
    have hremainingNat :
        HiddenStoppingOracle.rawCount before.transcript + 1 < n := by
      omega
    have hremaining :
        0 <
          (n : ℝ) -
            ((HiddenStoppingOracle.rawCount before.transcript : ℝ) +
              1) := by
      have hcast :
          ((HiddenStoppingOracle.rawCount before.transcript + 1 : ℕ) : ℝ) <
            (n : ℝ) := by
        exact_mod_cast hremainingNat
      push_cast at hcast
      linarith
    have hover :=
      HiddenStoppingOracle.firstCrossing_raw_overshoot
        hα0 hα1 hcross hremaining
    dsimp only at hover
    have hy :
        (k : ℝ) / ((n : ℝ) - (v : ℝ)) =
          (HiddenStoppingOracle.longCount u
              before.transcript : ℝ) /
            ((n : ℝ) -
              ((HiddenStoppingOracle.rawCount before.transcript : ℝ) +
                1)) := by
      rw [hvBefore, hkBefore]
      norm_num
    constructor
    · rw [hy]
      linarith [hover.1]
    · rw [hy]
      simpa [hvBefore] using le_of_lt hover.2

/-- The raw-safe hidden-stopping oracle satisfies the literal operational
pair-exchange premise with one uniform linear remainder. -/
theorem hiddenStoppingPairExchangeBridge :
    HiddenStoppingPairExchangeBridge := by
  intro u ratio hu certificate
  refine ⟨3 * u ^ 2 + 4 * u, by positivity, ?_⟩
  intro n strategy
  dsimp only
  intro hcompleted
  let fuel := 2 * n + 1
  let result :=
    (Online.adaptiveRun (.finite u)
      (HiddenStoppingOracle.oracle n u certificate.alpha)
      strategy fuel).result
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (HiddenStoppingOracle.oracle n u certificate.alpha)
      strategy (fun _ => 0) fuel
  let effective := vectorEffectiveLengths (.finite u) frozen
  change resultCompleted result at hcompleted
  change
    ratio *
        (triangular n +
          (u - 1) * triangular (binaryLongCount u effective)) ≤
      Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript +
        (3 * u ^ 2 + 4 * u) * n
  by_cases hnZero : n = 0
  · subst n
    have hfrozenValid :
        ∀ job, Online.ValueAdmissible (.finite u) (frozen job) := by
      dsimp [frozen]
      apply Online.frozenProcessingTimes_admissible
      · exact HiddenStoppingOracle.oracle_admissible
          (by linarith : 0 ≤ u)
      · exact HiddenStoppingOracle.zero_default_admissible
          (by linarith : 0 ≤ u)
    have hsuffixNonneg :
        0 ≤ Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript := by
      rw [← Online.completionCost_eq_suffixWeightedDuration]
      exact Online.completionCost_nonneg
        (by simp [Cap.Valid]; linarith)
        hfrozenValid result.config.transcript
    simpa [effective, vectorEffectiveLengths, triangular] using
      hsuffixNonneg
  · have hn : 0 < n := Nat.pos_of_ne_zero hnZero
    by_cases hcross :
        HiddenStoppingOracle.Crossed n u certificate.alpha
          result.config.transcript
    · have hreach :
          Online.AdaptiveReachable (.finite u)
            (HiddenStoppingOracle.oracle n u certificate.alpha)
            result.config
            (Online.adaptiveRun (.finite u)
              (HiddenStoppingOracle.oracle n u certificate.alpha)
              strategy fuel).assigned := by
        simpa [result] using
          Online.adaptiveRun_reachable (.finite u)
            (HiddenStoppingOracle.oracle n u certificate.alpha)
            strategy fuel
      obtain ⟨crossing, crossingAssignment, hfirst, _hextension,
          tail, happend, hlong⟩ :=
        HiddenStoppingOracle.adaptiveReachable_exists_firstCrossingPrefix
          hn (by linarith : u ≠ 0)
          certificate.alpha_pos.le certificate.alpha_pos
          hreach hcross
      obtain ⟨v, e, d, x, hsize, hv, _he, hed, hcanonical⟩ :=
        hiddenStopping_canonical_lower_of_firstCrossing
          hu certificate.alpha_pos.le strategy fuel
          hfirst happend hlong hcompleted
      have hbinaryLong :
          binaryLongCount u effective =
            HiddenStoppingOracle.longCount u
              result.config.transcript := by
        simpa [effective, frozen, result] using
          hiddenStopping_frozen_binaryLongCount_eq_longCount
            hu certificate.alpha strategy fuel
      have hbinaryCount :
          binaryLongCount u effective = e + d := by
        omega
      have hvle : v ≤ n := by omega
      by_cases hvn : v < n
      · have hnReal : 0 < (n : ℝ) := by
          exact_mod_cast hn
        have hv0 : 0 ≤ (v : ℝ) := by positivity
        have hvnReal : (v : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hvle
        have he0 : 0 ≤ (e : ℝ) := by positivity
        have hd0 : 0 ≤ (d : ℝ) := by positivity
        have hremaining :
            0 < (n : ℝ) - (v : ℝ) := by
          have hcast : (v : ℝ) < (n : ℝ) := by
            exact_mod_cast hvn
          linarith
        have hsizeReal :
            (n : ℝ) =
              (v : ℝ) + (e : ℝ) + (d : ℝ) + (x : ℝ) := by
          exact_mod_cast hsize
        have hmass :
            (e : ℝ) + (d : ℝ) ≤
              (n : ℝ) - (v : ℝ) := by
          have hx0 : 0 ≤ (x : ℝ) := by positivity
          linarith
        have hover :=
          hiddenStopping_firstCrossing_normalized_overshoot
            hfirst certificate.alpha_pos.le
              certificate.alpha_lt_one hv hed hvn
        have hyAlpha :
            certificate.alpha ≤
              ((e : ℝ) + (d : ℝ)) /
                ((n : ℝ) - (v : ℝ)) := by
          simpa only [Nat.cast_add] using hover.1
        have hyOvershoot :
            ((e : ℝ) + (d : ℝ)) /
                  ((n : ℝ) - (v : ℝ)) -
                certificate.alpha ≤
              1 / ((n : ℝ) - (v : ℝ)) := by
          simpa only [Nat.cast_add] using hover.2
        have hanalytic :=
          stoppingExact_competitive_of_firstCrossing
            (u := u) (ratio := ratio)
            (n := (n : ℝ)) (v := (v : ℝ))
            (e := (e : ℝ)) (d := (d : ℝ))
            hu certificate hnReal hv0 hvnReal he0 hd0
            hremaining hmass hyAlpha hyOvershoot
        rw [hbinaryCount,
          ← stoppingOptExact_eq_binary_triangular u n e d]
        exact hanalytic.trans
          (by
            simpa [add_comm] using
              add_le_add_right hcanonical
                ((3 * u ^ 2 + 4 * u) * n))
      · have hvEq : v = n := by omega
        have heZero : e = 0 := by omega
        have hdZero : d = 0 := by omega
        have hxZero : x = 0 := by omega
        have halgRaw :
            stoppingAlgExact u n n 0 0 =
              u * triangular n := by
          simpa [prefixCost_replicate] using
            stoppingAlgExact_eq_block_prefixCosts u n 0 0 0
        have honlineRaw :
            u * triangular n ≤
              Online.suffixWeightedDuration (.finite u) frozen
                result.config.transcript := by
          rw [← halgRaw]
          simpa [hvEq, heZero, hdZero, frozen, result] using
            hcanonical
        have htriangularNonneg : 0 ≤ triangular n := by
          unfold triangular
          positivity
        have hratioRaw :
            ratio * triangular n ≤ u * triangular n :=
          mul_le_mul_of_nonneg_right certificate.ratio_le_cap
            htriangularNonneg
        have hremainderNonneg :
            0 ≤ (3 * u ^ 2 + 4 * u) * (n : ℝ) := by
          positivity
        rw [hbinaryCount, heZero, hdZero, triangular_zero,
          mul_zero, add_zero]
        linarith
    · have hbase :
          ratio *
              (triangular n +
                (u - 1) *
                  triangular (binaryLongCount u effective)) ≤
            Online.suffixWeightedDuration (.finite u) frozen
              result.config.transcript := by
        simpa [fuel, frozen, effective, result] using
          hiddenStopping_noCross_lower
            hu certificate strategy fuel hcompleted hcross
      have hremainderNonneg :
          0 ≤ (3 * u ^ 2 + 4 * u) * (n : ℝ) := by
        positivity
      linarith

/-- The original finite-cost hidden-stopping interface is therefore
discharged without any additional operational premise. -/
theorem hiddenStoppingFiniteCostBridge :
    HiddenStoppingFiniteCostBridge :=
  hiddenStoppingFiniteCostBridge_of_pairExchange
    hiddenStoppingPairExchangeBridge

end LowerBound

end

end SchedulingPaper
