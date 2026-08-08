import SchedulingPaper.RandomizedOptionalOnline
import Mathlib.Tactic

/-!
# Exactly one completion event per optional-testing job

The online semantics records a tested zero as completed at its test, while a
later zero-length `process` operation changes the lifecycle state to `done`
without creating a second completion.  The invariant below makes this
bookkeeping explicit and proves that a completed legal run has exactly `n`
completion events.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section

def Transcript.completionLabels (processing : Label n → ℝ)
    (transcript : Transcript n) : List (Label n) :=
  transcript.filterMap (Observation.completionLabel processing)

@[simp] theorem Transcript.completionLabels_append
    (processing : Label n → ℝ) (left right : Transcript n) :
    (left ++ right).completionLabels processing =
      left.completionLabels processing ++ right.completionLabels processing := by
  simp [Transcript.completionLabels]

@[simp] theorem Transcript.completionLabels_test
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) (value : ℝ) :
    (transcript ++ [Observation.testResult job value]).completionLabels processing =
      transcript.completionLabels processing ++
        if value = 0 then [job] else [] := by
  rw [Transcript.completionLabels_append]
  by_cases hvalue : value = 0 <;>
    simp [Transcript.completionLabels, Observation.completionLabel, hvalue]

@[simp] theorem Transcript.completionLabels_process
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) :
    (transcript ++ [Observation.processed job]).completionLabels processing =
      transcript.completionLabels processing ++
        if processing job = 0 then [] else [job] := by
  rw [Transcript.completionLabels_append]
  by_cases hvalue : processing job = 0 <;>
    simp [Transcript.completionLabels, Observation.completionLabel, hvalue]

@[simp] theorem Transcript.completionLabels_blind
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) (value : ℝ) :
    (transcript ++ [Observation.blindCompleted job value]).completionLabels processing =
      transcript.completionLabels processing ++ [job] := by
  rw [Transcript.completionLabels_append]
  simp [Transcript.completionLabels, Observation.completionLabel]

theorem Transcript.completionLabels_length
    (processing : Label n → ℝ) (transcript : Transcript n) :
    (transcript.completionLabels processing).length =
      completionCount processing transcript := by
  induction transcript with
  | nil => simp [Transcript.completionLabels, completionCount]
  | cons observation rest ih =>
      unfold Transcript.completionLabels at ih ⊢
      cases observation with
      | testResult job value =>
          simp only [completionCount]
          rw [← ih]
          by_cases hvalue : value = 0 <;>
            simp [Observation.completionLabel, hvalue, Nat.add_comm]
      | processed job =>
          simp only [completionCount]
          rw [← ih]
          by_cases hvalue : processing job = 0 <;>
            simp [Observation.completionLabel, hvalue, Nat.add_comm]
      | blindCompleted job value =>
          simp only [completionCount]
          rw [← ih]
          simp [Observation.completionLabel, Nat.add_comm]

/-- A job has already generated its unique completion event exactly when it
is done, or when it is a tested zero awaiting its bookkeeping `process`. -/
structure CompletionInvariant
    (processing : Label n → ℝ) (config : Config n) : Prop where
  nodup : (config.transcript.completionLabels processing).Nodup
  mem_iff : ∀ job,
    job ∈ config.transcript.completionLabels processing ↔
      config.jobs job = .done ∨ config.jobs job = .tested 0

theorem Config.initial_completionInvariant
    (processing : Label n → ℝ) :
    CompletionInvariant processing (Config.initial n) := by
  constructor
  · simp [Config.initial, Transcript.completionLabels]
  · intro job
    simp [Config.initial, Transcript.completionLabels]

private theorem tested_value_eq_processing
    {processing : Label n → ℝ} {config : Config n}
    (hgood : HistoryInvariant processing config)
    {job : Label n} {value : ℝ} (hstate : config.jobs job = .tested value) :
    value = processing job := by
  have hrecorded := hgood.testedRecorded job value hstate
  exact hgood.revealsMatch job value
    (Transcript.mem_revealedResults_of_mem_testResults hrecorded)

theorem CompletionInvariant.step
    {processing : Label n → ℝ} {config next : Config n}
    (hgood : HistoryInvariant processing config)
    (hinv : CompletionInvariant processing config)
    {action : Action n} (hstep : config.step processing action = some next) :
    CompletionInvariant processing next := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          by_cases hp : processing job = 0
          · constructor
            · rw [Transcript.completionLabels_test]
              simp only [if_pos hp]
              have hnotmem :
                  job ∉ config.transcript.completionLabels processing := by
                intro hmem
                have := (hinv.mem_iff job).mp hmem
                rcases this with hdone | hzero <;> rw [hstate] at * <;>
                  contradiction
              simpa [List.concat_eq_append] using
                List.Nodup.concat hnotmem hinv.nodup
            · intro other
              rw [Transcript.completionLabels_test]
              simp only [if_pos hp, List.mem_append, List.mem_singleton]
              by_cases heq : other = job
              · subst other
                simp [Function.update, hp]
              · simp [Function.update, heq, hinv.mem_iff other]
          · constructor
            · rw [Transcript.completionLabels_test]
              simp only [if_neg hp, List.append_nil]
              exact hinv.nodup
            · intro other
              rw [Transcript.completionLabels_test]
              simp only [if_neg hp, List.append_nil]
              by_cases heq : other = job
              · subst other
                have hnotmem : job ∉ config.transcript.completionLabels processing := by
                  intro hmem
                  have := (hinv.mem_iff job).mp hmem
                  rcases this with hdone | hzero <;> rw [hstate] at * <;>
                    contradiction
                simp [Function.update, hp, hnotmem]
              · simp [Function.update, heq, hinv.mem_iff other]
  | process job =>
      cases hstate : config.jobs job with
      | untouched => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | tested value =>
          simp [Config.step, hstate] at hstep
          subst next
          have hvalue := tested_value_eq_processing hgood hstate
          by_cases hp : processing job = 0
          · have hvalue0 : value = 0 := hvalue.trans hp
            constructor
            · rw [Transcript.completionLabels_process]
              simp only [if_pos hp, List.append_nil]
              exact hinv.nodup
            · intro other
              rw [Transcript.completionLabels_process]
              simp only [if_pos hp, List.append_nil]
              by_cases heq : other = job
              · subst other
                have hmem : job ∈ config.transcript.completionLabels processing :=
                  (hinv.mem_iff job).mpr (Or.inr (by simpa [hvalue0] using hstate))
                simp [Function.update, hmem]
              · simp [Function.update, heq, hinv.mem_iff other]
          · have hvalue0 : value ≠ 0 := by
              intro hz
              apply hp
              rw [← hvalue, hz]
            constructor
            · rw [Transcript.completionLabels_process]
              simp only [if_neg hp]
              have hnotmem :
                  job ∉ config.transcript.completionLabels processing := by
                intro hmem
                have hold := (hinv.mem_iff job).mp hmem
                rcases hold with hdone | hzero
                · rw [hstate] at hdone
                  contradiction
                · rw [hstate] at hzero
                  cases hzero
                  exact hvalue0 rfl
              simpa [List.concat_eq_append] using
                List.Nodup.concat hnotmem hinv.nodup
            · intro other
              rw [Transcript.completionLabels_process]
              simp only [if_neg hp, List.mem_append, List.mem_singleton]
              by_cases heq : other = job
              · subst other
                simp [Function.update]
              · simp [Function.update, heq, hinv.mem_iff other]
  | blind job =>
      cases hstate : config.jobs job with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          constructor
          · rw [Transcript.completionLabels_blind]
            have hnotmem :
                job ∉ config.transcript.completionLabels processing := by
              intro hmem
              have hold := (hinv.mem_iff job).mp hmem
              rcases hold with hdone | hzero <;> rw [hstate] at * <;>
                contradiction
            simpa [List.concat_eq_append] using
              List.Nodup.concat hnotmem hinv.nodup
          · intro other
            rw [Transcript.completionLabels_blind]
            simp only [List.mem_append, List.mem_singleton]
            by_cases heq : other = job
            · subst other
              simp [Function.update]
            · simp [Function.update, heq, hinv.mem_iff other]

theorem runFuel_completionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (hgood : HistoryInvariant processing config)
    (hinv : CompletionInvariant processing config) :
    CompletionInvariant processing
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
          | some next =>
              exact ih next (hgood.step hstep) (hinv.step hgood hstep)

theorem run_completionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    CompletionInvariant processing (run processing strategy fuel).config := by
  unfold run
  exact runFuel_completionInvariant processing strategy fuel (Config.initial n)
    (Config.initial_historyInvariant processing)
    (Config.initial_completionInvariant processing)

@[simp] theorem completionCount_append
    (processing : Label n → ℝ) (left right : Transcript n) :
    completionCount processing (left ++ right) =
      completionCount processing left + completionCount processing right := by
  induction left with
  | nil => simp [completionCount]
  | cons observation rest ih =>
      simp only [List.cons_append, completionCount]
      rw [ih]
      omega

/-- In a reachable configuration every completed label has already been
first-touched.  Since both lists are duplicate-free, completion events are no
more numerous than first touches. -/
theorem completionCount_le_startedLabels_length
    {processing : Label n → ℝ} {config : Config n}
    (hhistory : HistoryInvariant processing config)
    (hcompletion : CompletionInvariant processing config) :
    completionCount processing config.transcript ≤
      config.transcript.startedLabels.length := by
  have hsubset :
      (config.transcript.completionLabels processing).toFinset ⊆
        config.transcript.startedLabels.toFinset := by
    intro job hjob
    have hmemCompletion :
        job ∈ config.transcript.completionLabels processing :=
      List.mem_toFinset.mp hjob
    have hstate := (hcompletion.mem_iff job).mp hmemCompletion
    apply List.mem_toFinset.mpr
    by_contra hnotStarted
    have huntouched := hhistory.notStartedUntouched job hnotStarted
    rcases hstate with hdone | htested <;> rw [huntouched] at * <;>
      contradiction
  rw [← config.transcript.completionLabels_length processing]
  calc
    (config.transcript.completionLabels processing).length =
        (config.transcript.completionLabels processing).toFinset.card :=
      (List.toFinset_card_of_nodup hcompletion.nodup).symm
    _ ≤ config.transcript.startedLabels.toFinset.card :=
      Finset.card_le_card hsubset
    _ = config.transcript.startedLabels.length :=
      List.toFinset_card_of_nodup hhistory.startedNodup

theorem run_completionCount_le_startedLabels_length
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    completionCount processing (run processing strategy fuel).config.transcript ≤
      (run processing strategy fuel).config.transcript.startedLabels.length :=
  completionCount_le_startedLabels_length
    (run_historyInvariant processing strategy fuel)
    (run_completionInvariant processing strategy fuel)

theorem run_completionCount_le_n
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    completionCount processing (run processing strategy fuel).config.transcript ≤ n := by
  have hstarted := (run_historyInvariant processing strategy fuel).startedNodup
  calc
    completionCount processing (run processing strategy fuel).config.transcript ≤
        (run processing strategy fuel).config.transcript.startedLabels.length :=
      run_completionCount_le_startedLabels_length processing strategy fuel
    _ = (run processing strategy fuel).config.transcript.startedLabels.toFinset.card :=
      (List.toFinset_card_of_nodup hstarted).symm
    _ ≤ n := by
      simpa using
        (Finset.card_le_card (Finset.subset_univ
          (run processing strategy fuel).config.transcript.startedLabels.toFinset))

/-- A completed reachable run has exactly one completion event per label. -/
theorem completionCount_eq_n_of_done
    {processing : Label n → ℝ} {config : Config n}
    (hinv : CompletionInvariant processing config)
    (hdone : ∀ job, config.jobs job = .done) :
    completionCount processing config.transcript = n := by
  have hmem : ∀ job : Label n,
      job ∈ config.transcript.completionLabels processing := by
    intro job
    exact (hinv.mem_iff job).mpr (Or.inl (hdone job))
  have hset : (config.transcript.completionLabels processing).toFinset =
      Finset.univ :=
    Finset.eq_univ_of_forall fun job => List.mem_toFinset.mpr (hmem job)
  rw [← config.transcript.completionLabels_length processing]
  calc
    (config.transcript.completionLabels processing).length =
        (config.transcript.completionLabels processing).toFinset.card :=
      (List.toFinset_card_of_nodup hinv.nodup).symm
    _ = n := by rw [hset]; simp

theorem run_completionCount_eq_n_of_done
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ job, (run processing strategy fuel).config.jobs job = .done) :
    completionCount processing (run processing strategy fuel).config.transcript = n :=
  completionCount_eq_n_of_done
    (run_completionInvariant processing strategy fuel) hdone

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
