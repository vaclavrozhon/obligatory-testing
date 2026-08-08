import SchedulingPaper.RandomizedOptionalCanonicalKernel
import Mathlib.Tactic

/-!
# Pair decomposition for observed optional-testing transcripts

For a completed legal transcript, total completion time is the sum of the
duration owned by every job before its own completion and all oriented
owner--target interactions.  This is the operational decomposition matched
by `canonicalSingleKernel` and `canonicalPairKernel`.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

open Randomized

noncomputable section

def Transcript.completionLabels
    (processing : Label n → ℝ) (transcript : Transcript n) : List (Label n) :=
  transcript.filterMap fun observation => observation.completionLabel processing

@[simp] theorem Transcript.completionLabels_nil
    (processing : Label n → ℝ) :
    Transcript.completionLabels processing [] = [] := rfl

@[simp] theorem Transcript.completionLabels_cons
    (processing : Label n → ℝ) (observation : Observation n)
    (rest : Transcript n) :
    Transcript.completionLabels processing (observation :: rest) =
      match observation.completionLabel processing with
      | some job => job :: Transcript.completionLabels processing rest
      | none => Transcript.completionLabels processing rest := by
  cases h : observation.completionLabel processing <;>
    simp [Transcript.completionLabels, h]

@[simp] theorem Transcript.completionLabels_append_test
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) (p : ℝ) :
    Transcript.completionLabels processing
        (transcript ++ [.testResult job p]) =
      Transcript.completionLabels processing transcript ++
        if p = 0 then [job] else [] := by
  by_cases hp : p = 0 <;>
    simp [Transcript.completionLabels, Observation.completionLabel, hp]

@[simp] theorem Transcript.completionLabels_append_process
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) :
    Transcript.completionLabels processing
        (transcript ++ [.processed job]) =
      Transcript.completionLabels processing transcript ++
        if processing job = 0 then [] else [job] := by
  by_cases hp : processing job = 0 <;>
    simp [Transcript.completionLabels, Observation.completionLabel, hp]

@[simp] theorem Transcript.completionLabels_append_blind
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) (p : ℝ) :
    Transcript.completionLabels processing
        (transcript ++ [.blindCompleted job p]) =
      Transcript.completionLabels processing transcript ++ [job] := by
  simp [Transcript.completionLabels, Observation.completionLabel]

/-! ## Logical-completion invariant -/

def Config.LogicallyComplete (config : Config n) (job : Label n) : Prop :=
  config.jobs job = .done ∨ config.jobs job = .tested 0

structure CompletionInvariant
    (processing : Label n → ℝ) (config : Config n) : Prop where
  nodup : (Transcript.completionLabels processing config.transcript).Nodup
  mem_iff : ∀ job,
    job ∈ Transcript.completionLabels processing config.transcript ↔
      config.LogicallyComplete job

theorem Config.initial_completionInvariant (processing : Label n → ℝ) :
    CompletionInvariant processing (Config.initial n) := by
  constructor
  · exact List.nodup_nil
  · intro job
    simp [Config.LogicallyComplete, Config.initial]

theorem CompletionInvariant.step
    {processing : Label n → ℝ} {config next : Config n}
    (hinv : CompletionInvariant processing config)
    (hhistory : HistoryInvariant processing config) {action : Action n}
    (hstep : config.step processing action = some next) :
    CompletionInvariant processing next := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotmem : job ∉
              Transcript.completionLabels processing config.transcript := by
            intro hmem
            have hlogical := (hinv.mem_iff job).mp hmem
            rcases hlogical with hdone | htested
            · rw [hstate] at hdone
              contradiction
            · rw [hstate] at htested
              contradiction
          by_cases hp : processing job = 0
          · constructor
            · simpa [hp] using hinv.nodup.concat hnotmem
            · intro other
              by_cases heq : other = job
              · subst other
                simp [hp, Config.LogicallyComplete, Function.update]
              · simp [hp, Config.LogicallyComplete, Function.update, heq,
                  hinv.mem_iff other]
          · constructor
            · simpa [hp] using hinv.nodup
            · intro other
              by_cases heq : other = job
              · subst other
                simp [hp, Config.LogicallyComplete, Function.update, hnotmem]
              · simp [hp, Config.LogicallyComplete, Function.update, heq,
                  hinv.mem_iff other]
  | process job =>
      cases hstate : config.jobs job with
      | untouched => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          have hp : processing job = p := by
            have hrecord := hhistory.testedRecorded job p hstate
            exact (hhistory.revealsMatch job p
              (Transcript.mem_revealedResults_of_mem_testResults hrecord)).symm
          by_cases hp0 : processing job = 0
          · have hmem : job ∈
                Transcript.completionLabels processing config.transcript := by
              apply (hinv.mem_iff job).mpr
              right
              rw [hstate]
              have : p = 0 := by linarith [hp]
              rw [this]
            constructor
            · simpa [hp0] using hinv.nodup
            · intro other
              by_cases heq : other = job
              · subst other
                simp [hp0, Config.LogicallyComplete, Function.update, hmem]
              · simp [hp0, Config.LogicallyComplete, Function.update, heq,
                  hinv.mem_iff other]
          · have hnotmem : job ∉
                Transcript.completionLabels processing config.transcript := by
              intro hmem
              have hlogical := (hinv.mem_iff job).mp hmem
              rcases hlogical with hdone | hzero
              · rw [hstate] at hdone
                contradiction
              · rw [hstate] at hzero
                have : p = 0 := by simpa using JobState.tested.inj hzero
                apply hp0
                simpa [hp] using this
            constructor
            · simpa [hp0] using hinv.nodup.concat hnotmem
            · intro other
              by_cases heq : other = job
              · subst other
                simp [hp0, Config.LogicallyComplete, Function.update]
              · simp [hp0, Config.LogicallyComplete, Function.update, heq,
                  hinv.mem_iff other]
  | blind job =>
      cases hstate : config.jobs job with
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          have hnotmem : job ∉
              Transcript.completionLabels processing config.transcript := by
            intro hmem
            have hlogical := (hinv.mem_iff job).mp hmem
            rcases hlogical with hdone | htested
            · rw [hstate] at hdone
              contradiction
            · rw [hstate] at htested
              contradiction
          constructor
          · simpa using hinv.nodup.concat hnotmem
          · intro other
            by_cases heq : other = job
            · subst other
              simp [Config.LogicallyComplete, Function.update]
            · simp [Config.LogicallyComplete, Function.update, heq,
                hinv.mem_iff other]

theorem runFuel_completionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hcompletion : CompletionInvariant processing config)
    (hhistory : HistoryInvariant processing config) :
    CompletionInvariant processing
      (runFuel processing strategy fuel config).config := by
  induction fuel generalizing config with
  | zero => exact hcompletion
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none => simp [haction, hcompletion]
      | some action =>
          cases hstep : config.step processing action with
          | none => simp [haction, hstep, hcompletion]
          | some next =>
              simp only [haction, hstep]
              exact ih next (hcompletion.step hhistory hstep)
                (hhistory.step hstep)

theorem run_completionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    CompletionInvariant processing
      (run processing strategy fuel).config := by
  unfold run
  exact runFuel_completionInvariant processing strategy fuel
    (Config.initial n) (Config.initial_completionInvariant processing)
    (Config.initial_historyInvariant processing)

theorem CompletionInvariant.completionLabels_perm_of_done
    {processing : Label n → ℝ} {config : Config n}
    (hinv : CompletionInvariant processing config)
    (hdone : ∀ job, config.jobs job = .done) :
    (Transcript.completionLabels processing config.transcript).Perm
      (List.ofFn id) := by
  apply (List.perm_ext_iff_of_nodup hinv.nodup
    (List.nodup_ofFn.mpr Function.injective_id)).2
  intro job
  constructor
  · intro _
    simp
  · intro _
    apply (hinv.mem_iff job).mpr
    exact Or.inl (hdone job)

theorem run_completionLabels_perm_of_done
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (run processing strategy fuel).config.jobs job = .done) :
    (Transcript.completionLabels processing
      (run processing strategy fuel).config.transcript).Perm
        (List.ofFn id) :=
  (run_completionInvariant processing strategy fuel).completionLabels_perm_of_done
    hdone

theorem completionCount_eq_completionLabels_length
    (processing : Label n → ℝ) (transcript : Transcript n) :
    completionCount processing transcript =
      (Transcript.completionLabels processing transcript).length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      rw [completionCount, Transcript.completionLabels_cons]
      cases h : observation.completionLabel processing with
      | none => simp [h, ih]
      | some job => simp [h, ih]; omega

def timeUntilCompletion
    (processing : Label n → ℝ) (job : Label n) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.actualDuration processing +
        if observation.completionLabel processing = some job then 0
        else timeUntilCompletion processing job rest

private theorem sum_map_const_add
    {ι : Type*} (duration : ℝ) (labels : List ι) (f : ι → ℝ) :
    (labels.map fun job => duration + f job).sum =
      labels.length * duration + (labels.map f).sum := by
  induction labels with
  | nil => simp
  | cons job labels ih => simp [ih]; ring

theorem suffixWeightedDuration_eq_sum_timeUntilCompletion
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hnodup :
      (Transcript.completionLabels processing transcript).Nodup) :
    suffixWeightedDuration processing transcript =
      ((Transcript.completionLabels processing transcript).map
        fun job => timeUntilCompletion processing job transcript).sum := by
  induction transcript with
  | nil => simp [suffixWeightedDuration]
  | cons observation rest ih =>
      rw [suffixWeightedDuration, completionCount_eq_completionLabels_length,
        Transcript.completionLabels_cons]
      cases hcompletion : observation.completionLabel processing with
      | none =>
          have htail :
              (Transcript.completionLabels processing rest).Nodup := by
            simpa [hcompletion] using hnodup
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion, reduceCtorEq,
            ↓reduceIte]
          rw [sum_map_const_add]
          ring
      | some completed =>
          have hcons :
              (completed :: Transcript.completionLabels processing rest).Nodup := by
            simpa [hcompletion] using hnodup
          have htail := (List.nodup_cons.mp hcons).2
          have hnotmem := (List.nodup_cons.mp hcons).1
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion, List.map_cons,
            List.sum_cons]
          have hmap :
              ((Transcript.completionLabels processing rest).map fun job =>
                observation.actualDuration processing +
                  (if some completed = some job then 0
                    else timeUntilCompletion processing job rest)).sum =
                ((Transcript.completionLabels processing rest).map fun job =>
                  observation.actualDuration processing +
                    timeUntilCompletion processing job rest).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro job hjob
            rw [if_neg]
            intro heq
            have : completed = job := Option.some.inj heq
            subst job
            exact hnotmem hjob
          rw [hmap, sum_map_const_add]
          simp
          ring

theorem completionCost_eq_sum_timeUntilCompletion
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processing transcript).Perm
        (List.ofFn id)) :
    completionCost processing transcript =
      ∑ job : Label n, timeUntilCompletion processing job transcript := by
  rw [completionCost_eq_suffixWeightedDuration]
  have hnodup :
      (Transcript.completionLabels processing transcript).Nodup :=
    hperm.nodup_iff.mpr (List.nodup_ofFn.mpr Function.injective_id)
  rw [suffixWeightedDuration_eq_sum_timeUntilCompletion processing transcript hnodup]
  calc
    ((Transcript.completionLabels processing transcript).map fun job =>
        timeUntilCompletion processing job transcript).sum =
        (List.ofFn fun job =>
          timeUntilCompletion processing job transcript).sum := by
      simpa only [List.map_ofFn, Function.comp_id] using
        (hperm.map fun job =>
          timeUntilCompletion processing job transcript).sum_eq
    _ = ∑ job : Label n,
        timeUntilCompletion processing job transcript := Fin.sum_ofFn _

def Observation.ownerLabel : Observation n → Label n
  | .testResult job _ | .processed job | .blindCompleted job _ => job

theorem Observation.ownerLabel_eq_of_completionLabel_eq
    {processing : Label n → ℝ} {observation : Observation n}
    {job : Label n}
    (hcompletion : observation.completionLabel processing = some job) :
    observation.ownerLabel = job := by
  cases observation with
  | testResult observed p =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · simpa [Observation.ownerLabel] using Option.some.inj hcompletion
      · contradiction
  | processed observed =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · contradiction
      · simpa [Observation.ownerLabel] using Option.some.inj hcompletion
  | blindCompleted observed p =>
      simpa [Observation.completionLabel, Observation.ownerLabel] using
        Option.some.inj hcompletion

def ownedDurationUntilCompletion
    (processing : Label n → ℝ) (target owner : Label n) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      (if observation.ownerLabel = owner
        then observation.actualDuration processing else 0) +
      if observation.completionLabel processing = some target then 0
      else ownedDurationUntilCompletion processing target owner rest

theorem timeUntilCompletion_eq_sum_owned
    (processing : Label n → ℝ) (target : Label n)
    (transcript : Transcript n) :
    timeUntilCompletion processing target transcript =
      ∑ owner : Label n,
        ownedDurationUntilCompletion processing target owner transcript := by
  induction transcript with
  | nil => simp [timeUntilCompletion, ownedDurationUntilCompletion]
  | cons observation rest ih =>
      simp only [timeUntilCompletion, ownedDurationUntilCompletion]
      by_cases hcompletion :
          observation.completionLabel processing = some target
      · simp [hcompletion]
      · simp only [if_neg hcompletion]
        rw [Finset.sum_add_distrib]
        simp [ih]

def observedTraceSelfCharge
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) : ℝ :=
  ownedDurationUntilCompletion processing job job transcript

def observedTraceOrientedCharge
    (processing : Label n → ℝ) (transcript : Transcript n)
    (owner target : Label n) : ℝ :=
  ownedDurationUntilCompletion processing target owner transcript

/-- Exact oriented decomposition, with no symmetry factors. -/
theorem completionCost_eq_self_add_orderedDistinct
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processing transcript).Perm
        (List.ofFn id)) :
    completionCost processing transcript =
      (∑ job, observedTraceSelfCharge processing transcript job) +
        ∑ z : OrderedDistinct (Label n),
          observedTraceOrientedCharge processing transcript
            z.val.1 z.val.2 := by
  rw [completionCost_eq_sum_timeUntilCompletion processing transcript hperm]
  simp_rw [timeUntilCompletion_eq_sum_owned]
  have hsplit :
      (∑ target : Label n, ∑ owner : Label n,
        ownedDurationUntilCompletion processing target owner transcript) =
      (∑ job : Label n,
        ownedDurationUntilCompletion processing job job transcript) +
      ∑ z : OrderedDistinct (Label n),
        ownedDurationUntilCompletion processing z.val.2 z.val.1 transcript := by
    have h := orderedDistinct_add_diagonal fun owner target =>
      ownedDurationUntilCompletion processing target owner transcript
    rw [Finset.sum_comm] at h
    linarith
  simpa [observedTraceSelfCharge, observedTraceOrientedCharge] using hsplit

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
