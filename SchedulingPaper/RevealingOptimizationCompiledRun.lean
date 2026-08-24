import SchedulingPaper.RevealingOptimizationCompiledStrategy
import Mathlib.Tactic

/-!
# Operational replay of the compiled revealing strategy

This module closes the semantic gap between a word which follows a public
strategy and the literal `Online.run`.  The generic replay lemma uses only
truthful terminal owner words; the second half verifies those words for the
pilot compiler.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace CompiledRun

open Online
open Randomized
open RandomizedOptional
open RandomizedOptional.ObservedEnvelope
open InstanceLearning
open QuotaStrategy
open QuotaRounding
open PilotCompiler
open QuotaRestriction
open CompiledStrategy

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every owner has one truthful legal terminal lifecycle word. -/
def TerminalOwnerWords
    {n : ℕ} (processing : Fin n → ℝ)
    (transcript : Online.Transcript n) : Prop :=
  ∀ job,
    transcript.pairProjection job job =
        [.testResult job (processing job), .processed job] ∨
      transcript.pairProjection job job = [.rawCompleted job]

/-- One next observation in a terminal-owner word is a successful fixed-input
step from any matching reachable prefix configuration. -/
theorem step_next_of_terminalOwnerWords
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    {full before after : Online.Transcript n}
    {observation : Online.Observation n} {config : Online.Config n}
    (hfull : full = before ++ observation :: after)
    (hconfig : config.transcript = before)
    (hself : SelfProjectionInvariant processing config)
    (hwords : TerminalOwnerWords processing full) :
    ∃ next,
      config.step (.finite u) (Online.fixedOracle processing)
          observation.requestedAction = some next ∧
        next.transcript = before ++ [observation] ∧
        SelfProjectionInvariant processing next := by
  subst before
  have hprojection := hwords observation.ownerLabel
  rw [hfull, Online.Transcript.pairProjection_append] at hprojection
  have hcons : Online.Transcript.pairProjection
      observation.ownerLabel observation.ownerLabel
        (observation :: after) =
      observation :: Online.Transcript.pairProjection
        observation.ownerLabel observation.ownerLabel after := by
    simp [Online.Transcript.pairProjection]
  rw [hcons] at hprojection
  cases observation with
  | testResult job value =>
      simp only [Online.Observation.requestedAction]
      cases hstate : config.jobs job with
      | untouched =>
          have hbefore := hself job
          rw [hstate] at hbefore
          simp [Online.Observation.ownerLabel, hbefore] at hprojection
          rcases hprojection with ⟨hvalue, _⟩
          subst value
          let next : Online.Config n := {
            jobs := Function.update config.jobs job (.tested (processing job))
            transcript := config.transcript ++
              [.testResult job (processing job)] }
          refine ⟨next, ?_, rfl, ?_⟩
          · simpa [next, Online.fixedOracle] using
              config.step_test_of_untouched (.finite u)
                (Online.fixedOracle processing) job hstate
          · apply selfProjectionInvariant_step hself
            simpa [next, Online.fixedOracle] using
              config.step_test_of_untouched (.finite u)
                (Online.fixedOracle processing) job hstate
      | tested stored =>
          have hbefore := hself job
          rw [hstate] at hbefore
          simp [Online.Observation.ownerLabel, hbefore] at hprojection
      | done =>
          have hbefore := hself job
          rw [hstate] at hbefore
          rcases hbefore with hraw | ⟨stored, htested⟩
          · simp [Online.Observation.ownerLabel, hraw] at hprojection
          · simp [Online.Observation.ownerLabel, htested] at hprojection
  | processed job =>
      simp only [Online.Observation.requestedAction]
      cases hstate : config.jobs job with
      | untouched =>
          have hbefore := hself job
          rw [hstate] at hbefore
          simp [Online.Observation.ownerLabel, hbefore] at hprojection
      | tested stored =>
          have hbefore := hself job
          rw [hstate] at hbefore
          let next : Online.Config n := {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.processed job] }
          have hstep : config.step (.finite u) (Online.fixedOracle processing)
              (.process job) = some next := by
            simp [Online.Config.step, hstate, next]
          exact ⟨next, hstep, rfl,
            selfProjectionInvariant_step hself hstep⟩
      | done =>
          have hbefore := hself job
          rw [hstate] at hbefore
          rcases hbefore with hraw | ⟨stored, htested⟩
          · simp [Online.Observation.ownerLabel, hraw] at hprojection
          · simp [Online.Observation.ownerLabel, htested] at hprojection
  | rawCompleted job =>
      simp only [Online.Observation.requestedAction]
      cases hstate : config.jobs job with
      | untouched =>
          let next : Online.Config n := {
            jobs := Function.update config.jobs job .done
            transcript := config.transcript ++ [.rawCompleted job] }
          have hstep : config.step (.finite u) (Online.fixedOracle processing)
              (.raw job) = some next := by
            simp [Online.Config.step, hstate, next]
          exact ⟨next, hstep, rfl,
            selfProjectionInvariant_step hself hstep⟩
      | tested stored =>
          have hbefore := hself job
          rw [hstate] at hbefore
          simp [Online.Observation.ownerLabel, hbefore] at hprojection
      | done =>
          have hbefore := hself job
          rw [hstate] at hbefore
          rcases hbefore with hraw | ⟨stored, htested⟩
          · simp [Online.Observation.ownerLabel, hraw] at hprojection
          · simp [Online.Observation.ownerLabel, htested] at hprojection

/-! ## Generic exact replay -/

/-- A terminal word which follows a strategy is reproduced exactly from any
matching legal prefix.  This is stronger than mere strategy consistency: it
also rules out an invalid action before the end of the displayed word. -/
theorem runFuel_replays_terminalWord
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    {strategy : Online.Strategy n}
    {full before todo : Online.Transcript n} {config : Online.Config n}
    (hsplit : full = before ++ todo)
    (hconfig : config.transcript = before)
    (hfollow : FollowsFrom strategy before todo)
    (hself : SelfProjectionInvariant processing config)
    (hwords : TerminalOwnerWords processing full) :
    (Online.runFuel (.finite u) (Online.fixedOracle processing)
      strategy todo.length config).config.transcript = full := by
  induction todo generalizing before config with
  | nil =>
      simp only [Online.runFuel]
      exact hconfig.trans (by simpa using hsplit.symm)
  | cons observation rest ih =>
      have haction := followsFrom_cons_head hfollow
      obtain ⟨next, hstep, hnextTranscript, hnextSelf⟩ :=
        step_next_of_terminalOwnerWords (u := u)
          hsplit hconfig hself hwords
      have htail := followsFrom_cons_tail hfollow
      have hnextSplit : full = (before ++ [observation]) ++ rest := by
        simpa [List.append_assoc] using hsplit
      have hactionConfig : strategy config.transcript =
          some observation.requestedAction := by
        simpa [hconfig] using haction
      rw [show (observation :: rest).length = rest.length + 1 by simp,
        Online.runFuel, hactionConfig]
      simp only
      rw [hstep]
      exact ih hnextSplit hnextTranscript htail hnextSelf

/-- Exact replay from the initial configuration. -/
theorem run_transcript_eq_of_follows_terminalOwnerWords
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    {strategy : Online.Strategy n} {transcript : Online.Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    (hwords : TerminalOwnerWords processing transcript) :
    (Online.run (.finite u) (Online.fixedOracle processing)
      strategy transcript.length).config.transcript = transcript := by
  unfold Online.run
  apply runFuel_replays_terminalWord
      (full := transcript) (before := []) (todo := transcript)
  · simp
  · rfl
  · simpa [FollowsFrom, Online.Transcript.FollowsStrategy] using hfollow
  · exact initial_selfProjectionInvariant processing
  · exact hwords

/-- The same replay with arbitrary extra fuel, provided the strategy stops
on the full displayed word. -/
theorem runFuel_replays_terminalWord_with_extra
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    {strategy : Online.Strategy n}
    {full before todo : Online.Transcript n} {config : Online.Config n}
    (hsplit : full = before ++ todo)
    (hconfig : config.transcript = before)
    (hfollow : FollowsFrom strategy before todo)
    (hself : SelfProjectionInvariant processing config)
    (hwords : TerminalOwnerWords processing full)
    (hstop : strategy full = none) (extra : ℕ) :
    let result := Online.runFuel (.finite u) (Online.fixedOracle processing)
      strategy (todo.length + 1 + extra) config
    result.config.transcript = full ∧
      result.reason = .strategyStopped := by
  induction todo generalizing before config with
  | nil =>
      have hfullConfig : config.transcript = full := by
        exact hconfig.trans (by simpa using hsplit.symm)
      have hstopConfig : strategy config.transcript = none := by
        simpa [hfullConfig] using hstop
      dsimp only
      simp only [List.length_nil]
      rw [show 1 + extra = extra + 1 by omega,
        Online.runFuel, hstopConfig]
      exact ⟨hfullConfig, rfl⟩
  | cons observation rest ih =>
      have haction := followsFrom_cons_head hfollow
      obtain ⟨next, hstep, hnextTranscript, hnextSelf⟩ :=
        step_next_of_terminalOwnerWords (u := u)
          hsplit hconfig hself hwords
      have htail := followsFrom_cons_tail hfollow
      have hnextSplit : full = (before ++ [observation]) ++ rest := by
        simpa [List.append_assoc] using hsplit
      have hactionConfig : strategy config.transcript =
          some observation.requestedAction := by
        simpa [hconfig] using haction
      dsimp only
      rw [show (observation :: rest).length + 1 + extra =
          (rest.length + 1 + extra) + 1 by simp; omega,
        Online.runFuel, hactionConfig]
      simp only
      rw [hstep]
      exact ih hnextSplit hnextTranscript htail hnextSelf

theorem run_with_extra_replays_terminalWord
    {n : ℕ} {u : ℝ} {processing : Fin n → ℝ}
    {strategy : Online.Strategy n} {transcript : Online.Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    (hwords : TerminalOwnerWords processing transcript)
    (hstop : strategy transcript = none) (extra : ℕ) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      strategy (transcript.length + 1 + extra)
    result.config.transcript = transcript ∧
      result.reason = .strategyStopped := by
  unfold Online.run
  apply runFuel_replays_terminalWord_with_extra
      (full := transcript) (before := []) (todo := transcript)
  · simp
  · rfl
  · simpa [FollowsFrom, Online.Transcript.FollowsStrategy] using hfollow
  · exact initial_selfProjectionInvariant processing
  · exact hwords
  · exact hstop

/-- Every successful finite online step appends one observation, so public
transcript growth is bounded by the supplied analysis fuel. -/
theorem runFuel_transcript_length_le_add_fuel
    {n : ℕ} (cap : Cap) (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) (config : Online.Config n) :
    (Online.runFuel cap oracle strategy fuel config).config.transcript.length ≤
      config.transcript.length + fuel := by
  induction fuel generalizing config with
  | zero => simp [Online.runFuel]
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simp [Online.runFuel, haction]
      | some action =>
          cases hstep : config.step cap oracle action with
          | none => simp [Online.runFuel, haction, hstep]
          | some next =>
              obtain ⟨observation, htranscript, _⟩ :=
                Online.Config.step_observation hstep
              have hrec := ih next
              have hnextLength : next.transcript.length =
                  config.transcript.length + 1 := by
                simp [htranscript]
              have hbound :
                  (Online.runFuel cap oracle strategy fuel next).config.transcript.length ≤
                    config.transcript.length + (fuel + 1) := by
                rw [hnextLength] at hrec
                omega
              simpa [Online.runFuel, haction, hstep] using hbound

theorem run_transcript_length_le_fuel
    {n : ℕ} (cap : Cap) (oracle : Online.Oracle n)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    (Online.run cap oracle strategy fuel).config.transcript.length ≤ fuel := by
  simpa [Online.run, Online.Config.initial] using
    runFuel_transcript_length_le_add_fuel cap oracle strategy fuel
      (Online.Config.initial n)

/-! ## Owner words of the physical compiler -/

theorem pairProjection_filter_owner_self
    {n : ℕ} (transcript : Online.Transcript n)
    (keep : Fin n → Prop) [DecidablePred keep] (job : Fin n) :
    Online.Transcript.pairProjection job job
        (transcript.filter fun observation => keep observation.ownerLabel) =
      if keep job then transcript.pairProjection job job else [] := by
  unfold Online.Transcript.pairProjection
  rw [List.filter_filter]
  by_cases hkeep : keep job
  · rw [if_pos hkeep]
    apply List.filter_congr
    intro observation _
    by_cases howner : observation.ownerLabel = job
    · simp [howner, hkeep]
    · simp [howner]
  · rw [if_neg hkeep]
    apply List.filter_eq_nil_iff.mpr
    intro observation _
    by_cases howner : observation.ownerLabel = job
    · simp [howner, hkeep]
    · simp [howner]

theorem pairProjection_map_relabel_self
    {n : ℕ} (order : Equiv.Perm (Fin n))
    (transcript : Online.Transcript n) (job : Fin n) :
    Online.Transcript.pairProjection (order job) (order job)
        (transcript.map (Online.Observation.relabel order)) =
      (transcript.pairProjection job job).map
        (Online.Observation.relabel order) := by
  unfold Online.Transcript.pairProjection
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro observation _
  simp [Function.comp_apply, ownerLabel_relabel, order.injective.eq_iff]

theorem pairProjection_pilotWords
    {n : ℕ} (processing : Fin n → ℝ)
    (order : Equiv.Perm (Fin n)) (job : Fin n)
    (positions : List (Fin n)) (hnodup : positions.Nodup) :
    Online.Transcript.pairProjection job job
        (positions.flatMap fun position =>
          pilotJobWord processing (order position)) =
      if order.symm job ∈ positions then pilotJobWord processing job else [] := by
  induction positions with
  | nil => simp [Online.Transcript.pairProjection]
  | cons position rest ih =>
      have hrestNodup := (List.nodup_cons.mp hnodup).2
      have hnotmem := (List.nodup_cons.mp hnodup).1
      by_cases heq : order position = job
      · have hinverse : order.symm job = position := by
          apply order.injective
          simp [heq]
        have hhead : Online.Transcript.pairProjection job job
            (pilotJobWord processing (order position)) =
              pilotJobWord processing job := by
          simp [pilotJobWord, Online.Transcript.pairProjection,
            Online.Observation.ownerLabel, heq]
        rw [List.flatMap_cons, Online.Transcript.pairProjection_append,
          hhead, ih hrestNodup]
        simp [hinverse, hnotmem]
      · have hinverseNe : order.symm job ≠ position := by
          intro h
          apply heq
          calc
            order position = order (order.symm job) := congrArg order h.symm
            _ = job := order.apply_symm_apply job
        have hhead : Online.Transcript.pairProjection job job
            (pilotJobWord processing (order position)) = [] := by
          simp [pilotJobWord, Online.Transcript.pairProjection,
            Online.Observation.ownerLabel, heq]
        rw [List.flatMap_cons, Online.Transcript.pairProjection_append,
          hhead, List.nil_append, ih hrestNodup]
        simp [hinverseNe]

theorem revealingPilotTranscript_pairProjection
    {n : ℕ} (processing : Fin n → ℝ)
    (positions : Finset (Fin n)) (order : Equiv.Perm (Fin n))
    (job : Fin n) :
    Online.Transcript.pairProjection job job
        (revealingPilotTranscript processing positions order) =
      if job ∈ pilotOccurrenceSet positions order then
        pilotJobWord processing job
      else [] := by
  rw [revealingPilotTranscript, pairProjection_pilotWords processing order job
    positions.toList positions.nodup_toList]
  have hmem : order.symm job ∈ positions.toList ↔
      job ∈ pilotOccurrenceSet positions order := by
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨order.symm job, by simpa using h,
        order.apply_symm_apply job⟩
    · intro h
      obtain ⟨position, hposition, heq⟩ := Finset.mem_image.mp h
      have hs : order.symm job = position := by
        apply order.injective
        simpa using heq.symm
      simpa [hs] using hposition
  by_cases h : order.symm job ∈ positions.toList
  · simp [h, hmem.mp h]
  · have hphysical : job ∉ pilotOccurrenceSet positions order :=
      fun hpilot => h (hmem.mpr hpilot)
    simp [h, hphysical]

theorem learnedRetainedTranscript_pairProjection
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) (job : Fin n) :
    Online.Transcript.pairProjection job job
        (learnedRetainedTranscript G positions pilotOrder mainOrder u) =
      if job ∈ pilotOccurrenceSet positions pilotOrder then []
      else if (mainOrder.symm job).val <
          (learnedTemplate G positions pilotOrder u).quota.val then
        [.testResult job (processing job), .processed job]
      else [.rawCompleted job] := by
  let T := learnedTemplate G positions pilotOrder u
  let virtualProcessing : Fin n → ℝ :=
    fun virtual => processing (mainOrder virtual)
  let virtual :=
    (quotaRun T.quota.val u virtualProcessing
      (roundedTemplateLow G T)).config.transcript
  let keep : Fin n → Prop := fun virtualJob =>
    mainOrder virtualJob ∉ pilotOccurrenceSet positions pilotOrder
  let virtualJob := mainOrder.symm job
  have hjob : mainOrder virtualJob = job := mainOrder.apply_symm_apply job
  have hmap := pairProjection_map_relabel_self mainOrder
    (virtual.filter fun observation => keep observation.ownerLabel) virtualJob
  rw [hjob] at hmap
  have hfilter := pairProjection_filter_owner_self virtual keep virtualJob
  have hcompleted := quotaRun_completed T.quota_le u virtualProcessing
    (roundedTemplateLow G T)
  have hterminal := hcompleted.2.1.selfProjection_eq_terminalWord
    T.quota_le hcompleted.2.2 virtualJob
  change virtual.pairProjection virtualJob virtualJob =
      (if virtualJob.val < T.quota.val then
        [.testResult virtualJob (virtualProcessing virtualJob),
          .processed virtualJob]
      else [.rawCompleted virtualJob]) at hterminal
  change Online.Transcript.pairProjection job job
      ((virtual.filter fun observation => keep observation.ownerLabel).map
        (Online.Observation.relabel mainOrder)) = _
  rw [hmap, hfilter]
  by_cases hp : job ∈ pilotOccurrenceSet positions pilotOrder
  · have hnotKeep : ¬keep virtualJob := by
      simpa [keep, hjob] using hp
    simp [hp, hnotKeep]
  · have hkeep : keep virtualJob := by
      simpa [keep, hjob] using hp
    rw [if_pos hkeep, hterminal]
    by_cases hquota : virtualJob.val < T.quota.val
    · simp [hp, hquota, T, virtualJob, virtualProcessing,
        Online.Observation.relabel]
    · simp [hp, hquota, T, virtualJob,
        Online.Observation.relabel]

/-- The pilot/main compiler word contains one truthful terminal lifecycle
for every physical job, with pilot owners appearing only in the pilot. -/
theorem learnedPilotTranscript_terminalOwnerWords
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    TerminalOwnerWords processing
      (learnedPilotTranscript G positions pilotOrder mainOrder u) := by
  intro job
  rw [learnedPilotTranscript,
    Online.Transcript.pairProjection_append,
    revealingPilotTranscript_pairProjection,
    learnedRetainedTranscript_pairProjection]
  by_cases hp : job ∈ pilotOccurrenceSet positions pilotOrder
  · left
    simp [hp, pilotJobWord]
  · by_cases hquota : (mainOrder.symm job).val <
        (learnedTemplate G positions pilotOrder u).quota.val
    · left
      simp [hp, hquota]
    · right
      simp [hp, hquota]

/-! ## Stopping after the displayed word -/

/-- After all kept owners of a completed quota word have finished, the
owner-restricted policy has no further action.  The selector used by the
restricted policy may differ from the selector which generated the word;
at a terminal configuration no tested job remains pending. -/
theorem keptQuotaStrategy_stops_on_filtered_quotaRun
    {n q : ℕ} (hq : q ≤ n) (u : ℝ) (processing : Fin n → ℝ)
    (runLow strategyLow : ℝ → Bool)
    (keep : Fin n → Prop) [DecidablePred keep] :
    keptQuotaStrategy n q strategyLow keep
      ((quotaRun q u processing runLow).config.transcript.filter
        fun observation => keep observation.ownerLabel) = none := by
  let full := (quotaRun q u processing runLow).config.transcript
  let retained := full.filter fun observation => keep observation.ownerLabel
  have hcompleted := quotaRun_completed hq u processing runLow
  have hgood := hcompleted.2.1
  have hdone := hcompleted.2.2
  have hallStarted : ∀ job : Fin n, keep job →
      job ∈ Online.Transcript.startedLabels retained := by
    intro job hkeep
    rw [show retained = full.filter
      (fun observation => keep observation.ownerLabel) by rfl,
      startedLabels_filter_owner]
    apply List.mem_filter.mpr
    exact ⟨hgood.process.nonuntouchedStarted job (by simp [hdone job]),
      by simpa using hkeep⟩
  have hremainingFull : Online.Transcript.remainingTestResults full = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro result hresult
    have hparts := List.mem_filter.mp hresult
    have htested := hgood.process.recordedUnprocessedTested
      result.1 result.2 hparts.1 (by simpa using hparts.2)
    rw [hdone result.1] at htested
    contradiction
  have hremaining : Online.Transcript.remainingTestResults retained = [] := by
    rw [show retained = full.filter
      (fun observation => keep observation.ownerLabel) by rfl,
      remainingTestResults_filter_owner, hremainingFull]
    rfl
  have hsafe : safeLastLowPending? strategyLow retained = none := by
    unfold safeLastLowPending?
    cases hlast : retained.getLast? with
    | none => rfl
    | some observation =>
        cases observation <;> simp [hremaining]
  have hshort : Online.Transcript.shortestRemaining? retained = none := by
    unfold Online.Transcript.shortestRemaining?
    rw [hremaining]
    rfl
  have hnextTest : nextKeptTouch? n keep
      (fun job => decide (job.val < q)) retained = none := by
    apply nextKeptTouch?_eq_none
    intro job _ hkeep
    exact hallStarted job hkeep
  have hnextRaw : nextKeptTouch? n keep
      (fun job => decide (q ≤ job.val)) retained = none := by
    apply nextKeptTouch?_eq_none
    intro job _ hkeep
    exact hallStarted job hkeep
  change keptQuotaStrategy n q strategyLow keep retained = none
  simp [keptQuotaStrategy, hsafe, hshort, hnextTest, hnextRaw]

theorem restrictedFixedMainStrategy_stops_on_learnedPilot
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    restrictedFixedMainStrategy n G.category
      (learnedTemplate G positions pilotOrder u)
      (pilotOccurrenceSet positions pilotOrder) mainOrder
      (learnedPilotTranscript G positions pilotOrder mainOrder u) = none := by
  let T := learnedTemplate G positions pilotOrder u
  let pilot := pilotOccurrenceSet positions pilotOrder
  let virtual :=
    (quotaRun T.quota.val u (fun job => processing (mainOrder job))
      (roundedTemplateLow G T)).config.transcript
  let keep : Fin n → Prop := fun virtualJob =>
    mainOrder virtualJob ∉ pilot
  have hhistory :
      (((learnedPilotTranscript G positions pilotOrder mainOrder u).filter
        fun observation => observation.ownerLabel ∉ pilot).map
          (Online.Observation.relabel mainOrder.symm)) =
        virtual.filter fun observation => keep observation.ownerLabel := by
    dsimp [pilot, keep]
    rw [learnedPilotTranscript, List.filter_append]
    rw [revealingPilotTranscript_filter_nonpilot]
    simp only [List.nil_append]
    change (((virtual.filter fun observation =>
        keep observation.ownerLabel).map
          (Online.Observation.relabel mainOrder)).filter
            fun observation => observation.ownerLabel ∉ pilot).map
              (Online.Observation.relabel mainOrder.symm) = _
    rw [filter_relabelled_owner_filter pilot mainOrder virtual]
    exact inverse_relabel_relabelled_owner_filter pilot mainOrder virtual
  unfold restrictedFixedMainStrategy
  rw [hhistory]
  have hstop := keptQuotaStrategy_stops_on_filtered_quotaRun
    T.quota_le u (fun job => processing (mainOrder job))
    (roundedTemplateLow G T) (publicTemplateLow G.category T) keep
  change (keptQuotaStrategy n T.quota.val
    (publicTemplateLow G.category T) keep
      (virtual.filter fun observation => keep observation.ownerLabel)).map
        (Online.Action.relabel mainOrder) = none
  rw [hstop]
  rfl

theorem compiledLearnedStrategy_stops_on_learnedPilot
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    compiledLearnedStrategy n G.category G.price u positions
      pilotOrder mainOrder
      (learnedPilotTranscript G positions pilotOrder mainOrder u) = none := by
  change compiledLearnedStrategy n G.category G.price u positions
      pilotOrder mainOrder
      (revealingPilotTranscript processing positions pilotOrder ++
        learnedRetainedTranscript G positions pilotOrder mainOrder u) = none
  rw [compiledLearnedStrategy_after_pilot G u positions pilotOrder mainOrder
    (learnedRetainedTranscript G positions pilotOrder mainOrder u)]
  exact restrictedFixedMainStrategy_stops_on_learnedPilot
    G positions pilotOrder mainOrder

/-- A uniform public fuel bound for the physical compiler.  The coarse
`4n+2` bound is sufficient here: the pilot has at most `2n` observations and
the retained main word is a subword of a `2n+1`-fuel quota run. -/
theorem learnedPilotTranscript_length_le
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    (learnedPilotTranscript G positions pilotOrder mainOrder u).length ≤
      4 * n + 1 := by
  have hpilot : positions.card ≤ n := by
    simpa using positions.card_le_univ
  have hvirtual :
      (learnedVirtualTranscript G positions pilotOrder mainOrder u).length ≤
        2 * n + 1 := by
    unfold learnedVirtualTranscript quotaRun
    exact run_transcript_length_le_fuel (.finite u)
      (Online.fixedOracle (fun job => processing (mainOrder job)))
      (quotaStrategy n
        (learnedTemplate G positions pilotOrder u).quota.val
        (roundedTemplateLow G
          (learnedTemplate G positions pilotOrder u))) (2 * n + 1)
  have hretained :
      (learnedRetainedTranscript G positions pilotOrder mainOrder u).length ≤
        (learnedVirtualTranscript G positions pilotOrder mainOrder u).length := by
    unfold learnedRetainedTranscript
    rw [List.length_map]
    exact List.length_filter_le _ _
  rw [learnedPilotTranscript, List.length_append,
    revealingPilotTranscript_length]
  omega

/-! ## Literal execution of the learned strategy -/

theorem compiledLearnedStrategy_run_transcript_eq
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    (Online.run (.finite u) (Online.fixedOracle processing)
      (compiledLearnedStrategy n G.category G.price u positions
        pilotOrder mainOrder)
      (learnedPilotTranscript G positions pilotOrder mainOrder u).length
      ).config.transcript =
        learnedPilotTranscript G positions pilotOrder mainOrder u := by
  apply run_transcript_eq_of_follows_terminalOwnerWords
  · exact compiledLearnedStrategy_follows_learnedPilot
      G hprice0 hprice u positions pilotOrder mainOrder
  · exact learnedPilotTranscript_terminalOwnerWords
      G positions pilotOrder mainOrder

theorem compiledLearnedStrategy_runCompletionCost_eq
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    Online.runCompletionCost (.finite u) processing
      (Online.run (.finite u) (Online.fixedOracle processing)
        (compiledLearnedStrategy n G.category G.price u positions
          pilotOrder mainOrder)
        (learnedPilotTranscript G positions pilotOrder mainOrder u).length) =
      learnedPilotCost G positions pilotOrder mainOrder u := by
  unfold Online.runCompletionCost learnedPilotCost
  rw [compiledLearnedStrategy_run_transcript_eq
    G hprice0 hprice positions pilotOrder mainOrder]

/-- With one public fuel bound, the literal compiled policy completes
normally and its public execution is exactly the compiler word. -/
theorem compiledLearnedStrategy_run_fixedFuel
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (compiledLearnedStrategy n G.category G.price u positions
        pilotOrder mainOrder) (4 * n + 2)
    result.config.transcript =
        learnedPilotTranscript G positions pilotOrder mainOrder u ∧
      result.reason = .strategyStopped := by
  let transcript := learnedPilotTranscript G positions pilotOrder mainOrder u
  let strategy := compiledLearnedStrategy n G.category G.price u positions
    pilotOrder mainOrder
  let extra := 4 * n + 1 - transcript.length
  have hlength : transcript.length ≤ 4 * n + 1 :=
    learnedPilotTranscript_length_le G positions pilotOrder mainOrder
  have hfuel : transcript.length + 1 + extra = 4 * n + 2 := by
    dsimp [extra]
    omega
  have hreplay := run_with_extra_replays_terminalWord
    (u := u) (processing := processing)
    (strategy := strategy) (transcript := transcript)
    (compiledLearnedStrategy_follows_learnedPilot
      G hprice0 hprice u positions pilotOrder mainOrder)
    (learnedPilotTranscript_terminalOwnerWords
      G positions pilotOrder mainOrder)
    (compiledLearnedStrategy_stops_on_learnedPilot
      G positions pilotOrder mainOrder) extra
  rw [hfuel] at hreplay
  simpa [strategy, transcript] using hreplay

theorem compiledLearnedStrategy_runCompletionCost_fixedFuel_eq
    {n : ℕ} {u : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n))
    (pilotOrder mainOrder : Equiv.Perm (Fin n)) :
    Online.runCompletionCost (.finite u) processing
      (Online.run (.finite u) (Online.fixedOracle processing)
        (compiledLearnedStrategy n G.category G.price u positions
          pilotOrder mainOrder) (4 * n + 2)) =
      learnedPilotCost G positions pilotOrder mainOrder u := by
  unfold Online.runCompletionCost learnedPilotCost
  rw [(compiledLearnedStrategy_run_fixedFuel G hprice0 hprice positions
    pilotOrder mainOrder).1]

/-- Fully operational version of the learned rounded-grid upper bound: the
averaged cost is now the cost of one literal transcript-only online strategy
run with public fixed fuel. -/
theorem compiledLearnedStrategy_expectedCost_le
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {processing : Fin n → ℝ} (G : RoundedPositiveGrid ι processing)
    (hprice0 : ∀ cell, 0 < G.price cell)
    (hprice : Function.Injective G.price)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (u : ℝ) (hu0 : 0 ≤ u)
    (hpriceU : ∀ cell, G.price cell ≤ u)
    (hroundedU : ∀ job, G.roundedProcessing job ≤ u)
    (target : InstanceLearning.Template ι n) :
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (compiledLearnedStrategy n G.category G.price u positions
              pilotOrder mainOrder) (4 * n + 2)) /
          (n : ℝ) ^ 2)) ≤
      InstanceLearning.gridTemplateValue
          (populationHistogram (roundedGridCell G)) G.price u target +
        2 * (u + 2) *
          Real.sqrt ((Fintype.card (Option ι) : ℝ) / positions.card) +
        (5 * u + 8) / (2 * n) +
        2 * positions.card * (u + 1) / n := by
  calc
    uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
      uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (compiledLearnedStrategy n G.category G.price u positions
              pilotOrder mainOrder) (4 * n + 2)) /
          (n : ℝ) ^ 2)) =
      uniformAverage (fun pilotOrder : Equiv.Perm (Fin n) =>
        uniformAverage (fun mainOrder : Equiv.Perm (Fin n) =>
          learnedPilotCost G positions pilotOrder mainOrder u /
            (n : ℝ) ^ 2)) := by
        apply congrArg uniformAverage
        funext pilotOrder
        apply congrArg uniformAverage
        funext mainOrder
        rw [compiledLearnedStrategy_runCompletionCost_fixedFuel_eq
          G hprice0 hprice positions pilotOrder mainOrder]
    _ ≤ _ := learnedRoundedPilotCost_le hn G hprice0 hprice positions
      hpositions u hu0 hpriceU hroundedU target

end

end CompiledRun
end RevealingOptimization
end SchedulingPaper
