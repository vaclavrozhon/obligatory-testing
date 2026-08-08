import SchedulingPaper.RandomizedOptionalTraceBijection
import SchedulingPaper.RandomizedOptionalSimultaneousUrn
import Mathlib.Tactic

/-!
# Extracting the first-touch trace of an observed optional-testing policy

For a deterministic policy that completes every placement, the existing
operational transcript already contains a duplicate-free list of all labels
in first-touch order.  This file packages that list as the permutation needed
by `RandomizedOptionalTraceBijection`; it does not introduce another runtime.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedTrace

open TraceBijection
open ObservedOnline
open Randomized

noncomputable section

abbrev Placement (n : ℕ) := Equiv.Perm (Fin n)

def actionObservation {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ) :
    ObservedOnline.Action n → ObservedOnline.Observation n
  | .test job => .testResult job (processing job)
  | .process job => .processed job
  | .blind job => .blindCompleted job (processing job)

def observationTouchChoice? {n : ℕ} :
    ObservedOnline.Observation n →
      Option (ObservedOnline.Label n × TraceBijection.TouchKind)
  | .testResult job _ => some (job, .test)
  | .processed _ => none
  | .blindCompleted job _ => some (job, .blind)

def touchChoices {n : ℕ} :
    ObservedOnline.Transcript n →
      List (ObservedOnline.Label n × TraceBijection.TouchKind)
  | [] => []
  | observation :: rest =>
      match observationTouchChoice? observation with
      | some choice => choice :: touchChoices rest
      | none => touchChoices rest

theorem touchChoices_eq_filterMap {n : ℕ}
    (transcript : ObservedOnline.Transcript n) :
    touchChoices transcript =
      transcript.filterMap observationTouchChoice? := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> simp [touchChoices, observationTouchChoice?, ih]

theorem touchChoices_prefix {n : ℕ}
    {left right : ObservedOnline.Transcript n} (h : left <+: right) :
    touchChoices left <+: touchChoices right := by
  rw [touchChoices_eq_filterMap, touchChoices_eq_filterMap]
  exact h.filterMap observationTouchChoice?

def touchValues {n : ℕ} :
    ObservedOnline.Transcript n → List ℝ
  | [] => []
  | .testResult _ p :: rest => p :: touchValues rest
  | .processed _ :: rest => touchValues rest
  | .blindCompleted _ p :: rest => p :: touchValues rest

theorem touchChoices_map_fst {n : ℕ}
    (transcript : ObservedOnline.Transcript n) :
    (touchChoices transcript).map Prod.fst = transcript.startedLabels := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [touchChoices, observationTouchChoice?,
          ObservedOnline.Transcript.startedLabels,
          ObservedOnline.Transcript.revealedResults, ih]

theorem touchValues_eq_startedLabels_map {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (transcript : ObservedOnline.Transcript n)
    (hmatch : ObservedOnline.AllRevealsMatch processing transcript) :
    touchValues transcript = transcript.startedLabels.map processing := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hrest : ObservedOnline.AllRevealsMatch processing rest := by
        intro job p hmem
        apply hmatch job p
        cases observation <;>
          simp [ObservedOnline.Transcript.revealedResults, hmem]
      cases observation with
      | testResult job p =>
          have hp : p = processing job := hmatch job p (by
            simp [ObservedOnline.Transcript.revealedResults])
          simp [touchValues, ObservedOnline.Transcript.startedLabels,
            ObservedOnline.Transcript.revealedResults, hp, ih hrest]
      | processed job =>
          simp [touchValues, ObservedOnline.Transcript.startedLabels,
            ObservedOnline.Transcript.revealedResults, ih hrest]
      | blindCompleted job p =>
          have hp : p = processing job := hmatch job p (by
            simp [ObservedOnline.Transcript.revealedResults])
          simp [touchValues, ObservedOnline.Transcript.startedLabels,
            ObservedOnline.Transcript.revealedResults, hp, ih hrest]

/-- Test-class counts are exactly the test-kind weights in the extracted
first-touch list. -/
theorem testClassCount_eq_touchChoices_sum {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (category : ℝ → Bool) (transcript : ObservedOnline.Transcript n)
    (hmatch : ObservedOnline.AllRevealsMatch processing transcript) :
    (ObservedOnline.testClassCount category transcript : ℝ) =
      ((touchChoices transcript).map fun choice =>
        if choice.2 = .test ∧ category (processing choice.1) then
          (1 : ℝ) else 0).sum := by
  induction transcript with
  | nil =>
      simp [ObservedOnline.testClassCount,
        ObservedOnline.Transcript.testResults, touchChoices]
  | cons observation rest ih =>
      have hrest : ObservedOnline.AllRevealsMatch processing rest := by
        intro job p hmem
        apply hmatch job p
        cases observation <;>
          simp [ObservedOnline.Transcript.revealedResults, hmem]
      cases observation with
      | testResult job p =>
          have hp : p = processing job := hmatch job p (by
            simp [ObservedOnline.Transcript.revealedResults])
          rw [hp]
          have ih' := ih hrest
          unfold ObservedOnline.testClassCount at ih' ⊢
          cases hcat : category (processing job)
          · simpa [ObservedOnline.Transcript.testResults, touchChoices,
              observationTouchChoice?, hcat] using ih'
          · simp [ObservedOnline.Transcript.testResults, touchChoices,
              observationTouchChoice?, hcat]
            linarith
      | processed job =>
          simpa [ObservedOnline.testClassCount,
            ObservedOnline.Transcript.testResults, touchChoices,
            observationTouchChoice?] using ih hrest
      | blindCompleted job p =>
          simpa [ObservedOnline.testClassCount,
            ObservedOnline.Transcript.testResults, touchChoices,
            observationTouchChoice?] using ih hrest

/-- Blind work is exactly the blind-kind processing-time weight in the
extracted first-touch list. -/
theorem blindWork_eq_touchChoices_sum {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (transcript : ObservedOnline.Transcript n)
    (hmatch : ObservedOnline.AllRevealsMatch processing transcript) :
    ObservedOnline.blindWork transcript =
      ((touchChoices transcript).map fun choice =>
        if choice.2 = .blind then processing choice.1 else 0).sum := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hrest : ObservedOnline.AllRevealsMatch processing rest := by
        intro job p hmem
        apply hmatch job p
        cases observation <;>
          simp [ObservedOnline.Transcript.revealedResults, hmem]
      cases observation with
      | testResult job p =>
          simpa [ObservedOnline.blindWork, touchChoices,
            observationTouchChoice?] using ih hrest
      | processed job =>
          simpa [ObservedOnline.blindWork, touchChoices,
            observationTouchChoice?] using ih hrest
      | blindCompleted job p =>
          have hp : p = processing job := hmatch job p (by
            simp [ObservedOnline.Transcript.revealedResults])
          simp [ObservedOnline.blindWork, touchChoices,
            observationTouchChoice?, hp, ih hrest]

theorem blindCount_eq_touchChoices_sum {n : ℕ}
    (transcript : ObservedOnline.Transcript n) :
    (ObservedOnline.blindCount transcript : ℝ) =
      ((touchChoices transcript).map fun choice =>
        if choice.2 = .blind then (1 : ℝ) else 0).sum := by
  induction transcript with
  | nil => simp [ObservedOnline.blindCount, touchChoices]
  | cons observation rest ih =>
      cases observation <;>
        simp [ObservedOnline.blindCount, touchChoices,
          observationTouchChoice?, ih]

@[simp] theorem testClassCount_true {n : ℕ}
    (transcript : ObservedOnline.Transcript n) :
    ObservedOnline.testClassCount (fun _ => true) transcript =
      transcript.testResults.length := by
  unfold ObservedOnline.testClassCount
  simp

/-- The fresh operation word produced after an arbitrary current
configuration.  It mirrors `runFuel`, but records only the newly appended
observations and is used solely for a lockstep causality proof. -/
def runWord {n : ℕ} (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) :
    ℕ → ObservedOnline.Config n → ObservedOnline.Transcript n
  | 0, _ => []
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => []
      | some action =>
          match config.step processing action with
          | none => []
          | some next => actionObservation processing action ::
              runWord processing strategy fuel next

theorem runWord_prefix_succ {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) (fuel : ℕ)
    (config : ObservedOnline.Config n) :
    runWord processing strategy fuel config <+:
      runWord processing strategy (fuel + 1) config := by
  induction fuel generalizing config with
  | zero => simp [runWord]
  | succ fuel ih =>
      simp only [runWord]
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none => simp
          | some next =>
              simp only
              rcases ih next with ⟨tail, htail⟩
              refine ⟨tail, ?_⟩
              simpa only [List.cons_append] using
                congrArg (List.cons (actionObservation processing action)) htail

theorem runWord_prefix_of_le {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) {fuel fuel' : ℕ}
    (hfuel : fuel ≤ fuel') (config : ObservedOnline.Config n) :
    runWord processing strategy fuel config <+:
      runWord processing strategy fuel' config := by
  induction fuel', hfuel using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ fuel' hle ih =>
      exact ih.trans (runWord_prefix_succ processing strategy fuel' config)

theorem runWord_length_le_fuel {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) (fuel : ℕ)
    (config : ObservedOnline.Config n) :
    (runWord processing strategy fuel config).length ≤ fuel := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      simp only [runWord]
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none => simp
          | some next =>
              simp only [List.length_cons]
              exact Nat.succ_le_succ (ih next)

/-- If a later run contains at least `fuel` successful observations, then the
`fuel`-truncated run contains exactly its full fuel budget.  In particular a
completed later run cannot hide an early stop or invalid action. -/
theorem runWord_length_eq_fuel_of_le_later {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) {fuel later : ℕ}
    (hfuel : fuel ≤ later) (config : ObservedOnline.Config n)
    (hlength : fuel ≤ (runWord processing strategy later config).length) :
    (runWord processing strategy fuel config).length = fuel := by
  induction fuel generalizing later config with
  | zero => rfl
  | succ fuel ih =>
      cases later with
      | zero => omega
      | succ later =>
          have hfuel' : fuel ≤ later := by omega
          simp only [runWord] at hlength ⊢
          cases haction : strategy config.transcript with
          | none => simp [haction] at hlength
          | some action =>
              simp only [haction] at hlength ⊢
              cases hstep : config.step processing action with
              | none => simp [hstep] at hlength
              | some next =>
                  simp only [hstep, List.length_cons] at hlength ⊢
                  exact congrArg Nat.succ
                    (ih hfuel' next (by omega))

theorem step_transcript_eq_append_observation {n : ℕ}
    {processing : ObservedOnline.Label n → ℝ}
    {config next : ObservedOnline.Config n} {action : ObservedOnline.Action n}
    (hstep : config.step processing action = some next) :
    next.transcript = config.transcript ++ [actionObservation processing action] := by
  cases action with
  | test job =>
      cases hstate : config.jobs job <;>
        simp [ObservedOnline.Config.step, hstate] at hstep
      subst next
      rfl
  | process job =>
      cases hstate : config.jobs job <;>
        simp [ObservedOnline.Config.step, hstate] at hstep
      subst next
      rfl
  | blind job =>
      cases hstate : config.jobs job <;>
        simp [ObservedOnline.Config.step, hstate] at hstep
      subst next
      rfl

theorem runFuel_transcript_eq_append_runWord {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) (fuel : ℕ)
    (config : ObservedOnline.Config n) :
    (ObservedOnline.runFuel processing strategy fuel config).config.transcript =
      config.transcript ++ runWord processing strategy fuel config := by
  induction fuel generalizing config with
  | zero => simp [ObservedOnline.runFuel, runWord]
  | succ fuel ih =>
      simp only [ObservedOnline.runFuel, runWord]
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
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) (fuel : ℕ) :
    (ObservedOnline.run processing strategy fuel).config.transcript =
      runWord processing strategy fuel (ObservedOnline.Config.initial n) := by
  unfold ObservedOnline.run
  simpa [ObservedOnline.Config.initial] using
    runFuel_transcript_eq_append_runWord processing strategy fuel
      (ObservedOnline.Config.initial n)

theorem run_transcript_prefix_of_le {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) {fuel fuel' : ℕ}
    (hfuel : fuel ≤ fuel') :
    (ObservedOnline.run processing strategy fuel).config.transcript <+:
      (ObservedOnline.run processing strategy fuel').config.transcript := by
  rw [run_transcript_eq_runWord, run_transcript_eq_runWord]
  exact runWord_prefix_of_le processing strategy hfuel
    (ObservedOnline.Config.initial n)

/-- Every operation prefix of a later run is reproduced exactly by choosing
fuel equal to the prefix length. -/
theorem run_transcript_eq_take_of_le_length {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) {fuel later : ℕ}
    (hfuel : fuel ≤ later)
    (hlength : fuel ≤
      (ObservedOnline.run processing strategy later).config.transcript.length) :
    (ObservedOnline.run processing strategy fuel).config.transcript =
      (ObservedOnline.run processing strategy later).config.transcript.take fuel := by
  have hprefix := run_transcript_prefix_of_le processing strategy hfuel
  have hlen :
      (ObservedOnline.run processing strategy fuel).config.transcript.length =
        fuel := by
    rw [run_transcript_eq_runWord]
    rw [run_transcript_eq_runWord] at hlength
    exact runWord_length_eq_fuel_of_le_later processing strategy hfuel
      (ObservedOnline.Config.initial n) hlength
  have heq := List.prefix_iff_eq_take.mp hprefix
  rw [hlen] at heq
  exact heq

theorem list_eq_take_of_prefix {X : Type*} {left right : List X}
    (h : left <+: right) : left = right.take left.length := by
  rcases h with ⟨tail, htail⟩
  rw [← htail, List.take_left]

def prefixIndexEquiv {n : ℕ} (cutoff : Fin n) :
    Fin (cutoff.val + 1) ≃ ↥(positionsThrough cutoff) where
  toFun k := by
    have hk : k.val ≤ cutoff.val := Nat.le_of_lt_succ k.isLt
    exact ⟨⟨k.val, hk.trans_lt cutoff.isLt⟩,
      mem_positionsThrough.mpr hk⟩
  invFun k := ⟨k.val.val,
    Nat.lt_succ_iff.mpr (mem_positionsThrough.mp k.property)⟩
  left_inv k := by ext; rfl
  right_inv k := by ext; rfl

theorem sum_positionsThrough_eq_prefixFin {n : ℕ} (cutoff : Fin n)
    (f : Fin n → ℝ) :
    (∑ k ∈ positionsThrough cutoff, f k) =
      ∑ j : Fin (cutoff.val + 1), f (prefixIndexEquiv cutoff j) := by
  rw [← Finset.sum_coe_sort]
  exact (Equiv.sum_comp (prefixIndexEquiv cutoff)
    (fun k : ↥(positionsThrough cutoff) => f k)).symm

theorem take_eq_ofFn_get {X : Type*} (items : List X) {m : ℕ}
    (hm : m ≤ items.length) :
    items.take m = List.ofFn (fun k : Fin m =>
      items.get ⟨k.val, lt_of_lt_of_le k.isLt hm⟩) := by
  apply List.ext_get
  · simp [List.length_take_of_le hm]
  · intro k hkLeft hkRight
    rw [List.get_ofFn]
    simp

theorem sum_map_take_eq_positionsThrough {n : ℕ} (items : List X)
    (hlength : items.length = n) (cutoff : Fin n) (f : X → ℝ) :
    ((items.take (cutoff.val + 1)).map f).sum =
      ∑ k ∈ positionsThrough cutoff,
        f (items.get ⟨k.val, by simpa [hlength] using k.isLt⟩) := by
  have hm : cutoff.val + 1 ≤ items.length := by
    rw [hlength]
    omega
  rw [take_eq_ofFn_get items hm, List.map_ofFn, List.sum_ofFn,
    sum_positionsThrough_eq_prefixFin]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

/-- Every fuel-truncated first-touch list is literally the corresponding
initial segment of the settled first-touch list. -/
theorem run_touchChoices_eq_settled_take {n : ℕ}
    (processing : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) :
    touchChoices (ObservedOnline.run processing strategy fuel).config.transcript =
      (touchChoices
        (ObservedOnline.run processing strategy (2 * n + 1)).config.transcript).take
          (touchChoices
            (ObservedOnline.run processing strategy fuel).config.transcript).length := by
  apply list_eq_take_of_prefix
  exact touchChoices_prefix
    (run_transcript_prefix_of_le processing strategy hfuel)

/-- Lockstep causality for the existing operational semantics.  If the next
`k` exposed values agree, then the first `k+1` test/blind choices agree.  A
`process` action reads no new value; test and blind choose their public label
before their truthful result is appended. -/
theorem runWord_touchChoices_causal {n : ℕ}
    (processing processing' : ObservedOnline.Label n → ℝ)
    (strategy : ObservedOnline.Strategy n) (fuel k : ℕ)
    (config : ObservedOnline.Config n)
    (hvalues :
      (touchValues (runWord processing strategy fuel config)).take k =
        (touchValues (runWord processing' strategy fuel config)).take k) :
    (touchChoices (runWord processing strategy fuel config)).take (k + 1) =
      (touchChoices (runWord processing' strategy fuel config)).take (k + 1) := by
  induction fuel generalizing config k with
  | zero => simp [runWord]
  | succ fuel ih =>
      simp only [runWord] at hvalues ⊢
      cases haction : strategy config.transcript with
      | none => simp
      | some action =>
          simp only [haction] at hvalues ⊢
          cases action with
          | process job =>
              cases hstate : config.jobs job with
              | untouched => simp [ObservedOnline.Config.step, hstate]
              | done => simp [ObservedOnline.Config.step, hstate]
              | tested p =>
                  simp only [ObservedOnline.Config.step, hstate,
                    actionObservation, observationTouchChoice?,
                    touchValues, touchChoices] at hvalues ⊢
                  exact ih k _ hvalues
          | test job =>
              cases hstate : config.jobs job with
              | tested p => simp [ObservedOnline.Config.step, hstate]
              | done => simp [ObservedOnline.Config.step, hstate]
              | untouched =>
                  cases k with
                  | zero => simp [ObservedOnline.Config.step, hstate,
                      actionObservation, observationTouchChoice?, touchChoices]
                  | succ k =>
                      simp only [ObservedOnline.Config.step, hstate,
                        actionObservation, touchValues,
                        List.take_succ_cons, List.cons.injEq] at hvalues
                      have hp : processing job = processing' job := hvalues.1
                      simp only [ObservedOnline.Config.step, hstate,
                        actionObservation, observationTouchChoice?, touchChoices,
                        List.take_succ_cons, List.cons.injEq]
                      rw [← hp] at hvalues ⊢
                      exact ⟨True.intro, ih k _ hvalues.2⟩
          | blind job =>
              cases hstate : config.jobs job with
              | tested p => simp [ObservedOnline.Config.step, hstate]
              | done => simp [ObservedOnline.Config.step, hstate]
              | untouched =>
                  cases k with
                  | zero => simp [ObservedOnline.Config.step, hstate,
                      actionObservation, observationTouchChoice?, touchChoices]
                  | succ k =>
                      simp only [ObservedOnline.Config.step, hstate,
                        actionObservation, touchValues,
                        List.take_succ_cons, List.cons.injEq] at hvalues
                      have hp : processing job = processing' job := hvalues.1
                      simp only [ObservedOnline.Config.step, hstate,
                        actionObservation, observationTouchChoice?, touchChoices,
                        List.take_succ_cons, List.cons.injEq]
                      rw [← hp] at hvalues ⊢
                      exact ⟨True.intro, ih k _ hvalues.2⟩

def placedProcessing {n : ℕ} (p : Fin n → ℝ)
    (σ : Placement n) : ObservedOnline.Label n → ℝ :=
  fun label ↦ p (σ label)

def settledRun {n : ℕ} (p : Fin n → ℝ)
    (strategy : ObservedOnline.Strategy n) (σ : Placement n) :
    ObservedOnline.RunResult n :=
  ObservedOnline.run (placedProcessing p σ) strategy (2 * n + 1)

/-- The policies relevant to a finite completion-time lower bound finish all
jobs legally for every placement of the fixed occurrence vector. -/
structure CompletePolicy {n : ℕ} (p : Fin n → ℝ) where
  strategy : ObservedOnline.Strategy n
  completes : ∀ σ job, (settledRun p strategy σ).config.jobs job = .done

private def listOrderFn {n : ℕ} (labels : List (Fin n))
    (hlength : labels.length = n) : Fin n → Fin n :=
  fun k ↦ labels.get (Fin.cast hlength.symm k)

private theorem listOrderFn_injective {n : ℕ} (labels : List (Fin n))
    (hlength : labels.length = n) (hnodup : labels.Nodup) :
    Function.Injective (listOrderFn labels hlength) := by
  intro i j hij
  have hcast : Fin.cast hlength.symm i = Fin.cast hlength.symm j :=
    hnodup.get_inj_iff.mp hij
  apply Fin.ext
  simpa using congrArg Fin.val hcast

/-- A duplicate-free length-`n` list of `Fin n` is canonically a
permutation. -/
def listOrderPerm {n : ℕ} (labels : List (Fin n))
    (hlength : labels.length = n) (hnodup : labels.Nodup) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (listOrderFn labels hlength) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨listOrderFn_injective labels hlength hnodup, rfl⟩

@[simp] theorem listOrderPerm_apply {n : ℕ} (labels : List (Fin n))
    (hlength : labels.length = n) (hnodup : labels.Nodup) (k : Fin n) :
    listOrderPerm labels hlength hnodup k =
      labels.get (Fin.cast hlength.symm k) := rfl

theorem listOrderPerm_ofFn {n : ℕ} (labels : List (Fin n))
    (hlength : labels.length = n) (hnodup : labels.Nodup) :
    List.ofFn (listOrderPerm labels hlength hnodup) = labels := by
  apply List.ext_get
  · simp [hlength]
  · intro k hkLeft hkRight
    simp only [List.length_ofFn] at hkLeft
    rw [List.get_ofFn]
    simp [listOrderPerm, listOrderFn]

theorem list_ofFn_cast_get {n : ℕ} {X : Type*} (items : List X)
    (hlength : items.length = n) :
    List.ofFn (fun k : Fin n ↦ items.get (Fin.cast hlength.symm k)) = items := by
  apply List.ext_get
  · simp [hlength]
  · intro k hkLeft hkRight
    simp only [List.length_ofFn] at hkLeft
    rw [List.get_ofFn]
    congr 1

private theorem settled_started_length {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    (settledRun p policy.strategy σ).config.transcript.startedLabels.length = n := by
  apply HistoryInvariant.startedLabels_length_eq_n_of_done
    (run_historyInvariant (placedProcessing p σ) policy.strategy (2 * n + 1))
  exact policy.completes σ

private theorem settled_started_nodup {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    (settledRun p policy.strategy σ).config.transcript.startedLabels.Nodup :=
  (run_historyInvariant (placedProcessing p σ)
    policy.strategy (2 * n + 1)).startedNodup

def touchLabelOrder {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) : Equiv.Perm (Fin n) :=
  let choices := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  let labels := choices.map Prod.fst
  have hlength : labels.length = n := by
    dsimp [labels, choices]
    rw [touchChoices_map_fst]
    exact settled_started_length p policy σ
  have hnodup : labels.Nodup := by
    dsimp [labels, choices]
    rw [touchChoices_map_fst]
    exact settled_started_nodup p policy σ
  listOrderPerm labels hlength hnodup

private theorem settled_choices_length {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    (touchChoices
      (settledRun p policy.strategy σ).config.transcript).length = n := by
  rw [← List.length_map, touchChoices_map_fst]
  exact settled_started_length p policy σ

/-- The actual completed operational run, viewed only through its order and
kind of first touches. -/
def touchTrace {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    TraceBijection.TouchTrace n where
  label := touchLabelOrder p policy σ
  kind := fun k ↦
    (touchChoices
      (settledRun p policy.strategy σ).config.transcript).get
        (Fin.cast (settled_choices_length p policy σ).symm k) |>.2

theorem touchLabelOrder_apply_get {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) (k : Fin n) :
    touchLabelOrder p policy σ k =
      ((touchChoices
        (settledRun p policy.strategy σ).config.transcript).map Prod.fst).get
          (Fin.cast (by simpa using (settled_choices_length p policy σ).symm) k) := by
  rfl

theorem touchLabelOrder_ofFn {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    List.ofFn (touchLabelOrder p policy σ) =
      (settledRun p policy.strategy σ).config.transcript.startedLabels := by
  unfold touchLabelOrder
  rw [listOrderPerm_ofFn, touchChoices_map_fst]

theorem settled_touchValues_eq_ofFn {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    touchValues (settledRun p policy.strategy σ).config.transcript =
      List.ofFn (fun k ↦
        p (TraceBijection.revealOrder (touchTrace p policy) σ k)) := by
  have hmatch := (run_historyInvariant (placedProcessing p σ)
    policy.strategy (2 * n + 1)).revealsMatch
  change touchValues
    (ObservedOnline.run (placedProcessing p σ) policy.strategy
      (2 * n + 1)).config.transcript = _
  rw [touchValues_eq_startedLabels_map (placedProcessing p σ) _ hmatch]
  have horder := touchLabelOrder_ofFn p policy σ
  unfold settledRun at horder
  rw [← horder, List.map_ofFn]
  rfl

theorem touchTrace_choice_eq_get {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) (k : Fin n) :
    ((touchTrace p policy σ).label k, (touchTrace p policy σ).kind k) =
      (touchChoices
        (settledRun p policy.strategy σ).config.transcript).get
          (Fin.cast (settled_choices_length p policy σ).symm k) := by
  apply Prod.ext
  · change
      touchLabelOrder p policy σ k =
        ((touchChoices
          (settledRun p policy.strategy σ).config.transcript).get
            (Fin.cast (settled_choices_length p policy σ).symm k)).1
    unfold touchLabelOrder
    simp [listOrderPerm, listOrderFn]
  · rfl

theorem touchTrace_choices_ofFn {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (σ : Placement n) :
    List.ofFn (fun k =>
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k)) =
      touchChoices (settledRun p policy.strategy σ).config.transcript := by
  let choices := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  have hlength : choices.length = n := settled_choices_length p policy σ
  calc
    List.ofFn (fun k =>
        ((touchTrace p policy σ).label k,
          (touchTrace p policy σ).kind k)) =
        List.ofFn (fun k => choices.get (Fin.cast hlength.symm k)) := by
      apply congrArg List.ofFn
      funext k
      exact touchTrace_choice_eq_get p policy σ k
    _ = choices := list_ofFn_cast_get choices hlength

/-- The scheduler-facing lemma promised by the trace-bijection reduction.
It is a direct consequence of the lockstep `runWord` theorem and the exact
identification of the operational first-touch values with `revealOrder`. -/
theorem touchTrace_causal {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    TraceBijection.Causal p (touchTrace p policy) := by
  intro σ τ k hprefix
  let processing := placedProcessing p σ
  let processing' := placedProcessing p τ
  let initial := ObservedOnline.Config.initial n
  have htakeOfFn :
      (List.ofFn (fun j ↦
        p (TraceBijection.revealOrder (touchTrace p policy) σ j))).take k.val =
      (List.ofFn (fun j ↦
        p (TraceBijection.revealOrder (touchTrace p policy) τ j))).take k.val :=
    TraceBijection.take_ofFn_eq_of_prefix _ _ hprefix
  have hvaluesσ := settled_touchValues_eq_ofFn p policy σ
  have hvaluesτ := settled_touchValues_eq_ofFn p policy τ
  have hrunσ := run_transcript_eq_runWord processing policy.strategy (2 * n + 1)
  have hrunτ := run_transcript_eq_runWord processing' policy.strategy (2 * n + 1)
  have htakeValues :
      (touchValues (runWord processing policy.strategy (2 * n + 1) initial)).take
          k.val =
        (touchValues (runWord processing' policy.strategy (2 * n + 1) initial)).take
          k.val := by
    unfold settledRun at hvaluesσ hvaluesτ
    dsimp [processing, processing', initial] at hrunσ hrunτ ⊢
    rw [← hrunσ, ← hrunτ, hvaluesσ, hvaluesτ]
    exact htakeOfFn
  have htakeChoicesWord := runWord_touchChoices_causal
    processing processing' policy.strategy (2 * n + 1) k.val initial htakeValues
  have htakeChoices :
      (touchChoices
        (settledRun p policy.strategy σ).config.transcript).take (k.val + 1) =
      (touchChoices
        (settledRun p policy.strategy τ).config.transcript).take (k.val + 1) := by
    unfold settledRun
    dsimp [processing, processing', initial] at hrunσ hrunτ htakeChoicesWord ⊢
    rw [hrunσ, hrunτ]
    exact htakeChoicesWord
  let left := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  let right := touchChoices
    (settledRun p policy.strategy τ).config.transcript
  have hkLeft : k.val < left.length := by
    dsimp [left]
    rw [settled_choices_length p policy σ]
    exact k.isLt
  have hkRight : k.val < right.length := by
    dsimp [right]
    rw [settled_choices_length p policy τ]
    exact k.isLt
  have hraw : left.get ⟨k.val, hkLeft⟩ = right.get ⟨k.val, hkRight⟩ :=
    TraceBijection.get_eq_of_take_succ_eq hkLeft hkRight (by
      simpa [left, right] using htakeChoices)
  have hpair :
      ((touchTrace p policy σ).label k, (touchTrace p policy σ).kind k) =
        ((touchTrace p policy τ).label k, (touchTrace p policy τ).kind k) := by
    rw [touchTrace_choice_eq_get p policy σ k,
      touchTrace_choice_eq_get p policy τ k]
    simpa [left, right] using hraw
  constructor
  · have hfst := congrArg
        (fun pair : Fin n × TraceBijection.TouchKind ↦ pair.1) hpair
    exact hfst
  · have hsnd := congrArg
        (fun pair : Fin n × TraceBijection.TouchKind ↦ pair.2) hpair
    exact hsnd

/-- The concrete predictable selector exported to the urn concentration
layer for an arbitrary completed observed policy. -/
def compiledTestSelector {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    Fin n → Equiv.Perm (Fin n) → ℝ :=
  TraceBijection.compiledTestSelector p (touchTrace p policy)
    (touchTrace_causal p policy)

theorem compiledTestSelector_nonneg {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    ∀ k reveal, 0 ≤ compiledTestSelector p policy k reveal := by
  intro k reveal
  simpa [compiledTestSelector] using
    TraceBijection.compiledTestSelector_nonneg p
      (touchTrace p policy) (touchTrace_causal p policy) k reveal

theorem compiledTestSelector_le_one {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    ∀ k reveal, compiledTestSelector p policy k reveal ≤ 1 := by
  intro k reveal
  simpa [compiledTestSelector] using
    TraceBijection.compiledTestSelector_le_one p
      (touchTrace p policy) (touchTrace_causal p policy) k reveal

def compiledBlindSelector {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    Fin n → Equiv.Perm (Fin n) → ℝ :=
  fun k reveal => 1 - compiledTestSelector p policy k reveal

theorem compiledBlindSelector_predictable {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    PredictableSelector (compiledBlindSelector p policy) := by
  intro k reveal reveal' hpref
  unfold compiledBlindSelector
  apply congrArg (fun z : ℝ => 1 - z)
  change TraceBijection.compiledTestSelector p (touchTrace p policy)
      (touchTrace_causal p policy) k reveal =
    TraceBijection.compiledTestSelector p (touchTrace p policy)
      (touchTrace_causal p policy) k reveal'
  exact TraceBijection.compiledTestSelector_predictable p
    (touchTrace p policy) (touchTrace_causal p policy)
      k reveal reveal' hpref

theorem compiledBlindSelector_nonneg {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    ∀ k reveal, 0 ≤ compiledBlindSelector p policy k reveal := by
  intro k reveal
  unfold compiledBlindSelector
  exact sub_nonneg.mpr (by
    simpa [compiledTestSelector] using
      TraceBijection.compiledTestSelector_le_one p
        (touchTrace p policy) (touchTrace_causal p policy) k reveal)

theorem compiledBlindSelector_le_one {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    ∀ k reveal, compiledBlindSelector p policy k reveal ≤ 1 := by
  intro k reveal
  unfold compiledBlindSelector
  linarith [show 0 ≤ compiledTestSelector p policy k reveal by
    simpa [compiledTestSelector] using
      TraceBijection.compiledTestSelector_nonneg p
        (touchTrace p policy) (touchTrace_causal p policy) k reveal]

theorem compiledTestSelector_predictable {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) :
    PredictableSelector (compiledTestSelector p policy) :=
  TraceBijection.compiledTestSelector_predictable p (touchTrace p policy)
    (touchTrace_causal p policy)

theorem uniformAverage_adaptive_revealOrder {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (f : Equiv.Perm (Fin n) → ℝ) :
    Randomized.uniformAverage (fun σ ↦
      f (TraceBijection.revealOrder (touchTrace p policy) σ)) =
        Randomized.uniformAverage f :=
  TraceBijection.uniformAverage_revealOrder p (touchTrace p policy)
    (touchTrace_causal p policy) f

theorem uniformProbability_adaptive_revealOrder {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Randomized.uniformProbability (fun σ =>
      P (TraceBijection.revealOrder (touchTrace p policy) σ)) =
        Randomized.uniformProbability P := by
  unfold Randomized.uniformProbability
  simpa [Function.comp_def] using
    TraceBijection.uniformAverage_revealOrder p (touchTrace p policy)
      (touchTrace_causal p policy)
      (fun reveal => if P reveal then (1 : ℝ) else 0)

/-- The all-categories/all-prefix predictable-urn event, reindexed back from
the canonical reveal permutation to the original hidden placement of an
arbitrary completed adaptive policy. -/
theorem adaptivePolicy_all_categories_prefix_probability_le
    {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 1 < n) (p : Fin n → ℝ) (policy : CompletePolicy p)
    (value : κ → Fin n → ℝ) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hvalue0 : ∀ c i, 0 ≤ value c i)
    (hvalue1 : ∀ c i, value c i ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    Randomized.uniformProbability (fun σ => ∃ c, ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            compiledTestSelector p policy k
                (TraceBijection.revealOrder (touchTrace p policy) σ) *
              value c
                (TraceBijection.revealOrder (touchTrace p policy) σ k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                (TraceBijection.revealOrder (touchTrace p policy) σ)|) ≤
      Fintype.card κ *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) := by
  let select := compiledTestSelector p policy
  let bad : Equiv.Perm (Fin n) → Prop := fun reveal =>
    ∃ c, ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            select k reveal * value c (reveal k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j, select k reveal|
  have hcanonical : Randomized.uniformProbability bad ≤
      Fintype.card κ *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) := by
    exact predictable_selected_all_categories_prefix_regular_probability_le
      hn value select cutoff hMartingaleStep hSuffixStep
        (compiledTestSelector_predictable p policy) hvalue0 hvalue1
        (fun k reveal => TraceBijection.compiledTestSelector_nonneg p
          (touchTrace p policy) (touchTrace_causal p policy) k reveal)
        (fun k reveal => TraceBijection.compiledTestSelector_le_one p
          (touchTrace p policy) (touchTrace_causal p policy) k reveal)
        he hr
  calc
    Randomized.uniformProbability (fun σ => ∃ c, ∃ j ∈ positionsThrough cutoff,
        e + martingaleStep +
            (r + 2 * suffixStep /
              (suffixPositions cutoff).card) * n <
          |(∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                  (TraceBijection.revealOrder (touchTrace p policy) σ) *
                value c
                  (TraceBijection.revealOrder (touchTrace p policy) σ k)) -
            populationMean (value c) *
              ∑ k ∈ positionsThrough j,
                compiledTestSelector p policy k
                  (TraceBijection.revealOrder (touchTrace p policy) σ)|) =
        Randomized.uniformProbability bad := by
      unfold Randomized.uniformProbability
      simpa [bad, select, Function.comp_def] using
        TraceBijection.uniformAverage_revealOrder p (touchTrace p policy)
          (touchTrace_causal p policy)
          (fun reveal => if bad reveal then (1 : ℝ) else 0)
    _ ≤ _ := hcanonical

/-- The same simultaneous-prefix event for blind selection (the complement
of the test selector). -/
theorem adaptivePolicy_blind_prefix_probability_le
    {n : ℕ} (hn : 1 < n) (p : Fin n → ℝ)
    (policy : CompletePolicy p) (value : Fin n → ℝ) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hvalue0 : ∀ i, 0 ≤ value i) (hvalue1 : ∀ i, value i ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    Randomized.uniformProbability (fun σ => ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            compiledBlindSelector p policy k
                (TraceBijection.revealOrder (touchTrace p policy) σ) *
              value (TraceBijection.revealOrder (touchTrace p policy) σ k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                (TraceBijection.revealOrder (touchTrace p policy) σ)|) ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
  let select := compiledBlindSelector p policy
  let bad : Equiv.Perm (Fin n) → Prop := fun reveal =>
    ∃ j ∈ positionsThrough cutoff,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n <
        |(∑ k ∈ positionsThrough j,
            select k reveal * value (reveal k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j, select k reveal|
  have hcanonical : Randomized.uniformProbability bad ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
    exact predictable_selected_all_prefix_regular_probability_le
      hn value select cutoff hMartingaleStep hSuffixStep
        (compiledBlindSelector_predictable p policy) hvalue0 hvalue1
        (compiledBlindSelector_nonneg p policy)
        (compiledBlindSelector_le_one p policy) he hr
  calc
    Randomized.uniformProbability (fun σ => ∃ j ∈ positionsThrough cutoff,
        e + martingaleStep +
            (r + 2 * suffixStep /
              (suffixPositions cutoff).card) * n <
          |(∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (TraceBijection.revealOrder (touchTrace p policy) σ) *
                value (TraceBijection.revealOrder (touchTrace p policy) σ k)) -
            populationMean value *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (TraceBijection.revealOrder (touchTrace p policy) σ)|) =
        Randomized.uniformProbability bad := by
      unfold Randomized.uniformProbability
      simpa [bad, select, Function.comp_def] using
        TraceBijection.uniformAverage_revealOrder p (touchTrace p policy)
          (touchTrace_causal p policy)
          (fun reveal => if bad reveal then (1 : ℝ) else 0)
    _ ≤ _ := hcanonical

theorem compiled_test_selection_identity {n : ℕ}
    (p value : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) :
    (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ) *
          value (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ∑ k, if (touchTrace p policy σ).kind k = .test then
        value (σ ((touchTrace p policy σ).label k)) else 0 :=
  TraceBijection.compiled_test_selection_identity p (touchTrace p policy)
    (touchTrace_causal p policy) value σ

theorem compiled_test_selection_prefix_identity {n : ℕ}
    (p value : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) (cutoff : Fin n) :
    (∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
          (TraceBijection.revealOrder (touchTrace p policy) σ) *
          value (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ∑ k ∈ positionsThrough cutoff,
        if (touchTrace p policy σ).kind k = .test then
          value (σ ((touchTrace p policy σ).label k)) else 0 :=
  TraceBijection.compiled_test_selection_prefix_identity p
    (touchTrace p policy) (touchTrace_causal p policy) value σ cutoff

theorem compiled_blind_selection_identity {n : ℕ}
    (p value : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) :
    (∑ k, (1 - compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ)) *
          value (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ∑ k, if (touchTrace p policy σ).kind k = .blind then
        value (σ ((touchTrace p policy σ).label k)) else 0 :=
  TraceBijection.compiled_blind_selection_identity p (touchTrace p policy)
    (touchTrace_causal p policy) value σ

theorem compiled_blind_selection_prefix_identity {n : ℕ}
    (p value : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) (cutoff : Fin n) :
    (∑ k ∈ positionsThrough cutoff,
        (1 - compiledTestSelector p policy k
          (TraceBijection.revealOrder (touchTrace p policy) σ)) *
          value (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ∑ k ∈ positionsThrough cutoff,
        if (touchTrace p policy σ).kind k = .blind then
          value (σ ((touchTrace p policy σ).label k)) else 0 :=
  TraceBijection.compiled_blind_selection_prefix_identity p
    (touchTrace p policy) (touchTrace_causal p policy) value σ cutoff

/-- The compiled full-trace selected class sum is the literal operational
test-class count. -/
theorem compiled_test_class_sum_eq_operational {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) (category : ℝ → Bool) :
    (∑ k, compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ) *
          (if category
            (p (TraceBijection.revealOrder (touchTrace p policy) σ k))
            then (1 : ℝ) else 0)) =
      ObservedOnline.testClassCount category
        (settledRun p policy.strategy σ).config.transcript := by
  have hcompiled := compiled_test_selection_identity p
    (fun x => if category (p x) then (1 : ℝ) else 0) policy σ
  rw [hcompiled]
  let choices := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  have hlist := touchTrace_choices_ofFn p policy σ
  have hmatch := (ObservedOnline.run_historyInvariant
    (placedProcessing p σ) policy.strategy (2 * n + 1)).revealsMatch
  have hoperational := testClassCount_eq_touchChoices_sum
    (placedProcessing p σ) category
    (settledRun p policy.strategy σ).config.transcript hmatch
  rw [hoperational]
  rw [← List.sum_ofFn]
  rw [show List.ofFn (fun k =>
      if (touchTrace p policy σ).kind k = .test then
        (if category (p (σ ((touchTrace p policy σ).label k))) then
          (1 : ℝ) else 0)
      else 0) =
    (List.ofFn (fun k =>
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k))).map (fun choice =>
        if choice.2 = .test ∧
            category ((placedProcessing p σ) choice.1) then
          (1 : ℝ) else 0) by
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext k
      by_cases ht : (touchTrace p policy σ).kind k = .test <;>
        by_cases hc : category
          (p (σ ((touchTrace p policy σ).label k)) ) <;>
        simp [placedProcessing, ht, hc]]
  rw [hlist]

/-- The compiled blind full-trace work is the literal operational blind
work. -/
theorem compiled_blind_work_sum_eq_operational {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p) (σ : Placement n) :
    (∑ k, (1 - compiledTestSelector p policy k
        (TraceBijection.revealOrder (touchTrace p policy) σ)) *
          p (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ObservedOnline.blindWork
        (settledRun p policy.strategy σ).config.transcript := by
  rw [compiled_blind_selection_identity]
  have hlist := touchTrace_choices_ofFn p policy σ
  have hmatch := (ObservedOnline.run_historyInvariant
    (placedProcessing p σ) policy.strategy (2 * n + 1)).revealsMatch
  have hoperational := blindWork_eq_touchChoices_sum
    (placedProcessing p σ)
    (settledRun p policy.strategy σ).config.transcript hmatch
  rw [hoperational]
  rw [← List.sum_ofFn]
  rw [show List.ofFn (fun k =>
      if (touchTrace p policy σ).kind k = .blind then
        p (σ ((touchTrace p policy σ).label k)) else 0) =
    (List.ofFn (fun k =>
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k))).map (fun choice =>
        if choice.2 = .blind then
          (placedProcessing p σ) choice.1 else 0) by
      rw [List.map_ofFn]
      rfl]
  rw [hlist]

/-- Literal test-class count in an arbitrary nonempty operational prefix,
expressed through the predictable selector on the canonical reveal
permutation.  The hypothesis records that the prefix has exactly the first
`cutoff + 1` touches. -/
theorem compiled_test_class_prefix_sum_eq_operational {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) (category : ℝ → Bool) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1) :
    (∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p policy k
            (TraceBijection.revealOrder (touchTrace p policy) σ) *
          (if category
            (p (TraceBijection.revealOrder (touchTrace p policy) σ k))
            then (1 : ℝ) else 0)) =
      ObservedOnline.testClassCount category
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript := by
  let current := touchChoices
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript
  let settled := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  let weight : Fin n × TraceBijection.TouchKind → ℝ := fun choice =>
    if choice.2 = .test ∧
        category ((placedProcessing p σ) choice.1) then 1 else 0
  have hmatch := (ObservedOnline.run_historyInvariant
    (placedProcessing p σ) policy.strategy fuel).revealsMatch
  have hoperational := testClassCount_eq_touchChoices_sum
    (placedProcessing p σ) category
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript hmatch
  have hcurrent : current = settled.take (cutoff.val + 1) := by
    dsimp [current, settled]
    rw [run_touchChoices_eq_settled_take (placedProcessing p σ)
      policy.strategy hfuel, hlength]
    rfl
  have hsettledLength : settled.length = n := by
    dsimp [settled]
    exact settled_choices_length p policy σ
  have hsum : ((settled.take (cutoff.val + 1)).map weight).sum =
      ∑ k ∈ positionsThrough cutoff,
        weight (settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩) :=
    sum_map_take_eq_positionsThrough settled hsettledLength cutoff weight
  rw [compiled_test_selection_prefix_identity p
    (fun x => if category (p x) then (1 : ℝ) else 0) policy σ cutoff]
  rw [hoperational]
  change (∑ k ∈ positionsThrough cutoff,
      if (touchTrace p policy σ).kind k = .test then
        (if category (p (σ ((touchTrace p policy σ).label k))) then 1 else 0)
      else 0) = (current.map weight).sum
  rw [hcurrent, hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hchoice := touchTrace_choice_eq_get p policy σ k
  have hget : settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩ =
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k) := by
    simpa [settled] using hchoice.symm
  change (if (touchTrace p policy σ).kind k = .test then
      (if category (p (σ ((touchTrace p policy σ).label k))) then 1 else 0)
    else 0) = weight _
  rw [hget]
  by_cases ht : (touchTrace p policy σ).kind k = .test <;>
    by_cases hc : category (p (σ ((touchTrace p policy σ).label k))) <;>
    simp [weight, placedProcessing, ht, hc]

/-- Literal blind work in an arbitrary nonempty operational prefix,
expressed through the complement of the predictable test selector. -/
theorem compiled_blind_work_prefix_sum_eq_operational {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1) :
    (∑ k ∈ positionsThrough cutoff,
        (1 - compiledTestSelector p policy k
            (TraceBijection.revealOrder (touchTrace p policy) σ)) *
          p (TraceBijection.revealOrder (touchTrace p policy) σ k)) =
      ObservedOnline.blindWork
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript := by
  let current := touchChoices
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript
  let settled := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  let weight : Fin n × TraceBijection.TouchKind → ℝ := fun choice =>
    if choice.2 = .blind then (placedProcessing p σ) choice.1 else 0
  have hmatch := (ObservedOnline.run_historyInvariant
    (placedProcessing p σ) policy.strategy fuel).revealsMatch
  have hoperational := blindWork_eq_touchChoices_sum
    (placedProcessing p σ)
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript hmatch
  have hcurrent : current = settled.take (cutoff.val + 1) := by
    dsimp [current, settled]
    rw [run_touchChoices_eq_settled_take (placedProcessing p σ)
      policy.strategy hfuel, hlength]
    rfl
  have hsettledLength : settled.length = n := by
    dsimp [settled]
    exact settled_choices_length p policy σ
  have hsum : ((settled.take (cutoff.val + 1)).map weight).sum =
      ∑ k ∈ positionsThrough cutoff,
        weight (settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩) :=
    sum_map_take_eq_positionsThrough settled hsettledLength cutoff weight
  rw [compiled_blind_selection_prefix_identity]
  rw [hoperational]
  change (∑ k ∈ positionsThrough cutoff,
      if (touchTrace p policy σ).kind k = .blind then
        p (σ ((touchTrace p policy σ).label k)) else 0) =
      (current.map weight).sum
  rw [hcurrent, hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hchoice := touchTrace_choice_eq_get p policy σ k
  have hget : settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩ =
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k) := by
    simpa [settled] using hchoice.symm
  change (if (touchTrace p policy σ).kind k = .blind then
      p (σ ((touchTrace p policy σ).label k)) else 0) = weight _
  rw [hget]
  by_cases hb : (touchTrace p policy σ).kind k = .blind <;>
    simp [weight, placedProcessing, hb]

/-- Literal blind-job count in an arbitrary nonempty operational prefix. -/
theorem compiled_blind_count_prefix_sum_eq_operational {n : ℕ}
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : Placement n) {fuel : ℕ}
    (hfuel : fuel ≤ 2 * n + 1) (cutoff : Fin n)
    (hlength :
      (touchChoices
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
          cutoff.val + 1) :
    (∑ k ∈ positionsThrough cutoff,
        (1 - compiledTestSelector p policy k
          (TraceBijection.revealOrder (touchTrace p policy) σ))) =
      ObservedOnline.blindCount
        (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript := by
  have hprefix := compiled_blind_selection_prefix_identity p
    (fun _ => (1 : ℝ)) policy σ cutoff
  have hprefix' :
      (∑ k ∈ positionsThrough cutoff,
        (1 - compiledTestSelector p policy k
          (TraceBijection.revealOrder (touchTrace p policy) σ))) =
        ∑ k ∈ positionsThrough cutoff,
          if (touchTrace p policy σ).kind k = .blind then 1 else 0 := by
    simpa using hprefix
  rw [hprefix']
  have hcurrent := run_touchChoices_eq_settled_take
    (placedProcessing p σ) policy.strategy hfuel
  let current := touchChoices
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript
  let settled := touchChoices
    (settledRun p policy.strategy σ).config.transcript
  let weight : Fin n × TraceBijection.TouchKind → ℝ := fun choice =>
    if choice.2 = .blind then 1 else 0
  have hcurrent' : current = settled.take (cutoff.val + 1) := by
    dsimp [current, settled]
    rw [hcurrent, hlength]
    rfl
  have hsettledLength : settled.length = n := by
    dsimp [settled]
    exact settled_choices_length p policy σ
  have hsum : ((settled.take (cutoff.val + 1)).map weight).sum =
      ∑ k ∈ positionsThrough cutoff,
        weight (settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩) :=
    sum_map_take_eq_positionsThrough settled hsettledLength cutoff weight
  have hoperational := blindCount_eq_touchChoices_sum
    (ObservedOnline.run (placedProcessing p σ) policy.strategy fuel).config.transcript
  rw [hoperational]
  change (∑ k ∈ positionsThrough cutoff,
      if (touchTrace p policy σ).kind k = .blind then 1 else 0) =
    (current.map weight).sum
  rw [hcurrent', hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hchoice := touchTrace_choice_eq_get p policy σ k
  have hget : settled.get ⟨k.val, by simpa [hsettledLength] using k.isLt⟩ =
      ((touchTrace p policy σ).label k,
        (touchTrace p policy σ).kind k) := by
    simpa [settled] using hchoice.symm
  rw [hget]

/-- Direct operational-policy wrapper around the existing predictable-urn
selected-count theorem.  The probability on the left is over original hidden
placements; trace bijectivity reindexes it to the canonical reveal
permutation used by the urn lemma. -/
theorem adaptivePolicy_selected_count_probability_le {n : ℕ}
    (p value : Fin n → ℝ) (policy : CompletePolicy p)
    (hvalue0 : ∀ i, 0 ≤ value i) (hvalue1 : ∀ i, value i ≤ 1)
    {populationMean e r suffixFailure : ℝ}
    (he : 0 < e) (hr : 0 ≤ r)
    (hSuffix :
      Randomized.uniformProbability (fun reveal ↦ ∃ j,
        r < |permutationSuffixMean value reveal j - populationMean|) ≤
        suffixFailure) :
    Randomized.uniformProbability (fun σ ↦
      e + r * n <
        |(∑ j, compiledTestSelector p policy j
              (TraceBijection.revealOrder (touchTrace p policy) σ) *
              value (TraceBijection.revealOrder (touchTrace p policy) σ j)) -
          populationMean *
            ∑ j, compiledTestSelector p policy j
              (TraceBijection.revealOrder (touchTrace p policy) σ)|) ≤
      n / e ^ 2 + suffixFailure := by
  classical
  let select := compiledTestSelector p policy
  let bad : Equiv.Perm (Fin n) → Prop := fun reveal ↦
    e + r * n <
      |(∑ j, select j reveal * value (reveal j)) -
        populationMean * ∑ j, select j reveal|
  have hbound : Randomized.uniformProbability bad ≤
      n / e ^ 2 + suffixFailure := by
    apply predictable_selected_count_probability_le value select
      (compiledTestSelector_predictable p policy)
      hvalue0 hvalue1
    · intro j reveal
      exact TraceBijection.compiledTestSelector_nonneg p (touchTrace p policy)
        (touchTrace_causal p policy) j reveal
    · intro j reveal
      exact TraceBijection.compiledTestSelector_le_one p (touchTrace p policy)
        (touchTrace_causal p policy) j reveal
    · exact he
    · exact hr
    · exact hSuffix
  calc
    Randomized.uniformProbability (fun σ ↦
        e + r * n <
          |(∑ j, compiledTestSelector p policy j
                (TraceBijection.revealOrder (touchTrace p policy) σ) *
                value (TraceBijection.revealOrder (touchTrace p policy) σ j)) -
            populationMean *
              ∑ j, compiledTestSelector p policy j
                (TraceBijection.revealOrder (touchTrace p policy) σ)|) =
        Randomized.uniformProbability bad := by
      unfold Randomized.uniformProbability
      simpa [bad, select, Function.comp_def] using
        TraceBijection.uniformAverage_revealOrder p (touchTrace p policy)
          (touchTrace_causal p policy)
          (fun reveal ↦ if bad reveal then (1 : ℝ) else 0)
    _ ≤ n / e ^ 2 + suffixFailure := hbound

end

end ObservedTrace
end RandomizedOptional
end SchedulingPaper
