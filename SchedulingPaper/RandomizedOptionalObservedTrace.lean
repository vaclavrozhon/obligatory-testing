import SchedulingPaper.RandomizedOptionalTraceBijection
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
