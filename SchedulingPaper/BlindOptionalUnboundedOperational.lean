import SchedulingPaper.BlindOptionalUnbounded
import SchedulingPaper.RandomizedOptionalObservedTrace
import SchedulingPaper.RandomizedOptionalCompletionInvariant
import Mathlib.Tactic

/-!
# Operational one-long-job lower bound for unbounded blind execution

This file closes the operational bridge in the unbounded blind-execution
argument.  It extracts the all-zero first-touch permutation from the literal
transcript, proves that its test area is paid by the literal completion cost,
and uses lockstep causality to show that a label first touched blindly still
has the same rank when that one label is changed to a long job.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace UnboundedOperational

open Randomized
open Unbounded
open ObservedOnline
open ObservedTrace
open TraceBijection

noncomputable section

def zeroProcessing (n : ℕ) : Fin n → ℝ := fun _ => 0

def oneLongProcessing (H : ℝ) (label : Fin n) : Fin n → ℝ :=
  fun job => if job = label then H else 0

def CompletesAllNonnegative {n : ℕ} (strategy : Strategy n) : Prop :=
  ∀ processing : Fin n → ℝ, (∀ job, 0 ≤ processing job) →
    ∀ job, (run processing strategy (2 * n + 1)).config.jobs job = .done

def settledCost {n : ℕ} (processing : Fin n → ℝ)
    (strategy : Strategy n) : ℝ :=
  completionCost processing
    (run processing strategy (2 * n + 1)).config.transcript

def choiceTestArea {n : ℕ} :
    List (Fin n × TouchKind) → ℝ
  | [] => 0
  | choice :: rest =>
      (if choice.2 = .test then (rest.length + 1 : ℕ) else 0) +
        choiceTestArea rest

@[simp] theorem revealedResults_append {n : ℕ}
    (left right : Transcript n) :
    ObservedOnline.Transcript.revealedResults (left ++ right) =
      ObservedOnline.Transcript.revealedResults left ++
        ObservedOnline.Transcript.revealedResults right := by
  induction left with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;>
        simp [ObservedOnline.Transcript.revealedResults, ih]

theorem choiceTestArea_eq_rank_sum {n : ℕ}
    (choices : List (Fin n × TouchKind)) :
    choiceTestArea choices =
      ∑ rank : Fin choices.length,
        if (choices.get rank).2 = .test then
          rankWeight choices.length rank else 0 := by
  induction choices with
  | nil => simp [choiceTestArea]
  | cons choice rest ih =>
      change choiceTestArea (choice :: rest) =
        ∑ rank : Fin (rest.length + 1),
          if ((choice :: rest).get rank).2 = .test then
            rankWeight (rest.length + 1) rank else 0
      rw [Fin.sum_univ_succ]
      simp [choiceTestArea, ih, rankWeight_succ_zero,
        rankWeight_succ_succ]

def traceTested {n : ℕ} (trace : TouchTrace n) (rank : Fin n) : Bool :=
  decide (trace.kind rank = .test)

theorem testedArea_traceTested {n : ℕ} (trace : TouchTrace n) :
    testedArea (traceTested trace) =
      ∑ rank, if trace.kind rank = .test then rankWeight n rank else 0 := by
  unfold testedArea traceTested
  apply Finset.sum_congr rfl
  intro rank _
  by_cases hkind : trace.kind rank = .test <;> simp [hkind]

theorem choiceTestArea_touchTrace {n : ℕ} (p : Fin n → ℝ)
    (policy : CompletePolicy p) (placement : ObservedTrace.Placement n) :
    choiceTestArea
        (touchChoices (settledRun p policy.strategy placement).config.transcript) =
      testedArea (traceTested (touchTrace p policy placement)) := by
  rw [← touchTrace_choices_ofFn p policy placement,
    choiceTestArea_eq_rank_sum, testedArea_traceTested]
  let f : Fin n → Fin n × TouchKind := fun rank =>
    ((touchTrace p policy placement).label rank,
      (touchTrace p policy placement).kind rank)
  change (∑ rank : Fin (List.ofFn f).length,
      if ((List.ofFn f).get rank).2 = .test then
        rankWeight (List.ofFn f).length rank else 0) =
    ∑ rank : Fin n,
      if (touchTrace p policy placement).kind rank = .test then
        rankWeight n rank else 0
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := f)))
  intro rank
  rw [List.get_ofFn]
  dsimp [f]
  unfold rankWeight
  simp only [List.length_ofFn]
  let index : Fin n := ⟨rank.val, by
    simpa using rank.isLt⟩
  have hindex : index = Fin.cast (List.length_ofFn (f := f)) rank := by
    apply Fin.ext
    rfl
  change (if (touchTrace p policy placement).kind index = .test then
      (n : ℝ) - rank.val else 0) =
    if (touchTrace p policy placement).kind
        (Fin.cast (List.length_ofFn (f := f)) rank) = .test then
      (n : ℝ) - (Fin.cast (List.length_ofFn (f := f)) rank).val else 0
  rw [hindex]
  rfl

theorem completionCount_zero_eq_touchChoices_length
    {n : ℕ} (transcript : Transcript n)
    (hzero : ∀ job p,
      (job, p) ∈ ObservedOnline.Transcript.revealedResults transcript → p = 0) :
    completionCount (zeroProcessing n) transcript =
      (touchChoices transcript).length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hrest : ∀ job p,
          (job, p) ∈ ObservedOnline.Transcript.revealedResults rest → p = 0 := by
        intro job p hmem
        apply hzero job p
        cases observation <;> simp [Transcript.revealedResults, hmem]
      cases observation with
      | testResult job p =>
          have hp : p = 0 := hzero job p (by
            simp [Transcript.revealedResults])
          simp [completionCount, Observation.completionLabel,
            zeroProcessing, touchChoices, observationTouchChoice?, hp, ih hrest]
          omega
      | processed job =>
          simp [completionCount, Observation.completionLabel,
            zeroProcessing, touchChoices, observationTouchChoice?, ih hrest]
      | blindCompleted job p =>
          simp [completionCount, Observation.completionLabel,
            zeroProcessing, touchChoices, observationTouchChoice?, ih hrest]
          omega

theorem zero_completionCost_eq_choiceTestArea
    {n : ℕ} (transcript : Transcript n)
    (hzero : ∀ job p,
      (job, p) ∈ ObservedOnline.Transcript.revealedResults transcript → p = 0) :
    completionCost (zeroProcessing n) transcript =
      choiceTestArea (touchChoices transcript) := by
  rw [completionCost_eq_suffixWeightedDuration]
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      have hrest : ∀ job p,
          (job, p) ∈ ObservedOnline.Transcript.revealedResults rest → p = 0 := by
        intro job p hmem
        apply hzero job p
        cases observation <;> simp [Transcript.revealedResults, hmem]
      cases observation with
      | testResult job p =>
          have hp : p = 0 := hzero job p (by
            simp [Transcript.revealedResults])
          simp only [suffixWeightedDuration, Observation.actualDuration,
            touchChoices, observationTouchChoice?, choiceTestArea]
          rw [completionCount_zero_eq_touchChoices_length _ hzero, ih hrest]
          simp [hp, touchChoices, observationTouchChoice?]
      | processed job =>
          simp [suffixWeightedDuration, Observation.actualDuration,
            zeroProcessing, touchChoices, observationTouchChoice?,
            choiceTestArea, ih hrest]
      | blindCompleted job p =>
          have hp : p = 0 := hzero job p (by
            simp [Transcript.revealedResults])
          simp [suffixWeightedDuration, Observation.actualDuration,
            zeroProcessing, touchChoices, observationTouchChoice?,
            choiceTestArea, hp, ih hrest]

theorem mem_revealedResults_of_mem_blind {n : ℕ}
    {transcript : Transcript n} {job : Fin n} {p : ℝ}
    (hmem : Observation.blindCompleted job p ∈ transcript) :
    (job, p) ∈ ObservedOnline.Transcript.revealedResults transcript := by
  induction transcript with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp [ObservedOnline.Transcript.revealedResults]
      · cases head <;>
          simp [ObservedOnline.Transcript.revealedResults, ih htail]

theorem actualDuration_nonneg_of_mem {n : ℕ} {processing : Fin n → ℝ}
    (hprocessing : ∀ job, 0 ≤ processing job) {transcript : Transcript n}
    (hmatch : AllRevealsMatch processing transcript)
    {observation : Observation n} (hmem : observation ∈ transcript) :
    0 ≤ observation.actualDuration processing := by
  cases observation with
  | testResult job p => simp [Observation.actualDuration]
  | processed job => simp [Observation.actualDuration, hprocessing]
  | blindCompleted job p =>
      have hp : p = processing job :=
        hmatch job p (mem_revealedResults_of_mem_blind hmem)
      simp [Observation.actualDuration, hp, hprocessing]

theorem suffixWeightedDuration_nonneg {n : ℕ}
    {processing : Fin n → ℝ} (hprocessing : ∀ job, 0 ≤ processing job)
    (transcript : Transcript n) (hmatch : AllRevealsMatch processing transcript) :
    0 ≤ suffixWeightedDuration processing transcript := by
  induction transcript with
  | nil => simp [suffixWeightedDuration]
  | cons observation rest ih =>
      have hrest : AllRevealsMatch processing rest := by
        intro job p hmem
        apply hmatch job p
        cases observation <;>
          simp [ObservedOnline.Transcript.revealedResults, hmem]
      simp only [suffixWeightedDuration]
      exact add_nonneg
        (mul_nonneg
          (actualDuration_nonneg_of_mem hprocessing hmatch (by simp))
          (by positivity)) (ih hrest)

theorem suffixWeightedDuration_suffix_le {n : ℕ}
    {processing : Fin n → ℝ} (hprocessing : ∀ job, 0 ≤ processing job)
    (pre suffix : Transcript n)
    (hmatch : AllRevealsMatch processing (pre ++ suffix)) :
    suffixWeightedDuration processing suffix ≤
      suffixWeightedDuration processing (pre ++ suffix) := by
  induction pre with
  | nil => simp
  | cons observation rest ih =>
      have hrest : AllRevealsMatch processing (rest ++ suffix) := by
        intro job p hmem
        apply hmatch job p
        cases observation with
        | testResult touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
        | processed touched =>
            exact hmem
        | blindCompleted touched value =>
            exact List.mem_cons_of_mem (touched, value) hmem
      simp only [List.cons_append, suffixWeightedDuration]
      have hterm : 0 ≤ observation.actualDuration processing *
          completionCount processing (observation :: (rest ++ suffix)) :=
        mul_nonneg
          (actualDuration_nonneg_of_mem hprocessing hmatch (by simp))
          (by positivity)
      linarith [ih hrest]

theorem settledCost_nonneg {n : ℕ} {processing : Fin n → ℝ}
    (hprocessing : ∀ job, 0 ≤ processing job) (strategy : Strategy n) :
    0 ≤ settledCost processing strategy := by
  unfold settledCost
  rw [completionCost_eq_suffixWeightedDuration]
  exact suffixWeightedDuration_nonneg hprocessing _
    (run_historyInvariant processing strategy (2 * n + 1)).revealsMatch

def asCompletePolicy {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ job, 0 ≤ p job) (strategy : Strategy n)
    (hcomplete : CompletesAllNonnegative strategy) : CompletePolicy p where
  strategy := strategy
  completes := by
    intro placement job
    exact hcomplete (placedProcessing p placement)
      (fun label => hp (placement label)) job

theorem zero_testedArea_eq_settledCost {n : ℕ}
    (strategy : Strategy n) (hcomplete : CompletesAllNonnegative strategy) :
    let policy := asCompletePolicy (zeroProcessing n) (by simp [zeroProcessing])
      strategy hcomplete
    let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
    testedArea (traceTested (touchTrace (zeroProcessing n) policy placement)) =
      settledCost (zeroProcessing n) strategy := by
  dsimp
  let policy := asCompletePolicy (zeroProcessing n) (by simp [zeroProcessing])
    strategy hcomplete
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let transcript :=
    (settledRun (zeroProcessing n) policy.strategy placement).config.transcript
  have hmatch := (run_historyInvariant (zeroProcessing n) strategy
    (2 * n + 1)).revealsMatch
  have hzero : ∀ job p,
      (job, p) ∈ ObservedOnline.Transcript.revealedResults transcript → p = 0 := by
    intro job p hmem
    have hp := hmatch job p (by
      simpa [transcript, settledRun, placedProcessing, policy, placement,
        zeroProcessing] using hmem)
    simpa [zeroProcessing] using hp
  calc
    testedArea (traceTested (touchTrace (zeroProcessing n) policy placement)) =
        choiceTestArea (touchChoices transcript) :=
      (choiceTestArea_touchTrace (zeroProcessing n) policy placement).symm
    _ = completionCost (zeroProcessing n) transcript :=
      (zero_completionCost_eq_choiceTestArea transcript hzero).symm
    _ = settledCost (zeroProcessing n) strategy := by
      rfl

/-- Causality stated directly for two fuel-truncated operational runs. -/
theorem run_touchChoices_causal {n : ℕ}
    (processing processing' : Fin n → ℝ) (strategy : Strategy n)
    (fuel k : ℕ)
    (hvalues :
      (touchValues (run processing strategy fuel).config.transcript).take k =
        (touchValues (run processing' strategy fuel).config.transcript).take k) :
    (touchChoices (run processing strategy fuel).config.transcript).take (k + 1) =
      (touchChoices (run processing' strategy fuel).config.transcript).take
        (k + 1) := by
  rw [run_transcript_eq_runWord, run_transcript_eq_runWord] at hvalues ⊢
  exact runWord_touchChoices_causal processing processing' strategy fuel k
    (Config.initial n) hvalues

/-- Before its first touch, changing one label from zero to `H` is
unobservable.  Hence that label has the same first-touch rank and kind in
the all-zero and one-long runs. -/
theorem zero_oneLong_same_rank_kind {n : ℕ} (strategy : Strategy n)
    (hcomplete : CompletesAllNonnegative strategy) {H : ℝ} (hH : 0 ≤ H)
    (label : Fin n) :
    let zeroPolicy := asCompletePolicy (zeroProcessing n)
      (by simp [zeroProcessing]) strategy hcomplete
    let longPolicy := asCompletePolicy (oneLongProcessing H label)
      (by
        intro job
        by_cases h : job = label <;> simp [oneLongProcessing, h, hH])
      strategy hcomplete
    let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
    let zeroTrace := touchTrace (zeroProcessing n) zeroPolicy placement
    let longTrace := touchTrace (oneLongProcessing H label) longPolicy placement
    zeroTrace.label.symm label = longTrace.label.symm label ∧
      zeroTrace.kind (zeroTrace.label.symm label) =
        longTrace.kind (longTrace.label.symm label) := by
  dsimp
  let zeroPolicy := asCompletePolicy (zeroProcessing n)
    (by simp [zeroProcessing]) strategy hcomplete
  let longPolicy := asCompletePolicy (oneLongProcessing H label)
    (by
      intro job
      by_cases h : job = label <;> simp [oneLongProcessing, h, hH])
    strategy hcomplete
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let zeroTraceFn := touchTrace (zeroProcessing n) zeroPolicy
  let longTraceFn := touchTrace (oneLongProcessing H label) longPolicy
  let zeroTrace := zeroTraceFn placement
  let longTrace := longTraceFn placement
  let zeroRank := zeroTrace.label.symm label
  let longRank := longTrace.label.symm label
  let kNat := min zeroRank.val longRank.val
  have hklt : kNat < n := lt_of_le_of_lt (min_le_left _ _) zeroRank.isLt
  let k : Fin n := ⟨kNat, hklt⟩
  have hvalues :
      (touchValues
        (settledRun (zeroProcessing n) zeroPolicy.strategy placement).config.transcript).take
          kNat =
      (touchValues
        (settledRun (oneLongProcessing H label) longPolicy.strategy placement).config.transcript).take
          kNat := by
    rw [settled_touchValues_eq_ofFn (zeroProcessing n) zeroPolicy placement,
      settled_touchValues_eq_ofFn (oneLongProcessing H label) longPolicy placement]
    apply take_ofFn_eq_of_prefix
    intro rank hrank
    have hrankLong : rank.val < longRank.val :=
      lt_of_lt_of_le hrank (min_le_right _ _)
    have hnotLabel : revealOrder longTraceFn placement rank ≠ label := by
      intro heq
      have heq' : longTrace.label rank = label := by
        simpa [longTrace, longTraceFn, placement, revealOrder] using heq
      have hrankEq : rank = longRank := by
        apply longTrace.label.injective
        simpa [longRank] using heq'
      rw [hrankEq] at hrankLong
      exact (Nat.lt_irrefl _ hrankLong)
    have hnotLabel' :
        revealOrder (touchTrace (oneLongProcessing H label) longPolicy)
          placement rank ≠ label := by
      simpa [longTraceFn] using hnotLabel
    simp [zeroProcessing, oneLongProcessing, hnotLabel']
  have hchoices :
      (touchChoices
        (settledRun (zeroProcessing n) zeroPolicy.strategy placement).config.transcript).take
          (kNat + 1) =
      (touchChoices
        (settledRun (oneLongProcessing H label) longPolicy.strategy placement).config.transcript).take
          (kNat + 1) := by
    simpa [settledRun, placedProcessing, zeroPolicy, longPolicy, placement,
      zeroProcessing] using
      run_touchChoices_causal (zeroProcessing n) (oneLongProcessing H label)
        strategy (2 * n + 1) kNat (by
          simpa [settledRun, placedProcessing, zeroPolicy, longPolicy, placement,
            zeroProcessing] using hvalues)
  let zeroChoices :=
    touchChoices
      (settledRun (zeroProcessing n) zeroPolicy.strategy placement).config.transcript
  let longChoices :=
    touchChoices
      (settledRun (oneLongProcessing H label) longPolicy.strategy placement).config.transcript
  have hzeroLength : zeroChoices.length = n := by
    have htrace := touchTrace_choices_ofFn (zeroProcessing n) zeroPolicy placement
    dsimp [zeroChoices]
    rw [← htrace]
    simp
  have hlongLength : longChoices.length = n := by
    have htrace := touchTrace_choices_ofFn
      (oneLongProcessing H label) longPolicy placement
    dsimp [longChoices]
    rw [← htrace]
    simp
  have hget : zeroChoices.get ⟨kNat, by simpa [hzeroLength] using hklt⟩ =
      longChoices.get ⟨kNat, by simpa [hlongLength] using hklt⟩ := by
    apply get_eq_of_take_succ_eq
    simpa [zeroChoices, longChoices] using hchoices
  have hzeroChoice := touchTrace_choice_eq_get
    (zeroProcessing n) zeroPolicy placement k
  have hlongChoice := touchTrace_choice_eq_get
    (oneLongProcessing H label) longPolicy placement k
  have hpair : (zeroTrace.label k, zeroTrace.kind k) =
      (longTrace.label k, longTrace.kind k) := by
    rw [hzeroChoice, hlongChoice]
    simpa [zeroChoices, longChoices, k] using hget
  have hpairComponents :
      zeroTrace.label k = longTrace.label k ∧
        zeroTrace.kind k = longTrace.kind k :=
    Prod.mk.inj hpair
  have hpairLabel := hpairComponents.1
  have hpairKind := hpairComponents.2
  have hranks : zeroRank = longRank := by
    rcases le_total zeroRank.val longRank.val with hle | hle
    · have hkzero : k = zeroRank := by
        apply Fin.ext
        exact min_eq_left hle
      have hlongLabel : longTrace.label k = label := by
        rw [← hpairLabel, hkzero]
        simp [zeroRank]
      have hklong : k = longRank := by
        apply longTrace.label.injective
        simpa [longRank] using hlongLabel
      exact hkzero.symm.trans hklong
    · have hklong : k = longRank := by
        apply Fin.ext
        exact min_eq_right hle
      have hzeroLabel : zeroTrace.label k = label := by
        rw [hpairLabel, hklong]
        simp [longRank]
      have hkzero : k = zeroRank := by
        apply zeroTrace.label.injective
        simpa [zeroRank] using hzeroLabel
      exact hkzero.symm.trans hklong
  refine ⟨hranks, ?_⟩
  change zeroTrace.kind zeroRank = longTrace.kind longRank
  have hkind := hpairKind
  have hkzero : k = zeroRank := by
    apply Fin.ext
    dsimp [k, kNat]
    rw [hranks]
    simp
  rw [hkzero] at hkind
  simpa [hranks] using hkind

theorem exists_blind_split_of_touchChoices_get {n : ℕ}
    (transcript : Transcript n) (k : ℕ)
    (hk : k < (touchChoices transcript).length) (label : Fin n)
    (hget : (touchChoices transcript).get ⟨k, hk⟩ = (label, .blind)) :
    ∃ pre post p,
      transcript = pre ++ .blindCompleted label p :: post ∧
        (touchChoices pre).length = k := by
  induction transcript generalizing k with
  | nil => simp [touchChoices] at hk
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          cases k with
          | zero =>
              simp [touchChoices, observationTouchChoice?] at hget
          | succ k =>
              have hkrest : k < (touchChoices rest).length := by
                simpa [touchChoices, observationTouchChoice?] using hk
              have hgetRest :
                  (touchChoices rest).get ⟨k, hkrest⟩ = (label, .blind) := by
                simpa [touchChoices, observationTouchChoice?] using hget
              obtain ⟨pre, post, value, hsplit, hlength⟩ :=
                ih k hkrest hgetRest
              refine ⟨.testResult job p :: pre, post, value, ?_, ?_⟩
              · simp [hsplit]
              · simp [touchChoices, observationTouchChoice?, hlength]
      | processed job =>
          have hkrest : k < (touchChoices rest).length := by
            simpa [touchChoices, observationTouchChoice?] using hk
          have hgetRest :
              (touchChoices rest).get ⟨k, hkrest⟩ = (label, .blind) := by
            simpa [touchChoices, observationTouchChoice?] using hget
          obtain ⟨pre, post, value, hsplit, hlength⟩ :=
            ih k hkrest hgetRest
          refine ⟨.processed job :: pre, post, value, ?_, ?_⟩
          · simp [hsplit]
          · simpa [touchChoices, observationTouchChoice?] using hlength
      | blindCompleted job p =>
          cases k with
          | zero =>
              have hlabel : job = label := by
                simpa [touchChoices, observationTouchChoice?] using
                  congrArg Prod.fst hget
              subst job
              exact ⟨[], rest, p, by simp, by simp [touchChoices]⟩
          | succ k =>
              have hkrest : k < (touchChoices rest).length := by
                simpa [touchChoices, observationTouchChoice?] using hk
              have hgetRest :
                  (touchChoices rest).get ⟨k, hkrest⟩ = (label, .blind) := by
                simpa [touchChoices, observationTouchChoice?] using hget
              obtain ⟨pre, post, value, hsplit, hlength⟩ :=
                ih k hkrest hgetRest
              refine ⟨.blindCompleted job p :: pre, post, value, ?_, ?_⟩
              · simp [hsplit]
              · simp [touchChoices, observationTouchChoice?, hlength]

/-- A literal blind first touch of the exceptional label at rank `rank`
pays `H` times the number of jobs not yet first-touched. -/
theorem oneLong_settledCost_ge_blind_rank {n : ℕ}
    (strategy : Strategy n) (hcomplete : CompletesAllNonnegative strategy)
    {H : ℝ} (hH : 0 ≤ H) (label rank : Fin n) :
    let policy := asCompletePolicy (oneLongProcessing H label)
      (by
        intro job
        by_cases h : job = label <;> simp [oneLongProcessing, h, hH])
      strategy hcomplete
    let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
    let trace := touchTrace (oneLongProcessing H label) policy placement
    trace.label rank = label → trace.kind rank = .blind →
      H * rankWeight n rank ≤
        settledCost (oneLongProcessing H label) strategy := by
  dsimp
  let processing := oneLongProcessing H label
  have hprocessing : ∀ job, 0 ≤ processing job := by
    intro job
    by_cases h : job = label <;> simp [processing, oneLongProcessing, h, hH]
  let policy := asCompletePolicy processing hprocessing strategy hcomplete
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let trace := touchTrace processing policy placement
  intro hlabel hkind
  let full := (settledRun processing policy.strategy placement).config.transcript
  let choices := touchChoices full
  have hchoicesLength : choices.length = n := by
    have htrace := touchTrace_choices_ofFn processing policy placement
    dsimp [choices, full]
    rw [← htrace]
    simp
  have hchoice := touchTrace_choice_eq_get processing policy placement rank
  have hlabel' : trace.label rank = label := by
    simpa [trace, processing, policy, placement] using hlabel
  have hkind' : trace.kind rank = .blind := by
    simpa [trace, processing, policy, placement] using hkind
  have hget : choices.get ⟨rank.val, by simpa [hchoicesLength] using rank.isLt⟩ =
      (label, .blind) := by
    have hchoice' : (trace.label rank, trace.kind rank) =
        choices.get ⟨rank.val, by simpa [hchoicesLength] using rank.isLt⟩ := by
      simpa [trace, choices, full] using hchoice
    rw [← hchoice', hlabel', hkind']
  obtain ⟨pre, post, value, hsplit, htouchLength⟩ :=
    exists_blind_split_of_touchChoices_get full rank.val
      (by
        change rank.val < choices.length
        rw [hchoicesLength]
        exact rank.isLt) label hget
  have hmatch : AllRevealsMatch processing full := by
    simpa [full, settledRun, placedProcessing, policy, placement, processing] using
      (run_historyInvariant processing strategy (2 * n + 1)).revealsMatch
  have hvalue : value = H := by
    have htruth := hmatch label value (by
      apply mem_revealedResults_of_mem_blind
      rw [hsplit]
      simp)
    simpa [processing, oneLongProcessing] using htruth
  have hprePrefix : pre <+: full := by
    rw [hsplit]
    exact List.prefix_append _ _
  have hpreLength : pre.length ≤ full.length := hprePrefix.length_le
  have hfullLength : full.length ≤ 2 * n + 1 := by
    dsimp [full, settledRun]
    rw [run_transcript_eq_runWord]
    exact runWord_length_le_fuel _ _ _ _
  have hfuel : pre.length ≤ 2 * n + 1 := hpreLength.trans hfullLength
  have hpreTake : pre = full.take pre.length := list_eq_take_of_prefix hprePrefix
  have hrunPre :
      (run processing strategy pre.length).config.transcript = pre := by
    have hrunTake := run_transcript_eq_take_of_le_length processing strategy
      hfuel hpreLength
    simpa [full, settledRun, placedProcessing, policy, placement] using
      hrunTake.trans hpreTake.symm
  have hpreCount : completionCount processing pre ≤ rank.val := by
    have hcount := run_completionCount_le_startedLabels_length
      processing strategy pre.length
    rw [hrunPre] at hcount
    have hstarted : pre.startedLabels.length = rank.val := by
      rw [← touchChoices_map_fst, List.length_map, htouchLength]
    simpa [hstarted] using hcount
  have hfullCount : completionCount processing full = n := by
    have hdone := hcomplete processing hprocessing
    have hcount := run_completionCount_eq_n_of_done processing strategy
      (2 * n + 1) hdone
    simpa [full, settledRun, placedProcessing, policy, placement] using hcount
  let suffix : Transcript n := .blindCompleted label value :: post
  have hcountSplit : completionCount processing full =
      completionCount processing pre + completionCount processing suffix := by
    rw [hsplit, completionCount_append]
  have hsuffixCount : n - rank.val ≤ completionCount processing suffix := by
    omega
  have hsuffixMatch : AllRevealsMatch processing suffix := by
    intro job p hmem
    apply hmatch job p
    rw [hsplit, revealedResults_append]
    apply List.mem_append_right
      (ObservedOnline.Transcript.revealedResults pre)
    simpa [suffix] using hmem
  have hpostMatch : AllRevealsMatch processing post := by
    intro job p hmem
    apply hsuffixMatch job p
    simp [suffix, ObservedOnline.Transcript.revealedResults, hmem]
  have hpostNonneg : 0 ≤ suffixWeightedDuration processing post :=
    suffixWeightedDuration_nonneg hprocessing post hpostMatch
  have hsuffixLower : H * rankWeight n rank ≤
      suffixWeightedDuration processing suffix := by
    have hsuffixCountR : ((n - rank.val : ℕ) : ℝ) ≤
        completionCount processing suffix := by exact_mod_cast hsuffixCount
    have hweighted := mul_le_mul_of_nonneg_left hsuffixCountR hH
    have hcastSub : (((n - rank.val : ℕ) : ℝ)) =
        (n : ℝ) - rank.val := by
      rw [Nat.cast_sub (Nat.le_of_lt rank.isLt)]
    unfold rankWeight
    calc
      H * ((n : ℝ) - rank.val) = H * ((n - rank.val : ℕ) : ℝ) := by
        rw [hcastSub]
      _ ≤ H * (completionCount processing suffix : ℝ) := hweighted
      _ ≤ suffixWeightedDuration processing suffix := by
        dsimp [suffix]
        simp only [suffixWeightedDuration, Observation.actualDuration]
        rw [hvalue]
        exact le_add_of_nonneg_right hpostNonneg
  have hsuffixLe : suffixWeightedDuration processing suffix ≤
      suffixWeightedDuration processing full := by
    have hle := suffixWeightedDuration_suffix_le hprocessing pre suffix (by
      simpa [hsplit, suffix] using hmatch)
    simpa [hsplit, suffix] using hle
  calc
    H * rankWeight n rank ≤ suffixWeightedDuration processing suffix := hsuffixLower
    _ ≤ suffixWeightedDuration processing full := hsuffixLe
    _ = settledCost processing strategy := by
      rw [← completionCost_eq_suffixWeightedDuration]
      rfl

/-- The abstract exceptional-label charge is bounded pointwise by the
literal completion cost of the operational one-long-job run. -/
theorem exceptionalCharge_le_oneLong_settledCost {n : ℕ}
    (strategy : Strategy n) (hcomplete : CompletesAllNonnegative strategy)
    {H : ℝ} (hH : 0 ≤ H) (label : Fin n) :
    let zeroPolicy := asCompletePolicy (zeroProcessing n)
      (by simp [zeroProcessing]) strategy hcomplete
    let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
    let zeroTrace := touchTrace (zeroProcessing n) zeroPolicy placement
    exceptionalCharge zeroTrace.label (traceTested zeroTrace) H label ≤
      settledCost (oneLongProcessing H label) strategy := by
  dsimp
  let zeroPolicy := asCompletePolicy (zeroProcessing n)
    (by simp [zeroProcessing]) strategy hcomplete
  let longPolicy := asCompletePolicy (oneLongProcessing H label)
    (by
      intro job
      by_cases h : job = label <;> simp [oneLongProcessing, h, hH])
    strategy hcomplete
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let zeroTrace := touchTrace (zeroProcessing n) zeroPolicy placement
  let longTrace := touchTrace (oneLongProcessing H label) longPolicy placement
  let rank := zeroTrace.label.symm label
  change exceptionalCharge zeroTrace.label (traceTested zeroTrace) H label ≤
    settledCost (oneLongProcessing H label) strategy
  have hsame := zero_oneLong_same_rank_kind strategy hcomplete hH label
  have hsame' : rank = longTrace.label.symm label ∧
      zeroTrace.kind rank = longTrace.kind (longTrace.label.symm label) := by
    simpa [zeroPolicy, longPolicy, placement, zeroTrace, longTrace, rank] using hsame
  by_cases htest : zeroTrace.kind rank = .test
  · have hcharge :
        exceptionalCharge zeroTrace.label (traceTested zeroTrace) H label = 0 := by
      simp [exceptionalCharge, traceTested, rank, htest]
    rw [hcharge]
    exact settledCost_nonneg
      (by
        intro job
        by_cases h : job = label <;> simp [oneLongProcessing, h, hH])
      strategy
  · have hblind : zeroTrace.kind rank = .blind := by
      cases hkind : zeroTrace.kind rank with
      | test => exact (htest hkind).elim
      | blind => rfl
    have hlongLabel : longTrace.label rank = label := by
      rw [hsame'.1]
      simp
    have hlongKind : longTrace.kind rank = .blind := by
      rw [hsame'.1, ← hsame'.2, hblind]
    have hpaid := oneLong_settledCost_ge_blind_rank
      strategy hcomplete hH label rank
    have hpaid' : H * rankWeight n rank ≤
        settledCost (oneLongProcessing H label) strategy := by
      apply hpaid
      · simpa [longPolicy, placement, longTrace] using hlongLabel
      · simpa [longPolicy, placement, longTrace] using hlongKind
    have hcharge :
        exceptionalCharge zeroTrace.label (traceTested zeroTrace) H label =
          H * rankWeight n rank := by
      simp [exceptionalCharge, traceTested, rank, hblind]
    rw [hcharge]
    exact hpaid'

/-- Fully operational finite-scale impossibility theorem.  A randomized
online algorithm is represented by a finite uniform private seed.  The two
cost assumptions concern the literal transcript completion costs on the
all-zero input and on every one-`n²` input; no abstract trace or charging
hypothesis remains in the statement. -/
theorem no_finite_ratio_at_quadratic_scale_operational
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (strategy : Ω → Strategy n)
    (hcomplete : ∀ seed, CompletesAllNonnegative (strategy seed))
    (R η : ℝ) (hR : 0 ≤ R) (hη : η ≤ 1 / 8)
    (hnlarge : 8 * R + 1 < 3 * n)
    (hzeroCost :
      uniformAverage (fun seed ↦ settledCost (zeroProcessing n) (strategy seed)) ≤
        η * (n : ℝ) ^ 2)
    (hcompetitive : ∀ label,
      uniformAverage (fun seed ↦
          settledCost (oneLongProcessing ((n : ℝ) ^ 2) label) (strategy seed)) ≤
        R * (n : ℝ) ^ 2 + η * (n : ℝ) ^ 2) : False := by
  let zeroPolicy (seed : Ω) := asCompletePolicy (zeroProcessing n)
    (by simp [zeroProcessing]) (strategy seed) (hcomplete seed)
  let placement : ObservedTrace.Placement n := Equiv.refl (Fin n)
  let zeroTrace (seed : Ω) :=
    touchTrace (zeroProcessing n) (zeroPolicy seed) placement
  let order (seed : Ω) : Equiv.Perm (Fin n) := (zeroTrace seed).label
  let tested (seed : Ω) : Fin n → Bool := traceTested (zeroTrace seed)
  let zeroCost :=
    uniformAverage (fun seed ↦ settledCost (zeroProcessing n) (strategy seed))
  let longCost (label : Fin n) :=
    uniformAverage (fun seed ↦
      settledCost (oneLongProcessing ((n : ℝ) ^ 2) label) (strategy seed))
  apply Unbounded.no_finite_ratio_at_quadratic_scale hn order tested
    R η zeroCost longCost hR hη hnlarge
  · have hpoint : ∀ seed,
        testedArea (tested seed) =
          settledCost (zeroProcessing n) (strategy seed) := by
      intro seed
      simpa [tested, order, zeroTrace, zeroPolicy, placement] using
        zero_testedArea_eq_settledCost (strategy seed) (hcomplete seed)
    apply le_of_eq
    unfold zeroCost
    congr 1
    funext seed
    exact hpoint seed
  · exact hzeroCost
  · intro label
    unfold longCost
    apply uniformAverage_mono
    intro seed
    simpa [order, tested, zeroTrace, zeroPolicy, placement] using
      exceptionalCharge_le_oneLong_settledCost
        (strategy seed) (hcomplete seed) (sq_nonneg (n : ℝ)) label
  · exact hcompetitive

end

end UnboundedOperational
end RandomizedOptional
end SchedulingPaper
