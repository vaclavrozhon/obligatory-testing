import SchedulingPaper.OfflineOptimal
import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Operational blind-optimization model

An action completes one previously untouched job either raw, in the public
time `u`, or as one contiguous optimized block of duration `1 + p`.  A raw
completion does not reveal `p`; an optimized completion reveals it only after
the block has finished.  This is the normal-form semantics used in the
blind-optimization section of the paper.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace Online

noncomputable section

inductive Mode where
  | raw
  | optimized
  deriving DecidableEq, Repr

structure Action (n : ℕ) where
  job : Fin n
  mode : Mode
  deriving DecidableEq

inductive Observation (n : ℕ) where
  | rawCompleted (job : Fin n)
  | optimizedCompleted (job : Fin n) (processing : ℝ)
  deriving DecidableEq

abbrev Transcript (n : ℕ) := List (Observation n)
abbrev Strategy (n : ℕ) := Transcript n → Option (Action n)

def Observation.job : Observation n → Fin n
  | .rawCompleted job => job
  | .optimizedCompleted job _ => job

def Observation.mode : Observation n → Mode
  | .rawCompleted _ => .raw
  | .optimizedCompleted _ _ => .optimized

def Observation.duration (u : ℝ) : Observation n → ℝ
  | .rawCompleted _ => u
  | .optimizedCompleted _ p => 1 + p

def Observation.processing? : Observation n → Option ℝ
  | .rawCompleted _ => none
  | .optimizedCompleted _ p => some p

structure Config (n : ℕ) where
  touched : Finset (Fin n)
  transcript : Transcript n

def Config.initial (n : ℕ) : Config n := ⟨∅, []⟩

def Config.step (processing : Fin n → ℝ) (config : Config n)
    (action : Action n) : Option (Config n) :=
  if action.job ∈ config.touched then none
  else
    let observation := match action.mode with
      | .raw => Observation.rawCompleted action.job
      | .optimized => Observation.optimizedCompleted action.job (processing action.job)
    some ⟨insert action.job config.touched,
      config.transcript ++ [observation]⟩

inductive StopReason where
  | strategyStopped
  | repeatedJob
  | outOfFuel
  deriving DecidableEq, Repr

structure RunResult (n : ℕ) where
  config : Config n
  reason : StopReason

def runFuel (processing : Fin n → ℝ) (strategy : Strategy n) :
    ℕ → Config n → RunResult n
  | 0, config => ⟨config, .outOfFuel⟩
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => ⟨config, .strategyStopped⟩
      | some action =>
          match config.step processing action with
          | none => ⟨config, .repeatedJob⟩
          | some next => runFuel processing strategy fuel next

def run (processing : Fin n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    RunResult n := runFuel processing strategy fuel (Config.initial n)

def completionCost (u : ℝ) (transcript : Transcript n) : ℝ :=
  prefixCost (transcript.map (Observation.duration u))

def runCost (u : ℝ) (processing : Fin n → ℝ)
    (strategy : Strategy n) (fuel : ℕ) : ℝ :=
  completionCost u (run processing strategy fuel).config.transcript

def Completes (processing : Fin n → ℝ) (strategy : Strategy n) : Prop :=
  (run processing strategy n).config.touched = Finset.univ

def CompletesAll (u : ℝ) (strategy : Strategy n) : Prop :=
  ∀ processing : Fin n → ℝ,
    (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) → Completes processing strategy

structure HistoryInvariant (config : Config n) : Prop where
  nodup : (config.transcript.map Observation.job).Nodup
  touched_eq : (config.transcript.map Observation.job).toFinset = config.touched

def Truthful (processing : Fin n → ℝ) (transcript : Transcript n) : Prop :=
  ∀ job p, Observation.optimizedCompleted job p ∈ transcript → p = processing job

theorem Config.initial_historyInvariant (n : ℕ) :
    HistoryInvariant (Config.initial n) := by
  constructor <;> simp [Config.initial]

theorem HistoryInvariant.step
    {processing : Fin n → ℝ} {config next : Config n} {action : Action n}
    (hinv : HistoryInvariant config)
    (hstep : config.step processing action = some next) :
    HistoryInvariant next := by
  classical
  unfold Config.step at hstep
  split at hstep
  · contradiction
  · rename_i hfresh
    split at hstep <;> simp only [Option.some.injEq] at hstep
    all_goals
      subst next
      constructor
      · rw [List.map_append]
        simp only [List.map_singleton, Observation.job]
        apply hinv.nodup.append
        · simp
        · intro job hjob hsingleton
          simp only [List.mem_singleton] at hsingleton
          subst job
          exact hfresh (hinv.touched_eq ▸ List.mem_toFinset.mpr hjob)
      · rw [List.map_append]
        simp [Observation.job, hinv.touched_eq]

theorem runFuel_historyInvariant
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (hinv : HistoryInvariant config) :
    HistoryInvariant (runFuel processing strategy fuel config).config := by
  induction fuel generalizing config with
  | zero => exact hinv
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runFuel, haction] using hinv
      | some action =>
          cases hstep : config.step processing action with
          | none =>
              simpa [runFuel, haction, hstep] using hinv
          | some next =>
              simpa [runFuel, haction, hstep] using ih next (hinv.step hstep)

theorem run_historyInvariant
    (processing : Fin n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    HistoryInvariant (run processing strategy fuel).config := by
  unfold run
  exact runFuel_historyInvariant processing strategy fuel (Config.initial n)
    (Config.initial_historyInvariant n)

theorem Truthful.nil (processing : Fin n → ℝ) :
    Truthful processing [] := by
  intro job p hmem
  simp at hmem

theorem Truthful.append_raw
    {processing : Fin n → ℝ} {transcript : Transcript n}
    (htruth : Truthful processing transcript) (job : Fin n) :
    Truthful processing (transcript ++ [.rawCompleted job]) := by
  intro other p hmem
  rw [List.mem_append] at hmem
  rcases hmem with hold | hnew
  · exact htruth other p hold
  · simp at hnew

theorem Truthful.append_optimized
    {processing : Fin n → ℝ} {transcript : Transcript n}
    (htruth : Truthful processing transcript) (job : Fin n) :
    Truthful processing
      (transcript ++ [.optimizedCompleted job (processing job)]) := by
  intro other p hmem
  rw [List.mem_append] at hmem
  rcases hmem with hold | hnew
  · exact htruth other p hold
  · have heq : Observation.optimizedCompleted other p =
        Observation.optimizedCompleted job (processing job) := by simpa using hnew
    injection heq with hjob hp
    subst other
    exact hp

theorem Truthful.step
    {processing : Fin n → ℝ} {config next : Config n} {action : Action n}
    (htruth : Truthful processing config.transcript)
    (hstep : config.step processing action = some next) :
    Truthful processing next.transcript := by
  unfold Config.step at hstep
  split at hstep
  · contradiction
  · split at hstep
    · cases hstep
      exact htruth.append_raw _
    · cases hstep
      exact htruth.append_optimized _

theorem runFuel_truthful
    (processing : Fin n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (htruth : Truthful processing config.transcript) :
    Truthful processing (runFuel processing strategy fuel config).config.transcript := by
  induction fuel generalizing config with
  | zero => exact htruth
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runFuel, haction] using htruth
      | some action =>
          cases hstep : config.step processing action with
          | none => simpa [runFuel, haction, hstep] using htruth
          | some next =>
              simpa [runFuel, haction, hstep] using ih next (htruth.step hstep)

theorem run_truthful
    (processing : Fin n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    Truthful processing (run processing strategy fuel).config.transcript := by
  unfold run
  exact runFuel_truthful processing strategy fuel (Config.initial n)
    (Truthful.nil processing)

theorem runFuel_transcript_length_le
    (processing : Fin n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) :
    (runFuel processing strategy fuel config).config.transcript.length ≤
      config.transcript.length + fuel := by
  induction fuel generalizing config with
  | zero => simp [runFuel]
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runFuel, haction] using
            (show config.transcript.length ≤ config.transcript.length + (fuel + 1) by omega)
      | some action =>
          cases hstep : config.step processing action with
          | none =>
              simpa [runFuel, haction, hstep] using
                (show config.transcript.length ≤ config.transcript.length + (fuel + 1) by omega)
          | some next =>
              have hlen : next.transcript.length = config.transcript.length + 1 := by
                unfold Config.step at hstep
                split at hstep
                · contradiction
                · split at hstep <;> cases hstep <;> simp
              have hbound := ih next
              have : next.transcript.length + fuel ≤
                  config.transcript.length + (fuel + 1) := by omega
              simpa [runFuel, haction, hstep] using hbound.trans this

theorem run_transcript_length_le_fuel
    (processing : Fin n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    (run processing strategy fuel).config.transcript.length ≤ fuel := by
  simpa [run, Config.initial] using
    runFuel_transcript_length_le processing strategy fuel (Config.initial n)

theorem transcript_length_eq_n_of_completes
    {processing : Fin n → ℝ} {strategy : Strategy n}
    (hcomplete : Completes processing strategy) :
    (run processing strategy n).config.transcript.length = n := by
  have hinv := run_historyInvariant processing strategy n
  have hle := run_transcript_length_le_fuel processing strategy n
  have hcard :
      (run processing strategy n).config.touched.card = n := by
    rw [hcomplete]
    simp
  rw [← hinv.touched_eq, List.toFinset_card_of_nodup hinv.nodup] at hcard
  simpa using hcard

/-! ## Clairvoyant benchmark and two canonical strategies -/

def effectiveLength (u p : ℝ) : ℝ := min u (1 + p)

def offlineCost (u : ℝ) (processing : Fin n → ℝ) : ℝ :=
  pairCost (List.ofFn fun job => effectiveLength u (processing job))

def firstUntouched? (n : ℕ) (transcript : Transcript n) : Option (Fin n) :=
  (Finset.univ \ (transcript.map Observation.job).toFinset).toList.head?

def fixedModeStrategy (n : ℕ) (mode : Mode) : Strategy n := fun transcript =>
  (firstUntouched? n transcript).map fun job => ⟨job, mode⟩

def rawStrategy (n : ℕ) : Strategy n := fixedModeStrategy n .raw

def optimizeAllStrategy (n : ℕ) : Strategy n :=
  fixedModeStrategy n .optimized

theorem exists_firstUntouched_of_card_lt
    (transcript : Transcript n)
    (hcard : (transcript.map Observation.job).toFinset.card < n) :
    ∃ job,
      firstUntouched? n transcript = some job ∧
      job ∉ (transcript.map Observation.job).toFinset := by
  classical
  let remaining :=
    Finset.univ \ (transcript.map Observation.job).toFinset
  have hremaining : remaining.Nonempty := by
    dsimp [remaining]
    apply Finset.sdiff_nonempty_of_card_lt_card
    simpa using hcard
  have hlist : remaining.toList ≠ [] := by
    simpa using hremaining.ne_empty
  let job := remaining.toList.head hlist
  have hhead : remaining.toList.head? = some job := by
    exact List.head?_eq_some_head hlist
  have hmem : job ∈ remaining := by
    apply Finset.mem_toList.mp
    change job ∈ remaining.toList
    exact List.head_mem hlist
  refine ⟨job, ?_, ?_⟩
  · simpa [firstUntouched?, remaining] using hhead
  · simpa [remaining] using hmem

/-- A fixed-mode strategy consumes one fresh label at every step until all
labels have been completed. -/
theorem runFuel_fixedMode_touched_card
    (processing : Fin n → ℝ) (mode : Mode) (fuel : ℕ)
    (config : Config n) (hinv : HistoryInvariant config)
    (hbound : config.touched.card + fuel ≤ n) :
    (runFuel processing (fixedModeStrategy n mode) fuel config).config.touched.card =
      config.touched.card + fuel := by
  induction fuel generalizing config with
  | zero => simp [runFuel]
  | succ fuel ih =>
      have hcardlt : config.touched.card < n := by omega
      have htranscriptCard :
          (config.transcript.map Observation.job).toFinset.card < n := by
        rw [hinv.touched_eq]
        exact hcardlt
      obtain ⟨job, hfirst, hfreshTranscript⟩ :=
        exists_firstUntouched_of_card_lt config.transcript htranscriptCard
      have hfresh : job ∉ config.touched := by
        rw [← hinv.touched_eq]
        exact hfreshTranscript
      let observation := match mode with
        | .raw => Observation.rawCompleted job
        | .optimized =>
            Observation.optimizedCompleted job (processing job)
      let next : Config n :=
        ⟨insert job config.touched,
          config.transcript ++ [observation]⟩
      have haction :
          fixedModeStrategy n mode config.transcript = some ⟨job, mode⟩ := by
        simp [fixedModeStrategy, hfirst]
      have hstep : config.step processing ⟨job, mode⟩ = some next := by
        cases mode <;> simp [Config.step, hfresh, next, observation]
      have hinvNext : HistoryInvariant next := hinv.step hstep
      have hcardNext : next.touched.card = config.touched.card + 1 := by
        simp [next, Finset.card_insert_of_notMem hfresh]
      have hboundNext : next.touched.card + fuel ≤ n := by
        rw [hcardNext]
        omega
      have hrec := ih next hinvNext hboundNext
      have hrec' :
          (runFuel processing (fixedModeStrategy n mode) fuel next).config.touched.card =
            config.touched.card + (fuel + 1) := by
        rw [hrec, hcardNext]
        omega
      simpa [runFuel, haction, hstep] using hrec'

theorem fixedModeStrategy_completes
    (processing : Fin n → ℝ) (mode : Mode) :
    Completes processing (fixedModeStrategy n mode) := by
  have hinv := Config.initial_historyInvariant n
  have hcard := runFuel_fixedMode_touched_card processing mode n
    (Config.initial n) hinv (by simp [Config.initial])
  unfold Completes run
  apply Finset.eq_univ_of_card
  simpa [Config.initial] using hcard

theorem rawStrategy_completes (processing : Fin n → ℝ) :
    Completes processing (rawStrategy n) := by
  exact fixedModeStrategy_completes processing .raw

theorem optimizeAllStrategy_completes (processing : Fin n → ℝ) :
    Completes processing (optimizeAllStrategy n) := by
  exact fixedModeStrategy_completes processing .optimized

theorem rawStrategy_completesAll (u : ℝ) :
    CompletesAll u (rawStrategy n) := by
  intro processing _hp
  exact rawStrategy_completes processing

theorem optimizeAllStrategy_completesAll (u : ℝ) :
    CompletesAll u (optimizeAllStrategy n) := by
  intro processing _hp
  exact optimizeAllStrategy_completes processing

def UsesMode (mode : Mode) (transcript : Transcript n) : Prop :=
  ∀ observation ∈ transcript, observation.mode = mode

theorem UsesMode.nil (mode : Mode) : UsesMode mode ([] : Transcript n) := by
  simp [UsesMode]

theorem UsesMode.step
    {processing : Fin n → ℝ} {config next : Config n}
    {action : Action n} {mode : Mode}
    (huses : UsesMode mode config.transcript)
    (haction : action.mode = mode)
    (hstep : config.step processing action = some next) :
    UsesMode mode next.transcript := by
  unfold Config.step at hstep
  split at hstep
  · contradiction
  · cases action with
    | mk job actionMode =>
      simp only at haction
      subst actionMode
      cases mode <;> cases hstep
      all_goals
        intro observation hmem
        rw [List.mem_append] at hmem
        rcases hmem with hold | hnew
        · exact huses observation hold
        · simp only [List.mem_singleton] at hnew
          subst observation
          rfl

theorem runFuel_fixedMode_usesMode
    (processing : Fin n → ℝ) (mode : Mode) (fuel : ℕ)
    (config : Config n) (huses : UsesMode mode config.transcript) :
    UsesMode mode
      (runFuel processing (fixedModeStrategy n mode) fuel config).config.transcript := by
  induction fuel generalizing config with
  | zero => simpa [runFuel] using huses
  | succ fuel ih =>
      cases hfirst : firstUntouched? n config.transcript with
      | none => simpa [runFuel, fixedModeStrategy, hfirst] using huses
      | some job =>
          have haction : fixedModeStrategy n mode config.transcript =
              some ⟨job, mode⟩ := by
            simp [fixedModeStrategy, hfirst]
          cases hstep : config.step processing ⟨job, mode⟩ with
          | none => simpa [runFuel, haction, hstep] using huses
          | some next =>
              have hnext : UsesMode mode next.transcript :=
                huses.step rfl hstep
              simpa [runFuel, haction, hstep] using ih next hnext

theorem run_fixedMode_usesMode
    (processing : Fin n → ℝ) (mode : Mode) (fuel : ℕ) :
    UsesMode mode
      (run processing (fixedModeStrategy n mode) fuel).config.transcript := by
  unfold run
  exact runFuel_fixedMode_usesMode processing mode fuel (Config.initial n)
    (UsesMode.nil mode)

theorem rawStrategy_duration_list
    (u : ℝ) (processing : Fin n → ℝ) :
    ((run processing (rawStrategy n) n).config.transcript.map
      (Observation.duration u)) = List.replicate n u := by
  let transcript := (run processing (rawStrategy n) n).config.transcript
  have huses : UsesMode .raw transcript := by
    exact run_fixedMode_usesMode processing .raw n
  have hlength : transcript.length = n :=
    transcript_length_eq_n_of_completes (rawStrategy_completes processing)
  calc
    transcript.map (Observation.duration u) = transcript.map (fun _ ↦ u) := by
      apply List.map_congr_left
      intro observation hmem
      have hmode := huses observation hmem
      cases observation <;> simp [Observation.mode, Observation.duration] at hmode ⊢
    _ = List.replicate transcript.length u := by simp
    _ = List.replicate n u := by rw [hlength]

theorem prefixCost_mono_of_forall₂ {xs ys : List ℝ}
    (h : List.Forall₂ (· ≤ ·) xs ys) : prefixCost xs ≤ prefixCost ys := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hrest ih =>
      simp only [prefixCost_cons]
      have hlength : xs.length = ys.length := hrest.length_eq
      rw [hlength]
      have hcoefficient : 0 ≤ (ys.length + 1 : ℝ) := by positivity
      exact add_le_add (mul_le_mul_of_nonneg_left hxy hcoefficient) ih

theorem full_label_permutation
    {processing : Fin n → ℝ} {strategy : Strategy n}
    (hcomplete : Completes processing strategy) :
    ((run processing strategy n).config.transcript.map Observation.job).Perm
      (List.ofFn fun job : Fin n => job) := by
  let transcript := (run processing strategy n).config.transcript
  have hinv := run_historyInvariant processing strategy n
  apply (List.perm_ext_iff_of_nodup hinv.nodup
    (List.nodup_ofFn.mpr fun _ _ hij => hij)).2
  intro job
  constructor
  · intro _
    simp
  · intro _
    have hmem : job ∈
        ((run processing strategy n).config.transcript.map Observation.job).toFinset := by
      rw [hinv.touched_eq, hcomplete]
      simp
    exact List.mem_toFinset.mp hmem

theorem optimizeAllStrategy_duration_perm
    (u : ℝ) (processing : Fin n → ℝ) :
    ((run processing (optimizeAllStrategy n) n).config.transcript.map
      (Observation.duration u)).Perm
        (List.ofFn fun job ↦ 1 + processing job) := by
  let transcript :=
    (run processing (optimizeAllStrategy n) n).config.transcript
  have huses : UsesMode .optimized transcript := by
    exact run_fixedMode_usesMode processing .optimized n
  have htruth : Truthful processing transcript := by
    exact run_truthful processing (optimizeAllStrategy n) n
  have hduration :
      transcript.map (Observation.duration u) =
        transcript.map (fun observation ↦ 1 + processing observation.job) := by
    apply List.map_congr_left
    intro observation hmem
    have hmode := huses observation hmem
    cases observation with
    | rawCompleted job => simp [Observation.mode] at hmode
    | optimizedCompleted job p =>
        have hp := htruth job p hmem
        simp [Observation.duration, Observation.job, hp]
  rw [hduration]
  have hlabels := full_label_permutation
    (optimizeAllStrategy_completes processing)
  simpa [transcript, List.map_map] using
    hlabels.map (fun job ↦ 1 + processing job)

theorem effective_le_observed_duration
    {u : ℝ} {processing : Fin n → ℝ} {transcript : Transcript n}
    (htruth : Truthful processing transcript) :
    List.Forall₂ (· ≤ ·)
      (transcript.map fun observation =>
        effectiveLength u (processing observation.job))
      (transcript.map (Observation.duration u)) := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      have hrest : Truthful processing rest := by
        intro job p hmem
        exact htruth job p (by simp [hmem])
      simp only [List.map_cons, List.forall₂_cons]
      constructor
      · cases observation with
        | rawCompleted job => exact min_le_left _ _
        | optimizedCompleted job p =>
            have hp := htruth job p (by simp)
            change min u (1 + processing job) ≤ 1 + p
            rw [hp]
            exact min_le_right _ _
      · exact ih hrest

/-- Every complete normal-form blind-optimization run dominates the literal
clairvoyant SPT benchmark, with no semantic interface assumptions. -/
theorem offlineCost_le_runCost
    {u : ℝ} (processing : Fin n → ℝ)
    (strategy : Strategy n) (hcomplete : Completes processing strategy) :
    offlineCost u processing ≤ runCost u processing strategy n := by
  let transcript := (run processing strategy n).config.transcript
  have hlabels := full_label_permutation hcomplete
  have heffective :
      (transcript.map fun observation =>
        effectiveLength u (processing observation.job)).Perm
      (List.ofFn fun job : Fin n => effectiveLength u (processing job)) := by
    simpa [transcript, List.map_map] using
      hlabels.map (fun job => effectiveLength u (processing job))
  have htruth := run_truthful processing strategy n
  unfold offlineCost runCost completionCost
  rw [← pairCost_perm heffective]
  exact (pairCost_le_prefixCost _).trans
    (prefixCost_mono_of_forall₂
      (effective_le_observed_duration (transcript := transcript) htruth))

end

end Online
end BlindOptimization
end SchedulingPaper
