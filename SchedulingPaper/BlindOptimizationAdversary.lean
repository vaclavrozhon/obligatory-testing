import SchedulingPaper.BlindOptimizationModel
import SchedulingPaper.BlindOptimizationAlgebra
import SchedulingPaper.RandomPermutation
import Mathlib.Tactic

/-!
# Fixed-input adversaries for blind optimization

The adaptive rule assigns value zero to a raw job and value two to an
optimized job.  Because raw execution hides the value and optimization sees
it only after committing to the block, the completed adaptive transcript can
be frozen to one ordinary labeled input.  The replay theorem below checks
that statement against the operational semantics rather than assuming it as
an interface hypothesis.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace Adversary

open Online

noncomputable section
attribute [local instance] Classical.propDecidable

def responseProcessing {n : ℕ} (action : Action n) : Fin n → ℝ :=
  fun job => if action.mode = .optimized ∧ job = action.job then 2 else 0

def adaptiveStep {n : ℕ} (config : Config n) (action : Action n) :
    Option (Config n) := config.step (responseProcessing action) action

def adaptiveRunFuel {n : ℕ} (strategy : Strategy n) :
    ℕ → Config n → RunResult n
  | 0, config => ⟨config, .outOfFuel⟩
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => ⟨config, .strategyStopped⟩
      | some action =>
          match adaptiveStep config action with
          | none => ⟨config, .repeatedJob⟩
          | some next => adaptiveRunFuel strategy fuel next

def adaptiveRun {n : ℕ} (strategy : Strategy n) : RunResult n :=
  adaptiveRunFuel strategy n (Config.initial n)

def FrozenOptimized {n : ℕ} (transcript : Transcript n) (job : Fin n) : Prop :=
  ∃ p, Observation.optimizedCompleted job p ∈ transcript

def frozenProcessing {n : ℕ} (transcript : Transcript n) (job : Fin n) : ℝ :=
  if FrozenOptimized transcript job then 2 else 0

theorem frozenProcessing_mem_Icc (transcript : Transcript n) (job : Fin n) :
    frozenProcessing transcript job ∈ Set.Icc (0 : ℝ) 2 := by
  unfold frozenProcessing
  split <;> norm_num

theorem frozenProcessing_eq_two_of_mem
    {transcript : Transcript n} {job : Fin n} {p : ℝ}
    (hmem : Observation.optimizedCompleted job p ∈ transcript) :
    frozenProcessing transcript job = 2 := by
  rw [frozenProcessing, if_pos]
  exact ⟨p, hmem⟩

theorem adaptiveStep_eq_fixedStep_of_prefix
    {config next final : Config n} {action : Action n}
    (hstep : adaptiveStep config action = some next)
    (hprefix : next.transcript <+: final.transcript) :
    config.step (frozenProcessing final.transcript) action = some next := by
  have hfresh : action.job ∉ config.touched := by
    intro hrepeat
    simp [adaptiveStep, Config.step, hrepeat] at hstep
  cases hmode : action.mode with
  | raw =>
      simpa [adaptiveStep, Config.step, hfresh, hmode] using hstep
  | optimized =>
      have hnext : next =
          ⟨insert action.job config.touched,
            config.transcript ++
              [Observation.optimizedCompleted action.job 2]⟩ := by
        simpa [adaptiveStep, Config.step, hfresh, responseProcessing, hmode]
          using hstep.symm
      subst next
      have hmem : Observation.optimizedCompleted action.job 2 ∈ final.transcript :=
        hprefix.subset (by simp)
      simp [Config.step, hfresh, hmode,
        frozenProcessing_eq_two_of_mem hmem]

theorem adaptiveRunFuel_transcript_prefix
    (strategy : Strategy n) (fuel : ℕ) (config : Config n) :
    config.transcript <+:
      (adaptiveRunFuel strategy fuel config).config.transcript := by
  induction fuel generalizing config with
  | zero => exact List.prefix_rfl
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [adaptiveRunFuel, haction]
      | some action =>
          cases hstep : adaptiveStep config action with
          | none => simpa [adaptiveRunFuel, haction, hstep]
          | some next =>
              have hone : config.transcript <+: next.transcript := by
                unfold adaptiveStep Config.step at hstep
                split at hstep
                · contradiction
                · split at hstep <;> cases hstep <;>
                    exact List.prefix_append _ _
              simpa [adaptiveRunFuel, haction, hstep] using hone.trans (ih next)

/-- Freezing the adaptive transcript yields a genuine fixed input with the
identical completed run. -/
theorem adaptiveRunFuel_replay
    (strategy : Strategy n) (fuel : ℕ) (config : Config n) :
    let result := adaptiveRunFuel strategy fuel config
    runFuel (frozenProcessing result.config.transcript) strategy fuel config = result := by
  induction fuel generalizing config with
  | zero => simp [adaptiveRunFuel, runFuel]
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simp [adaptiveRunFuel, runFuel, haction]
      | some action =>
          cases hstep : adaptiveStep config action with
          | none =>
              have hrepeat : action.job ∈ config.touched := by
                by_contra hfresh
                simp [adaptiveStep, Config.step, hfresh] at hstep
              have hfixed : config.step
                  (frozenProcessing config.transcript) action = none := by
                simp [Config.step, hrepeat]
              simp [adaptiveRunFuel, runFuel, haction, hstep, hfixed]
          | some next =>
              let result := adaptiveRunFuel strategy fuel next
              have hprefix : next.transcript <+: result.config.transcript :=
                adaptiveRunFuel_transcript_prefix strategy fuel next
              have hfixed : config.step
                  (frozenProcessing result.config.transcript) action = some next :=
                adaptiveStep_eq_fixedStep_of_prefix hstep hprefix
              have htail := ih next
              dsimp at htail
              simpa [adaptiveRunFuel, runFuel, haction, hstep, result, hfixed]
                using htail

theorem adaptiveRun_replay (strategy : Strategy n) :
    let result := adaptiveRun strategy
    run (frozenProcessing result.config.transcript) strategy n = result := by
  dsimp [adaptiveRun, run]
  exact adaptiveRunFuel_replay strategy n (Config.initial n)

theorem adaptiveRun_complete_of_completesAll
    {strategy : Strategy n} (hcomplete : CompletesAll 2 strategy) :
    (adaptiveRun strategy).config.touched = Finset.univ := by
  let result := adaptiveRun strategy
  let processing := frozenProcessing result.config.transcript
  have hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) 2 :=
    fun job => frozenProcessing_mem_Icc _ _
  have hfixed := hcomplete processing hp
  have hreplay := adaptiveRun_replay strategy
  dsimp [result] at hreplay ⊢
  rw [← hreplay]
  exact hfixed

/-! ## The deterministic instance-optimality gap -/

def optimizedCount (transcript : Transcript n) : ℕ :=
  transcript.countP fun observation => observation.mode = .optimized

theorem optimizedCount_le_length (transcript : Transcript n) :
    optimizedCount transcript ≤ transcript.length := by
  exact List.countP_le_length

theorem optimized_observation_eq_two
    {strategy : Strategy n} {job : Fin n} {p : ℝ}
    (hmem : Observation.optimizedCompleted job p ∈
      (adaptiveRun strategy).config.transcript) : p = 2 := by
  let result := adaptiveRun strategy
  let processing := frozenProcessing result.config.transcript
  have hreplay := adaptiveRun_replay strategy
  have htruth := run_truthful processing strategy n
  dsimp [result] at processing hreplay htruth ⊢
  rw [hreplay] at htruth
  have hp := htruth job p hmem
  calc
    p = frozenProcessing (adaptiveRun strategy).config.transcript job := by
      simpa [processing, result] using hp
    _ = 2 := frozenProcessing_eq_two_of_mem hmem

theorem adversarial_duration_mem (strategy : Strategy n)
    {duration : ℝ}
    (hmem : duration ∈
      (adaptiveRun strategy).config.transcript.map (Observation.duration 2)) :
    duration = 2 ∨ duration = 3 := by
  rcases List.mem_map.mp hmem with ⟨observation, hobservation, rfl⟩
  cases observation with
  | rawCompleted job => simp [Observation.duration]
  | optimizedCompleted job p =>
      have hp := optimized_observation_eq_two hobservation
      right
      simp [Observation.duration, hp]
      norm_num

theorem count_two_add_three_eq_length_of_values
    (values : List ℝ) (hvalues : ∀ x ∈ values, x = 2 ∨ x = 3) :
    values.count 2 + values.count 3 = values.length := by
  induction values with
  | nil => simp
  | cons x rest ih =>
      have hx := hvalues x (by simp)
      have hrest : ∀ y ∈ rest, y = 2 ∨ y = 3 := by
        intro y hy
        exact hvalues y (by simp [hy])
      have hih := ih hrest
      rcases hx with rfl | rfl <;>
        simp only [List.count_cons, List.length_cons] <;> norm_num <;> omega

theorem count_three_durations_eq_optimizedCount_of_two
    (transcript : Transcript n)
    (hopt : ∀ job p, Observation.optimizedCompleted job p ∈ transcript → p = 2) :
    (transcript.map (Observation.duration 2)).count 3 =
      optimizedCount transcript := by
  induction transcript with
  | nil => simp [optimizedCount]
  | cons observation rest ih =>
      have hrest : ∀ job p,
          Observation.optimizedCompleted job p ∈ rest → p = 2 := by
        intro job p hmem
        exact hopt job p (by simp [hmem])
      cases observation with
      | rawCompleted job =>
          have hcount : optimizedCount (Observation.rawCompleted job :: rest) =
              optimizedCount rest := by
            simp [optimizedCount, Observation.mode]
          rw [hcount]
          simpa [Observation.duration] using ih hrest
      | optimizedCompleted job p =>
          have hp : p = 2 := hopt job p (by simp)
          have hcount :
              optimizedCount (Observation.optimizedCompleted job p :: rest) =
                optimizedCount rest + 1 := by
            simp [optimizedCount, Observation.mode]
          rw [hcount, hp]
          have hih := ih hrest
          simp only [List.map_cons, Observation.duration]
          norm_num
          omega

theorem count_three_durations_eq_optimizedCount (strategy : Strategy n) :
    ((adaptiveRun strategy).config.transcript.map
      (Observation.duration 2)).count 3 =
      optimizedCount (adaptiveRun strategy).config.transcript := by
  apply count_three_durations_eq_optimizedCount_of_two
  intro job p hmem
  exact optimized_observation_eq_two hmem

theorem prefixCost_replicate (k : ℕ) (a : ℝ) :
    prefixCost (List.replicate k a) = a * k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, prefixCost_cons, List.length_replicate, ih]
      push_cast
      ring

theorem pairwise_two_three (r m : ℕ) :
    (List.replicate r (2 : ℝ) ++ List.replicate m 3).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  simp
  norm_num

theorem prefixCost_two_three (n m : ℕ) (hm : m ≤ n) :
    prefixCost
        (List.replicate (n - m) (2 : ℝ) ++ List.replicate m 3) =
      (n : ℝ) ^ 2 + n + ((m : ℝ) ^ 2 + m) / 2 := by
  rw [prefixCost_append, prefixCost_replicate, prefixCost_replicate]
  simp only [List.length_replicate, List.sum_replicate, nsmul_eq_mul]
  rw [Nat.cast_sub hm]
  push_cast
  ring

/-- The operational adversarial run has exactly the lower bound used in the
paper's deterministic instance-optimality counterexample. -/
theorem deterministic_adversarial_cost
    {strategy : Strategy n} (hcomplete : CompletesAll 2 strategy) :
    let result := adaptiveRun strategy
    let processing := frozenProcessing result.config.transcript
    let m := optimizedCount result.config.transcript
    runCost 2 processing strategy n ≥
      (n : ℝ) ^ 2 + n + ((m : ℝ) ^ 2 + m) / 2 := by
  dsimp
  let result := adaptiveRun strategy
  let processing := frozenProcessing result.config.transcript
  let transcript := result.config.transcript
  let durations := transcript.map (Observation.duration 2)
  let m := optimizedCount transcript
  have hcompleteAdaptive := adaptiveRun_complete_of_completesAll hcomplete
  have hlength : transcript.length = n := by
    have hreplay := adaptiveRun_replay strategy
    have hfixed : Completes processing strategy := by
      exact hcomplete processing (fun job => frozenProcessing_mem_Icc _ _)
    have := transcript_length_eq_n_of_completes hfixed
    dsimp [processing, transcript, result] at this hreplay ⊢
    rwa [hreplay] at this
  have hm : m ≤ n := by
    exact (optimizedCount_le_length transcript).trans_eq hlength
  have hvalues : ∀ x ∈ durations, x = 2 ∨ x = 3 := by
    intro x hx
    exact adversarial_duration_mem strategy hx
  have hcount3 : durations.count 3 = m := by
    dsimp [durations, m, transcript, result]
    exact count_three_durations_eq_optimizedCount strategy
  have hcount2 : durations.count 2 = n - m := by
    have hsum := count_two_add_three_eq_length_of_values durations hvalues
    have hdlen : durations.length = n := by simpa [durations] using hlength
    rw [hcount3, hdlen] at hsum
    omega
  have hsubset : durations ⊆ [(2 : ℝ), 3] := by
    intro x hx
    rcases hvalues x hx with rfl | rfl <;> simp
  have hperm : durations.Perm
      (List.replicate (n - m) (2 : ℝ) ++ List.replicate m 3) := by
    exact (List.perm_replicate_append_replicate (by norm_num : (2 : ℝ) ≠ 3)).2
      ⟨hcount2, hcount3, hsubset⟩
  have hminimal := pairwise_prefixCost_minimal
    (pairwise_two_three (n - m) m) hperm.symm
  rw [prefixCost_two_three n m hm] at hminimal
  have hreplay := adaptiveRun_replay strategy
  unfold runCost completionCost
  dsimp [processing, durations, transcript, result] at hreplay ⊢
  rw [hreplay]
  exact hminimal

theorem frozen_indicator_sum_eq_optimizedCount
    (transcript : Transcript n)
    (hnodup : (transcript.map Observation.job).Nodup) :
    ((transcript.map Observation.job).map fun job =>
      if frozenProcessing transcript job = 2 then 1 else 0).sum =
        optimizedCount transcript := by
  induction transcript with
  | nil => simp [optimizedCount]
  | cons observation rest ih =>
      cases observation with
      | rawCompleted job =>
          have hnodup' : job ∉ rest.map Observation.job ∧
              (rest.map Observation.job).Nodup :=
            List.nodup_cons.mp (by simpa [Observation.job] using hnodup)
          have ih' := ih hnodup'.2
          have hnot : ¬ FrozenOptimized
              (Observation.rawCompleted job :: rest) job := by
            rintro ⟨p, hmem⟩
            simp only [List.mem_cons] at hmem
            rcases hmem with hfalse | hrest
            · contradiction
            · apply hnodup'.1
              exact List.mem_map.mpr
                ⟨Observation.optimizedCompleted job p, hrest, rfl⟩
          have hmap :
              (rest.map Observation.job).map (fun other =>
                if frozenProcessing (Observation.rawCompleted job :: rest) other = 2
                then 1 else 0) =
              (rest.map Observation.job).map (fun other =>
                if frozenProcessing rest other = 2 then 1 else 0) := by
            apply List.map_congr_left
            intro other hother
            congr 2
            unfold frozenProcessing FrozenOptimized
            simp
          have hzero :
              frozenProcessing (Observation.rawCompleted job :: rest) job = 0 := by
            simp [frozenProcessing, hnot]
          have hcount :
              optimizedCount (Observation.rawCompleted job :: rest) =
                optimizedCount rest := by
            simp [optimizedCount, Observation.mode]
          change (if frozenProcessing
              (Observation.rawCompleted job :: rest) job = 2 then 1 else 0) +
              ((rest.map Observation.job).map fun other =>
                if frozenProcessing (Observation.rawCompleted job :: rest) other = 2
                then 1 else 0).sum =
              optimizedCount (Observation.rawCompleted job :: rest)
          rw [hzero, hmap, ih', hcount]
          simp
      | optimizedCompleted job p =>
          have hnodup' : job ∉ rest.map Observation.job ∧
              (rest.map Observation.job).Nodup :=
            List.nodup_cons.mp (by simpa [Observation.job] using hnodup)
          have ih' := ih hnodup'.2
          have hhead : frozenProcessing
              (Observation.optimizedCompleted job p :: rest) job = 2 :=
            frozenProcessing_eq_two_of_mem (p := p) (by simp)
          have hmap :
              (rest.map Observation.job).map (fun other =>
                if frozenProcessing
                    (Observation.optimizedCompleted job p :: rest) other = 2
                then 1 else 0) =
              (rest.map Observation.job).map (fun other =>
                if frozenProcessing rest other = 2 then 1 else 0) := by
            apply List.map_congr_left
            intro other hother
            have hne : other ≠ job := by
              intro heq
              subst other
              exact hnodup'.1 hother
            congr 2
            have hFrozen :
                FrozenOptimized (Observation.optimizedCompleted job p :: rest) other ↔
                  FrozenOptimized rest other := by
              constructor
              · rintro ⟨q, hmem⟩
                simp only [List.mem_cons] at hmem
                rcases hmem with heq | hrest
                · injection heq with hjob _
                  exact (hne hjob).elim
                · exact ⟨q, hrest⟩
              · rintro ⟨q, hrest⟩
                exact ⟨q, by simp [hrest]⟩
            unfold frozenProcessing
            rw [if_congr hFrozen rfl rfl]
          have hcount :
              optimizedCount (Observation.optimizedCompleted job p :: rest) =
                optimizedCount rest + 1 := by
            simp [optimizedCount, Observation.mode]
          change (if frozenProcessing
              (Observation.optimizedCompleted job p :: rest) job = 2 then 1 else 0) +
              ((rest.map Observation.job).map fun other =>
                if frozenProcessing
                    (Observation.optimizedCompleted job p :: rest) other = 2
                then 1 else 0).sum =
              optimizedCount (Observation.optimizedCompleted job p :: rest)
          rw [hhead, hmap, ih', hcount]
          simp
          omega

theorem frozen_two_card_eq_optimizedCount
    {strategy : Strategy n} (hcomplete : CompletesAll 2 strategy) :
    let result := adaptiveRun strategy
    let processing := frozenProcessing result.config.transcript
    (Finset.univ.filter fun job => processing job = 2).card =
      optimizedCount result.config.transcript := by
  dsimp
  let result := adaptiveRun strategy
  let processing := frozenProcessing result.config.transcript
  let transcript := result.config.transcript
  have hfixed : Completes processing strategy :=
    hcomplete processing (fun job => frozenProcessing_mem_Icc _ _)
  have hlabels := full_label_permutation hfixed
  have hreplay := adaptiveRun_replay strategy
  have hinv := run_historyInvariant processing strategy n
  dsimp [processing, transcript, result] at hlabels hreplay hinv ⊢
  rw [hreplay] at hlabels hinv
  let indicator : Fin n → ℕ := fun job =>
    if frozenProcessing (adaptiveRun strategy).config.transcript job = 2 then 1 else 0
  calc
    (Finset.univ.filter fun job =>
        frozenProcessing (adaptiveRun strategy).config.transcript job = 2).card =
        ∑ job, indicator job := by
          simp [indicator]
    _ = (List.ofFn indicator).sum := by rw [List.sum_ofFn]
    _ = (((adaptiveRun strategy).config.transcript.map Observation.job).map
          indicator).sum := by
        simpa [List.map_ofFn] using (hlabels.map indicator).sum_eq.symm
    _ = optimizedCount (adaptiveRun strategy).config.transcript := by
      simpa [indicator, List.map_map] using
        frozen_indicator_sum_eq_optimizedCount
          (adaptiveRun strategy).config.transcript hinv.nodup

/-- End-to-end deterministic instance-optimality counterexample from the
paper.  The returned vector is fixed before either comparator seed is drawn;
the two comparator values are the exact costs of uniform-random
`OptimizeAll` (first branch) and `Raw` (second branch). -/
theorem deterministic_instance_gap
    {strategy : Strategy n} (heven : Even n)
    (hcomplete : CompletesAll 2 strategy) :
    ∃ processing : Fin n → ℝ,
      (∀ job, processing job = 0 ∨ processing job = 2) ∧
      let m := (Finset.univ.filter fun job => processing job = 2).card
      runCost 2 processing strategy n ≥
        (if m ≤ n / 2 then
          (n + 1 : ℝ) * ((n : ℝ) + 2 * m) / 2
        else (n : ℝ) * (n + 1)) + (n : ℝ) ^ 2 / 8 := by
  let result := adaptiveRun strategy
  let processing := frozenProcessing result.config.transcript
  let m := (Finset.univ.filter fun job => processing job = 2).card
  refine ⟨processing, ?_, ?_⟩
  · intro job
    unfold processing frozenProcessing
    split <;> simp
  · have hcount := frozen_two_card_eq_optimizedCount hcomplete
    have hcost := deterministic_adversarial_cost hcomplete
    dsimp [result, processing, m] at hcount hcost ⊢
    rw [hcount] at ⊢
    let q := optimizedCount (adaptiveRun strategy).config.transcript
    have hq : q ≤ n := by
      have hfixed : Completes
          (frozenProcessing (adaptiveRun strategy).config.transcript) strategy :=
        hcomplete _ (fun job => frozenProcessing_mem_Icc _ _)
      have hlen := transcript_length_eq_n_of_completes hfixed
      have hreplay := adaptiveRun_replay strategy
      dsimp at hreplay
      rw [hreplay] at hlen
      exact (optimizedCount_le_length _).trans_eq hlen
    have hqR : (q : ℝ) ≤ n := by exact_mod_cast hq
    have hhalf : ((n / 2 : ℕ) : ℝ) = (n : ℝ) / 2 := by
      rcases heven with ⟨k, hk⟩
      rw [hk]
      rw [show (k + k) / 2 = k by omega]
      push_cast
      ring
    by_cases hbranch : q ≤ n / 2
    · rw [if_pos hbranch]
      have hbranchR : (q : ℝ) ≤ (n : ℝ) / 2 := by
        have hcast : (q : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
          exact_mod_cast hbranch
        rwa [hhalf] at hcast
      have halg := deterministic_instance_gap_algebra
        (n := (n : ℝ)) (m := (q : ℝ))
        (by positivity) (by positivity) hqR
      have hgap := halg.1 hbranchR
      dsimp [q] at hgap
      linarith
    · rw [if_neg hbranch]
      have hbranchR : (n : ℝ) / 2 ≤ (q : ℝ) := by
        have hnat : n / 2 ≤ q := le_of_lt (lt_of_not_ge hbranch)
        have hcast : ((n / 2 : ℕ) : ℝ) ≤ q := by exact_mod_cast hnat
        rwa [hhalf] at hcast
      have halg := deterministic_instance_gap_algebra
        (n := (n : ℝ)) (m := (q : ℝ))
        (by positivity) (by positivity) hqR
      have hgap := halg.2 hbranchR
      dsimp [q] at hgap
      linarith

/-! ## The announced random-order comparator -/

def randomOptimizeOrderCost (processing : Fin n → ℝ)
    (order : Equiv.Perm (Fin n)) : ℝ :=
  prefixCost (List.ofFn fun position => 1 + processing (order position))

def expectedRandomOptimizeCost (processing : Fin n → ℝ) : ℝ :=
  Randomized.uniformAverage (randomOptimizeOrderCost processing)

theorem prefixCost_ofFn_eq_weighted_sum
    (values : Fin n → ℝ) :
    prefixCost (List.ofFn values) =
      ∑ i : Fin n, (n - i.val : ℕ) * values i := by
  induction n with
  | zero => simp
  | succ n ih =>
      let tail : Fin n → ℝ := fun i => values i.succ
      have hih := ih tail
      rw [List.ofFn_succ, prefixCost_cons, Fin.sum_univ_succ]
      simp only [List.length_ofFn, Fin.val_zero, Nat.sub_zero]
      rw [hih]
      congr 1
      · push_cast
        ring
      · apply Finset.sum_congr rfl
        intro i _
        dsimp [tail]
        have hnat : n + 1 - (i.val + 1) = n - i.val := by
          have hi := i.isLt
          omega
        rw [hnat]

theorem two_mul_sum_fin_reverse_weights (n : ℕ) :
    2 * (∑ i : Fin n, (n - i.val : ℕ)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ]
      have htail : (∑ i : Fin n, (n + 1 - (i.val + 1))) =
          ∑ i : Fin n, (n - i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        have hnat : n + 1 - (i.val + 1) = n - i.val := by
          have hi := i.isLt
          omega
        exact hnat
      rw [htail]
      have hih := ih
      nlinarith

theorem expectedRandomOptimizeCost_eq
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ) :
    expectedRandomOptimizeCost processing =
      (n + 1 : ℝ) / 2 * ∑ job, (1 + processing job) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold expectedRandomOptimizeCost randomOptimizeOrderCost
  simp_rw [prefixCost_ofFn_eq_weighted_sum]
  rw [Randomized.uniformAverage_fintype_sum]
  have hposition : ∀ i : Fin n,
      Randomized.uniformAverage (fun order : Equiv.Perm (Fin n) =>
        (n - i.val : ℕ) * (1 + processing (order i))) =
      (n - i.val : ℕ) *
        ((∑ job, (1 + processing job)) / n) := by
    intro i
    change Randomized.uniformAverage (fun order : Equiv.Perm (Fin n) =>
        ((n - i.val : ℕ) : ℝ) * (1 + processing (order i))) = _
    rw [Randomized.uniformAverage_smul]
    congr 1
    simpa using Randomized.uniformAverage_perm_apply
      (fun job => 1 + processing job) i
  simp_rw [hposition]
  rw [← Finset.sum_mul]
  have hweights :
      2 * (∑ i : Fin n, ((n - i.val : ℕ) : ℝ)) =
        (n : ℝ) * (n + 1) := by
    exact_mod_cast two_mul_sum_fin_reverse_weights n
  have hweightsEq :
      (∑ i : Fin n, ((n - i.val : ℕ) : ℝ)) =
        (n : ℝ) * (n + 1) / 2 := by
    linarith
  rw [hweightsEq]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

theorem sum_frozenProcessing_eq_two_mul_optimizedCount
    {strategy : Strategy n} (hcomplete : CompletesAll 2 strategy) :
    let result := adaptiveRun strategy
    let processing := frozenProcessing result.config.transcript
    (∑ job, processing job) = 2 * optimizedCount result.config.transcript := by
  dsimp
  have hcount := frozen_two_card_eq_optimizedCount hcomplete
  let processing := frozenProcessing (adaptiveRun strategy).config.transcript
  have hp : ∀ job, processing job = 0 ∨ processing job = 2 := by
    intro job
    unfold processing frozenProcessing
    split <;> simp
  calc
    (∑ job, processing job) =
        ∑ job, if processing job = 2 then (2 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro job _
      rcases hp job with hzero | htwo
      · simp [hzero]
      · simp [htwo]
    _ = 2 * (Finset.univ.filter fun job => processing job = 2).card := by
      rw [← Finset.sum_filter]
      simp
      ring
    _ = 2 * optimizedCount (adaptiveRun strategy).config.transcript := by
      simpa [processing] using congrArg (fun k : ℕ => (2 : ℝ) * k) hcount

/-- Exact cost of the announced random-order comparator on the fixed
adversarial input. -/
theorem adversarial_expectedRandomOptimizeCost
    {n : ℕ} (hn : 0 < n) {strategy : Strategy n}
    (hcomplete : CompletesAll 2 strategy) :
    let result := adaptiveRun strategy
    let processing := frozenProcessing result.config.transcript
    let m := optimizedCount result.config.transcript
    expectedRandomOptimizeCost processing =
      (n + 1 : ℝ) * ((n : ℝ) + 2 * m) / 2 := by
  dsimp
  rw [expectedRandomOptimizeCost_eq hn]
  have hsum := sum_frozenProcessing_eq_two_mul_optimizedCount hcomplete
  dsimp at hsum
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hsum]
  ring

theorem expectedRandomOptimizeCost_binary
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    (hbinary : ∀ job, processing job = 0 ∨ processing job = 2) :
    let m := (Finset.univ.filter fun job => processing job = 2).card
    expectedRandomOptimizeCost processing =
      (n + 1 : ℝ) * ((n : ℝ) + 2 * m) / 2 := by
  dsimp
  rw [expectedRandomOptimizeCost_eq hn]
  have hsum : (∑ job, processing job) =
      2 * (Finset.univ.filter fun job => processing job = 2).card := by
    calc
      (∑ job, processing job) =
          ∑ job, if processing job = 2 then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro job _
        rcases hbinary job with hzero | htwo
        · simp [hzero]
        · simp [htwo]
      _ = 2 * (Finset.univ.filter fun job => processing job = 2).card := by
        rw [← Finset.sum_filter]
        simp
        ring
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hsum]
  ring

/-- Public form of `thm:bo-det-not-instance-optimal`: the comparison value is
the cost of an actual announced finite-seed policy (uniform random
`OptimizeAll`) or the deterministic `Raw` policy, whichever is smaller. -/
theorem no_deterministic_instance_optimal
    {strategy : Strategy n} (hn : 0 < n) (heven : Even n)
    (hcomplete : CompletesAll 2 strategy) :
    ∃ processing : Fin n → ℝ,
      (∀ job, processing job = 0 ∨ processing job = 2) ∧
      runCost 2 processing strategy n ≥
        min (expectedRandomOptimizeCost processing)
          ((n : ℝ) * (n + 1)) + (n : ℝ) ^ 2 / 8 := by
  rcases deterministic_instance_gap heven hcomplete with
    ⟨processing, hbinary, hgap⟩
  refine ⟨processing, hbinary, ?_⟩
  let m := (Finset.univ.filter fun job => processing job = 2).card
  have hopt := expectedRandomOptimizeCost_binary hn processing hbinary
  dsimp [m] at hopt
  dsimp at hgap
  by_cases hbranch : m ≤ n / 2
  · rw [if_pos hbranch] at hgap
    rw [hopt]
    linarith [min_le_left
      ((n + 1 : ℝ) * ((n : ℝ) + 2 * m) / 2)
      ((n : ℝ) * (n + 1))]
  · rw [if_neg hbranch] at hgap
    linarith [min_le_right (expectedRandomOptimizeCost processing)
      ((n : ℝ) * (n + 1))]


end

end Adversary
end BlindOptimization
end SchedulingPaper
