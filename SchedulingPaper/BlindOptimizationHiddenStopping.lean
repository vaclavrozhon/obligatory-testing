import SchedulingPaper.BlindOptimizationReplay
import SchedulingPaper.BlindOptimizationDeterministicLower
import SchedulingPaper.BlindOptimizationDeterministicUpper
import Mathlib.Tactic

/-!
# Raw-safe hidden stopping for blind optimization

Before the line `L ≥ α (n-v)` is crossed, each optimized block receives
the long value `u`; afterwards it receives zero.  Raw blocks never query the
oracle.  Generic replay freezes the completed interaction to a single fixed
binary labeled input.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace HiddenStopping

open Online
open Replay

noncomputable section
attribute [local instance] Classical.propDecidable

def rawCount : Transcript n → ℕ
  | [] => 0
  | .rawCompleted _ :: rest => rawCount rest + 1
  | .optimizedCompleted _ _ :: rest => rawCount rest

def longCount (u : ℝ) : Transcript n → ℕ
  | [] => 0
  | .rawCompleted _ :: rest => longCount u rest
  | .optimizedCompleted _ p :: rest =>
      (if p = u then 1 else 0) + longCount u rest

theorem rawCount_append (left right : Transcript n) :
    rawCount (left ++ right) = rawCount left + rawCount right := by
  induction left with
  | nil => simp [rawCount]
  | cons observation left ih =>
      cases observation <;> simp [rawCount, ih, Nat.add_comm, Nat.add_left_comm]

theorem longCount_append (u : ℝ) (left right : Transcript n) :
    longCount u (left ++ right) = longCount u left + longCount u right := by
  induction left with
  | nil => simp [longCount]
  | cons observation left ih =>
      cases observation with
      | rawCompleted job => simp [longCount, ih]
      | optimizedCompleted job p =>
          by_cases hp : p = u <;>
            simp [longCount, hp, ih, Nat.add_comm, Nat.add_left_comm]

def surplus (n : ℕ) (u alpha : ℝ) (transcript : Transcript n) : ℝ :=
  longCount u transcript - alpha * (n - rawCount transcript)

def Crossed (n : ℕ) (u alpha : ℝ) (transcript : Transcript n) : Prop :=
  0 < longCount u transcript ∧ 0 ≤ surplus n u alpha transcript

def oracle (n : ℕ) (u alpha : ℝ) : Replay.Oracle n :=
  fun transcript _job ↦ if Crossed n u alpha transcript then 0 else u

theorem oracle_binary (n : ℕ) (u alpha : ℝ)
    (transcript : Transcript n) (job : Fin n) :
    oracle n u alpha transcript job = 0 ∨
      oracle n u alpha transcript job = u := by
  unfold oracle
  split <;> simp

theorem oracle_admissible (n : ℕ) {u alpha : ℝ} (hu0 : 0 ≤ u) :
    (oracle n u alpha).Admissible u := by
  intro transcript job
  rcases oracle_binary n u alpha transcript job with h | h <;>
    rw [h] <;> exact ⟨by positivity, by linarith⟩

def AssignmentBinary (u : ℝ) (assignment : Replay.PartialAssignment n) : Prop :=
  ∀ job p, assignment job = some p → p = 0 ∨ p = u

theorem assignmentAfter_binary
    {u alpha : ℝ} (config : Config n)
    (assignment : Replay.PartialAssignment n) (action : Action n)
    (hassignment : AssignmentBinary u assignment) :
    AssignmentBinary u
      (Replay.assignmentAfter (oracle n u alpha) config assignment action) := by
  intro job p hjob
  cases hmode : action.mode with
  | raw =>
      exact hassignment job p (by
        simpa [Replay.assignmentAfter, hmode] using hjob)
  | optimized =>
      by_cases heq : job = action.job
      · subst job
        have hp : Replay.adaptiveValue (oracle n u alpha) assignment
            config.transcript action.job = p := by
          simpa [Replay.assignmentAfter, hmode] using hjob
        cases hassigned : assignment action.job with
        | none =>
            rw [Replay.adaptiveValue, hassigned] at hp
            simpa [← hp] using oracle_binary n u alpha config.transcript action.job
        | some q =>
            rw [Replay.adaptiveValue, hassigned] at hp
            simpa [← hp] using hassignment action.job q hassigned
      · exact hassignment job p (by
          simpa [Replay.assignmentAfter, hmode, Function.update, heq] using hjob)

theorem adaptiveStep_binary
    {u alpha : ℝ} (config next : Config n)
    (assignment nextAssignment : Replay.PartialAssignment n)
    (action : Action n) (hassignment : AssignmentBinary u assignment)
    (hstep : Replay.adaptiveStep (oracle n u alpha) config assignment action =
      some (next, nextAssignment)) :
    AssignmentBinary u nextAssignment := by
  unfold Replay.adaptiveStep at hstep
  cases hbase : config.step
      (Replay.adaptiveProcessing (oracle n u alpha) assignment config.transcript)
      action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_binary config assignment action hassignment

theorem runAdaptiveFuel_binary
    {u alpha : ℝ} (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : Replay.PartialAssignment n)
    (hassignment : AssignmentBinary u assignment) :
    AssignmentBinary u
      (Replay.runAdaptiveFuel (oracle n u alpha) strategy fuel
        config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero => simpa [Replay.runAdaptiveFuel] using hassignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [Replay.runAdaptiveFuel, haction] using hassignment
      | some action =>
          cases hstep : Replay.adaptiveStep (oracle n u alpha)
              config assignment action with
          | none =>
              simpa [Replay.runAdaptiveFuel, haction, hstep] using hassignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext := adaptiveStep_binary config next assignment
                nextAssignment action hassignment hstep
              simpa [Replay.runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

def frozenProcessing (n : ℕ) (u alpha : ℝ)
    (strategy : Strategy n) : Fin n → ℝ :=
  Replay.frozenProcessing (oracle n u alpha) strategy (fun _ ↦ 0) n

theorem frozenProcessing_binary
    (n : ℕ) (u alpha : ℝ) (strategy : Strategy n) (job : Fin n) :
    frozenProcessing n u alpha strategy job = 0 ∨
      frozenProcessing n u alpha strategy job = u := by
  unfold frozenProcessing Replay.frozenProcessing Replay.completeAssignment
  cases hjob : (Replay.adaptiveRun (oracle n u alpha) strategy n).assigned job with
  | none => simp
  | some p =>
      have hbinary := runAdaptiveFuel_binary (u := u) (alpha := alpha)
        strategy n (Config.initial n) Replay.emptyAssignment (by
          intro other q h
          simp [Replay.emptyAssignment] at h)
      simpa [Replay.adaptiveRun, hjob] using hbinary job p hjob

theorem frozenProcessing_admissible
    (n : ℕ) {u alpha : ℝ} (hu0 : 0 ≤ u) (strategy : Strategy n) :
    ∀ job, frozenProcessing n u alpha strategy job ∈ Set.Icc (0 : ℝ) u := by
  intro job
  rcases frozenProcessing_binary n u alpha strategy job with h | h <;>
    rw [h] <;> exact ⟨by positivity, by linarith⟩

theorem replay_fixed_binary
    (n : ℕ) (u alpha : ℝ) (strategy : Strategy n) :
    Online.run (frozenProcessing n u alpha strategy) strategy n =
      (Replay.adaptiveRun (oracle n u alpha) strategy n).result := by
  exact Replay.replay (oracle n u alpha) strategy (fun _ ↦ 0) n

theorem adaptiveRun_complete_of_completesAll
    (n : ℕ) {u alpha : ℝ} (hu0 : 0 ≤ u)
    {strategy : Strategy n} (hcomplete : CompletesAll u strategy) :
    (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.touched =
      Finset.univ := by
  let processing := frozenProcessing n u alpha strategy
  have hfixed : Completes processing strategy :=
    hcomplete processing (frozenProcessing_admissible n hu0 strategy)
  have hreplay := replay_fixed_binary n u alpha strategy
  unfold Completes at hfixed
  rw [hreplay] at hfixed
  exact hfixed

/-! ## Generated traces and the first crossing -/

inductive Generated (n : ℕ) (u alpha : ℝ) : Transcript n → Prop
  | nil : Generated n u alpha []
  | raw {transcript : Transcript n} (h : Generated n u alpha transcript)
      (job : Fin n) :
      Generated n u alpha (transcript ++ [.rawCompleted job])
  | optimized {transcript : Transcript n}
      (h : Generated n u alpha transcript) (job : Fin n) :
      Generated n u alpha
        (transcript ++ [.optimizedCompleted job (oracle n u alpha transcript job)])

def SupportedByTouched (assignment : Replay.PartialAssignment n)
    (config : Config n) : Prop :=
  ∀ job p, assignment job = some p → job ∈ config.touched

theorem adaptiveStep_supportedByTouched
    (config next : Config n)
    (assignment nextAssignment : Replay.PartialAssignment n)
    (action : Action n)
    (hsupported : SupportedByTouched assignment config)
    (hstep : Replay.adaptiveStep (oracle n u alpha) config assignment action =
      some (next, nextAssignment)) :
    SupportedByTouched nextAssignment next := by
  unfold Replay.adaptiveStep at hstep
  cases hbase : config.step
      (Replay.adaptiveProcessing (oracle n u alpha) assignment config.transcript)
      action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      have hfresh : action.job ∉ config.touched := by
        intro hmem
        simp [Config.step, hmem] at hbase
      intro job p hjob
      cases hmode : action.mode with
      | raw =>
          have hnext : next.touched = insert action.job config.touched := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.rawCompleted action.job]⟩ := by
              simpa [Config.step, hfresh, hmode] using hbase.symm
            rw [this]
          have hold : assignment job = some p := by
            simpa [Replay.assignmentAfter, hmode] using hjob
          have hmem := hsupported job p hold
          rw [hnext]
          exact Finset.mem_insert_of_mem hmem
      | optimized =>
          have hnext : next.touched = insert action.job config.touched := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.optimizedCompleted action.job
                  (Replay.adaptiveValue (oracle n u alpha) assignment
                    config.transcript action.job)]⟩ := by
              simpa [Config.step, hfresh, hmode, Replay.adaptiveProcessing] using
                hbase.symm
            rw [this]
          by_cases heq : job = action.job
          · subst job
            rw [hnext]
            simp
          · have hold : assignment job = some p := by
              simpa [Replay.assignmentAfter, hmode, Function.update, heq] using hjob
            have hmem := hsupported job p hold
            rw [hnext]
            exact Finset.mem_insert_of_mem hmem

theorem adaptiveStep_generated
    (config next : Config n)
    (assignment nextAssignment : Replay.PartialAssignment n)
    (action : Action n)
    (hgenerated : Generated n u alpha config.transcript)
    (hsupported : SupportedByTouched assignment config)
    (hstep : Replay.adaptiveStep (oracle n u alpha) config assignment action =
      some (next, nextAssignment)) :
    Generated n u alpha next.transcript := by
  unfold Replay.adaptiveStep at hstep
  cases hbase : config.step
      (Replay.adaptiveProcessing (oracle n u alpha) assignment config.transcript)
      action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      have hfresh : action.job ∉ config.touched := by
        intro hmem
        simp [Config.step, hmem] at hbase
      cases hmode : action.mode with
      | raw =>
          have hnext : next.transcript =
              config.transcript ++ [.rawCompleted action.job] := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.rawCompleted action.job]⟩ := by
              simpa [Config.step, hfresh, hmode] using hbase.symm
            rw [this]
          rw [hnext]
          exact Generated.raw hgenerated action.job
      | optimized =>
          have hunassigned : assignment action.job = none := by
            cases hassigned : assignment action.job with
            | none => rfl
            | some p => exact (hfresh (hsupported action.job p hassigned)).elim
          have hvalue : Replay.adaptiveValue (oracle n u alpha) assignment
              config.transcript action.job = oracle n u alpha config.transcript action.job := by
            simp [Replay.adaptiveValue, hunassigned]
          have hnext : next.transcript =
              config.transcript ++ [.optimizedCompleted action.job
                (oracle n u alpha config.transcript action.job)] := by
            have : next = ⟨insert action.job config.touched,
                config.transcript ++ [.optimizedCompleted action.job
                  (oracle n u alpha config.transcript action.job)]⟩ := by
              simpa [Config.step, hfresh, hmode, Replay.adaptiveProcessing,
                hvalue] using hbase.symm
            rw [this]
          rw [hnext]
          exact Generated.optimized hgenerated action.job

theorem runAdaptiveFuel_generated_supported
    (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : Replay.PartialAssignment n)
    (hgenerated : Generated n u alpha config.transcript)
    (hsupported : SupportedByTouched assignment config) :
    Generated n u alpha
        (Replay.runAdaptiveFuel (oracle n u alpha) strategy fuel
          config assignment).result.config.transcript ∧
      SupportedByTouched
        (Replay.runAdaptiveFuel (oracle n u alpha) strategy fuel
          config assignment).assigned
        (Replay.runAdaptiveFuel (oracle n u alpha) strategy fuel
          config assignment).result.config := by
  induction fuel generalizing config assignment with
  | zero => simpa [Replay.runAdaptiveFuel] using And.intro hgenerated hsupported
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [Replay.runAdaptiveFuel, haction] using
            And.intro hgenerated hsupported
      | some action =>
          cases hstep : Replay.adaptiveStep (oracle n u alpha)
              config assignment action with
          | none =>
              simpa [Replay.runAdaptiveFuel, haction, hstep] using
                And.intro hgenerated hsupported
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hgenNext := adaptiveStep_generated config next assignment
                nextAssignment action hgenerated hsupported hstep
              have hsupNext := adaptiveStep_supportedByTouched config next
                assignment nextAssignment action hsupported hstep
              simpa [Replay.runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hgenNext hsupNext

theorem adaptiveRun_generated (strategy : Strategy n) :
    Generated n u alpha
      (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript := by
  exact (runAdaptiveFuel_generated_supported strategy n (Config.initial n)
    Replay.emptyAssignment Generated.nil (by
      intro job p h
      simp [Replay.emptyAssignment] at h)).1

theorem surplus_append_raw
    (transcript : Transcript n) (job : Fin n) :
    surplus n u alpha (transcript ++ [.rawCompleted job]) =
      surplus n u alpha transcript + alpha := by
  unfold surplus
  rw [rawCount_append, longCount_append]
  simp [rawCount, longCount]
  ring

theorem surplus_append_long
    (transcript : Transcript n) (job : Fin n) :
    surplus n u alpha (transcript ++ [.optimizedCompleted job u]) =
      surplus n u alpha transcript + 1 := by
  unfold surplus
  rw [rawCount_append, longCount_append]
  simp [rawCount, longCount]
  ring

theorem surplus_append_zero
    (transcript : Transcript n) (job : Fin n) (hu0 : 0 < u) :
    surplus n u alpha (transcript ++ [.optimizedCompleted job 0]) =
      surplus n u alpha transcript := by
  unfold surplus
  rw [rawCount_append, longCount_append]
  simp [rawCount, longCount, ne_of_lt hu0]

theorem Generated.all_optimized_long_of_not_crossed
    {transcript : Transcript n} (hu0 : 0 < u) (ha0 : 0 ≤ alpha)
    (hgenerated : Generated n u alpha transcript)
    (hnot : ¬ Crossed n u alpha transcript) :
    ∀ job p, Observation.optimizedCompleted job p ∈ transcript → p = u := by
  induction hgenerated with
  | nil => simp
  | @raw prior hprior actionJob ih =>
      have hpriorNot : ¬ Crossed n u alpha prior := by
        intro hcross
        apply hnot
        constructor
        · simpa [longCount_append, longCount] using hcross.1
        · rw [surplus_append_raw]
          linarith [hcross.2]
      intro job p hmem
      rw [List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact ih hpriorNot job p hold
      · simp at hnew
  | @optimized prior hprior actionJob ih =>
      have hpriorNot : ¬ Crossed n u alpha prior := by
        intro hcross
        have horacle : oracle n u alpha prior actionJob = 0 := by
          simp [oracle, hcross]
        apply hnot
        constructor
        · simpa [longCount_append, longCount, horacle, ne_of_lt hu0] using
            hcross.1
        · rw [horacle, surplus_append_zero prior actionJob hu0]
          exact hcross.2
      have horacle : oracle n u alpha prior actionJob = u := by
        simp [oracle, hpriorNot]
      intro job p hmem
      rw [List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact ih hpriorNot job p hold
      · simp only [List.mem_singleton] at hnew
        injection hnew with _ hp
        exact hp.trans horacle

def FirstCrossing (n : ℕ) (u alpha : ℝ)
    (transcript : Transcript n) : Prop :=
  ∃ before suffix : Transcript n, ∃ observation : Observation n,
    transcript = before ++ observation :: suffix ∧
    Generated n u alpha before ∧
    Generated n u alpha (before ++ [observation]) ∧
    ¬ Crossed n u alpha before ∧
    Crossed n u alpha (before ++ [observation]) ∧
    ((∃ job, observation = .rawCompleted job) ∨
      (∃ job, observation = .optimizedCompleted job u)) ∧
    longCount u transcript = longCount u (before ++ [observation])

theorem Generated.firstCrossing_of_crossed
    {transcript : Transcript n} (hn : 0 < n) (hu0 : 0 < u)
    (ha0 : 0 ≤ alpha) (haPos : 0 < alpha)
    (hgenerated : Generated n u alpha transcript)
    (hcrossed : Crossed n u alpha transcript) :
    FirstCrossing n u alpha transcript := by
  induction hgenerated with
  | nil =>
      simpa [Crossed, longCount] using hcrossed.1
  | @raw prior hprior job ih =>
      by_cases hpriorCrossed : Crossed n u alpha prior
      · obtain ⟨before, after, observation, hsplit, hgenBefore, hgenAt,
          hbefore, hat, hkind, hlong⟩ :=
          ih hpriorCrossed
        refine ⟨before, after ++ [.rawCompleted job], observation, ?_,
          hgenBefore, hgenAt, hbefore, hat, hkind, ?_⟩
        rw [hsplit]
        simp [List.append_assoc]
        simpa [longCount_append, longCount] using hlong
      · refine ⟨prior, [], .rawCompleted job, by simp,
          hprior, Generated.raw hprior job, hpriorCrossed, hcrossed,
          Or.inl ⟨job, rfl⟩, rfl⟩
  | @optimized prior hprior job ih =>
      by_cases hpriorCrossed : Crossed n u alpha prior
      · obtain ⟨before, after, observation, hsplit, hgenBefore, hgenAt,
          hbefore, hat, hkind, hlong⟩ :=
          ih hpriorCrossed
        refine ⟨before,
          after ++ [.optimizedCompleted job (oracle n u alpha prior job)],
          observation, ?_, hgenBefore, hgenAt, hbefore, hat, hkind, ?_⟩
        rw [hsplit]
        simp [List.append_assoc]
        have horacle : oracle n u alpha prior job = 0 := by
          simp [oracle, hpriorCrossed]
        rw [longCount_append]
        simp [longCount, horacle, ne_of_lt hu0, hlong]
      · have horacle : oracle n u alpha prior job = u := by
          simp [oracle, hpriorCrossed]
        refine ⟨prior, [], .optimizedCompleted job u, ?_,
          hprior, ?_, hpriorCrossed, ?_, Or.inr ⟨job, rfl⟩, ?_⟩
        · simp [horacle]
        · simpa [horacle] using Generated.optimized hprior job
        · simpa [horacle] using hcrossed
        · simp [horacle]

theorem firstCrossing_long_overshoot
    {before : Transcript n} {job : Fin n} {u alpha : ℝ}
    (haPos : 0 < alpha)
    (hbefore : ¬ Crossed n u alpha before)
    (hafter : Crossed n u alpha
      (before ++ [.optimizedCompleted job u]))
    (hremaining : 0 < (n : ℝ) - rawCount before) :
    let y := ((longCount u before : ℝ) + 1) /
      ((n : ℝ) - rawCount before)
    0 ≤ y - alpha ∧
      y - alpha < 1 / ((n : ℝ) - rawCount before) := by
  dsimp only
  have hpre : surplus n u alpha before < 0 := by
    by_cases hlong : 0 < longCount u before
    · exact lt_of_not_ge (fun hs ↦ hbefore ⟨hlong, hs⟩)
    · have hzero : longCount u before = 0 := Nat.eq_zero_of_not_pos hlong
      unfold surplus
      rw [hzero]
      norm_num
      nlinarith
  have hpost : 0 ≤ surplus n u alpha before + 1 := by
    rw [← surplus_append_long before job]
    exact hafter.2
  let S : ℝ := (n : ℝ) - rawCount before
  let L : ℝ := longCount u before
  have hS : 0 < S := hremaining
  have hpre' : L - alpha * S < 0 := by
    simpa [surplus, S, L] using hpre
  have hpost' : 0 ≤ L + 1 - alpha * S := by
    have : 0 ≤ L - alpha * S + 1 := by
      simpa [surplus, S, L] using hpost
    linarith
  have hid : (L + 1) / S - alpha = (L + 1 - alpha * S) / S := by
    field_simp [hS.ne']
  constructor
  · rw [hid]
    exact div_nonneg hpost' hS.le
  · rw [hid, div_lt_div_iff_of_pos_right hS]
    linarith

theorem firstCrossing_raw_overshoot
    {before : Transcript n} {job : Fin n} {u alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hbefore : ¬ Crossed n u alpha before)
    (hafter : Crossed n u alpha (before ++ [.rawCompleted job]))
    (hremaining : 0 < (n : ℝ) - ((rawCount before : ℝ) + 1)) :
    let y := (longCount u before : ℝ) /
      ((n : ℝ) - ((rawCount before : ℝ) + 1))
    0 ≤ y - alpha ∧
      y - alpha <
        1 / ((n : ℝ) - ((rawCount before : ℝ) + 1)) := by
  dsimp only
  have hlongBefore : 0 < longCount u before := by
    simpa [longCount_append, longCount] using hafter.1
  have hpre : surplus n u alpha before < 0 :=
    lt_of_not_ge (fun hs ↦ hbefore ⟨hlongBefore, hs⟩)
  have hpost : 0 ≤ surplus n u alpha before + alpha := by
    rw [← surplus_append_raw before job]
    exact hafter.2
  let S : ℝ := (n : ℝ) - ((rawCount before : ℝ) + 1)
  let L : ℝ := longCount u before
  have hS : 0 < S := hremaining
  have hbeforeDen : (n : ℝ) - rawCount before = S + 1 := by
    dsimp [S]
    ring
  have hpre' : L - alpha * (S + 1) < 0 := by
    unfold surplus at hpre
    rw [hbeforeDen] at hpre
    simpa [L] using hpre
  have hpost' : 0 ≤ L - alpha * S := by
    have hre : surplus n u alpha before + alpha = L - alpha * S := by
      unfold surplus
      rw [hbeforeDen]
      dsimp [L]
      ring
    rw [← hre]
    exact hpost
  have hstrict : L - alpha * S < 1 := by nlinarith
  have hid : L / S - alpha = (L - alpha * S) / S := by
    field_simp [hS.ne']
  constructor
  · rw [hid]
    exact div_nonneg hpost' hS.le
  · rw [hid, div_lt_div_iff_of_pos_right hS]
    exact hstrict

/-! ## Completion-cost accounting at the crossing -/

theorem duration_mem_two_values_of_all_long
    {transcript : Transcript n} {u : ℝ}
    (hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript → p = u)
    {duration : ℝ}
    (hmem : duration ∈ transcript.map (Observation.duration u)) :
    duration = u ∨ duration = 1 + u := by
  rcases List.mem_map.mp hmem with ⟨observation, hobservation, rfl⟩
  cases observation with
  | rawCompleted job => simp [Observation.duration]
  | optimizedCompleted job p =>
      right
      simp [Observation.duration, hall job p hobservation]

theorem duration_count_raw_of_all_long
    {transcript : Transcript n} {u : ℝ}
    (hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript → p = u) :
    (transcript.map (Observation.duration u)).count u = rawCount transcript := by
  induction transcript with
  | nil => simp [rawCount]
  | cons observation rest ih =>
      have hrest : ∀ job p,
          Observation.optimizedCompleted job p ∈ rest → p = u := by
        intro job p hmem
        exact hall job p (by simp [hmem])
      cases observation with
      | rawCompleted job =>
          simpa [Observation.duration, rawCount] using ih hrest
      | optimizedCompleted job p =>
          have hp := hall job p (by simp)
          have hne : 1 + u ≠ u := by linarith
          simpa [Observation.duration, rawCount, hp, hne] using ih hrest

theorem duration_count_long_of_all_long
    {transcript : Transcript n} {u : ℝ}
    (hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript → p = u) :
    (transcript.map (Observation.duration u)).count (1 + u) =
      longCount u transcript := by
  induction transcript with
  | nil => simp [longCount]
  | cons observation rest ih =>
      have hrest : ∀ job p,
          Observation.optimizedCompleted job p ∈ rest → p = u := by
        intro job p hmem
        exact hall job p (by simp [hmem])
      cases observation with
      | rawCompleted job =>
          have hne : u ≠ 1 + u := by linarith
          simpa [Observation.duration, longCount, hne] using ih hrest
      | optimizedCompleted job p =>
          have hp := hall job p (by simp)
          simpa [Observation.duration, longCount, hp, Nat.add_comm] using ih hrest

theorem rawCount_add_longCount_eq_length_of_all_long
    {transcript : Transcript n} {u : ℝ}
    (hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript → p = u) :
    rawCount transcript + longCount u transcript = transcript.length := by
  induction transcript with
  | nil => simp [rawCount, longCount]
  | cons observation rest ih =>
      have hrest : ∀ job p,
          Observation.optimizedCompleted job p ∈ rest → p = u := by
        intro job p hmem
        exact hall job p (by simp [hmem])
      have hih := ih hrest
      cases observation with
      | rawCompleted job => simp [rawCount, longCount]; omega
      | optimizedCompleted job p =>
          have hp := hall job p (by simp)
          simp [rawCount, longCount, hp]
          omega

theorem crossing_duration_perm
    {transcript : Transcript n} {u : ℝ}
    (hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript → p = u) :
    (transcript.map (Observation.duration u)).Perm
      (List.replicate (rawCount transcript) u ++
        List.replicate (longCount u transcript) (1 + u)) := by
  let durations := transcript.map (Observation.duration u)
  have hne : u ≠ 1 + u := by linarith
  apply (List.perm_replicate_append_replicate hne).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [durations] using duration_count_raw_of_all_long hall
  · simpa [durations] using duration_count_long_of_all_long hall
  · intro duration hmem
    rcases duration_mem_two_values_of_all_long hall
      (by simpa [durations] using hmem) with h | h
    · simp [h]
    · simp [h]

theorem pairwise_crossing_sorted (u : ℝ) (v ell : ℕ) :
    (List.replicate v u ++ List.replicate ell (1 + u)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  simp

theorem prefixCost_replicate_one_le
    (values : List ℝ) (hvalues : ∀ x ∈ values, (1 : ℝ) ≤ x) :
    prefixCost (List.replicate values.length 1) ≤ prefixCost values := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      have hx : 1 ≤ x := hvalues x (by simp)
      have hxs : ∀ y ∈ xs, (1 : ℝ) ≤ y := by
        intro y hy
        exact hvalues y (by simp [hy])
      have htail := ih hxs
      simp only [List.length_cons, List.replicate_succ, prefixCost_cons,
        List.length_replicate] at htail ⊢
      have hcoef : 0 ≤ (xs.length + 1 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hx hcoef]

theorem Generated.duration_ge_one
    {transcript : Transcript n} {u alpha : ℝ} (hu : 1 ≤ u)
    (hgenerated : Generated n u alpha transcript) :
    ∀ duration ∈ transcript.map (Observation.duration u),
      (1 : ℝ) ≤ duration := by
  induction hgenerated with
  | nil => simp
  | @raw prior hprior job ih =>
      intro duration hmem
      rw [List.map_append, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact ih duration hold
      · simp [Observation.duration] at hnew
        linarith
  | @optimized prior hprior job ih =>
      intro duration hmem
      rw [List.map_append, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact ih duration hold
      · simp [Observation.duration] at hnew
        rcases oracle_binary n u alpha prior job with horacle | horacle <;>
          rw [horacle] at hnew <;> linarith

/-- Pure list form of the exchange at the crossing.  Only the completed
prefix is sorted; future blocks remain after it and are relaxed to unit
length. -/
theorem prefixCost_crossing_lower
    {full crossing suffix : Transcript n} {u alpha : ℝ}
    (hu : 1 ≤ u)
    (hsplit : full = crossing ++ suffix)
    (hfullLength : full.length = n)
    (hfullGenerated : Generated n u alpha full)
    (hallCrossing : ∀ job p,
      Observation.optimizedCompleted job p ∈ crossing → p = u) :
    let v : ℝ := rawCount crossing
    let ell : ℝ := longCount u crossing
    prefixCost (full.map (Observation.duration u)) ≥
      stoppingAlgorithmCost u n v ell := by
  dsimp only
  let crossingDurations := crossing.map (Observation.duration u)
  let suffixDurations := suffix.map (Observation.duration u)
  let vN := rawCount crossing
  let ellN := longCount u crossing
  have hcountLength : vN + ellN = crossing.length := by
    exact rawCount_add_longCount_eq_length_of_all_long hallCrossing
  have hperm : crossingDurations.Perm
      (List.replicate vN u ++ List.replicate ellN (1 + u)) := by
    exact crossing_duration_perm hallCrossing
  have hpast := pairwise_prefixCost_minimal
    (pairwise_crossing_sorted u vN ellN) hperm.symm
  have hpastSum : crossingDurations.sum =
      u * vN + (1 + u) * ellN := by
    rw [hperm.sum_eq]
    simp [mul_comm]
    ring
  have hsuffixValues : ∀ x ∈ suffixDurations, (1 : ℝ) ≤ x := by
    intro x hx
    apply hfullGenerated.duration_ge_one hu x
    rw [hsplit, List.map_append, List.mem_append]
    exact Or.inr (by simpa [suffixDurations] using hx)
  have hsuffixPrefix := prefixCost_replicate_one_le
    suffixDurations hsuffixValues
  have hsuffixSum : (suffixDurations.length : ℝ) ≤ suffixDurations.sum := by
    calc
      (suffixDurations.length : ℝ) =
          (suffixDurations.map fun _ ↦ (1 : ℝ)).sum := by simp
      _ ≤ suffixDurations.sum := by
        simpa using (List.sum_le_sum fun x hx ↦ hsuffixValues x hx)
  have htotal : crossing.length + suffix.length = n := by
    calc
      crossing.length + suffix.length = (crossing ++ suffix).length := by simp
      _ = full.length := congrArg List.length hsplit.symm
      _ = n := hfullLength
  have hlengthSuffix : suffix.length = n - crossing.length := by
    omega
  have hcrossLe : crossing.length ≤ n := by omega
  rw [hsplit, List.map_append, prefixCost_append]
  dsimp [crossingDurations, suffixDurations] at hpast hpastSum hsuffixPrefix hsuffixSum
  rw [List.length_map, hlengthSuffix] at hsuffixPrefix hsuffixSum ⊢
  rw [prefixCost_replicate_eq] at hsuffixPrefix
  rw [prefixCost_append, prefixCost_replicate_eq, prefixCost_replicate_eq] at hpast
  simp only [List.length_replicate, List.sum_replicate, nsmul_eq_mul] at hpast
  rw [Nat.cast_sub hcrossLe] at hsuffixPrefix hsuffixSum ⊢
  have hcastLength : (crossing.length : ℝ) = vN + ellN := by
    exact_mod_cast hcountLength.symm
  rw [hcastLength]
  dsimp [vN, ellN]
  unfold stoppingAlgorithmCost
  dsimp only
  nlinarith [hpastSum]

theorem frozen_indicator_sum_eq_longCount
    {transcript : Transcript n} {u : ℝ} (hu0 : 0 < u)
    (processing : Fin n → ℝ)
    (hoptimized : ∀ job p,
      Observation.optimizedCompleted job p ∈ transcript →
        processing job = p)
    (hraw : ∀ job, Observation.rawCompleted job ∈ transcript →
      processing job = 0) :
    ((transcript.map Observation.job).map fun job ↦
      if processing job = u then 1 else 0).sum = longCount u transcript := by
  induction transcript with
  | nil => simp [longCount]
  | cons observation rest ih =>
      have hoptimizedRest : ∀ job p,
          Observation.optimizedCompleted job p ∈ rest →
            processing job = p := by
        intro job p hmem
        exact hoptimized job p (by simp [hmem])
      have hrawRest : ∀ job, Observation.rawCompleted job ∈ rest →
          processing job = 0 := by
        intro job hmem
        exact hraw job (by simp [hmem])
      have hih := ih hoptimizedRest hrawRest
      simp only [List.map_map] at hih ⊢
      cases observation with
      | rawCompleted job =>
          have hp := hraw job (by simp)
          have hne : (0 : ℝ) ≠ u := ne_of_lt hu0
          simpa [Observation.job, longCount, hp, hne] using hih
      | optimizedCompleted job p =>
          have hp := hoptimized job p (by simp)
          by_cases hpu : p = u
          · simp [Observation.job, longCount, hp, hpu, hih]
          · simp [Observation.job, longCount, hp, hpu, hih]

theorem frozen_long_card_eq_longCount
    (n : ℕ) {u alpha : ℝ} (hu0 : 0 < u)
    {strategy : Strategy n} (hcomplete : CompletesAll u strategy) :
    let full :=
      (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
    (Finset.univ.filter fun job ↦
      frozenProcessing n u alpha strategy job = u).card =
        longCount u full := by
  dsimp only
  let full :=
    (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
  let processing := frozenProcessing n u alpha strategy
  have hfixed : Completes processing strategy :=
    hcomplete processing (frozenProcessing_admissible n hu0.le strategy)
  have hlabels := Online.full_label_permutation hfixed
  have hreplay := replay_fixed_binary n u alpha strategy
  dsimp [processing, full] at hlabels hreplay ⊢
  rw [hreplay] at hlabels
  have hinv := Online.run_historyInvariant processing strategy n
  rw [hreplay] at hinv
  have hraw : ∀ job,
      Observation.rawCompleted job ∈
        (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript →
      processing job = 0 := by
    intro job hrawMem
    apply Replay.frozenProcessing_eq_default_of_not_optimized
    rintro ⟨p, hoptMem⟩
    have heq := List.inj_on_of_nodup_map hinv.nodup
      hrawMem hoptMem rfl
    contradiction
  have hoptimized : ∀ job p,
      Observation.optimizedCompleted job p ∈
        (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript →
      processing job = p := by
    intro job p hmem
    exact Replay.frozenProcessing_eq_of_optimized
      (oracle n u alpha) strategy (fun _ ↦ 0) n hmem
  let indicator : Fin n → ℕ := fun job ↦
    if processing job = u then 1 else 0
  have hsumTranscript := frozen_indicator_sum_eq_longCount hu0 processing
    hoptimized hraw
  calc
    (Finset.univ.filter fun job ↦ processing job = u).card =
        ∑ job, indicator job := by simp [indicator]
    _ = (List.ofFn indicator).sum := by rw [List.sum_ofFn]
    _ = (((Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript.map
          Observation.job).map indicator).sum := by
      simpa [List.map_ofFn] using (hlabels.map indicator).sum_eq.symm
    _ = longCount u
        (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript := by
      simpa [indicator, List.map_map] using hsumTranscript

theorem offlineCost_binary_eq_stoppingOffline
    {n : ℕ} {u : ℝ} (hu : 1 < u) (processing : Fin n → ℝ)
    (hbinary : ∀ job, processing job = 0 ∨ processing job = u) :
    let m := (Finset.univ.filter fun job ↦ processing job = u).card
    Online.offlineCost u processing = stoppingOfflineCost u n m := by
  dsimp only
  let m := (Finset.univ.filter fun job ↦ processing job = u).card
  let indicator : Fin n → ℝ := fun job ↦
    if processing job = u then 1 else 0
  have hsumIndicator : (∑ job, indicator job) = (m : ℝ) := by
    simp [indicator, m]
  have heffective : ∀ job,
      Online.effectiveLength u (processing job) =
        1 + (u - 1) * indicator job := by
    intro job
    rcases hbinary job with hp | hp
    · have hne : (0 : ℝ) ≠ u := by linarith
      simp [Online.effectiveLength, indicator, hp, hne, min_eq_right hu.le]
    · simp [Online.effectiveLength, indicator, hp,
        min_eq_left (by linarith : u ≤ 1 + u)]
  have hmin : ∀ i j,
      min (Online.effectiveLength u (processing i))
          (Online.effectiveLength u (processing j)) =
        1 + (u - 1) * (indicator i * indicator j) := by
    intro i j
    rw [heffective i, heffective j]
    have h0u : (0 : ℝ) ≠ u := ne_of_lt (lt_trans (by norm_num) hu)
    rcases hbinary i with hi | hi <;> rcases hbinary j with hj | hj
    all_goals
      simp [indicator, hi, hj, h0u, min_eq_left hu.le, min_eq_right hu.le]
  have hdoubleIndicator :
      (∑ i, ∑ j, indicator i * indicator j) = (m : ℝ) ^ 2 := by
    calc
      (∑ i, ∑ j, indicator i * indicator j) =
          (∑ i, indicator i) * (∑ j, indicator j) := by
            exact (Fintype.sum_mul_sum indicator indicator).symm
      _ = (m : ℝ) ^ 2 := by rw [hsumIndicator]; ring
  have hsumEffective :
      (∑ job, Online.effectiveLength u (processing job)) =
        n + (u - 1) * m := by
    calc
      (∑ job, Online.effectiveLength u (processing job)) =
          ∑ job, (1 + (u - 1) * indicator job) := by simp_rw [heffective]
      _ = (∑ _job : Fin n, (1 : ℝ)) +
          ∑ job, (u - 1) * indicator job := Finset.sum_add_distrib
      _ = (∑ _job : Fin n, (1 : ℝ)) +
          (u - 1) * (∑ job, indicator job) := by
            rw [Finset.mul_sum]
      _ = n + (u - 1) * m := by rw [hsumIndicator]; simp
  have hdoubleEffective :
      (∑ i, ∑ j, min (Online.effectiveLength u (processing i))
        (Online.effectiveLength u (processing j))) =
        (n : ℝ) ^ 2 + (u - 1) * (m : ℝ) ^ 2 := by
    have hfactor :
        (∑ i, ∑ j, (u - 1) * (indicator i * indicator j)) =
          (u - 1) * (∑ i, ∑ j, indicator i * indicator j) := by
      simp_rw [Finset.mul_sum]
    calc
      (∑ i, ∑ j, min (Online.effectiveLength u (processing i))
          (Online.effectiveLength u (processing j))) =
          ∑ i, ∑ j, (1 + (u - 1) * (indicator i * indicator j)) := by
            simp_rw [hmin]
      _ = (∑ i : Fin n, ∑ _j : Fin n, (1 : ℝ)) +
          (∑ i, ∑ j, (u - 1) * (indicator i * indicator j)) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (n : ℝ) ^ 2 +
          (u - 1) * (∑ i, ∑ j, indicator i * indicator j) := by
            rw [hfactor]
            simp
            ring
      _ = (n : ℝ) ^ 2 + (u - 1) * (m : ℝ) ^ 2 := by
            rw [hdoubleIndicator]
  have htwo := two_mul_pairCost_ofFn
    (fun job : Fin n ↦ Online.effectiveLength u (processing job))
  unfold Online.offlineCost
  unfold stoppingOfflineCost
  rw [hsumEffective, hdoubleEffective] at htwo
  nlinarith

/-! ## Operational hidden-stopping witness -/

/-- If the adaptive hidden-stopping interaction crosses its line, replay
freezes it to one fixed binary input.  The first crossing supplies integral
counts whose literal run cost dominates `stoppingAlgorithmCost`, whose
clairvoyant cost is exactly `stoppingOfflineCost`, and whose normalized long
count lies within one job of the stopping line. -/
theorem crossed_run_witness
    {n : ℕ} (hn : 0 < n) {u alpha : ℝ}
    (hu : 1 < u) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    {strategy : Online.Strategy n} (hcomplete : Online.CompletesAll u strategy)
    (hcrossed :
      let full :=
        (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
      Crossed n u alpha full) :
    let processing := frozenProcessing n u alpha strategy
    ∃ v ell : ℕ,
      v + ell ≤ n ∧ v < n ∧
      Online.runCost u processing strategy n ≥
        stoppingAlgorithmCost u n v ell ∧
      Online.offlineCost u processing = stoppingOfflineCost u n ell ∧
      alpha ≤ (ell : ℝ) / ((n : ℝ) - v) ∧
      (ell : ℝ) / ((n : ℝ) - v) ≤ 1 ∧
      (ell : ℝ) / ((n : ℝ) - v) - alpha ≤
        1 / ((n : ℝ) - v) := by
  dsimp only at hcrossed ⊢
  let full :=
    (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
  let processing := frozenProcessing n u alpha strategy
  have hgenerated : Generated n u alpha full := by
    exact adaptiveRun_generated strategy
  obtain ⟨before, suffix, observation, hsplit, hgenBefore, hgenCrossing,
      hnotCrossed, hatCrossing, hkind, hlongAfter⟩ :=
    hgenerated.firstCrossing_of_crossed hn (by linarith) ha0.le ha0 hcrossed
  let crossing := before ++ [observation]
  let v := rawCount crossing
  let ell := longCount u crossing
  have hfullSplit : full = crossing ++ suffix := by
    simpa [crossing, List.append_assoc] using hsplit
  have hallBefore : ∀ job p,
      Observation.optimizedCompleted job p ∈ before → p = u :=
    hgenBefore.all_optimized_long_of_not_crossed (by linarith) ha0.le hnotCrossed
  have hallCrossing : ∀ job p,
      Observation.optimizedCompleted job p ∈ crossing → p = u := by
    intro job p hmem
    dsimp [crossing] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hbefore | hlast
    · exact hallBefore job p hbefore
    · simp only [List.mem_singleton] at hlast
      rcases hkind with ⟨rawJob, hraw⟩ | ⟨longJob, hlong⟩
      · rw [hraw] at hlast
        simp at hlast
      · have heq := hlast.trans hlong
        injection heq
  have hfixed : Online.Completes processing strategy :=
    hcomplete processing (frozenProcessing_admissible n (by linarith) strategy)
  have hlengthFixed := Online.transcript_length_eq_n_of_completes hfixed
  have hreplay := replay_fixed_binary n u alpha strategy
  have hfullLength : full.length = n := by
    dsimp [full]
    rw [← hreplay]
    exact hlengthFixed
  have hcount : v + ell = crossing.length := by
    exact rawCount_add_longCount_eq_length_of_all_long hallCrossing
  have hcrossingLe : crossing.length ≤ n := by
    have : crossing.length + suffix.length = n := by
      calc
        crossing.length + suffix.length = (crossing ++ suffix).length := by simp
        _ = full.length := congrArg List.length hfullSplit.symm
        _ = n := hfullLength
    omega
  have hvell : v + ell ≤ n := by omega
  have hellPos : 0 < ell := by
    simpa [ell] using hatCrossing.1
  have hvlt : v < n := by omega
  have hremaining : 0 < (n : ℝ) - v := by
    have hvltR : (v : ℝ) < n := by exact_mod_cast hvlt
    linarith
  have hcost : Online.runCost u processing strategy n ≥
      stoppingAlgorithmCost u n v ell := by
    have hpref := prefixCost_crossing_lower hu.le hfullSplit hfullLength
      hgenerated hallCrossing
    unfold Online.runCost Online.completionCost
    rw [hreplay]
    exact hpref
  have hoffline : Online.offlineCost u processing =
      stoppingOfflineCost u n ell := by
    have hoff := offlineCost_binary_eq_stoppingOffline hu processing
      (frozenProcessing_binary n u alpha strategy)
    have hcard := frozen_long_card_eq_longCount (alpha := alpha) n
      (by linarith) hcomplete
    dsimp [processing, full] at hoff hcard hlongAfter ⊢
    rw [hoff, hcard, hlongAfter]
  have hyAlpha : alpha ≤ (ell : ℝ) / ((n : ℝ) - v) := by
    have hsurplus := hatCrossing.2
    have hlinear : alpha * ((n : ℝ) - v) ≤ ell := by
      simpa [surplus, crossing, v, ell] using hsurplus
    exact (le_div_iff₀ hremaining).2 (by simpa [mul_comm] using hlinear)
  have hyOne : (ell : ℝ) / ((n : ℝ) - v) ≤ 1 := by
    rw [div_le_one hremaining]
    have hvellR : (v : ℝ) + ell ≤ n := by exact_mod_cast hvell
    linarith
  have hyOvershoot : (ell : ℝ) / ((n : ℝ) - v) - alpha ≤
      1 / ((n : ℝ) - v) := by
    rcases hkind with ⟨job, hraw⟩ | ⟨job, hlong⟩
    · subst observation
      have hremainingRaw :
          0 < (n : ℝ) - ((rawCount before : ℝ) + 1) := by
        simpa [crossing, v, rawCount_append, rawCount] using hremaining
      have hover := firstCrossing_raw_overshoot ha0.le ha1 hnotCrossed
        hatCrossing hremainingRaw
      simpa [crossing, v, ell, rawCount_append, longCount_append,
        rawCount, longCount] using hover.2.le
    · subst observation
      have hremainingLong : 0 < (n : ℝ) - rawCount before := by
        simpa [crossing, v, rawCount_append, rawCount] using hremaining
      have hover := firstCrossing_long_overshoot ha0 hnotCrossed
        hatCrossing hremainingLong
      simpa [crossing, v, ell, rawCount_append, longCount_append,
        rawCount, longCount] using hover.2.le
  exact ⟨v, ell, hvell, hvlt, hcost, hoffline, hyAlpha, hyOne,
    hyOvershoot⟩

/-- If the stopping line is never crossed, completeness forces the frozen
input to be all zero and the entire interaction to run raw.  Thus both costs
are the corresponding exact triangular costs. -/
theorem uncrossed_run_exact
    {n : ℕ} {u alpha : ℝ} (hu : 1 < u)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    {strategy : Online.Strategy n} (hcomplete : Online.CompletesAll u strategy)
    (hnotCrossed :
      let full :=
        (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
      ¬ Crossed n u alpha full) :
    let processing := frozenProcessing n u alpha strategy
    Online.runCost u processing strategy n = u * n * (n + 1) / 2 ∧
      Online.offlineCost u processing = n * (n + 1) / 2 := by
  dsimp only at hnotCrossed ⊢
  let full :=
    (Replay.adaptiveRun (oracle n u alpha) strategy n).result.config.transcript
  let processing := frozenProcessing n u alpha strategy
  have hgenerated : Generated n u alpha full := adaptiveRun_generated strategy
  have hall : ∀ job p,
      Observation.optimizedCompleted job p ∈ full → p = u :=
    hgenerated.all_optimized_long_of_not_crossed (by linarith) ha0.le hnotCrossed
  have hfixed : Online.Completes processing strategy :=
    hcomplete processing (frozenProcessing_admissible n (by linarith) strategy)
  have hreplay := replay_fixed_binary n u alpha strategy
  have hlength : full.length = n := by
    dsimp [full]
    rw [← hreplay]
    exact Online.transcript_length_eq_n_of_completes hfixed
  have hcount : rawCount full + longCount u full = n := by
    rw [rawCount_add_longCount_eq_length_of_all_long hall, hlength]
  have hlongZero : longCount u full = 0 := by
    by_contra hne
    have hpos : 0 < longCount u full := Nat.pos_of_ne_zero hne
    apply hnotCrossed
    constructor
    · exact hpos
    · unfold surplus
      have hcountR : (rawCount full : ℝ) + longCount u full = n := by
        exact_mod_cast hcount
      have hlongR : (0 : ℝ) < longCount u full := by exact_mod_cast hpos
      nlinarith
  have hrawEq : rawCount full = n := by omega
  have hdurations : full.map (Observation.duration u) =
      List.replicate n u := by
    have hperm := crossing_duration_perm hall
    rw [hrawEq, hlongZero] at hperm
    simpa using (List.perm_replicate.mp (by simpa using hperm))
  have hrun : Online.runCost u processing strategy n =
      u * n * (n + 1) / 2 := by
    unfold Online.runCost Online.completionCost
    rw [hreplay]
    dsimp [full] at hdurations
    rw [hdurations, prefixCost_replicate_eq]
  have hoffline : Online.offlineCost u processing = n * (n + 1) / 2 := by
    have hoff := offlineCost_binary_eq_stoppingOffline hu processing
      (frozenProcessing_binary n u alpha strategy)
    have hcard := frozen_long_card_eq_longCount (alpha := alpha) n
      (by linarith) hcomplete
    dsimp [processing, full] at hoff hcard hlongZero ⊢
    rw [hoff, hcard, hlongZero]
    simp [stoppingOfflineCost]
  exact ⟨hrun, hoffline⟩

end

end HiddenStopping
end BlindOptimization
end SchedulingPaper
