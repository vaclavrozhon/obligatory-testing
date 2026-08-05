import SchedulingPaper.HiddenStopping
import SchedulingPaper.TimedOnline

/-!
# The raw-safe hidden-stopping oracle

This file implements the public-transcript adversary from the paper's
raw-safe hidden-stopping lemma.  Before the stopping line is reached, every
fresh test receives processing time `u`; after the first crossing every fresh
test receives zero.  Raw jobs never query the oracle and receive zero when
the adaptive interaction is frozen.

The file proves:

* legality of the oracle at finite cap `u`;
* binary range preservation through `adaptiveRun` and completion by zero;
* exact one-step changes of the stopping surplus;
* the strict first-crossing overshoot bounds for both possible crossing
  touches (a long test or a raw completion);
* fixed-input and timed-cost replay specialized to this oracle.

The remaining operational part of the paper's lemma is the scheduling
exchange argument that lower-bounds an arbitrary completed transcript by
`stoppingAlgExact`, identifies its offline value with `stoppingOptExact`, and
handles the no-crossing/termination cases.  The uniform overshoot-to-`O(n)`
comparison is proved in `LowerBoundAssembly`.
-/

namespace SchedulingPaper

noncomputable section

namespace HiddenStoppingOracle

open Online

/-! ## Public counters and the stopping line -/

/-- Number of jobs already executed raw in a public transcript. -/
def rawCount : Transcript n → ℕ
  | [] => 0
  | .rawCompleted _ :: rest => rawCount rest + 1
  | _ :: rest => rawCount rest

/-- Number of tests that revealed the long value `u`. -/
def longCount (u : ℝ) : Transcript n → ℕ
  | [] => 0
  | .testResult _ p :: rest =>
      (if p = u then 1 else 0) + longCount u rest
  | _ :: rest => longCount u rest

@[simp] theorem rawCount_nil :
    rawCount ([] : Transcript n) = 0 := rfl

@[simp] theorem rawCount_rawCompleted_cons
    (job : Label n) (transcript : Transcript n) :
    rawCount (.rawCompleted job :: transcript) =
      rawCount transcript + 1 := rfl

@[simp] theorem rawCount_testResult_cons
    (job : Label n) (p : ℝ) (transcript : Transcript n) :
    rawCount (.testResult job p :: transcript) =
      rawCount transcript := rfl

@[simp] theorem rawCount_processed_cons
    (job : Label n) (transcript : Transcript n) :
    rawCount (.processed job :: transcript) =
      rawCount transcript := rfl

@[simp] theorem longCount_nil (u : ℝ) :
    longCount u ([] : Transcript n) = 0 := rfl

@[simp] theorem longCount_rawCompleted_cons
    (u : ℝ) (job : Label n) (transcript : Transcript n) :
    longCount u (.rawCompleted job :: transcript) =
      longCount u transcript := rfl

@[simp] theorem longCount_processed_cons
    (u : ℝ) (job : Label n) (transcript : Transcript n) :
    longCount u (.processed job :: transcript) =
      longCount u transcript := rfl

@[simp] theorem longCount_testResult_same_cons
    (u : ℝ) (job : Label n) (transcript : Transcript n) :
    longCount u (.testResult job u :: transcript) =
      longCount u transcript + 1 := by
  simp [longCount, Nat.add_comm]

theorem rawCount_append
    (left right : Transcript n) :
    rawCount (left ++ right) = rawCount left + rawCount right := by
  induction left with
  | nil => simp
  | cons observation left ih =>
      cases observation <;> simp [ih, Nat.add_comm,
        Nat.add_left_comm]

theorem longCount_append
    (u : ℝ) (left right : Transcript n) :
    longCount u (left ++ right) =
      longCount u left + longCount u right := by
  induction left with
  | nil => simp
  | cons observation left ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = u <;>
            simp [longCount, hp, ih, Nat.add_comm,
              Nat.add_left_comm]
      | processed job => simp [longCount, ih]
      | rawCompleted job => simp [longCount, ih]

@[simp] theorem rawCount_append_raw
    (transcript : Transcript n) (job : Label n) :
    rawCount (transcript ++ [.rawCompleted job]) =
      rawCount transcript + 1 := by
  rw [rawCount_append]
  simp

@[simp] theorem longCount_append_raw
    (u : ℝ) (transcript : Transcript n) (job : Label n) :
    longCount u (transcript ++ [.rawCompleted job]) =
      longCount u transcript := by
  rw [longCount_append]
  simp

@[simp] theorem rawCount_append_long
    (transcript : Transcript n) (job : Label n) (u : ℝ) :
    rawCount (transcript ++ [.testResult job u]) =
      rawCount transcript := by
  rw [rawCount_append]
  simp

@[simp] theorem longCount_append_long
    (transcript : Transcript n) (job : Label n) (u : ℝ) :
    longCount u (transcript ++ [.testResult job u]) =
      longCount u transcript + 1 := by
  rw [longCount_append]
  simp

@[simp] theorem rawCount_append_processed
    (transcript : Transcript n) (job : Label n) :
    rawCount (transcript ++ [.processed job]) =
      rawCount transcript := by
  rw [rawCount_append]
  simp

@[simp] theorem longCount_append_processed
    (u : ℝ) (transcript : Transcript n) (job : Label n) :
    longCount u (transcript ++ [.processed job]) =
      longCount u transcript := by
  rw [longCount_append]
  simp

theorem rawCount_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    rawCount (transcript ++ [.testResult job p]) =
      rawCount transcript := by
  rw [rawCount_append]
  simp

theorem longCount_append_testResult_ne
    (u : ℝ) (transcript : Transcript n) (job : Label n) (p : ℝ)
    (hp : p ≠ u) :
    longCount u (transcript ++ [.testResult job p]) =
      longCount u transcript := by
  rw [longCount_append]
  simp [longCount, hp]

/-- `L - α(n-v)`, where `L` is the number of tested-long jobs and `v` the
number of raw completions. -/
def surplus (n : ℕ) (u α : ℝ) (transcript : Transcript n) : ℝ :=
  longCount u transcript -
    α * ((n : ℝ) - rawCount transcript)

/-- The stopping line has been reached. -/
def Crossed (n : ℕ) (u α : ℝ) (transcript : Transcript n) : Prop :=
  0 ≤ surplus n u α transcript

/-- A particular public observation is the first crossing touch. -/
def FirstCrossingAt
    (n : ℕ) (u α : ℝ) (before : Transcript n)
    (observation : Observation n) : Prop :=
  ¬ Crossed n u α before ∧
    Crossed n u α (before ++ [observation])

theorem surplus_append_raw
    (n : ℕ) (u α : ℝ) (transcript : Transcript n) (job : Label n) :
    surplus n u α (transcript ++ [.rawCompleted job]) =
      surplus n u α transcript + α := by
  unfold surplus
  simp
  ring

theorem surplus_append_long
    (n : ℕ) (u α : ℝ) (transcript : Transcript n) (job : Label n) :
    surplus n u α (transcript ++ [.testResult job u]) =
      surplus n u α transcript + 1 := by
  unfold surplus
  simp
  ring

theorem surplus_append_processed
    (n : ℕ) (u α : ℝ) (transcript : Transcript n) (job : Label n) :
    surplus n u α (transcript ++ [.processed job]) =
      surplus n u α transcript := by
  simp [surplus]

theorem surplus_append_testResult_ne
    (n : ℕ) (u α : ℝ) (transcript : Transcript n)
    (job : Label n) (p : ℝ) (hp : p ≠ u) :
    surplus n u α (transcript ++ [.testResult job p]) =
      surplus n u α transcript := by
  simp [surplus, longCount_append_testResult_ne, hp]

/-- Once crossed, raw completions cannot return below the line. -/
theorem Crossed.append_raw
    {n : ℕ} {u α : ℝ} {transcript : Transcript n}
    (hcross : Crossed n u α transcript) (hα : 0 ≤ α)
    (job : Label n) :
    Crossed n u α (transcript ++ [.rawCompleted job]) := by
  unfold Crossed at *
  rw [surplus_append_raw]
  exact add_nonneg hcross hα

/-- Processing a tested job leaves the stopping line unchanged. -/
theorem Crossed.append_processed
    {n : ℕ} {u α : ℝ} {transcript : Transcript n}
    (hcross : Crossed n u α transcript) (job : Label n) :
    Crossed n u α (transcript ++ [.processed job]) := by
  unfold Crossed at *
  rwa [surplus_append_processed]

/-- Every post-crossing zero answer preserves crossing when `u ≠ 0`. -/
theorem Crossed.append_zero_test
    {n : ℕ} {u α : ℝ} {transcript : Transcript n}
    (hcross : Crossed n u α transcript) (hu : u ≠ 0)
    (job : Label n) :
    Crossed n u α (transcript ++ [.testResult job 0]) := by
  unfold Crossed at *
  rwa [surplus_append_testResult_ne n u α transcript job 0
    (Ne.symm hu)]

/-! ## The explicit oracle -/

/-- Return the long value while the public trace is below the line, and zero
from the first crossing onward. -/
noncomputable def oracle (n : ℕ) (u α : ℝ) : Oracle n :=
  fun transcript _job =>
    @ite ℝ (Crossed n u α transcript)
      (Classical.propDecidable _) 0 u

theorem oracle_eq_zero_of_crossed
    {n : ℕ} {u α : ℝ} {transcript : Transcript n}
    (h : Crossed n u α transcript) (job : Label n) :
    oracle n u α transcript job = 0 := by
  simp [oracle, h]

theorem oracle_eq_long_of_not_crossed
    {n : ℕ} {u α : ℝ} {transcript : Transcript n}
    (h : ¬ Crossed n u α transcript) (job : Label n) :
    oracle n u α transcript job = u := by
  simp [oracle, h]

theorem oracle_binary
    (n : ℕ) (u α : ℝ) (transcript : Transcript n) (job : Label n) :
    oracle n u α transcript job = 0 ∨
      oracle n u α transcript job = u := by
  unfold oracle
  split_ifs <;> simp

/-- Legality at finite cap `u`. -/
theorem oracle_admissible
    {n : ℕ} {u α : ℝ} (hu : 0 ≤ u) :
    (oracle n u α).Admissible (.finite u) := by
  intro transcript job
  rcases oracle_binary n u α transcript job with hzero | hlong
  · rw [hzero]
    exact ⟨le_rfl, hu⟩
  · rw [hlong]
    exact ⟨hu, le_rfl⟩

theorem zero_default_admissible
    {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    ∀ _job : Label n, ValueAdmissible (.finite u) 0 :=
  fun _ => ⟨le_rfl, hu⟩

/-! ## Binary range through adaptive assignment and freezing -/

def AssignmentBinary (u : ℝ) (assignment : PartialAssignment n) : Prop :=
  ∀ job p, assignment job = some p → p = 0 ∨ p = u

theorem emptyAssignment_binary (u : ℝ) :
    AssignmentBinary u (emptyAssignment : PartialAssignment n) := by
  intro job p h
  simp [emptyAssignment] at h

theorem adaptiveValue_binary
    {u : ℝ} {adversary : Oracle n} {assignment : PartialAssignment n}
    (horacle :
      ∀ transcript job,
        adversary transcript job = 0 ∨ adversary transcript job = u)
    (hassignment : AssignmentBinary u assignment)
    (transcript : Transcript n) (job : Label n) :
    adaptiveValue adversary assignment transcript job = 0 ∨
      adaptiveValue adversary assignment transcript job = u := by
  cases hjob : assignment job with
  | none =>
      simpa [adaptiveValue, hjob] using horacle transcript job
  | some p =>
      simpa [adaptiveValue, hjob] using hassignment job p hjob

theorem assignmentAfter_binary
    {u : ℝ} {adversary : Oracle n}
    (horacle :
      ∀ transcript job,
        adversary transcript job = 0 ∨ adversary transcript job = u)
    {config : Config n} {assignment : PartialAssignment n}
    (hassignment : AssignmentBinary u assignment)
    (action : Action n) :
    AssignmentBinary u
      (assignmentAfter adversary config assignment action) := by
  cases action with
  | process job => exact hassignment
  | raw job => exact hassignment
  | test testedJob =>
      intro job p hjob
      by_cases heq : job = testedJob
      · subst job
        have hp :
            adaptiveValue adversary assignment
                config.transcript testedJob = p := by
          simpa [assignmentAfter] using hjob
        rw [← hp]
        exact adaptiveValue_binary horacle hassignment
          config.transcript testedJob
      · apply hassignment job p
        simpa [assignmentAfter, Function.update, heq] using hjob

theorem adaptiveStep_binary
    {cap : Cap} {u : ℝ} {adversary : Oracle n}
    (horacle :
      ∀ transcript job,
        adversary transcript job = 0 ∨ adversary transcript job = u)
    {config next : Config n}
    {assignment nextAssignment : PartialAssignment n}
    (hassignment : AssignmentBinary u assignment)
    {action : Action n}
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    AssignmentBinary u nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase :
      config.step cap (adaptiveOracle adversary assignment) action with
  | none => simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_binary horacle hassignment action

theorem runAdaptiveFuel_binary
    {cap : Cap} {u : ℝ} {adversary : Oracle n}
    (horacle :
      ∀ transcript job,
        adversary transcript job = 0 ∨ adversary transcript job = u)
    (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : PartialAssignment n)
    (hassignment : AssignmentBinary u assignment) :
    AssignmentBinary u
      (runAdaptiveFuel cap adversary strategy fuel
        config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hassignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hassignment
      | some action =>
          cases hstep :
              adaptiveStep cap adversary config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hassignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                adaptiveStep_binary horacle hassignment hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem adaptiveRun_binary
    (n : ℕ) (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    AssignmentBinary u
      (adaptiveRun (.finite u) (oracle n u α) strategy fuel).assigned := by
  apply runAdaptiveFuel_binary
    (adversary := oracle n u α)
    (fun transcript job => oracle_binary n u α transcript job)
  exact emptyAssignment_binary u

/-- Completing every untested label by zero produces a genuinely binary
fixed vector. -/
theorem frozenProcessingTimes_binary
    (n : ℕ) (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) (job : Label n) :
    frozenProcessingTimes (.finite u) (oracle n u α) strategy
        (fun _ => 0) fuel job = 0 ∨
      frozenProcessingTimes (.finite u) (oracle n u α) strategy
        (fun _ => 0) fuel job = u := by
  unfold frozenProcessingTimes completeAssignment
  cases hjob :
      (adaptiveRun (.finite u) (oracle n u α) strategy fuel).assigned job with
  | none => simp
  | some p =>
      simpa [hjob] using
        adaptiveRun_binary n u α strategy fuel job p hjob

/-! ## First-crossing overshoot -/

/-- If the first crossing touch is a long test, its normalized overshoot is
strictly below one remaining job. -/
theorem firstCrossing_long_overshoot
    {n : ℕ} {u α : ℝ} {before : Transcript n} {job : Label n}
    (hcross :
      FirstCrossingAt n u α before (.testResult job u))
    (hremaining :
      0 < (n : ℝ) - rawCount before) :
    let y :=
      ((longCount u before : ℝ) + 1) /
        ((n : ℝ) - rawCount before)
    0 ≤ y - α ∧
      y - α < 1 / ((n : ℝ) - rawCount before) := by
  dsimp only
  rcases hcross with ⟨hbefore, hafter⟩
  have hbeforeSurplus : surplus n u α before < 0 :=
    lt_of_not_ge hbefore
  have hafterSurplus :
      0 ≤ surplus n u α before + 1 := by
    rw [← surplus_append_long n u α before job]
    exact hafter
  let S : ℝ := (n : ℝ) - rawCount before
  let L : ℝ := longCount u before
  have hS : 0 < S := hremaining
  have hpre : L - α * S < 0 := by
    simpa [surplus, S, L] using hbeforeSurplus
  have hpost : 0 ≤ L + 1 - α * S := by
    have hbase : 0 ≤ L - α * S + 1 := by
      simpa [surplus, S, L] using hafterSurplus
    linarith
  have hid :
      (L + 1) / S - α = (L + 1 - α * S) / S := by
    field_simp [hS.ne']
  constructor
  · rw [hid]
    exact div_nonneg hpost hS.le
  · rw [hid, div_lt_div_iff_of_pos_right hS]
    linarith

/-- If the first crossing touch is raw, the gap grows by `α < 1`, giving the
same strict normalized overshoot. -/
theorem firstCrossing_raw_overshoot
    {n : ℕ} {u α : ℝ} {before : Transcript n} {job : Label n}
    (_hα0 : 0 ≤ α) (hα1 : α < 1)
    (hcross :
      FirstCrossingAt n u α before (.rawCompleted job))
    (hremaining :
      0 < (n : ℝ) - ((rawCount before : ℝ) + 1)) :
    let y :=
      (longCount u before : ℝ) /
        ((n : ℝ) - ((rawCount before : ℝ) + 1))
    0 ≤ y - α ∧
      y - α <
        1 / ((n : ℝ) - ((rawCount before : ℝ) + 1)) := by
  dsimp only
  rcases hcross with ⟨hbefore, hafter⟩
  have hbeforeSurplus : surplus n u α before < 0 :=
    lt_of_not_ge hbefore
  have hafterSurplus :
      0 ≤ surplus n u α before + α := by
    rw [← surplus_append_raw n u α before job]
    exact hafter
  let S : ℝ := (n : ℝ) - ((rawCount before : ℝ) + 1)
  let L : ℝ := longCount u before
  have hS : 0 < S := hremaining
  have hbeforeDen :
      (n : ℝ) - rawCount before = S + 1 := by
    dsimp [S]
    ring
  have hpre : L - α * (S + 1) < 0 := by
    unfold surplus at hbeforeSurplus
    rw [hbeforeDen] at hbeforeSurplus
    simpa [L] using hbeforeSurplus
  have hpost : 0 ≤ L - α * S := by
    have hrewrite :
        surplus n u α before + α = L - α * S := by
      unfold surplus
      rw [hbeforeDen]
      dsimp [L]
      ring
    rw [← hrewrite]
    exact hafterSurplus
  have hstrict : L - α * S < 1 := by
    nlinarith
  have hid :
      L / S - α = (L - α * S) / S := by
    field_simp [hS.ne']
  constructor
  · rw [hid]
    exact div_nonneg hpost hS.le
  · rw [hid, div_lt_div_iff_of_pos_right hS]
    exact hstrict

/-! ## Specialized replay -/

theorem replay_fixed_binary
    {n : ℕ} (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    run (.finite u)
        (fixedOracle
          (frozenProcessingTimes (.finite u) (oracle n u α) strategy
            (fun _ => 0) fuel))
        strategy fuel =
      (adaptiveRun (.finite u) (oracle n u α) strategy fuel).result :=
  replay (.finite u) (oracle n u α) strategy (fun _ => 0) fuel

theorem replay_fixed_binary_completionCost
    {n : ℕ} (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    let frozen :=
      frozenProcessingTimes (.finite u) (oracle n u α) strategy
        (fun _ => 0) fuel
    runCompletionCost (.finite u) frozen
        (run (.finite u) (fixedOracle frozen) strategy fuel) =
      runCompletionCost (.finite u) frozen
        (adaptiveRun (.finite u) (oracle n u α) strategy fuel).result :=
  replay_preserves_completionCost
    (.finite u) (oracle n u α) strategy (fun _ => 0) fuel

end HiddenStoppingOracle

end

end SchedulingPaper
