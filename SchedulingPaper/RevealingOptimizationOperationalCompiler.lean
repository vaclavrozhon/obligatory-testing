import SchedulingPaper.RevealingOptimizationBinaryYao
import SchedulingPaper.RevealingOptimizationSurvival
import SchedulingPaper.TimedOnline
import SchedulingPaper.TranscriptPairAccounting
import Mathlib.Tactic

/-!
# Operational compiler for revealing optimization

This file mechanically unfolds a transcript-only strategy in the common
test--process--raw semantics into the label-preserving binary tree used by
the revealing-optimization lower bound.  Tested zero jobs are already
complete for the scheduling objective; their later zero-duration
administrative `process` action is therefore simulated silently while its
public observation is retained for subsequent decisions.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace RandomizedYao

noncomputable section

/-- The fixed labelled binary assignment followed by one branch. -/
def binaryProcessing (positive : ℝ) (input : BinaryInput n) (job : Fin n) : ℝ :=
  if input job then positive else 0

/-- Literal public operations emitted by a label-preserving tree. -/
def LabelledPolicy.observations
    {fresh known : Finset (Fin n)} (policy : LabelledPolicy n fresh known)
    (positive : ℝ) (input : BinaryInput n) : Online.Transcript n :=
  match policy with
  | .done => []
  | .raw job _ next =>
      .rawCompleted job :: next.observations positive input
  | .process job _ next =>
      .processed job :: next.observations positive input
  | .test job _ _ zeroBranch positiveBranch =>
      if input job then
        .testResult job positive :: positiveBranch.observations positive input
      else
        .testResult job 0 :: zeroBranch.observations positive input

/-- Every branch completes exactly the fresh and known positive jobs. -/
theorem LabelledPolicy.completionCount_observations
    {fresh known : Finset (Fin n)} (policy : LabelledPolicy n fresh known)
    {positive : ℝ} (hpositive : positive ≠ 0) (input : BinaryInput n)
    (hknown : ∀ job ∈ known, input job = true) :
    Online.completionCount (binaryProcessing positive input)
        (policy.observations positive input) = fresh.card + known.card := by
  induction policy with
  | done => simp [LabelledPolicy.observations]
  | @raw fresh known job hjob next ih =>
      simp only [LabelledPolicy.observations, Online.completionCount_cons,
        Online.Observation.completionLabel, Option.isSome_some, if_true]
      rw [ih hknown]
      have hcard := Finset.card_erase_add_one hjob
      omega
  | @process fresh known job hjob next ih =>
      have hbit : input job = true := hknown job hjob
      have hp : binaryProcessing positive input job = positive := by
        simp [binaryProcessing, hbit]
      have hknown' : ∀ other ∈ known.erase job, input other = true := by
        intro other hother
        exact hknown other (Finset.mem_of_mem_erase hother)
      simp only [LabelledPolicy.observations, Online.completionCount_cons,
        Online.Observation.completionLabel, hp, hpositive, if_false,
        Option.isSome_some, if_true]
      rw [ih hknown']
      have hcard := Finset.card_erase_add_one hjob
      omega
  | @test fresh known job hfresh hnotKnown zeroBranch positiveBranch
      ihZero ihPositive =>
      cases hbit : input job
      · simp only [LabelledPolicy.observations, hbit, Bool.false_eq_true,
          if_false, Online.completionCount_cons,
          Online.Observation.completionLabel, Option.isSome_some, if_true]
        rw [ihZero hknown]
        have hcard := Finset.card_erase_add_one hfresh
        omega
      · have hknown' : ∀ other ∈ insert job known, input other = true := by
          intro other hother
          rw [Finset.mem_insert] at hother
          rcases hother with rfl | hother
          · exact hbit
          · exact hknown other hother
        simp only [LabelledPolicy.observations, hbit, if_true,
          Online.completionCount_cons, Online.Observation.completionLabel,
          hpositive, if_false, Option.isSome_none, Bool.false_eq_true]
        rw [ihPositive hknown']
        have hfreshCard := Finset.card_erase_add_one hfresh
        have hknownCard := Finset.card_insert_of_notMem hnotKnown
        omega

/-- The recursive tree cost is the literal completion cost of its emitted
public test--process--raw transcript. -/
theorem LabelledPolicy.cost_eq_completionCost_observations
    {fresh known : Finset (Fin n)} (policy : LabelledPolicy n fresh known)
    {rawDuration positive : ℝ} (hpositive : positive ≠ 0)
    (input : BinaryInput n)
    (hknown : ∀ job ∈ known, input job = true) :
    policy.cost rawDuration positive input =
      Online.completionCost (.finite rawDuration)
        (binaryProcessing positive input)
        (policy.observations positive input) := by
  rw [Online.completionCost_eq_suffixWeightedDuration]
  induction policy with
  | done => simp [LabelledPolicy.cost, LabelledPolicy.observations]
  | @raw fresh known job hjob next ih =>
      simp only [LabelledPolicy.cost, LabelledPolicy.observations,
        Online.suffixWeightedDuration_cons, Online.Observation.duration,
        Online.rawDuration, Online.completionCount_cons,
        Online.Observation.completionLabel, Option.isSome_some, if_true]
      rw [next.completionCount_observations hpositive input hknown, ih hknown]
      have hcard := Finset.card_erase_add_one hjob
      have hsum : (fresh.card : ℝ) + known.card =
          1 + ((fresh.erase job).card + known.card) := by
        exact_mod_cast (by omega : fresh.card + known.card =
          1 + ((fresh.erase job).card + known.card))
      rw [hsum]
      push_cast
      ring
  | @process fresh known job hjob next ih =>
      have hbit : input job = true := hknown job hjob
      have hp : binaryProcessing positive input job = positive := by
        simp [binaryProcessing, hbit]
      have hknown' : ∀ other ∈ known.erase job, input other = true := by
        intro other hother
        exact hknown other (Finset.mem_of_mem_erase hother)
      simp only [LabelledPolicy.cost, LabelledPolicy.observations,
        Online.suffixWeightedDuration_cons, Online.Observation.duration, hp,
        Online.completionCount_cons, Online.Observation.completionLabel,
        hpositive, if_false, Option.isSome_some, if_true]
      rw [next.completionCount_observations hpositive input hknown',
        ih hknown']
      have hcard := Finset.card_erase_add_one hjob
      have hsum : (fresh.card : ℝ) + known.card =
          1 + (fresh.card + (known.erase job).card) := by
        exact_mod_cast (by omega : fresh.card + known.card =
          1 + (fresh.card + (known.erase job).card))
      rw [hsum]
      push_cast
      ring
  | @test fresh known job hfresh hnotKnown zeroBranch positiveBranch
      ihZero ihPositive =>
      cases hbit : input job
      · simp only [LabelledPolicy.cost, LabelledPolicy.observations, hbit,
          Bool.false_eq_true, if_false, Online.suffixWeightedDuration_cons,
          Online.Observation.duration, Online.completionCount_cons,
          Online.Observation.completionLabel, Option.isSome_some, if_true,
          one_mul]
        rw [zeroBranch.completionCount_observations hpositive input hknown,
          ihZero hknown]
        have hcard := Finset.card_erase_add_one hfresh
        have hsum : (fresh.card : ℝ) + known.card =
            1 + ((fresh.erase job).card + known.card) := by
          exact_mod_cast (by omega : fresh.card + known.card =
            1 + ((fresh.erase job).card + known.card))
        rw [hsum]
        push_cast
        ring
      · have hknown' : ∀ other ∈ insert job known, input other = true := by
          intro other hother
          rw [Finset.mem_insert] at hother
          rcases hother with rfl | hother
          · exact hbit
          · exact hknown other hother
        simp only [LabelledPolicy.cost, LabelledPolicy.observations, hbit,
          if_true, Online.suffixWeightedDuration_cons,
          Online.Observation.duration, Online.completionCount_cons,
          Online.Observation.completionLabel, hpositive, if_false,
          Option.isSome_none, Bool.false_eq_true, one_mul]
        rw [positiveBranch.completionCount_observations hpositive input hknown',
          ihPositive hknown']
        have hfreshCard := Finset.card_erase_add_one hfresh
        have hknownCard := Finset.card_insert_of_notMem hnotKnown
        have hsum : (fresh.card : ℝ) + known.card =
            (fresh.erase job).card + (insert job known).card := by
          exact_mod_cast (by omega : fresh.card + known.card =
            (fresh.erase job).card + (insert job known).card)
        rw [hsum]
        push_cast
        ring

end

end RandomizedYao

namespace OperationalCompiler

open RandomizedYao

noncomputable section

/-! ## Literal operational state and zero-process erasure -/

/-- A tested zero job is already complete for the scheduling objective.  Its
later `process` operation is nevertheless part of the public history seen by
the strategy.  Erasing precisely these zero-time, non-completing observations
does not change the completion cost. -/
def eraseZeroProcesses (processing : Fin n → ℝ) :
    Online.Transcript n → Online.Transcript n
  | [] => []
  | observation :: rest =>
      match observation with
      | .processed job =>
          if processing job = 0 then eraseZeroProcesses processing rest
          else observation :: eraseZeroProcesses processing rest
      | .testResult _ _ | .rawCompleted _ =>
          observation :: eraseZeroProcesses processing rest

@[simp] theorem eraseZeroProcesses_nil (processing : Fin n → ℝ) :
    eraseZeroProcesses processing [] = [] := rfl

theorem eraseZeroProcesses_append (processing : Fin n → ℝ)
    (left right : Online.Transcript n) :
    eraseZeroProcesses processing (left ++ right) =
      eraseZeroProcesses processing left ++ eraseZeroProcesses processing right := by
  induction left with
  | nil => rfl
  | cons observation left ih =>
      cases observation with
      | testResult job p => simp [eraseZeroProcesses, ih]
      | rawCompleted job => simp [eraseZeroProcesses, ih]
      | processed job =>
          by_cases hzero : processing job = 0 <;>
            simp [eraseZeroProcesses, hzero, ih]

/-- Administrative processing of tested zero jobs is invisible to total
completion cost, at every starting time. -/
theorem completionCostFrom_eraseZeroProcesses
    (cap : Cap) (processing : Fin n → ℝ) (time : ℝ)
    (transcript : Online.Transcript n) :
    Online.completionCostFrom cap processing time
        (eraseZeroProcesses processing transcript) =
      Online.completionCostFrom cap processing time transcript := by
  induction transcript generalizing time with
  | nil => rfl
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          simp only [eraseZeroProcesses, Online.completionCostFrom,
            Online.Observation.duration]
          split_ifs <;> rw [ih]
      | rawCompleted job =>
          simp only [eraseZeroProcesses, Online.completionCostFrom,
            Online.Observation.duration]
          split_ifs <;> rw [ih]
      | processed job =>
          by_cases hzero : processing job = 0
          · simp [eraseZeroProcesses, hzero, Online.completionCostFrom,
              Online.Observation.duration, Online.Observation.completionLabel,
              ih]
          · simp only [eraseZeroProcesses, hzero, if_false,
              Online.completionCostFrom, Online.Observation.duration,
              Online.Observation.completionLabel]
            simp only [hzero, if_false, Option.isSome_some, Bool.true_eq]
            rw [ih]

theorem completionCost_eraseZeroProcesses
    (cap : Cap) (processing : Fin n → ℝ)
    (transcript : Online.Transcript n) :
    Online.completionCost cap processing
        (eraseZeroProcesses processing transcript) =
      Online.completionCost cap processing transcript := by
  exact completionCostFrom_eraseZeroProcesses cap processing 0 transcript

/-- Machine state represented by the three compiler sets.  Labels in no set
are already fully processed or were run raw. -/
def compilerJobState (positive : ℝ)
    (fresh known zero : Finset (Fin n)) (job : Fin n) : Online.JobState :=
  if job ∈ fresh then .untouched
  else if job ∈ known then .tested positive
  else if job ∈ zero then .tested 0
  else .done

def compilerConfig (positive : ℝ)
    (fresh known zero : Finset (Fin n))
    (transcript : Online.Transcript n) : Online.Config n where
  jobs := compilerJobState positive fresh known zero
  transcript := transcript

@[simp] theorem compilerConfig_transcript
    (positive : ℝ) (fresh known zero : Finset (Fin n))
    (transcript : Online.Transcript n) :
    (compilerConfig positive fresh known zero transcript).transcript = transcript := rfl

@[simp] theorem compilerConfig_jobs
    (positive : ℝ) (fresh known zero : Finset (Fin n))
    (transcript : Online.Transcript n) (job : Fin n) :
    (compilerConfig positive fresh known zero transcript).jobs job =
      compilerJobState positive fresh known zero job := rfl

/-- Reachable compiler states keep the three lifecycle classes disjoint. -/
def StateValid (fresh known zero : Finset (Fin n)) : Prop :=
  Disjoint fresh known ∧ Disjoint fresh zero ∧ Disjoint known zero

/-- Tested symbolic classes agree with the fixed binary input selecting the
current branch. -/
def StateConsistent (input : BinaryInput n)
    (known zero : Finset (Fin n)) : Prop :=
  (∀ job ∈ known, input job = true) ∧
    (∀ job ∈ zero, input job = false)

theorem stateValid_initial :
    StateValid (Finset.univ : Finset (Fin n)) ∅ ∅ := by
  simp [StateValid]

theorem stateConsistent_initial (input : BinaryInput n) :
    StateConsistent input ∅ ∅ := by
  simp [StateConsistent]

theorem StateConsistent.after_process_known
    {input : BinaryInput n} {known zero : Finset (Fin n)}
    (hconsistent : StateConsistent input known zero) (job : Fin n) :
    StateConsistent input (known.erase job) zero := by
  constructor
  · intro other hother
    exact hconsistent.1 other (Finset.mem_of_mem_erase hother)
  · exact hconsistent.2

theorem StateConsistent.after_process_zero
    {input : BinaryInput n} {known zero : Finset (Fin n)}
    (hconsistent : StateConsistent input known zero) (job : Fin n) :
    StateConsistent input known (zero.erase job) := by
  constructor
  · exact hconsistent.1
  · intro other hother
    exact hconsistent.2 other (Finset.mem_of_mem_erase hother)

theorem StateConsistent.after_test_zero
    {input : BinaryInput n} {known zero : Finset (Fin n)}
    (hconsistent : StateConsistent input known zero)
    {job : Fin n} (hbit : input job = false) :
    StateConsistent input known (insert job zero) := by
  constructor
  · exact hconsistent.1
  · intro other hother
    rw [Finset.mem_insert] at hother
    rcases hother with rfl | hother
    · exact hbit
    · exact hconsistent.2 other hother

theorem StateConsistent.after_test_positive
    {input : BinaryInput n} {known zero : Finset (Fin n)}
    (hconsistent : StateConsistent input known zero)
    {job : Fin n} (hbit : input job = true) :
    StateConsistent input (insert job known) zero := by
  constructor
  · intro other hother
    rw [Finset.mem_insert] at hother
    rcases hother with rfl | hother
    · exact hbit
    · exact hconsistent.1 other hother
  · exact hconsistent.2

theorem StateValid.not_known_of_fresh
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) : job ∉ known := by
  exact Finset.disjoint_left.mp hvalid.1 hjob

theorem StateValid.not_zero_of_fresh
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) : job ∉ zero := by
  exact Finset.disjoint_left.mp hvalid.2.1 hjob

theorem StateValid.not_fresh_of_known
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ known) : job ∉ fresh := by
  exact Finset.disjoint_right.mp hvalid.1 hjob

theorem StateValid.not_zero_of_known
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ known) : job ∉ zero := by
  exact Finset.disjoint_left.mp hvalid.2.2 hjob

theorem StateValid.not_fresh_of_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ zero) : job ∉ fresh := by
  exact Finset.disjoint_right.mp hvalid.2.1 hjob

theorem StateValid.not_known_of_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ zero) : job ∉ known := by
  exact Finset.disjoint_right.mp hvalid.2.2 hjob

theorem StateValid.after_raw
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    (job : Fin n) : StateValid (fresh.erase job) known zero := by
  exact ⟨hvalid.1.mono_left (Finset.erase_subset _ _),
    hvalid.2.1.mono_left (Finset.erase_subset _ _), hvalid.2.2⟩

theorem StateValid.after_process_known
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    (job : Fin n) : StateValid fresh (known.erase job) zero := by
  exact ⟨hvalid.1.mono_right (Finset.erase_subset _ _), hvalid.2.1,
    hvalid.2.2.mono_left (Finset.erase_subset _ _)⟩

theorem StateValid.after_process_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    (job : Fin n) : StateValid fresh known (zero.erase job) := by
  exact ⟨hvalid.1, hvalid.2.1.mono_right (Finset.erase_subset _ _),
    hvalid.2.2.mono_right (Finset.erase_subset _ _)⟩

theorem StateValid.after_test_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) :
    StateValid (fresh.erase job) known (insert job zero) := by
  constructor
  · exact hvalid.1.mono_left (Finset.erase_subset _ _)
  constructor
  · rw [Finset.disjoint_insert_right]
    exact ⟨(by simp),
      hvalid.2.1.mono_left (Finset.erase_subset _ _)⟩
  · rw [Finset.disjoint_insert_right]
    exact ⟨hvalid.not_known_of_fresh hjob, hvalid.2.2⟩

theorem StateValid.after_test_positive
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) :
    StateValid (fresh.erase job) (insert job known) zero := by
  constructor
  · rw [Finset.disjoint_insert_right]
    exact ⟨(by simp),
      hvalid.1.mono_left (Finset.erase_subset _ _)⟩
  constructor
  · exact hvalid.2.1.mono_left (Finset.erase_subset _ _)
  · rw [Finset.disjoint_insert_left]
    exact ⟨hvalid.not_zero_of_fresh hjob, hvalid.2.2⟩

@[simp] theorem compilerConfig_step_raw
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) (u positive : ℝ)
    (processing : Fin n → ℝ) (transcript : Online.Transcript n) :
    (compilerConfig positive fresh known zero transcript).step
        (.finite u) (Online.fixedOracle processing) (.raw job) =
      some (compilerConfig positive (fresh.erase job) known zero
        (transcript ++ [.rawCompleted job])) := by
  unfold compilerConfig compilerJobState Online.Config.step
  simp only [hjob, if_true]
  congr 2
  funext other
  by_cases heq : other = job
  · subst other
    simp [compilerJobState, hjob, hvalid.not_known_of_fresh hjob,
      hvalid.not_zero_of_fresh hjob]
  · simp [compilerJobState, Function.update, heq, Finset.mem_erase]

@[simp] theorem compilerConfig_step_process_known
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ known) (positive : ℝ)
    (processing : Fin n → ℝ) (transcript : Online.Transcript n) (cap : Cap) :
    (compilerConfig positive fresh known zero transcript).step
        cap (Online.fixedOracle processing) (.process job) =
      some (compilerConfig positive fresh (known.erase job) zero
        (transcript ++ [.processed job])) := by
  unfold compilerConfig compilerJobState Online.Config.step
  simp only [hvalid.not_fresh_of_known hjob, if_false, hjob, if_true]
  congr 2
  funext other
  by_cases heq : other = job
  · subst other
    simp [compilerJobState, hvalid.not_fresh_of_known hjob,
      hvalid.not_zero_of_known hjob, hjob]
  · simp [compilerJobState, Function.update, heq, Finset.mem_erase]

@[simp] theorem compilerConfig_step_process_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ zero) (positive : ℝ)
    (processing : Fin n → ℝ) (transcript : Online.Transcript n) (cap : Cap) :
    (compilerConfig positive fresh known zero transcript).step
        cap (Online.fixedOracle processing) (.process job) =
      some (compilerConfig positive fresh known (zero.erase job)
        (transcript ++ [.processed job])) := by
  unfold compilerConfig compilerJobState Online.Config.step
  simp only [hvalid.not_fresh_of_zero hjob, if_false,
    hvalid.not_known_of_zero hjob, hjob, if_true]
  congr 2
  funext other
  by_cases heq : other = job
  · subst other
    simp [compilerJobState, hvalid.not_fresh_of_zero hjob,
      hvalid.not_known_of_zero hjob, hjob]
  · simp [compilerJobState, Function.update, heq, Finset.mem_erase]

@[simp] theorem compilerConfig_step_test_zero
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) (positive : ℝ)
    (input : BinaryInput n) (hbit : input job = false)
    (transcript : Online.Transcript n) (cap : Cap) :
    (compilerConfig positive fresh known zero transcript).step cap
        (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
        (.test job) =
      some (compilerConfig positive (fresh.erase job) known (insert job zero)
        (transcript ++ [.testResult job 0])) := by
  unfold compilerConfig compilerJobState Online.Config.step
  simp only [hjob, if_true, Online.fixedOracle]
  have hp : RandomizedYao.binaryProcessing positive input job = 0 := by
    simp [RandomizedYao.binaryProcessing, hbit]
  rw [hp]
  congr 2
  funext other
  by_cases heq : other = job
  · subst other
    simp [compilerJobState, hjob, hvalid.not_known_of_fresh hjob]
  · simp [compilerJobState, Function.update, heq, Finset.mem_erase]

@[simp] theorem compilerConfig_step_test_positive
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {job : Fin n} (hjob : job ∈ fresh) (positive : ℝ)
    (input : BinaryInput n) (hbit : input job = true)
    (transcript : Online.Transcript n) (cap : Cap) :
    (compilerConfig positive fresh known zero transcript).step cap
        (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
        (.test job) =
      some (compilerConfig positive (fresh.erase job) (insert job known) zero
        (transcript ++ [.testResult job positive])) := by
  unfold compilerConfig compilerJobState Online.Config.step
  simp only [hjob, if_true, Online.fixedOracle]
  have hp : RandomizedYao.binaryProcessing positive input job = positive := by
    simp [RandomizedYao.binaryProcessing, hbit]
  rw [hp]
  congr 2
  funext other
  by_cases heq : other = job
  · subst other
    simp [compilerJobState, hjob]
  · simp [compilerJobState, Function.update, heq, Finset.mem_erase]


/-- Canonical completion used only after fuel exhaustion, an explicit stop,
or an invalid action.  Fresh jobs are run raw; known positive jobs are then
processed. -/
def fallback (fresh known : Finset (Fin n)) :
    LabelledPolicy n fresh known := by
  classical
  by_cases hfresh : fresh.Nonempty
  · let job := hfresh.choose
    have hjob : job ∈ fresh := hfresh.choose_spec
    exact .raw job hjob (fallback (fresh.erase job) known)
  · by_cases hknown : known.Nonempty
    · let job := hknown.choose
      have hjob : job ∈ known := hknown.choose_spec
      exact .process job hjob (fallback fresh (known.erase job))
    · have hfreshEmpty : fresh = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hfresh
      have hknownEmpty : known = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hknown
      subst fresh
      subst known
      exact .done
termination_by fresh.card + known.card
decreasing_by
  · have hlt : (fresh.erase hfresh.choose).card < fresh.card :=
      Finset.card_erase_lt_of_mem hfresh.choose_spec
    omega
  · have hlt : (known.erase hknown.choose).card < known.card :=
      Finset.card_erase_lt_of_mem hknown.choose_spec
    omega

@[simp] theorem fallback_empty :
    fallback (∅ : Finset (Fin n)) ∅ = .done := by
  rw [fallback]
  simp

theorem compilerConfig_done_sets_empty
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {positive : ℝ} {transcript : Online.Transcript n}
    (hdone : ∀ job,
      (compilerConfig positive fresh known zero transcript).jobs job = .done) :
    fresh = ∅ ∧ known = ∅ ∧ zero = ∅ := by
  have hfresh : fresh = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨job, hjob⟩ := hnonempty
    have hstate := hdone job
    simp [compilerConfig, compilerJobState, hjob] at hstate
  have hknown : known = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨job, hjob⟩ := hnonempty
    have hstate := hdone job
    simp [compilerConfig, compilerJobState,
      hvalid.not_fresh_of_known hjob, hjob] at hstate
  have hzero : zero = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨job, hjob⟩ := hnonempty
    have hstate := hdone job
    simp [compilerConfig, compilerJobState,
      hvalid.not_fresh_of_zero hjob, hvalid.not_known_of_zero hjob,
      hjob] at hstate
  exact ⟨hfresh, hknown, hzero⟩

/-- Fuelled unfolding of a literal public-transcript strategy.  `fresh`
contains untouched labels, `known` tested positive labels, and `zero`
tested zero labels awaiting only their cost-free administrative process.
The positive test value is a parameter because the two lower-bound
families use respectively `u` and `τ`. -/
def compile (strategy : Online.Strategy n) (positive : ℝ) :
    ℕ → (fresh known zero : Finset (Fin n)) → Online.Transcript n →
      LabelledPolicy n fresh known
  | 0, fresh, known, _zero, _transcript => fallback fresh known
  | fuel + 1, fresh, known, zero, transcript =>
      match strategy transcript with
      | none => fallback fresh known
      | some (.raw job) =>
          if hjob : job ∈ fresh then
            .raw job hjob
              (compile strategy positive fuel (fresh.erase job) known zero
                (transcript ++ [.rawCompleted job]))
          else fallback fresh known
      | some (.process job) =>
          if hknown : job ∈ known then
            .process job hknown
              (compile strategy positive fuel fresh (known.erase job) zero
                (transcript ++ [.processed job]))
          else if _hzero : job ∈ zero then
            compile strategy positive fuel fresh known (zero.erase job)
              (transcript ++ [.processed job])
          else fallback fresh known
      | some (.test job) =>
          if hfresh : job ∈ fresh then
            if hknown : job ∉ known then
              .test job hfresh hknown
                (compile strategy positive fuel (fresh.erase job) known
                  (insert job zero)
                  (transcript ++ [.testResult job 0]))
                (compile strategy positive fuel (fresh.erase job)
                  (insert job known) zero
                  (transcript ++ [.testResult job positive]))
            else fallback fresh known
          else fallback fresh known

/-- Initial labelled tree of a literal strategy.  Every valid revealing run
uses at most two public operations per label; the extra unit also exposes a
normal strategy stop after the last administrative operation. -/
def compileInitial (strategy : Online.Strategy n) (positive : ℝ) :
    LabelledPolicy n Finset.univ ∅ :=
  compile strategy positive (2 * n + 1) Finset.univ ∅ ∅ []

@[simp] theorem compilerConfig_initial (positive : ℝ) :
    compilerConfig positive (Finset.univ : Finset (Fin n)) ∅ ∅ [] =
      Online.Config.initial n := by
  rw [Online.Config.mk.injEq]
  constructor
  · funext job
    simp [compilerConfig, compilerJobState, Online.Config.initial]
  · rfl

private theorem erasedTranscript_eq_fallback_of_done
    {fresh known zero : Finset (Fin n)} (hvalid : StateValid fresh known zero)
    {positive : ℝ} {transcript : Online.Transcript n}
    (input : BinaryInput n)
    (hdone : ∀ job,
      (compilerConfig positive fresh known zero transcript).jobs job = .done) :
    eraseZeroProcesses (RandomizedYao.binaryProcessing positive input)
        (compilerConfig positive fresh known zero transcript).transcript =
      eraseZeroProcesses (RandomizedYao.binaryProcessing positive input) transcript ++
        (fallback fresh known).observations positive input := by
  obtain ⟨rfl, rfl, rfl⟩ := compilerConfig_done_sets_empty hvalid hdone
  simp [compilerConfig, LabelledPolicy.observations]

/-- On every branch on which the operational strategy really completes all
jobs, its public trace, after erasing only zero-duration administrative
process observations, is exactly the branch emitted by the compiled policy.
Thus all fallback branches are proved unreachable except at an already
completed state. -/
theorem compile_mirror_erasedTranscript
    (strategy : Online.Strategy n) (rawDuration positive : ℝ)
    (hpositive : positive ≠ 0)
    (fuel : ℕ) (fresh known zero : Finset (Fin n))
    (transcript : Online.Transcript n) (input : BinaryInput n)
    (hvalid : StateValid fresh known zero)
    (hconsistent : StateConsistent input known zero)
    (hdone : ∀ job,
      (Online.runFuel (.finite rawDuration)
        (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
        strategy fuel (compilerConfig positive fresh known zero transcript)).config.jobs job =
          .done) :
    eraseZeroProcesses (RandomizedYao.binaryProcessing positive input)
        (Online.runFuel (.finite rawDuration)
          (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
          strategy fuel (compilerConfig positive fresh known zero transcript)).config.transcript =
      eraseZeroProcesses (RandomizedYao.binaryProcessing positive input) transcript ++
        (compile strategy positive fuel fresh known zero transcript).observations
          positive input := by
  induction fuel generalizing fresh known zero transcript with
  | zero =>
      have hterminal := erasedTranscript_eq_fallback_of_done
        (positive := positive) (transcript := transcript)
        hvalid input (by simpa [Online.runFuel] using hdone)
      simpa [Online.runFuel, compile] using hterminal
  | succ fuel ih =>
      cases haction : strategy transcript with
      | none =>
          have hterminal := erasedTranscript_eq_fallback_of_done
            (positive := positive) (transcript := transcript)
            hvalid input (by simpa [Online.runFuel, haction] using hdone)
          simpa [Online.runFuel, compile, haction] using hterminal
      | some action =>
          cases action with
          | raw job =>
              by_cases hjob : job ∈ fresh
              · have hstep := compilerConfig_step_raw hvalid hjob rawDuration
                  positive (RandomizedYao.binaryProcessing positive input) transcript
                have hchildDone : ∀ other,
                    (Online.runFuel (.finite rawDuration)
                      (Online.fixedOracle
                        (RandomizedYao.binaryProcessing positive input))
                      strategy fuel
                      (compilerConfig positive (fresh.erase job) known zero
                        (transcript ++ [.rawCompleted job]))).config.jobs other = .done := by
                  simpa [Online.runFuel, haction, hstep] using hdone
                have hrec := ih (fresh.erase job) known zero
                  (transcript ++ [.rawCompleted job])
                  (hvalid.after_raw job) hconsistent hchildDone
                simpa [Online.runFuel, haction, hstep, compile, hjob,
                  LabelledPolicy.observations, eraseZeroProcesses_append,
                  eraseZeroProcesses, List.append_assoc] using hrec
              · have hstep :
                    (compilerConfig positive fresh known zero transcript).step
                      (.finite rawDuration)
                      (Online.fixedOracle
                        (RandomizedYao.binaryProcessing positive input))
                      (.raw job) = none := by
                  by_cases hknown : job ∈ known
                  · simp [compilerConfig, compilerJobState, Online.Config.step,
                      hjob, hknown]
                  · by_cases hzero : job ∈ zero
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hjob, hknown, hzero]
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hjob, hknown, hzero]
                have hcurrent : ∀ other,
                    (compilerConfig positive fresh known zero transcript).jobs other =
                      .done := by
                  simpa [Online.runFuel, haction, hstep] using hdone
                have hterminal := erasedTranscript_eq_fallback_of_done
                  hvalid input hcurrent
                simpa [Online.runFuel, haction, hstep, compile, hjob] using hterminal
          | process job =>
              by_cases hknown : job ∈ known
              · have hstep := compilerConfig_step_process_known hvalid hknown positive
                  (RandomizedYao.binaryProcessing positive input) transcript
                  (.finite rawDuration)
                have hchildDone : ∀ other,
                    (Online.runFuel (.finite rawDuration)
                      (Online.fixedOracle
                        (RandomizedYao.binaryProcessing positive input))
                      strategy fuel
                      (compilerConfig positive fresh (known.erase job) zero
                        (transcript ++ [.processed job]))).config.jobs other = .done := by
                  simpa [Online.runFuel, haction, hstep] using hdone
                have hrec := ih fresh (known.erase job) zero
                  (transcript ++ [.processed job])
                  (hvalid.after_process_known job)
                  (hconsistent.after_process_known job) hchildDone
                have hp : RandomizedYao.binaryProcessing positive input job = positive := by
                  have hbit : input job = true := hconsistent.1 job hknown
                  simp [RandomizedYao.binaryProcessing, hbit]
                simpa [Online.runFuel, haction, hstep, compile, hknown,
                  LabelledPolicy.observations, eraseZeroProcesses_append,
                  eraseZeroProcesses, hp, hpositive, List.append_assoc] using hrec
              · by_cases hzero : job ∈ zero
                · have hstep := compilerConfig_step_process_zero hvalid hzero positive
                    (RandomizedYao.binaryProcessing positive input) transcript
                    (.finite rawDuration)
                  have hchildDone : ∀ other,
                      (Online.runFuel (.finite rawDuration)
                        (Online.fixedOracle
                          (RandomizedYao.binaryProcessing positive input))
                        strategy fuel
                        (compilerConfig positive fresh known (zero.erase job)
                          (transcript ++ [.processed job]))).config.jobs other = .done := by
                    simpa [Online.runFuel, haction, hstep] using hdone
                  have hrec := ih fresh known (zero.erase job)
                    (transcript ++ [.processed job])
                    (hvalid.after_process_zero job)
                    (hconsistent.after_process_zero job) hchildDone
                  have hp : RandomizedYao.binaryProcessing positive input job = 0 := by
                    have hbit : input job = false := hconsistent.2 job hzero
                    simp [RandomizedYao.binaryProcessing, hbit]
                  simpa [Online.runFuel, haction, hstep, compile, hknown, hzero,
                    eraseZeroProcesses_append, eraseZeroProcesses, hp,
                    List.append_assoc] using hrec
                · have hstep :
                      (compilerConfig positive fresh known zero transcript).step
                        (.finite rawDuration)
                        (Online.fixedOracle
                          (RandomizedYao.binaryProcessing positive input))
                        (.process job) = none := by
                    by_cases hfresh : job ∈ fresh
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hfresh, hknown, hzero]
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hfresh, hknown, hzero]
                  have hcurrent : ∀ other,
                      (compilerConfig positive fresh known zero transcript).jobs other =
                        .done := by
                    simpa [Online.runFuel, haction, hstep] using hdone
                  have hterminal := erasedTranscript_eq_fallback_of_done
                    hvalid input hcurrent
                  simpa [Online.runFuel, haction, hstep, compile, hknown, hzero]
                    using hterminal
          | test job =>
              by_cases hfresh : job ∈ fresh
              · have hnotKnown : job ∉ known := hvalid.not_known_of_fresh hfresh
                cases hbit : input job
                · have hstep := compilerConfig_step_test_zero hvalid hfresh positive
                    input hbit transcript (.finite rawDuration)
                  have hchildDone : ∀ other,
                      (Online.runFuel (.finite rawDuration)
                        (Online.fixedOracle
                          (RandomizedYao.binaryProcessing positive input))
                        strategy fuel
                        (compilerConfig positive (fresh.erase job) known
                          (insert job zero)
                          (transcript ++ [.testResult job 0]))).config.jobs other = .done := by
                    simpa [Online.runFuel, haction, hstep] using hdone
                  have hrec := ih (fresh.erase job) known (insert job zero)
                    (transcript ++ [.testResult job 0])
                    (hvalid.after_test_zero hfresh)
                    (hconsistent.after_test_zero hbit) hchildDone
                  simpa [Online.runFuel, haction, hstep, compile, hfresh,
                    hnotKnown, hbit, LabelledPolicy.observations,
                    eraseZeroProcesses_append, eraseZeroProcesses,
                    List.append_assoc] using hrec
                · have hstep := compilerConfig_step_test_positive hvalid hfresh
                    positive input hbit transcript (.finite rawDuration)
                  have hchildDone : ∀ other,
                      (Online.runFuel (.finite rawDuration)
                        (Online.fixedOracle
                          (RandomizedYao.binaryProcessing positive input))
                        strategy fuel
                        (compilerConfig positive (fresh.erase job)
                          (insert job known) zero
                          (transcript ++ [.testResult job positive]))).config.jobs other =
                            .done := by
                    simpa [Online.runFuel, haction, hstep] using hdone
                  have hrec := ih (fresh.erase job) (insert job known) zero
                    (transcript ++ [.testResult job positive])
                    (hvalid.after_test_positive hfresh)
                    (hconsistent.after_test_positive hbit) hchildDone
                  simpa [Online.runFuel, haction, hstep, compile, hfresh,
                    hnotKnown, hbit, LabelledPolicy.observations,
                    eraseZeroProcesses_append, eraseZeroProcesses,
                    List.append_assoc] using hrec
              · have hstep :
                    (compilerConfig positive fresh known zero transcript).step
                      (.finite rawDuration)
                      (Online.fixedOracle
                        (RandomizedYao.binaryProcessing positive input))
                      (.test job) = none := by
                  by_cases hknown : job ∈ known
                  · simp [compilerConfig, compilerJobState, Online.Config.step,
                      hfresh, hknown]
                  · by_cases hzero : job ∈ zero
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hfresh, hknown, hzero]
                    · simp [compilerConfig, compilerJobState, Online.Config.step,
                        hfresh, hknown, hzero]
                have hcurrent : ∀ other,
                    (compilerConfig positive fresh known zero transcript).jobs other =
                      .done := by
                  simpa [Online.runFuel, haction, hstep] using hdone
                have hterminal := erasedTranscript_eq_fallback_of_done
                  hvalid input hcurrent
                simpa [Online.runFuel, haction, hstep, compile, hfresh] using hterminal

/-- The initial compiled branch cost is a literal timed completion cost. -/
theorem compileInitial_cost_eq_completionCost
    (strategy : Online.Strategy n) {rawDuration positive : ℝ}
    (hpositive : positive ≠ 0) (input : BinaryInput n) :
    (compileInitial strategy positive).cost rawDuration positive input =
      Online.completionCost (.finite rawDuration)
        (RandomizedYao.binaryProcessing positive input)
        ((compileInitial strategy positive).observations positive input) := by
  exact (compileInitial strategy positive).cost_eq_completionCost_observations
    hpositive input (by simp)

/-- End-to-end operational compiler theorem.  On a binary input completed by
the literal transcript-only strategy, the compiled Bellman-tree branch has
exactly the `runCompletionCost` returned by the public machine semantics. -/
theorem compileInitial_cost_eq_runCompletionCost
    (strategy : Online.Strategy n) {rawDuration positive : ℝ}
    (hpositive : positive ≠ 0) (input : BinaryInput n)
    (hdone : ∀ job,
      (Online.run (.finite rawDuration)
        (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
        strategy (2 * n + 1)).config.jobs job = .done) :
    (compileInitial strategy positive).cost rawDuration positive input =
      Online.runCompletionCost (.finite rawDuration)
        (RandomizedYao.binaryProcessing positive input)
        (Online.run (.finite rawDuration)
          (Online.fixedOracle (RandomizedYao.binaryProcessing positive input))
          strategy (2 * n + 1)) := by
  let processing := RandomizedYao.binaryProcessing positive input
  let result := Online.run (.finite rawDuration)
    (Online.fixedOracle processing) strategy (2 * n + 1)
  have hmirror := compile_mirror_erasedTranscript strategy rawDuration positive
    hpositive (2 * n + 1) Finset.univ ∅ ∅ [] input
    stateValid_initial (stateConsistent_initial input) (by
      simpa [Online.run, processing, result] using hdone)
  have herased :
      eraseZeroProcesses processing result.config.transcript =
        (compileInitial strategy positive).observations positive input := by
    simpa [Online.run, processing, result, compileInitial] using hmirror
  rw [compileInitial_cost_eq_completionCost strategy hpositive input]
  unfold Online.runCompletionCost
  change Online.completionCost (.finite rawDuration) processing
      ((compileInitial strategy positive).observations positive input) =
    Online.completionCost (.finite rawDuration) processing result.config.transcript
  rw [← herased]
  exact completionCost_eraseZeroProcesses
    (.finite rawDuration) processing result.config.transcript

/-! ## Literal finite offline benchmark -/

/-- Effective length of the positive atom of a revealing binary input. -/
def binaryEffectiveHigh (u positive : ℝ) : ℝ :=
  1 + min (u - 1) positive

theorem binaryEffectiveHigh_gt_one
    {u positive : ℝ} (hu : 1 < u) (hpositive : 0 < positive) :
    1 < binaryEffectiveHigh u positive := by
  unfold binaryEffectiveHigh
  have : 0 < min (u - 1) positive := lt_min (by linarith) hpositive
  linarith

/-- The revealing binary benchmark is the same pair objective as a blind
binary benchmark whose high effective length is `1 + min (u-1) positive`.
This identifies the literal finite denominator, including its diagonal. -/
theorem empiricalOfflineCost_binary_eq_blindOfflineCost
    {u positive : ℝ} (hu : 1 < u) (hpositive : 0 < positive)
    (input : BinaryInput n) :
    empiricalRevealingOfflineCost u
        (RandomizedYao.binaryProcessing positive input) =
      BlindOptimization.Online.offlineCost (binaryEffectiveHigh u positive)
        (BlindOptimization.RandomizedCompiler.binaryProcessing
          (binaryEffectiveHigh u positive) input) := by
  unfold empiricalRevealingOfflineCost BlindOptimization.Online.offlineCost
  rw [shortestFirst_pair_formula]
  apply congrArg pairCost
  apply congrArg (fun f : Fin n → ℝ => List.ofFn f)
  funext job
  cases hbit : input job
  · have hhigh := binaryEffectiveHigh_gt_one hu hpositive
    simp only [RandomizedYao.binaryProcessing, hbit, Bool.false_eq_true,
      if_false, effectiveLength_finite,
      BlindOptimization.RandomizedCompiler.binaryProcessing,
      BlindOptimization.Online.effectiveLength, add_zero]
    rw [min_eq_right (by linarith : (1 : ℝ) ≤ u),
      min_eq_right (by linarith : (1 : ℝ) ≤ binaryEffectiveHigh u positive)]
  · have hhigh := binaryEffectiveHigh_gt_one hu hpositive
    have hleft : min u (1 + positive) = binaryEffectiveHigh u positive := by
      unfold binaryEffectiveHigh
      calc
        min u (1 + positive) = min (1 + (u - 1)) (1 + positive) := by ring_nf
        _ = 1 + min (u - 1) positive := min_add_add_left 1 (u - 1) positive
    simp only [RandomizedYao.binaryProcessing, hbit, if_true,
      effectiveLength_finite,
      BlindOptimization.RandomizedCompiler.binaryProcessing,
      BlindOptimization.Online.effectiveLength]
    rw [hleft, min_eq_left (by
      linarith [hhigh] : binaryEffectiveHigh u positive ≤
        1 + binaryEffectiveHigh u positive)]

/-- Exact Bernoulli expectation of the literal revealing offline optimum. -/
theorem finiteExpectation_empiricalOfflineCost_binary
    {u positive x : ℝ} (hu : 1 < u) (hpositive : 0 < positive) :
    Randomized.finiteExpectation (bernoulliWeight n x)
        (fun input => empiricalRevealingOfflineCost u
          (RandomizedYao.binaryProcessing positive input)) =
      BlindOptimization.RandomizedLower.binaryExpectedOfflineCost n
        (binaryEffectiveHigh u positive) x := by
  rw [show (fun input : BinaryInput n => empiricalRevealingOfflineCost u
      (RandomizedYao.binaryProcessing positive input)) =
      (fun input => BlindOptimization.Online.offlineCost
        (binaryEffectiveHigh u positive)
        (BlindOptimization.RandomizedCompiler.binaryProcessing
          (binaryEffectiveHigh u positive) input)) by
      funext input
      exact empiricalOfflineCost_binary_eq_blindOfflineCost hu hpositive input]
  exact
    BlindOptimization.RandomizedCompiler.finiteExpectation_binary_offlineCost
      (binaryEffectiveHigh_gt_one hu hpositive)

/-- The compiler can be plugged directly into the two binary families and
the checked finite-Yao theorem. -/
theorem finiteSeed_compiled_binary_families_attain_curve
    {n : ℕ} {u : ℝ} (hu : 1 < u)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Online.Strategy n) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u, ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + (u - 1) * survivalMass τ ^ 2)) ≤
        Randomized.uniformAverage fun seed =>
          (compileInitial (strategy seed) u).cost u u input) ∨
    (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1), ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + τ * survivalMass τ ^ 2)) ≤
        Randomized.uniformAverage fun seed =>
          (compileInitial (strategy seed) τ).cost u τ input) := by
  exact finiteSeed_binary_families_attain_curve hu
    (fun seed _τ => compileInitial (strategy seed) u)
    (fun seed τ => compileInitial (strategy seed) τ)

/-- Literal completion-cost presentation of the preceding compiled Yao
bound.  The selected binary assignment is fixed before the private seed. -/
theorem finiteSeed_compiled_literal_families_attain_curve
    {n : ℕ} {u : ℝ} (hu : 1 < u)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Online.Strategy n) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u, ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + (u - 1) * survivalMass τ ^ 2)) ≤
        Randomized.uniformAverage fun seed =>
          Online.completionCost (.finite u)
            (RandomizedYao.binaryProcessing u input)
            ((compileInitial (strategy seed) u).observations u input)) ∨
    (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1), ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + τ * survivalMass τ ^ 2)) ≤
        Randomized.uniformAverage fun seed =>
          Online.completionCost (.finite u)
            (RandomizedYao.binaryProcessing τ input)
            ((compileInitial (strategy seed) τ).observations τ input)) := by
  rcases finiteSeed_compiled_binary_families_attain_curve hu strategy with
      hB | hA
  · left
    rcases hB with ⟨τ, hτ, input, hcost⟩
    refine ⟨τ, hτ, input, ?_⟩
    have heq :
        (fun seed => (compileInitial (strategy seed) u).cost u u input) =
          (fun seed => Online.completionCost (.finite u)
            (RandomizedYao.binaryProcessing u input)
            ((compileInitial (strategy seed) u).observations u input)) := by
      funext seed
      exact compileInitial_cost_eq_completionCost (strategy seed)
        (by linarith : u ≠ 0) input
    rw [heq] at hcost
    exact hcost
  · right
    rcases hA with ⟨τ, hτ, input, hcost⟩
    refine ⟨τ, hτ, input, ?_⟩
    have heq :
        (fun seed => (compileInitial (strategy seed) τ).cost u τ input) =
          (fun seed => Online.completionCost (.finite u)
            (RandomizedYao.binaryProcessing τ input)
            ((compileInitial (strategy seed) τ).observations τ input)) := by
      funext seed
      exact compileInitial_cost_eq_completionCost (strategy seed)
        (by linarith [hτ.1] : τ ≠ 0) input
    rw [heq] at hcost
    exact hcost

end

end OperationalCompiler
end RevealingOptimization
end SchedulingPaper
