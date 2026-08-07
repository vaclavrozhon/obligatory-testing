import SchedulingPaper.RandomizedIidBinaryLower
import SchedulingPaper.CompletionPairDecomposition
import Mathlib.Tactic

/-!
# Compiling an operational strategy to a fair `0/2` decision tree

This module is the lower-bound bridge between the public-transcript online
semantics and the binary Yao tree.  The symbolic state remembers whether a
completed job was zero or two; this makes zero-duration administrative
`process` actions genuine skip nodes rather than false completions.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open Online

noncomputable section

inductive SymbolicBinaryJobState where
  | untouched
  | testedZero
  | testedTwo
  | doneZero
  | doneTwo
  deriving DecidableEq

def SymbolicBinaryJobState.unfinished : SymbolicBinaryJobState → ℕ
  | .untouched | .testedTwo => 1
  | .testedZero | .doneZero | .doneTwo => 0

def SymbolicBinaryJobState.toOnline : SymbolicBinaryJobState → JobState
  | .untouched => .untouched
  | .testedZero => .tested 0
  | .testedTwo => .tested 2
  | .doneZero | .doneTwo => .done

structure SymbolicBinaryConfig (n : ℕ) where
  jobs : Label n → SymbolicBinaryJobState
  transcript : Transcript n

def SymbolicBinaryConfig.initial (n : ℕ) : SymbolicBinaryConfig n where
  jobs := fun _ => .untouched
  transcript := []

def SymbolicBinaryConfig.unfinished (config : SymbolicBinaryConfig n) : ℕ :=
  ∑ job, (config.jobs job).unfinished

def SymbolicBinaryConfig.toOnline
    (config : SymbolicBinaryConfig n) : Config n where
  jobs := fun job => (config.jobs job).toOnline
  transcript := config.transcript

@[simp] theorem SymbolicBinaryConfig.toOnline_transcript
    (config : SymbolicBinaryConfig n) :
    config.toOnline.transcript = config.transcript := rfl

@[simp] theorem SymbolicBinaryConfig.toOnline_jobs
    (config : SymbolicBinaryConfig n) (job : Label n) :
    config.toOnline.jobs job = (config.jobs job).toOnline := rfl

def SymbolicBinaryConfig.afterTestZero
    (config : SymbolicBinaryConfig n) (job : Label n) :
    SymbolicBinaryConfig n where
  jobs := Function.update config.jobs job .testedZero
  transcript := config.transcript ++ [.testResult job 0]

def SymbolicBinaryConfig.afterTestTwo
    (config : SymbolicBinaryConfig n) (job : Label n) :
    SymbolicBinaryConfig n where
  jobs := Function.update config.jobs job .testedTwo
  transcript := config.transcript ++ [.testResult job 2]

def SymbolicBinaryConfig.afterProcessZero
    (config : SymbolicBinaryConfig n) (job : Label n) :
    SymbolicBinaryConfig n where
  jobs := Function.update config.jobs job .doneZero
  transcript := config.transcript ++ [.processed job]

def SymbolicBinaryConfig.afterProcessTwo
    (config : SymbolicBinaryConfig n) (job : Label n) :
    SymbolicBinaryConfig n where
  jobs := Function.update config.jobs job .doneTwo
  transcript := config.transcript ++ [.processed job]

@[simp] theorem SymbolicBinaryConfig.toOnline_afterTestZero
    (config : SymbolicBinaryConfig n) (job : Label n) :
    (config.afterTestZero job).toOnline =
      { jobs := Function.update config.toOnline.jobs job (.tested 0)
        transcript := config.transcript ++ [.testResult job 0] } := by
  cases config with
  | mk jobs transcript =>
      rw [Config.mk.injEq]
      constructor
      · funext i
        by_cases hi : i = job <;>
          simp [SymbolicBinaryConfig.toOnline,
            SymbolicBinaryConfig.afterTestZero,
            SymbolicBinaryJobState.toOnline, Function.update, hi]
      · rfl

@[simp] theorem SymbolicBinaryConfig.toOnline_afterTestTwo
    (config : SymbolicBinaryConfig n) (job : Label n) :
    (config.afterTestTwo job).toOnline =
      { jobs := Function.update config.toOnline.jobs job (.tested 2)
        transcript := config.transcript ++ [.testResult job 2] } := by
  cases config with
  | mk jobs transcript =>
      rw [Config.mk.injEq]
      constructor
      · funext i
        by_cases hi : i = job <;>
          simp [SymbolicBinaryConfig.toOnline,
            SymbolicBinaryConfig.afterTestTwo,
            SymbolicBinaryJobState.toOnline, Function.update, hi]
      · rfl

@[simp] theorem SymbolicBinaryConfig.toOnline_afterProcessZero
    (config : SymbolicBinaryConfig n) (job : Label n) :
    (config.afterProcessZero job).toOnline =
      { jobs := Function.update config.toOnline.jobs job .done
        transcript := config.transcript ++ [.processed job] } := by
  cases config with
  | mk jobs transcript =>
      rw [Config.mk.injEq]
      constructor
      · funext i
        by_cases hi : i = job <;>
          simp [SymbolicBinaryConfig.toOnline,
            SymbolicBinaryConfig.afterProcessZero,
            SymbolicBinaryJobState.toOnline, Function.update, hi]
      · rfl

@[simp] theorem SymbolicBinaryConfig.toOnline_afterProcessTwo
    (config : SymbolicBinaryConfig n) (job : Label n) :
    (config.afterProcessTwo job).toOnline =
      { jobs := Function.update config.toOnline.jobs job .done
        transcript := config.transcript ++ [.processed job] } := by
  cases config with
  | mk jobs transcript =>
      rw [Config.mk.injEq]
      constructor
      · funext i
        by_cases hi : i = job <;>
          simp [SymbolicBinaryConfig.toOnline,
            SymbolicBinaryConfig.afterProcessTwo,
            SymbolicBinaryJobState.toOnline, Function.update, hi]
      · rfl

theorem SymbolicBinaryConfig.initial_unfinished (n : ℕ) :
    (SymbolicBinaryConfig.initial n).unfinished = n := by
  simp [SymbolicBinaryConfig.unfinished, SymbolicBinaryConfig.initial,
    SymbolicBinaryJobState.unfinished]

private theorem sum_update_unfinished
    (jobs : Label n → SymbolicBinaryJobState) (job : Label n)
    (state : SymbolicBinaryJobState) :
    (∑ i, (Function.update jobs job state i).unfinished) =
      (∑ i, (jobs i).unfinished) - (jobs job).unfinished + state.unfinished := by
  classical
  have hrest :
      (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
          (Function.update jobs job state i).unfinished) =
        ∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
          (jobs i).unfinished := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Function.update, (Finset.mem_erase.mp hi).1]
  have hupdated := Finset.sum_erase_add
    (Finset.univ : Finset (Label n))
    (fun i => (Function.update jobs job state i).unfinished)
    (Finset.mem_univ job)
  have horiginal := Finset.sum_erase_add
    (Finset.univ : Finset (Label n))
    (fun i => (jobs i).unfinished) (Finset.mem_univ job)
  have hsame :
      (Function.update jobs job state job).unfinished = state.unfinished := by
    simp [Function.update]
  calc
    (∑ i, (Function.update jobs job state i).unfinished) =
        (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
          (Function.update jobs job state i).unfinished) +
            (Function.update jobs job state job).unfinished := hupdated.symm
    _ = (∑ i ∈ (Finset.univ : Finset (Label n)).erase job,
          (jobs i).unfinished) + state.unfinished := by rw [hrest, hsame]
    _ = (∑ i, (jobs i).unfinished) - (jobs job).unfinished +
          state.unfinished := by
      rw [← horiginal]
      simp

private theorem unfinished_positive_of_state_one
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hstate : (config.jobs job).unfinished = 1) :
    1 ≤ config.unfinished := by
  unfold SymbolicBinaryConfig.unfinished
  calc
    1 = (config.jobs job).unfinished := hstate.symm
    _ ≤ ∑ i, (config.jobs i).unfinished :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun i => (config.jobs i).unfinished)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ job)

theorem SymbolicBinaryConfig.afterTestZero_unfinished
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) :
    (config.afterTestZero job).unfinished + 1 = config.unfinished := by
  unfold SymbolicBinaryConfig.unfinished SymbolicBinaryConfig.afterTestZero
  rw [sum_update_unfinished]
  have hpositive : 1 ≤ ∑ i, (config.jobs i).unfinished :=
    unfinished_positive_of_state_one config job (by
    simp [hjob, SymbolicBinaryJobState.unfinished])
  simp only [hjob, SymbolicBinaryJobState.unfinished]
  simpa [Nat.add_assoc] using Nat.sub_add_cancel hpositive

theorem SymbolicBinaryConfig.afterTestTwo_unfinished
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) :
    (config.afterTestTwo job).unfinished = config.unfinished := by
  unfold SymbolicBinaryConfig.unfinished SymbolicBinaryConfig.afterTestTwo
  rw [sum_update_unfinished]
  have hpositive : 1 ≤ ∑ i, (config.jobs i).unfinished :=
    unfinished_positive_of_state_one config job (by
    simp [hjob, SymbolicBinaryJobState.unfinished])
  simp only [hjob, SymbolicBinaryJobState.unfinished]
  simpa using Nat.sub_add_cancel hpositive

theorem SymbolicBinaryConfig.afterProcessZero_unfinished
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedZero) :
    (config.afterProcessZero job).unfinished = config.unfinished := by
  unfold SymbolicBinaryConfig.unfinished SymbolicBinaryConfig.afterProcessZero
  rw [sum_update_unfinished]
  simp [hjob, SymbolicBinaryJobState.unfinished]

theorem SymbolicBinaryConfig.afterProcessTwo_unfinished
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedTwo) :
    (config.afterProcessTwo job).unfinished + 1 = config.unfinished := by
  unfold SymbolicBinaryConfig.unfinished SymbolicBinaryConfig.afterProcessTwo
  rw [sum_update_unfinished]
  have hpositive : 1 ≤ ∑ i, (config.jobs i).unfinished :=
    unfinished_positive_of_state_one config job (by
    simp [hjob, SymbolicBinaryJobState.unfinished])
  simp only [hjob, SymbolicBinaryJobState.unfinished]
  simpa [Nat.add_assoc] using Nat.sub_add_cancel hpositive

/-- A total symbolic execution tree.  `stop` assigns the potential `r²` to
an unfinished aborted branch.  For a strategy that actually completes every
binary input this penalty is reached only with `r=0`, hence costs zero. -/
inductive OnlineBinaryTree (n : ℕ) : SymbolicBinaryConfig n → Type
  | stop (config : SymbolicBinaryConfig n) : OnlineBinaryTree n config
  | processZero {config : SymbolicBinaryConfig n} (job : Label n)
      (hjob : config.jobs job = .testedZero)
      (next : OnlineBinaryTree n (config.afterProcessZero job)) :
      OnlineBinaryTree n config
  | processTwo {config : SymbolicBinaryConfig n} (job : Label n)
      (hjob : config.jobs job = .testedTwo)
      (next : OnlineBinaryTree n (config.afterProcessTwo job)) :
      OnlineBinaryTree n config
  | test {config : SymbolicBinaryConfig n} (job : Label n)
      (hjob : config.jobs job = .untouched)
      (zeroBranch : OnlineBinaryTree n (config.afterTestZero job))
      (twoBranch : OnlineBinaryTree n (config.afterTestTwo job)) :
      OnlineBinaryTree n config

def OnlineBinaryTree.cost
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) : ℝ :=
  match tree with
  | .stop config => (config.unfinished : ℝ) ^ 2
  | .processZero _ _ next => next.cost input
  | .processTwo (config := config) _ _ next =>
      2 * (config.unfinished : ℝ) + next.cost input
  | .test (config := config) job _ zeroBranch twoBranch =>
      (config.unfinished : ℝ) +
        if input job then twoBranch.cost input else zeroBranch.cost input

def OnlineBinaryTree.expectedArea
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) : ℝ :=
  match tree with
  | .stop config => (config.unfinished : ℝ) ^ 2
  | .processZero _ _ next => next.expectedArea
  | .processTwo (config := config) _ _ next =>
      2 * (config.unfinished : ℝ) + next.expectedArea
  | .test (config := config) _ _ zeroBranch twoBranch =>
      (config.unfinished : ℝ) +
        (zeroBranch.expectedArea + twoBranch.expectedArea) / 2

/-- Once a coordinate has been tested, the continuation tree and its cost no
longer depend on that coordinate's hidden input bit.  This is the operational
freshness fact needed to average a test node as a fair binary branch. -/
theorem OnlineBinaryTree.cost_flip_of_not_untouched
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n)
    {i : Label n} (hi : config.jobs i ≠ .untouched) :
    tree.cost (flipAt i input) = tree.cost input := by
  induction tree with
  | stop => rfl
  | @processZero config job hjob next ih =>
      simp only [OnlineBinaryTree.cost]
      apply ih
      by_cases hij : i = job
      · subst i
        simp [SymbolicBinaryConfig.afterProcessZero]
      · simpa [SymbolicBinaryConfig.afterProcessZero,
          Function.update, hij]
  | @processTwo config job hjob next ih =>
      simp only [OnlineBinaryTree.cost]
      congr 1
      apply ih
      by_cases hij : i = job
      · subst i
        simp [SymbolicBinaryConfig.afterProcessTwo]
      · simpa [SymbolicBinaryConfig.afterProcessTwo,
          Function.update, hij]
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      have hij : i ≠ job := by
        intro hij
        subst i
        exact hi hjob
      simp only [OnlineBinaryTree.cost]
      rw [flipAt_apply_other input hij]
      cases hbit : input job
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
        rw [ihZero (by
          simpa [SymbolicBinaryConfig.afterTestZero,
            Function.update, hij])]
      · simp only [hbit, ↓reduceIte]
        rw [ihTwo (by
          simpa [SymbolicBinaryConfig.afterTestTwo,
            Function.update, hij])]

/-- The recursive fair-coin area is exactly the uniform average over all
fixed oblivious binary inputs, even though the strategy chooses later labels
adaptively from its public transcript. -/
theorem OnlineBinaryTree.uniformAverage_cost_eq_expectedArea
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) :
    uniformAverage (tree.cost : BinaryInput n → ℝ) = tree.expectedArea := by
  induction tree with
  | stop => simp [OnlineBinaryTree.cost, OnlineBinaryTree.expectedArea]
  | @processZero config job hjob next ih =>
      simpa [OnlineBinaryTree.cost, OnlineBinaryTree.expectedArea] using ih
  | @processTwo config job hjob next ih =>
      simp only [OnlineBinaryTree.cost, OnlineBinaryTree.expectedArea]
      rw [show (fun input : BinaryInput n =>
          2 * (config.unfinished : ℝ) + next.cost input) =
        (fun input =>
          (fun _ : BinaryInput n => 2 * (config.unfinished : ℝ)) input +
            next.cost input) by rfl]
      rw [uniformAverage_add, uniformAverage_const, ih]
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      simp only [OnlineBinaryTree.cost, OnlineBinaryTree.expectedArea]
      rw [show (fun input : BinaryInput n =>
          (config.unfinished : ℝ) +
            (if input job then twoBranch.cost input else zeroBranch.cost input)) =
        (fun input =>
          (fun _ : BinaryInput n => (config.unfinished : ℝ)) input +
            (if input job then twoBranch.cost input else zeroBranch.cost input)) by
              rfl]
      rw [uniformAverage_add, uniformAverage_const]
      rw [uniformAverage_fresh_binary_branch job
        zeroBranch.cost twoBranch.cost
        (fun input => zeroBranch.cost_flip_of_not_untouched input (by
          simp [SymbolicBinaryConfig.afterTestZero]))
        (fun input => twoBranch.cost_flip_of_not_untouched input (by
          simp [SymbolicBinaryConfig.afterTestTwo])),
        ihZero, ihTwo]

/-! ## Exact transcript semantics of a symbolic branch -/

/-- The symbolic history agrees with the fixed hidden binary input. -/
def SymbolicBinaryConfig.Consistent
    (config : SymbolicBinaryConfig n) (input : BinaryInput n) : Prop :=
  ∀ job,
    match config.jobs job with
    | .untouched => True
    | .testedZero | .doneZero => input job = false
    | .testedTwo | .doneTwo => input job = true

theorem SymbolicBinaryConfig.initial_consistent
    (n : ℕ) (input : BinaryInput n) :
    (SymbolicBinaryConfig.initial n).Consistent input := by
  intro job
  simp [SymbolicBinaryConfig.Consistent, SymbolicBinaryConfig.initial]

theorem SymbolicBinaryConfig.afterTestZero_consistent
    {config : SymbolicBinaryConfig n} {input : BinaryInput n}
    (hconsistent : config.Consistent input) (job : Label n)
    (hbit : input job = false) :
    (config.afterTestZero job).Consistent input := by
  intro i
  by_cases hi : i = job
  · subst i
    simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterTestZero] using hbit
  · simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterTestZero, Function.update, hi] using
        hconsistent i

theorem SymbolicBinaryConfig.afterTestTwo_consistent
    {config : SymbolicBinaryConfig n} {input : BinaryInput n}
    (hconsistent : config.Consistent input) (job : Label n)
    (hbit : input job = true) :
    (config.afterTestTwo job).Consistent input := by
  intro i
  by_cases hi : i = job
  · subst i
    simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterTestTwo] using hbit
  · simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterTestTwo, Function.update, hi] using
        hconsistent i

theorem SymbolicBinaryConfig.afterProcessZero_consistent
    {config : SymbolicBinaryConfig n} {input : BinaryInput n}
    (hconsistent : config.Consistent input) (job : Label n)
    (hjob : config.jobs job = .testedZero) :
    (config.afterProcessZero job).Consistent input := by
  intro i
  by_cases hi : i = job
  · subst i
    have hbit : input job = false := by
      have h := hconsistent job
      simpa [SymbolicBinaryConfig.Consistent, hjob] using h
    simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterProcessZero, Function.update] using hbit
  · simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterProcessZero, Function.update, hi] using
        hconsistent i

theorem SymbolicBinaryConfig.afterProcessTwo_consistent
    {config : SymbolicBinaryConfig n} {input : BinaryInput n}
    (hconsistent : config.Consistent input) (job : Label n)
    (hjob : config.jobs job = .testedTwo) :
    (config.afterProcessTwo job).Consistent input := by
  intro i
  by_cases hi : i = job
  · subst i
    have hbit : input job = true := by
      have h := hconsistent job
      simpa [SymbolicBinaryConfig.Consistent, hjob] using h
    simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterProcessTwo, Function.update] using hbit
  · simpa [SymbolicBinaryConfig.Consistent,
      SymbolicBinaryConfig.afterProcessTwo, Function.update, hi] using
        hconsistent i

/-- Operations generated along the unique branch selected by a fixed input. -/
def OnlineBinaryTree.observations
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) : Transcript n :=
  match tree with
  | .stop _ => []
  | .processZero job _ next => .processed job :: next.observations input
  | .processTwo job _ next => .processed job :: next.observations input
  | .test job _ zeroBranch twoBranch =>
      if input job then
        .testResult job 2 :: twoBranch.observations input
      else
        .testResult job 0 :: zeroBranch.observations input

/-- Terminal symbolic configuration along the branch selected by an input. -/
def OnlineBinaryTree.finalConfig
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) :
    SymbolicBinaryConfig n :=
  match tree with
  | .stop config => config
  | .processZero _ _ next => next.finalConfig input
  | .processTwo _ _ next => next.finalConfig input
  | .test job _ zeroBranch twoBranch =>
      if input job then twoBranch.finalConfig input
      else zeroBranch.finalConfig input

theorem OnlineBinaryTree.finalConfig_consistent
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n)
    (hconsistent : config.Consistent input) :
    (tree.finalConfig input).Consistent input := by
  induction tree with
  | stop => exact hconsistent
  | @processZero config job hjob next ih =>
      exact ih (SymbolicBinaryConfig.afterProcessZero_consistent
        hconsistent job hjob)
  | @processTwo config job hjob next ih =>
      exact ih (SymbolicBinaryConfig.afterProcessTwo_consistent
        hconsistent job hjob)
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      cases hbit : input job
      · simp only [OnlineBinaryTree.finalConfig, hbit, ↓reduceIte]
        exact ihZero (SymbolicBinaryConfig.afterTestZero_consistent
          hconsistent job hbit)
      · simp only [OnlineBinaryTree.finalConfig, hbit, ↓reduceIte]
        exact ihTwo (SymbolicBinaryConfig.afterTestTwo_consistent
          hconsistent job hbit)

theorem OnlineBinaryTree.finalConfig_transcript
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) :
    (tree.finalConfig input).transcript =
      config.transcript ++ tree.observations input := by
  induction tree with
  | stop => simp [OnlineBinaryTree.finalConfig, OnlineBinaryTree.observations]
  | @processZero config job hjob next ih =>
      simp only [OnlineBinaryTree.finalConfig, OnlineBinaryTree.observations]
      rw [ih]
      simp [SymbolicBinaryConfig.afterProcessZero, List.append_assoc]
  | @processTwo config job hjob next ih =>
      simp only [OnlineBinaryTree.finalConfig, OnlineBinaryTree.observations]
      rw [ih]
      simp [SymbolicBinaryConfig.afterProcessTwo, List.append_assoc]
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      cases hbit : input job
      · simp only [OnlineBinaryTree.finalConfig, OnlineBinaryTree.observations,
          hbit, Bool.false_eq_true, ↓reduceIte]
        rw [ihZero]
        simp [SymbolicBinaryConfig.afterTestZero, List.append_assoc]
      · simp only [OnlineBinaryTree.finalConfig, OnlineBinaryTree.observations,
          hbit, ↓reduceIte]
        rw [ihTwo]
        simp [SymbolicBinaryConfig.afterTestTwo, List.append_assoc]

@[simp] theorem iidBinaryProcessingTime_eq_zero_of_false
    {n : ℕ} (input : BinaryInput n) (job : Label n)
    (hbit : input job = false) :
    iidBinaryProcessingTime input job = 0 := by
  simp [iidBinaryProcessingTime, positiveIndicator, hbit]

@[simp] theorem iidBinaryProcessingTime_eq_two_of_true
    {n : ℕ} (input : BinaryInput n) (job : Label n)
    (hbit : input job = true) :
    iidBinaryProcessingTime input job = 2 := by
  simp [iidBinaryProcessingTime, positiveIndicator, hbit]

/-- Along every branch, the number of jobs completed by its observations plus
the number still unfinished at its leaf is exactly the number unfinished at
the root.  In particular, a completed leaf generates every required
completion exactly once. -/
theorem OnlineBinaryTree.completionCount_add_final_unfinished
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n)
    (hconsistent : config.Consistent input) :
    completionCount (iidBinaryProcessingTime input)
        (tree.observations input) +
      (tree.finalConfig input).unfinished = config.unfinished := by
  induction tree with
  | stop => simp [OnlineBinaryTree.observations, OnlineBinaryTree.finalConfig]
  | @processZero config job hjob next ih =>
      have hbit : input job = false := by
        have h := hconsistent job
        simpa [SymbolicBinaryConfig.Consistent, hjob] using h
      have hchild := ih (SymbolicBinaryConfig.afterProcessZero_consistent
        hconsistent job hjob)
      have htransition := config.afterProcessZero_unfinished job hjob
      simp only [OnlineBinaryTree.observations, OnlineBinaryTree.finalConfig,
        completionCount_cons]
      simp [Observation.completionLabel, hbit] at hchild ⊢
      omega
  | @processTwo config job hjob next ih =>
      have hbit : input job = true := by
        have h := hconsistent job
        simpa [SymbolicBinaryConfig.Consistent, hjob] using h
      have hchild := ih (SymbolicBinaryConfig.afterProcessTwo_consistent
        hconsistent job hjob)
      have htransition := config.afterProcessTwo_unfinished job hjob
      simp only [OnlineBinaryTree.observations, OnlineBinaryTree.finalConfig,
        completionCount_cons]
      simp [Observation.completionLabel, hbit] at hchild ⊢
      omega
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      cases hbit : input job
      · have hchild := ihZero
          (SymbolicBinaryConfig.afterTestZero_consistent hconsistent job hbit)
        have htransition := config.afterTestZero_unfinished job hjob
        simp only [OnlineBinaryTree.observations, OnlineBinaryTree.finalConfig,
          hbit, Bool.false_eq_true, ↓reduceIte, completionCount_cons]
        simp [Observation.completionLabel] at hchild ⊢
        omega
      · have hchild := ihTwo
          (SymbolicBinaryConfig.afterTestTwo_consistent hconsistent job hbit)
        have htransition := config.afterTestTwo_unfinished job hjob
        simp only [OnlineBinaryTree.observations, OnlineBinaryTree.finalConfig]
        simp [hbit, Observation.completionLabel] at hchild ⊢
        omega

/-- On a branch that finishes every job, the symbolic recursive cost is
exactly the suffix-weighted duration of the emitted operational transcript. -/
theorem OnlineBinaryTree.cost_eq_suffixWeightedDuration
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n)
    (hconsistent : config.Consistent input)
    (hcomplete : (tree.finalConfig input).unfinished = 0) :
    tree.cost input =
      suffixWeightedDuration .infinite (iidBinaryProcessingTime input)
        (tree.observations input) := by
  induction tree with
  | stop =>
      simp [OnlineBinaryTree.cost, OnlineBinaryTree.observations,
        OnlineBinaryTree.finalConfig] at hcomplete ⊢
      exact hcomplete
  | @processZero config job hjob next ih =>
      have hbit : input job = false := by
        have h := hconsistent job
        simpa [SymbolicBinaryConfig.Consistent, hjob] using h
      have hchildComplete : (next.finalConfig input).unfinished = 0 := hcomplete
      have hchildConsistent :=
        SymbolicBinaryConfig.afterProcessZero_consistent hconsistent job hjob
      have hchild := ih hchildConsistent hchildComplete
      simp only [OnlineBinaryTree.cost, OnlineBinaryTree.observations,
        suffixWeightedDuration_cons]
      simp [Observation.duration, hbit, hchild]
  | @processTwo config job hjob next ih =>
      have hbit : input job = true := by
        have h := hconsistent job
        simpa [SymbolicBinaryConfig.Consistent, hjob] using h
      have hchildComplete : (next.finalConfig input).unfinished = 0 := hcomplete
      have hchildConsistent :=
        SymbolicBinaryConfig.afterProcessTwo_consistent hconsistent job hjob
      have hchild := ih hchildConsistent hchildComplete
      have hcount := OnlineBinaryTree.completionCount_add_final_unfinished
        (OnlineBinaryTree.processTwo job hjob next) input hconsistent
      rw [hcomplete, Nat.add_zero] at hcount
      simp only [OnlineBinaryTree.observations] at hcount
      simp only [OnlineBinaryTree.cost, OnlineBinaryTree.observations,
        suffixWeightedDuration_cons]
      rw [hcount, hchild]
      simp [Observation.duration, hbit]
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      cases hbit : input job
      · have hchildComplete :
            (zeroBranch.finalConfig input).unfinished = 0 := by
          simpa [OnlineBinaryTree.finalConfig, hbit] using hcomplete
        have hchild := ihZero
          (SymbolicBinaryConfig.afterTestZero_consistent hconsistent job hbit)
            hchildComplete
        have hcount := OnlineBinaryTree.completionCount_add_final_unfinished
          (OnlineBinaryTree.test job hjob zeroBranch twoBranch) input hconsistent
        rw [hcomplete, Nat.add_zero] at hcount
        simp only [OnlineBinaryTree.observations, hbit, Bool.false_eq_true,
          ↓reduceIte] at hcount
        simp only [OnlineBinaryTree.cost, OnlineBinaryTree.observations,
          hbit, Bool.false_eq_true, ↓reduceIte, suffixWeightedDuration_cons]
        rw [hcount, hchild]
        simp [Observation.duration]
      · have hchildComplete :
            (twoBranch.finalConfig input).unfinished = 0 := by
          simpa [OnlineBinaryTree.finalConfig, hbit] using hcomplete
        have hchild := ihTwo
          (SymbolicBinaryConfig.afterTestTwo_consistent hconsistent job hbit)
            hchildComplete
        have hcount := OnlineBinaryTree.completionCount_add_final_unfinished
          (OnlineBinaryTree.test job hjob zeroBranch twoBranch) input hconsistent
        rw [hcomplete, Nat.add_zero] at hcount
        simp only [OnlineBinaryTree.observations, hbit, ↓reduceIte] at hcount
        simp only [OnlineBinaryTree.cost, OnlineBinaryTree.observations,
          hbit, ↓reduceIte, suffixWeightedDuration_cons]
        rw [hcount, hchild]
        simp [Observation.duration]
/-- The fair-binary potential survives arbitrary transcript-dependent choices,
zero-duration administrative processing, invalid actions, and early stops. -/
theorem OnlineBinaryTree.sq_le_expectedArea
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) :
    (config.unfinished : ℝ) ^ 2 ≤ tree.expectedArea := by
  induction tree with
  | stop => rfl
  | @processZero config job hjob next ih =>
      simp only [OnlineBinaryTree.expectedArea]
      rw [config.afterProcessZero_unfinished job hjob] at ih
      exact ih
  | @processTwo config job hjob next ih =>
      simp only [OnlineBinaryTree.expectedArea]
      have hcount := config.afterProcessTwo_unfinished job hjob
      have hcountR :
          ((config.afterProcessTwo job).unfinished : ℝ) + 1 =
            (config.unfinished : ℝ) := by
        exact_mod_cast hcount
      nlinarith
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      simp only [OnlineBinaryTree.expectedArea]
      have hzero := config.afterTestZero_unfinished job hjob
      have htwo := config.afterTestTwo_unfinished job hjob
      have hzeroR :
          ((config.afterTestZero job).unfinished : ℝ) + 1 =
            (config.unfinished : ℝ) := by
        exact_mod_cast hzero
      have htwoR :
          ((config.afterTestTwo job).unfinished : ℝ) =
            (config.unfinished : ℝ) := by
        exact_mod_cast htwo
      nlinarith

/-- Compile `fuel` steps of any deterministic transcript-only strategy.  Raw
and invalid actions become `stop` nodes; legal tests branch on a fresh hidden
bit, and legal processing actions follow the revealed symbolic state. -/
def compileOnlineBinaryTree
    {n : ℕ} (strategy : Strategy n) :
    (fuel : ℕ) → (config : SymbolicBinaryConfig n) →
      OnlineBinaryTree n config
  | 0, config => .stop config
  | fuel + 1, config =>
      match strategy config.transcript with
      | none => .stop config
      | some (.raw _) => .stop config
      | some (.test job) =>
          if hjob : config.jobs job = .untouched then
            .test job hjob
              (compileOnlineBinaryTree strategy fuel
                (config.afterTestZero job))
              (compileOnlineBinaryTree strategy fuel
                (config.afterTestTwo job))
          else .stop config
      | some (.process job) =>
          if hzero : config.jobs job = .testedZero then
            .processZero job hzero
              (compileOnlineBinaryTree strategy fuel
                (config.afterProcessZero job))
          else if htwo : config.jobs job = .testedTwo then
            .processTwo job htwo
              (compileOnlineBinaryTree strategy fuel
                (config.afterProcessTwo job))
          else .stop config

@[simp] theorem Config.step_symbolic_testZero
    {n : ℕ} (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) (input : BinaryInput n)
    (hbit : input job = false) :
    Config.step .infinite (fixedOracle (iidBinaryProcessingTime input))
        config.toOnline (.test job) =
      some (config.afterTestZero job).toOnline := by
  rw [SymbolicBinaryConfig.toOnline_afterTestZero]
  simp [Config.step, SymbolicBinaryConfig.toOnline,
    SymbolicBinaryJobState.toOnline, hjob, fixedOracle,
    iidBinaryProcessingTime, positiveIndicator, hbit]

@[simp] theorem Config.step_symbolic_testTwo
    {n : ℕ} (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) (input : BinaryInput n)
    (hbit : input job = true) :
    Config.step .infinite (fixedOracle (iidBinaryProcessingTime input))
        config.toOnline (.test job) =
      some (config.afterTestTwo job).toOnline := by
  rw [SymbolicBinaryConfig.toOnline_afterTestTwo]
  simp [Config.step, SymbolicBinaryConfig.toOnline,
    SymbolicBinaryJobState.toOnline, hjob, fixedOracle,
    iidBinaryProcessingTime, positiveIndicator, hbit]

@[simp] theorem Config.step_symbolic_processZero
    {n : ℕ} (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedZero) (input : BinaryInput n) :
    Config.step .infinite (fixedOracle (iidBinaryProcessingTime input))
        config.toOnline (.process job) =
      some (config.afterProcessZero job).toOnline := by
  rw [SymbolicBinaryConfig.toOnline_afterProcessZero]
  simp [Config.step, SymbolicBinaryConfig.toOnline,
    SymbolicBinaryJobState.toOnline, hjob]

@[simp] theorem Config.step_symbolic_processTwo
    {n : ℕ} (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedTwo) (input : BinaryInput n) :
    Config.step .infinite (fixedOracle (iidBinaryProcessingTime input))
        config.toOnline (.process job) =
      some (config.afterProcessTwo job).toOnline := by
  rw [SymbolicBinaryConfig.toOnline_afterProcessTwo]
  simp [Config.step, SymbolicBinaryConfig.toOnline,
    SymbolicBinaryJobState.toOnline, hjob]
/-- The symbolic compiler follows exactly the same configurations as the
fuelled operational semantics on a fixed `0/2` oracle. -/
theorem compileOnlineBinaryTree_finalConfig_toOnline
    {n : ℕ} (strategy : Strategy n) (fuel : ℕ)
    (config : SymbolicBinaryConfig n) (input : BinaryInput n) :
    ((compileOnlineBinaryTree strategy fuel config).finalConfig input).toOnline =
      (runFuel .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel config.toOnline).config := by
  induction fuel generalizing config with
  | zero =>
      simp [compileOnlineBinaryTree, OnlineBinaryTree.finalConfig, runFuel]
  | succ fuel ih =>
      cases hs : strategy config.transcript with
      | none =>
          simp [compileOnlineBinaryTree, OnlineBinaryTree.finalConfig,
            runFuel, SymbolicBinaryConfig.toOnline, hs]
      | some action =>
          cases action with
          | raw job =>
              simp [compileOnlineBinaryTree, OnlineBinaryTree.finalConfig,
                runFuel, SymbolicBinaryConfig.toOnline, hs, Config.step]
          | test job =>
              cases hstate : config.jobs job with
              | untouched =>
                  cases hbit : input job
                  · have hp := iidBinaryProcessingTime_eq_zero_of_false
                      input job hbit
                    simpa only [compileOnlineBinaryTree, hs, dif_pos hstate,
                      OnlineBinaryTree.finalConfig, hbit,
                      Bool.false_eq_true, ↓reduceIte, runFuel,
                      SymbolicBinaryConfig.toOnline_transcript,
                      Config.step_symbolic_testZero config job hstate input hbit,
                      Option.some.injEq] using
                      ih (config.afterTestZero job)
                  · have hp := iidBinaryProcessingTime_eq_two_of_true
                      input job hbit
                    simpa only [compileOnlineBinaryTree, hs, dif_pos hstate,
                      OnlineBinaryTree.finalConfig, hbit, ↓reduceIte, runFuel,
                      SymbolicBinaryConfig.toOnline_transcript,
                      Config.step_symbolic_testTwo config job hstate input hbit,
                      Option.some.injEq] using
                      ih (config.afterTestTwo job)
              | testedZero =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
              | testedTwo =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
              | doneZero =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
              | doneTwo =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
          | process job =>
              cases hstate : config.jobs job with
              | untouched =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
              | testedZero =>
                  simpa only [compileOnlineBinaryTree, hs, hstate,
                    OnlineBinaryTree.finalConfig, runFuel,
                    SymbolicBinaryConfig.toOnline_transcript,
                    Config.step_symbolic_processZero config job hstate input,
                    Option.some.injEq] using
                    ih (config.afterProcessZero job)
              | testedTwo =>
                  simpa only [compileOnlineBinaryTree, hs, hstate,
                    OnlineBinaryTree.finalConfig, runFuel,
                    SymbolicBinaryConfig.toOnline_transcript,
                    Config.step_symbolic_processTwo config job hstate input,
                    Option.some.injEq] using
                    ih (config.afterProcessTwo job)
              | doneZero =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]
              | doneTwo =>
                  simp [compileOnlineBinaryTree,
                    OnlineBinaryTree.finalConfig, runFuel, hs, hstate,
                    Config.step, SymbolicBinaryConfig.toOnline,
                    SymbolicBinaryJobState.toOnline]

theorem SymbolicBinaryConfig.unfinished_eq_zero_of_toOnline_done
    (config : SymbolicBinaryConfig n)
    (hdone : ∀ job, config.toOnline.jobs job = .done) :
    config.unfinished = 0 := by
  unfold SymbolicBinaryConfig.unfinished
  apply Finset.sum_eq_zero
  intro job _
  have h := hdone job
  cases hstate : config.jobs job <;>
    simp [SymbolicBinaryConfig.toOnline, SymbolicBinaryJobState.toOnline,
      SymbolicBinaryJobState.unfinished, hstate] at h ⊢

theorem compileOnlineBinaryTree_initial_lower
    (n fuel : ℕ) (strategy : Strategy n) :
    (n : ℝ) ^ 2 ≤
      (compileOnlineBinaryTree strategy fuel
        (SymbolicBinaryConfig.initial n)).expectedArea := by
  have h := OnlineBinaryTree.sq_le_expectedArea
    (compileOnlineBinaryTree strategy fuel (SymbolicBinaryConfig.initial n))
  simpa [SymbolicBinaryConfig.initial_unfinished] using h

theorem compileOnlineBinaryTree_initial_uniform_lower
    (n fuel : ℕ) (strategy : Strategy n) :
    (n : ℝ) ^ 2 ≤ uniformAverage fun input : BinaryInput n =>
      (compileOnlineBinaryTree strategy fuel
        (SymbolicBinaryConfig.initial n)).cost input := by
  rw [(compileOnlineBinaryTree strategy fuel
    (SymbolicBinaryConfig.initial n)).uniformAverage_cost_eq_expectedArea]
  exact compileOnlineBinaryTree_initial_lower n fuel strategy

/-- For a terminating execution, the compiled branch cost is the literal
sum of completion times returned by the public operational semantics. -/
theorem compileOnlineBinaryTree_initial_cost_eq_runCompletionCost
    {n : ℕ} (strategy : Strategy n) (fuel : ℕ)
    (input : BinaryInput n)
    (hdone : ∀ job,
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel).config.jobs job = .done) :
    (compileOnlineBinaryTree strategy fuel
        (SymbolicBinaryConfig.initial n)).cost input =
      runCompletionCost .infinite (iidBinaryProcessingTime input)
        (run .infinite (fixedOracle (iidBinaryProcessingTime input))
          strategy fuel) := by
  let tree := compileOnlineBinaryTree strategy fuel
    (SymbolicBinaryConfig.initial n)
  let result := run .infinite
    (fixedOracle (iidBinaryProcessingTime input)) strategy fuel
  have hmirror : (tree.finalConfig input).toOnline = result.config := by
    simpa [tree, result, run] using
      compileOnlineBinaryTree_finalConfig_toOnline strategy fuel
        (SymbolicBinaryConfig.initial n) input
  have hfinalDone : ∀ job,
      (tree.finalConfig input).toOnline.jobs job = .done := by
    intro job
    rw [hmirror]
    exact hdone job
  have hcomplete : (tree.finalConfig input).unfinished = 0 :=
    (tree.finalConfig input).unfinished_eq_zero_of_toOnline_done hfinalDone
  have hcost := tree.cost_eq_suffixWeightedDuration input
    (SymbolicBinaryConfig.initial_consistent n input) hcomplete
  have hfinalTranscript := tree.finalConfig_transcript input
  have hmirrorTranscript := congrArg (fun c : Config n => c.transcript) hmirror
  have htranscript : tree.observations input = result.config.transcript := by
    simpa [SymbolicBinaryConfig.initial] using
      hfinalTranscript.symm.trans hmirrorTranscript
  rw [runCompletionCost_eq_suffixWeightedDuration]
  simpa [result, htranscript] using hcost

/-- Every deterministic terminating transcript-only strategy pays at least
`n²` on average under independent fair hidden processing times `0/2`. -/
theorem onlineStrategy_iidBinary_uniformAverage_lower
    {n : ℕ} (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ input job,
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel).config.jobs job = .done) :
    (n : ℝ) ^ 2 ≤ uniformAverage fun input : BinaryInput n =>
      runCompletionCost .infinite (iidBinaryProcessingTime input)
        (run .infinite (fixedOracle (iidBinaryProcessingTime input))
          strategy fuel) := by
  calc
    (n : ℝ) ^ 2 ≤ uniformAverage fun input : BinaryInput n =>
        (compileOnlineBinaryTree strategy fuel
          (SymbolicBinaryConfig.initial n)).cost input :=
      compileOnlineBinaryTree_initial_uniform_lower n fuel strategy
    _ = uniformAverage fun input : BinaryInput n =>
        runCompletionCost .infinite (iidBinaryProcessingTime input)
          (run .infinite (fixedOracle (iidBinaryProcessingTime input))
            strategy fuel) := by
      apply congrArg uniformAverage
      funext input
      exact compileOnlineBinaryTree_initial_cost_eq_runCompletionCost
        strategy fuel input (hdone input)

/-- Operational Yao lower bound: no abstract policy-tree premise remains.
Each seed is an arbitrary public-transcript `Online.Strategy`; the only
premise says that the supplied common fuel suffices to finish every binary
input.  The selected input is fixed before the seed is drawn. -/
theorem onlineStrategies_oblivious_iid_binary_lower_actualOPT
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Strategy n) (fuel : ℕ)
    (hdone : ∀ seed input job,
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        (strategy seed) fuel).config.jobs job = .done) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) *
          finiteObligatoryOPT (iidBinaryProcessingTime input) ≤
        uniformAverage fun seed =>
          runCompletionCost .infinite (iidBinaryProcessingTime input)
            (run .infinite (fixedOracle (iidBinaryProcessingTime input))
              (strategy seed) fuel) := by
  let cost : BinaryInput n → Seeds → ℝ := fun input seed =>
    runCompletionCost .infinite (iidBinaryProcessingTime input)
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        (strategy seed) fuel)
  have hjoint : (n : ℝ) ^ 2 ≤ uniformAverage fun input : BinaryInput n =>
      uniformAverage fun seed => cost input seed := by
    rw [uniformAverage_comm]
    calc
      (n : ℝ) ^ 2 = uniformAverage (fun _seed : Seeds => (n : ℝ) ^ 2) :=
        (uniformAverage_const _).symm
      _ ≤ uniformAverage (fun seed =>
          uniformAverage fun input : BinaryInput n => cost input seed) := by
        apply uniformAverage_mono
        intro seed
        exact onlineStrategy_iidBinary_uniformAverage_lower
          (strategy seed) fuel (hdone seed)
  apply finite_yao_select_ratio cost
    (fun input => finiteObligatoryOPT (iidBinaryProcessingTime input))
      (L := (n : ℝ) ^ 2)
      (O := (3 * (n : ℝ) ^ 2 + 5 * n) / 4)
  · exact hjoint
  · calc
      uniformAverage (fun input : BinaryInput n =>
          finiteObligatoryOPT (iidBinaryProcessingTime input)) =
          uniformAverage (iidBinaryOfflineCost n) := by
            apply congrArg uniformAverage
            funext input
            exact (iidBinaryOfflineCost_eq_finiteObligatoryOPT hn input).symm
      _ = (3 * (n : ℝ) ^ 2 + 5 * n) / 4 :=
        uniformAverage_iidBinaryOfflineCost n
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    field_simp
    norm_num

end

end RandomizedObligatory
end SchedulingPaper
