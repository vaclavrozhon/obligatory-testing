import SchedulingPaper.BlindOptimizationModel
import SchedulingPaper.BlindOptimizationDeterministicUpper
import SchedulingPaper.BlindOptimizationRandomizedLower
import SchedulingPaper.RandomizedIidBinaryLower

/-!
# Compiling operational blind-optimization strategies to binary trees

This is the structural part of the randomized lower-bound bridge.  Starting
from an arbitrary transcript-only deterministic strategy, it unfolds the
strategy on the two possible optimized observations.  Raw completions have a
single continuation because they reveal no processing time.  Invalid or
prematurely stopped branches are completed by a canonical raw fallback; on a
strategy that completes every input these branches are unreachable.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace RandomizedCompiler

open Online
open RandomizedLower

noncomputable section

def rawFallback : (remaining : ℕ) → BinaryPolicy remaining
  | 0 => .done
  | remaining + 1 => .raw (rawFallback remaining)

@[simp] theorem rawFallback_expectedCost (remaining : ℕ) (u b : ℝ) :
    (rawFallback remaining).expectedCost u b =
      u * triangularCount remaining := by
  induction remaining with
  | zero => simp [rawFallback, BinaryPolicy.expectedCost]
  | succ remaining ih =>
      simp only [rawFallback, BinaryPolicy.expectedCost, ih,
        triangularCount_succ]
      push_cast
      ring

/-- Unfold an arbitrary operational strategy from a truthful binary-history
state.  `remaining` is the set of labels not yet completed. -/
def compileStrategy (strategy : Strategy n) (u : ℝ) :
    (remaining : Finset (Fin n)) → Transcript n →
      BinaryPolicy remaining.card
  | remaining, transcript =>
      match haction : strategy transcript with
      | none => rawFallback remaining.card
      | some action =>
          if hfresh : action.job ∈ remaining then
            let rest := remaining.erase action.job
            have hcard : rest.card + 1 = remaining.card :=
              Finset.card_erase_add_one hfresh
            match action.mode with
            | .raw =>
                hcard ▸ BinaryPolicy.raw
                  (compileStrategy strategy u rest
                    (transcript ++ [.rawCompleted action.job]))
            | .optimized =>
                hcard ▸ BinaryPolicy.optimized
                  (compileStrategy strategy u rest
                    (transcript ++
                      [.optimizedCompleted action.job 0]))
                  (compileStrategy strategy u rest
                    (transcript ++
                      [.optimizedCompleted action.job u]))
          else rawFallback remaining.card
termination_by remaining => remaining.card
decreasing_by
  all_goals
    exact Finset.card_erase_lt_of_mem hfresh

def compileInitial (strategy : Strategy n) (u : ℝ) : BinaryPolicy n := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  exact hcard ▸ compileStrategy strategy u Finset.univ []

/-- Every literal deterministic online strategy therefore supplies a fully
adaptive binary tree to which the checked tree lower bound applies. -/
theorem compileInitial_expectedCost_lower
    (strategy : Strategy n) {u b : ℝ}
    (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    triangularCount n * min u (1 + b * u) ≤
      (compileInitial strategy u).expectedCost u b := by
  exact BinaryPolicy.expectedCost_lower
    (compileInitial strategy u) hu0 hb0 hb1

/-- At a curve-maximizing Bernoulli mass, the compiled operational strategy
obeys the exact adaptive-tree leading lower bound. -/
theorem exists_binary_mass_compiled_curve_lower
    (strategy : Strategy n) {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      (n : ℝ) * (n + 1) / 2 *
          (randomizedCurve u * (1 + (u - 1) * b ^ 2)) ≤
        (compileInitial strategy u).expectedCost u b := by
  exact exists_binary_mass_adaptive_curve_lower
    (compileInitial strategy u) hu

/-! ## Label-preserving operational compiler

`compileStrategy` above is the smallest object needed for the scalar
potential argument.  The following labelled tree retains the chosen job at
every node.  This extra information lets us prove that its branch cost is
literally the cost returned by `Online.run`, and hence closes the operational
Yao bridge.
-/

/-- A total decision tree over the jobs in `remaining`.  A stop node carries
the canonical all-raw penalty.  For a completing strategy such a node can be
reached only after every job has been completed, where the penalty is zero. -/
inductive LabelledTree (n : ℕ) : Finset (Fin n) → Type
  | stop {remaining : Finset (Fin n)} : LabelledTree n remaining
  | raw {remaining : Finset (Fin n)} (job : Fin n)
      (hjob : job ∈ remaining)
      (next : LabelledTree n (remaining.erase job)) :
      LabelledTree n remaining
  | optimized {remaining : Finset (Fin n)} (job : Fin n)
      (hjob : job ∈ remaining)
      (zeroBranch longBranch : LabelledTree n (remaining.erase job)) :
      LabelledTree n remaining

/-- The binary processing-time assignment represented by an input bit-vector. -/
def binaryProcessing (u : ℝ) (input : BinaryInput n) (job : Fin n) : ℝ :=
  if input job then u else 0

/-- The observations emitted on the branch selected by `input`. -/
def LabelledTree.observations
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u : ℝ) (input : BinaryInput n) : Transcript n :=
  match tree with
  | .stop => []
  | .raw job _ next =>
      .rawCompleted job :: next.observations u input
  | .optimized job _ zeroBranch longBranch =>
      if input job then
        .optimizedCompleted job u :: longBranch.observations u input
      else
        .optimizedCompleted job 0 :: zeroBranch.observations u input

/-- Jobs still unfinished at the leaf selected by `input`. -/
def LabelledTree.finalRemaining
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (input : BinaryInput n) : Finset (Fin n) :=
  match tree with
  | .stop => remaining
  | .raw _ _ next => next.finalRemaining input
  | .optimized job _ zeroBranch longBranch =>
      if input job then longBranch.finalRemaining input
      else zeroBranch.finalRemaining input

/-- Completion area accumulated after the current history. -/
def LabelledTree.cost
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u : ℝ) (input : BinaryInput n) : ℝ :=
  match tree with
  | .stop => u * triangularCount remaining.card
  | .raw _ _ next =>
      u * remaining.card + next.cost u input
  | .optimized job _ zeroBranch longBranch =>
      if input job then
        (1 + u) * remaining.card + longBranch.cost u input
      else
        remaining.card + zeroBranch.cost u input

/-- Recursive expectation under the exact iid Bernoulli law. -/
def LabelledTree.expectedCost
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u b : ℝ) : ℝ :=
  match tree with
  | .stop => u * triangularCount remaining.card
  | .raw _ _ next =>
      u * remaining.card + next.expectedCost u b
  | .optimized _ _ zeroBranch longBranch =>
      (1 - b) * (remaining.card + zeroBranch.expectedCost u b) +
        b * ((1 + u) * remaining.card + longBranch.expectedCost u b)

/-- Flipping a coordinate outside `remaining` cannot affect a branch cost. -/
theorem LabelledTree.cost_flip_of_not_mem
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u : ℝ) (input : BinaryInput n) {job : Fin n}
    (hjob : job ∉ remaining) :
    tree.cost u (RandomizedObligatory.flipAt job input) = tree.cost u input := by
  induction tree with
  | stop => rfl
  | @raw remaining selected hselected next ih =>
      simp only [LabelledTree.cost]
      rw [ih (by simp [hjob])]
  | @optimized remaining selected hselected zeroBranch longBranch ihZero ihLong =>
      have hne : job ≠ selected := by
        intro heq
        subst job
        exact hjob hselected
      simp only [LabelledTree.cost]
      rw [RandomizedObligatory.flipAt_apply_other input hne]
      split
      · rw [ihLong (by simp [hjob])]
      · rw [ihZero (by simp [hjob])]

private theorem bernoulliWeight_factor
    (b : ℝ) (job : Fin n) (input : BinaryInput n) :
    bernoulliWeight n b input =
      (if input job then b else 1 - b) *
        ∏ other ∈ (Finset.univ : Finset (Fin n)).erase job,
          if input other then b else 1 - b := by
  unfold bernoulliWeight
  exact (Finset.mul_prod_erase Finset.univ
    (fun other => if input other then b else 1 - b)
    (Finset.mem_univ job)).symm

/-- Exact Bernoulli analogue of the fresh fair-coin branch lemma. -/
theorem finiteExpectation_fresh_bernoulli_branch
    (b : ℝ) (job : Fin n) (zero long : BinaryInput n → ℝ)
    (hzero : ∀ input,
      zero (RandomizedObligatory.flipAt job input) = zero input)
    (hlong : ∀ input,
      long (RandomizedObligatory.flipAt job input) = long input) :
    Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => if input job then long input else zero input) =
      (1 - b) * Randomized.finiteExpectation (bernoulliWeight n b) zero +
        b * Randomized.finiteExpectation (bernoulliWeight n b) long := by
  let branch : BinaryInput n → ℝ := fun input =>
    if input job then long input else zero input
  let flip := RandomizedObligatory.flipAt job
  have hreparam :
      Randomized.finiteExpectation
          ((bernoulliWeight n b) ∘ flip) (branch ∘ flip) =
        Randomized.finiteExpectation (bernoulliWeight n b) branch :=
    Randomized.finiteExpectation_comp_equiv flip _ _
  have hpair : ∀ input,
      bernoulliWeight n b input * branch input +
          bernoulliWeight n b (flip input) * branch (flip input) =
        (1 - b) *
            (bernoulliWeight n b input * zero input +
              bernoulliWeight n b (flip input) * zero (flip input)) +
          b *
            (bernoulliWeight n b input * long input +
              bernoulliWeight n b (flip input) * long (flip input)) := by
    intro input
    have hw := bernoulliWeight_factor b job input
    have hwflip := bernoulliWeight_factor b job (flip input)
    have hrest :
        (∏ other ∈ (Finset.univ : Finset (Fin n)).erase job,
            if flip input other then b else 1 - b) =
          ∏ other ∈ (Finset.univ : Finset (Fin n)).erase job,
            if input other then b else 1 - b := by
      apply Finset.prod_congr rfl
      intro other hother
      rw [RandomizedObligatory.flipAt_apply_other input
        (Finset.ne_of_mem_erase hother).symm]
    rw [hrest] at hwflip
    rw [hw, hwflip]
    cases hbit : input job <;>
      simp [branch, flip, hbit, hzero, hlong,
        RandomizedObligatory.flipAt_apply_same] <;> ring
  change (∑ input, bernoulliWeight n b input * branch input) =
    (1 - b) * (∑ input, bernoulliWeight n b input * zero input) +
      b * (∑ input, bernoulliWeight n b input * long input)
  have hsumPair := Finset.sum_congr
    (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun input _ => hpair input)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPair
  have hflipBranch :
      (∑ input, bernoulliWeight n b (flip input) * branch (flip input)) =
        ∑ input, bernoulliWeight n b input * branch input := by
    simpa [Randomized.finiteExpectation, Function.comp_apply] using hreparam
  have hflipZero :
      (∑ input, bernoulliWeight n b (flip input) * zero (flip input)) =
        ∑ input, bernoulliWeight n b input * zero input := by
    simpa using Fintype.sum_equiv flip
      (fun input => bernoulliWeight n b (flip input) * zero (flip input))
      (fun input => bernoulliWeight n b input * zero input) (fun _ => rfl)
  have hflipLong :
      (∑ input, bernoulliWeight n b (flip input) * long (flip input)) =
        ∑ input, bernoulliWeight n b input * long input := by
    simpa using Fintype.sum_equiv flip
      (fun input => bernoulliWeight n b (flip input) * long (flip input))
      (fun input => bernoulliWeight n b input * long input) (fun _ => rfl)
  rw [hflipBranch, hflipZero, hflipLong] at hsumPair
  linarith

/-- Structural expectation equals the exact weighted finite expectation over
all labelled oblivious binary inputs. -/
theorem LabelledTree.finiteExpectation_cost_eq_expectedCost
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u b : ℝ) :
    Randomized.finiteExpectation (bernoulliWeight n b) (tree.cost u) =
      tree.expectedCost u b := by
  induction tree with
  | @stop remaining =>
      exact Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b) _
  | @raw remaining job hjob next ih =>
      simp only [LabelledTree.cost, LabelledTree.expectedCost]
      rw [show (fun input : BinaryInput n =>
          u * (remaining.card : ℝ) + next.cost u input) =
        (fun input => (fun _ : BinaryInput n => u * (remaining.card : ℝ)) input +
          next.cost u input) by rfl,
        Randomized.finiteExpectation_add,
        Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b), ih]
  | @optimized remaining job hjob zeroBranch longBranch ihZero ihLong =>
      simp only [LabelledTree.cost, LabelledTree.expectedCost]
      rw [finiteExpectation_fresh_bernoulli_branch b job
        (fun input => (remaining.card : ℝ) + zeroBranch.cost u input)
        (fun input => (1 + u) * (remaining.card : ℝ) + longBranch.cost u input)
        (fun input => by
          dsimp
          rw [zeroBranch.cost_flip_of_not_mem u input (by simp)])
        (fun input => by
          dsimp
          rw [longBranch.cost_flip_of_not_mem u input (by simp)])]
      rw [Randomized.finiteExpectation_add,
        Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b), ihZero]
      rw [Randomized.finiteExpectation_add,
        Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b), ihLong]

/-- The labelled tree satisfies the same adaptive potential lower bound as
the scalar tree, including early stops and invalid operational actions. -/
theorem LabelledTree.expectedCost_lower
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    {u b : ℝ} (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    triangularCount remaining.card * min u (1 + b * u) ≤
      tree.expectedCost u b := by
  induction tree with
  | @stop remaining =>
      simp only [LabelledTree.expectedCost]
      have htri : 0 ≤ triangularCount remaining.card := by
        rw [triangularCount]
        positivity
      calc
        triangularCount remaining.card * min u (1 + b * u) ≤
            triangularCount remaining.card * u :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) htri
        _ = u * triangularCount remaining.card := by ring
  | @raw remaining job hjob next ih =>
      simp only [LabelledTree.expectedCost]
      have hcard := Finset.card_erase_add_one hjob
      have hcardR : (remaining.card : ℝ) =
          ((remaining.erase job).card : ℝ) + 1 := by exact_mod_cast hcard.symm
      rw [hcardR]
      rw [← hcard, triangularCount_succ]
      have hblock := mul_le_mul_of_nonneg_left (min_le_left u (1 + b * u))
        (show (0 : ℝ) ≤ (remaining.erase job).card + 1 by positivity)
      calc
        (((remaining.erase job).card + 1 : ℕ) +
            triangularCount (remaining.erase job).card) * min u (1 + b * u) =
            ((remaining.erase job).card + 1 : ℝ) * min u (1 + b * u) +
              triangularCount (remaining.erase job).card * min u (1 + b * u) := by
                push_cast
                ring
        _ ≤ ((remaining.erase job).card + 1 : ℝ) * u +
            next.expectedCost u b := add_le_add hblock ih
        _ = u * (((remaining.erase job).card : ℝ) + 1) +
            next.expectedCost u b := by ring
  | @optimized remaining job hjob zeroBranch longBranch ihZero ihLong =>
      simp only [LabelledTree.expectedCost]
      have hcard := Finset.card_erase_add_one hjob
      have hcardR : (remaining.card : ℝ) =
          ((remaining.erase job).card : ℝ) + 1 := by exact_mod_cast hcard.symm
      rw [hcardR]
      rw [← hcard, triangularCount_succ]
      have hzeroWeight : 0 ≤ 1 - b := by linarith
      have hcontinuation :
          triangularCount (remaining.erase job).card * min u (1 + b * u) ≤
            (1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b := by
        calc
          triangularCount (remaining.erase job).card * min u (1 + b * u) =
              (1 - b) *
                  (triangularCount (remaining.erase job).card * min u (1 + b * u)) +
                b * (triangularCount (remaining.erase job).card * min u (1 + b * u)) := by ring
          _ ≤ (1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b :=
            add_le_add (mul_le_mul_of_nonneg_left ihZero hzeroWeight)
              (mul_le_mul_of_nonneg_left ihLong hb0)
      have hblock := mul_le_mul_of_nonneg_left (min_le_right u (1 + b * u))
        (show (0 : ℝ) ≤ (remaining.erase job).card + 1 by positivity)
      calc
        (((remaining.erase job).card + 1 : ℕ) +
            triangularCount (remaining.erase job).card) * min u (1 + b * u) =
            ((remaining.erase job).card + 1 : ℝ) * min u (1 + b * u) +
              triangularCount (remaining.erase job).card * min u (1 + b * u) := by
                push_cast
                ring
        _ ≤ ((remaining.erase job).card + 1 : ℝ) * (1 + b * u) +
            ((1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b) := add_le_add hblock hcontinuation
        _ = (1 - b) *
              (((remaining.erase job).card + 1 : ℝ) + zeroBranch.expectedCost u b) +
            b * ((1 + u) * ((remaining.erase job).card + 1 : ℝ) +
              longBranch.expectedCost u b) := by ring

/-- Unfold `fuel` operational actions while retaining their labels. -/
def compileLabelled (strategy : Strategy n) (u : ℝ) :
    ℕ → (remaining : Finset (Fin n)) → Transcript n → LabelledTree n remaining
  | 0, remaining, _ => .stop
  | fuel + 1, remaining, transcript =>
      match strategy transcript with
      | none => .stop
      | some action =>
          if hjob : action.job ∈ remaining then
            match action.mode with
            | .raw =>
                .raw action.job hjob
                  (compileLabelled strategy u fuel (remaining.erase action.job)
                    (transcript ++ [.rawCompleted action.job]))
            | .optimized =>
                .optimized action.job hjob
                  (compileLabelled strategy u fuel (remaining.erase action.job)
                    (transcript ++ [.optimizedCompleted action.job 0]))
                  (compileLabelled strategy u fuel (remaining.erase action.job)
                    (transcript ++ [.optimizedCompleted action.job u]))
          else .stop

def compileLabelledInitial (strategy : Strategy n) (u : ℝ) :
    LabelledTree n Finset.univ :=
  compileLabelled strategy u n Finset.univ []

/-- Operational configuration corresponding to a compiler state. -/
def compilerConfig (remaining : Finset (Fin n))
    (transcript : Transcript n) : Config n where
  touched := Finset.univ \ remaining
  transcript := transcript

@[simp] theorem compilerConfig_touched
    (remaining : Finset (Fin n)) (transcript : Transcript n) :
    (compilerConfig remaining transcript).touched = Finset.univ \ remaining := rfl

@[simp] theorem compilerConfig_transcript
    (remaining : Finset (Fin n)) (transcript : Transcript n) :
    (compilerConfig remaining transcript).transcript = transcript := rfl

private theorem insert_sdiff_eq_sdiff_erase
    {remaining : Finset (Fin n)} {job : Fin n} (hjob : job ∈ remaining) :
    insert job (Finset.univ \ remaining) =
      Finset.univ \ remaining.erase job := by
  ext other
  by_cases heq : other = job
  · subst other
    simp [hjob]
  · simp [heq]

@[simp] theorem compilerConfig_step_raw
    (processing : Fin n → ℝ) (remaining : Finset (Fin n))
    (transcript : Transcript n) (job : Fin n) (hjob : job ∈ remaining) :
    (compilerConfig remaining transcript).step processing ⟨job, .raw⟩ =
      some (compilerConfig (remaining.erase job)
        (transcript ++ [.rawCompleted job])) := by
  unfold compilerConfig Config.step
  simp only
  have hfresh : job ∉ Finset.univ \ remaining := by simp [hjob]
  rw [if_neg hfresh]
  rw [insert_sdiff_eq_sdiff_erase hjob]

@[simp] theorem compilerConfig_step_optimized
    (u : ℝ) (input : BinaryInput n) (remaining : Finset (Fin n))
    (transcript : Transcript n) (job : Fin n) (hjob : job ∈ remaining) :
    (compilerConfig remaining transcript).step (binaryProcessing u input)
        ⟨job, .optimized⟩ =
      some (compilerConfig (remaining.erase job)
        (transcript ++ [.optimizedCompleted job (binaryProcessing u input job)])) := by
  unfold compilerConfig Config.step
  simp only
  have hfresh : job ∉ Finset.univ \ remaining := by simp [hjob]
  rw [if_neg hfresh]
  rw [insert_sdiff_eq_sdiff_erase hjob]

/-- The labelled compiler follows exactly the fuelled operational semantics. -/
theorem compileLabelled_mirror
    (strategy : Strategy n) (u : ℝ) (fuel : ℕ)
    (remaining : Finset (Fin n)) (transcript : Transcript n)
    (input : BinaryInput n) :
    let tree := compileLabelled strategy u fuel remaining transcript
    let result := runFuel (binaryProcessing u input) strategy fuel
      (compilerConfig remaining transcript)
    result.config.touched = Finset.univ \ tree.finalRemaining input ∧
      result.config.transcript = transcript ++ tree.observations u input := by
  induction fuel generalizing remaining transcript with
  | zero =>
      simp [compileLabelled, runFuel, compilerConfig,
        LabelledTree.finalRemaining, LabelledTree.observations]
  | succ fuel ih =>
      cases haction : strategy transcript with
      | none =>
          simp [compileLabelled, runFuel, haction, compilerConfig,
            LabelledTree.finalRemaining, LabelledTree.observations]
      | some action =>
          cases action with
          | mk job mode =>
              by_cases hjob : job ∈ remaining
              · cases mode with
                | raw =>
                    have hstep := compilerConfig_step_raw
                      (binaryProcessing u input) remaining transcript job hjob
                    have hrec := ih (remaining.erase job)
                      (transcript ++ [.rawCompleted job])
                    simpa [compileLabelled, runFuel, haction, hjob, hstep,
                      LabelledTree.finalRemaining,
                      LabelledTree.observations, List.append_assoc] using hrec
                | optimized =>
                    have hstep := compilerConfig_step_optimized u input remaining
                      transcript job hjob
                    cases hbit : input job
                    · have hp : binaryProcessing u input job = 0 := by
                        simp [binaryProcessing, hbit]
                      have hrec := ih (remaining.erase job)
                        (transcript ++ [.optimizedCompleted job 0])
                      simpa [compileLabelled, runFuel, haction, hjob, hstep,
                        hbit, hp, LabelledTree.finalRemaining,
                        LabelledTree.observations, List.append_assoc] using hrec
                    · have hp : binaryProcessing u input job = u := by
                        simp [binaryProcessing, hbit]
                      have hrec := ih (remaining.erase job)
                        (transcript ++ [.optimizedCompleted job u])
                      simpa [compileLabelled, runFuel, haction, hjob, hstep,
                        hbit, hp, LabelledTree.finalRemaining,
                        LabelledTree.observations, List.append_assoc] using hrec
              · have hrepeat : job ∈
                    (compilerConfig remaining transcript).touched := by
                  simp [compilerConfig, hjob]
                have hstep : (compilerConfig remaining transcript).step
                    (binaryProcessing u input) ⟨job, mode⟩ = none := by
                  simp [Config.step, compilerConfig, hjob]
                simp [compileLabelled, runFuel, haction, hjob, hstep,
                  LabelledTree.finalRemaining,
                  LabelledTree.observations]

theorem LabelledTree.observations_length_add_final_card
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u : ℝ) (input : BinaryInput n) :
    (tree.observations u input).length + (tree.finalRemaining input).card =
      remaining.card := by
  induction tree with
  | stop => simp [LabelledTree.observations, LabelledTree.finalRemaining]
  | @raw remaining job hjob next ih =>
      simp only [LabelledTree.observations, LabelledTree.finalRemaining,
        List.length_cons]
      have hcard := Finset.card_erase_add_one hjob
      omega
  | @optimized remaining job hjob zeroBranch longBranch ihZero ihLong =>
      cases hbit : input job <;>
        simp only [LabelledTree.observations, LabelledTree.finalRemaining,
          hbit, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      · have hcard := Finset.card_erase_add_one hjob
        omega
      · have hcard := Finset.card_erase_add_one hjob
        omega

/-- On a completed branch, recursive area is exactly the completion-time sum
of the emitted observations. -/
theorem LabelledTree.cost_eq_prefixCost
    {remaining : Finset (Fin n)} (tree : LabelledTree n remaining)
    (u : ℝ) (input : BinaryInput n)
    (hcomplete : tree.finalRemaining input = ∅) :
    tree.cost u input =
      prefixCost ((tree.observations u input).map (Observation.duration u)) := by
  induction tree with
  | @stop remaining =>
      simp only [LabelledTree.finalRemaining] at hcomplete
      subst remaining
      simp [LabelledTree.cost, LabelledTree.observations]
  | @raw remaining job hjob next ih =>
      simp only [LabelledTree.finalRemaining] at hcomplete
      have htailLength := next.observations_length_add_final_card u input
      rw [hcomplete, Finset.card_empty, Nat.add_zero] at htailLength
      simp only [LabelledTree.cost, LabelledTree.observations, List.map_cons,
        Observation.duration, prefixCost_cons]
      rw [ih hcomplete, List.length_map, htailLength]
      have hcard := Finset.card_erase_add_one hjob
      rw [← hcard]
      push_cast
      ring
  | @optimized remaining job hjob zeroBranch longBranch ihZero ihLong =>
      cases hbit : input job
      · simp only [LabelledTree.finalRemaining, hbit, Bool.false_eq_true,
          ↓reduceIte] at hcomplete
        have htailLength := zeroBranch.observations_length_add_final_card u input
        rw [hcomplete, Finset.card_empty, Nat.add_zero] at htailLength
        simp only [LabelledTree.cost, LabelledTree.observations, hbit,
          Bool.false_eq_true, ↓reduceIte, List.map_cons, Observation.duration,
          prefixCost_cons]
        rw [ihZero hcomplete, List.length_map, htailLength]
        have hcard := Finset.card_erase_add_one hjob
        rw [← hcard]
        push_cast
        ring
      · simp only [LabelledTree.finalRemaining, hbit, ↓reduceIte] at hcomplete
        have htailLength := longBranch.observations_length_add_final_card u input
        rw [hcomplete, Finset.card_empty, Nat.add_zero] at htailLength
        simp only [LabelledTree.cost, LabelledTree.observations, hbit,
          ↓reduceIte, List.map_cons, Observation.duration, prefixCost_cons]
        rw [ihLong hcomplete, List.length_map, htailLength]
        have hcard := Finset.card_erase_add_one hjob
        rw [← hcard]
        push_cast
        ring

private theorem finalRemaining_eq_empty_of_sdiff_eq_univ
    {remaining : Finset (Fin n)}
    (h : Finset.univ \ remaining = Finset.univ) : remaining = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨job, hmem⟩ := hnonempty
  have : job ∈ Finset.univ \ remaining := h.symm ▸ Finset.mem_univ job
  exact (Finset.mem_sdiff.mp this).2 hmem

/-- The compiled branch cost is the literal operational `runCost` whenever
the strategy completes that binary input. -/
theorem compileLabelledInitial_cost_eq_runCost
    (strategy : Strategy n) {u : ℝ} (input : BinaryInput n)
    (hcomplete : Completes (binaryProcessing u input) strategy) :
    (compileLabelledInitial strategy u).cost u input =
      runCost u (binaryProcessing u input) strategy n := by
  let tree := compileLabelledInitial strategy u
  have hmirror :
      (run (binaryProcessing u input) strategy n).config.touched =
          Finset.univ \ tree.finalRemaining input ∧
        (run (binaryProcessing u input) strategy n).config.transcript =
          tree.observations u input := by
    simpa [run, compilerConfig, Config.initial, compileLabelledInitial, tree] using
      (compileLabelled_mirror strategy u n Finset.univ [] input)
  rw [hcomplete] at hmirror
  have hfinal : tree.finalRemaining input = ∅ :=
    finalRemaining_eq_empty_of_sdiff_eq_univ hmirror.1.symm
  have hcost := tree.cost_eq_prefixCost u input hfinal
  unfold runCost completionCost
  change tree.cost u input =
    prefixCost ((run (binaryProcessing u input) strategy n).config.transcript.map
      (Observation.duration u))
  rw [hcost, hmirror.2]

/-- End-to-end operational lower bound: the finite Bernoulli expectation of
the literal transcript-only strategy cost obeys the adaptive tree bound. -/
theorem operational_binary_finiteExpectation_lower
    (strategy : Strategy n) {u b : ℝ}
    (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hcomplete : CompletesAll u strategy) :
    triangularCount n * min u (1 + b * u) ≤
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => runCost u (binaryProcessing u input) strategy n) := by
  let tree := compileLabelledInitial strategy u
  calc
    triangularCount n * min u (1 + b * u) =
        triangularCount (Finset.univ : Finset (Fin n)).card *
          min u (1 + b * u) := by simp
    _ ≤ tree.expectedCost u b := tree.expectedCost_lower hu0 hb0 hb1
    _ = Randomized.finiteExpectation (bernoulliWeight n b) (tree.cost u) :=
      (tree.finiteExpectation_cost_eq_expectedCost u b).symm
    _ = Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => runCost u (binaryProcessing u input) strategy n) := by
      congr 1
      funext input
      apply compileLabelledInitial_cost_eq_runCost strategy input
      apply hcomplete
      intro job
      constructor
      · unfold binaryProcessing
        split <;> simp [hu0]
      · unfold binaryProcessing
        split <;> simp [hu0]

theorem effectiveLength_binaryProcessing
    {u : ℝ} (hu : 1 < u) (input : BinaryInput n) (job : Fin n) :
    effectiveLength u (binaryProcessing u input job) =
      if input job then u else 1 := by
  cases hbit : input job
  · simp [binaryProcessing, hbit, effectiveLength, min_def, hu.le,
      not_le.mpr hu]
  · simp [binaryProcessing, hbit, effectiveLength, min_def]

theorem finiteExpectation_binary_effective
    {u b : ℝ} (hu : 1 < u) (job : Fin n) :
    Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => effectiveLength u (binaryProcessing u input job)) =
      1 + (u - 1) * b := by
  simp_rw [effectiveLength_binaryProcessing hu]
  rw [finiteExpectation_fresh_bernoulli_branch b job
    (fun _input => 1) (fun _input => u) (fun _ => rfl) (fun _ => rfl),
    Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b),
    Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b)]
  ring

theorem finiteExpectation_binary_pair_effective
    {u b : ℝ} (hu : 1 < u) {left right : Fin n}
    (hne : left ≠ right) :
    Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => min
          (effectiveLength u (binaryProcessing u input left))
          (effectiveLength u (binaryProcessing u input right))) =
      1 + (u - 1) * b ^ 2 := by
  simp_rw [effectiveLength_binaryProcessing hu]
  have hpoint : (fun input : BinaryInput n =>
      min (if input left then u else 1) (if input right then u else 1)) =
      fun input => if input left then (if input right then u else 1) else 1 := by
    funext input
    cases hleft : input left <;> cases hright : input right <;>
      simp [hleft, hright, min_def, hu.le, not_le.mpr hu]
  rw [hpoint]
  rw [finiteExpectation_fresh_bernoulli_branch b left
    (fun _input => 1) (fun input => if input right then u else 1)
    (fun _ => rfl) (fun input => by
      dsimp
      rw [RandomizedObligatory.flipAt_apply_other input hne])]
  rw [Randomized.finiteExpectation_const _ (bernoulliWeight_mass n b)]
  have hright := finiteExpectation_binary_effective
    (n := n) (b := b) hu right
  simp_rw [effectiveLength_binaryProcessing hu] at hright
  rw [hright]
  ring

/-- The exact finite Bernoulli expectation of the literal clairvoyant
benchmark.  In particular this checks the diagonal correction used in
`binaryFiniteYaoRatio`. -/
theorem finiteExpectation_binary_offlineCost
    {u b : ℝ} (hu : 1 < u) :
    Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => offlineCost u (binaryProcessing u input)) =
      binaryExpectedOfflineCost n u b := by
  let diagonal := 1 + (u - 1) * b
  let pair := 1 + (u - 1) * b ^ 2
  have hentry (left right : Fin n) :
      Randomized.finiteExpectation (bernoulliWeight n b)
          (fun input => min
            (effectiveLength u (binaryProcessing u input left))
            (effectiveLength u (binaryProcessing u input right))) =
        pair + if left = right then diagonal - pair else 0 := by
    by_cases heq : left = right
    · subst right
      simp only [↓reduceIte, min_self]
      exact (finiteExpectation_binary_effective (n := n) (b := b) hu left).trans
        (by dsimp [diagonal, pair]; ring)
    · simp only [heq, ↓reduceIte, add_zero]
      exact finiteExpectation_binary_pair_effective (n := n) (b := b) hu heq
  have hpoint (input : BinaryInput n) :=
    two_mul_pairCost_ofFn
      (fun job : Fin n => effectiveLength u (binaryProcessing u input job))
  have havg := congrArg
    (Randomized.finiteExpectation (bernoulliWeight n b))
    (funext fun input => by
      simpa [offlineCost] using hpoint input)
  rw [Randomized.finiteExpectation_smul,
    Randomized.finiteExpectation_add] at havg
  simp_rw [Randomized.finiteExpectation_fintype_sum] at havg
  simp_rw [hentry, finiteExpectation_binary_effective (n := n) (b := b) hu] at havg
  have hdouble :
      (∑ left : Fin n, ∑ right : Fin n,
        (pair + if left = right then diagonal - pair else 0)) =
      (n : ℝ) ^ 2 * pair + n * (diagonal - pair) := by
    simp only [Finset.sum_add_distrib]
    simp
    push_cast
    ring
  have hdiagonal : (∑ _job : Fin n, diagonal) = n * diagonal := by
    simp
  rw [hdouble, hdiagonal] at havg
  unfold offlineCost
  simp_rw [onlineEffective_eq_distributionEffective]
  unfold binaryExpectedOfflineCost
  dsimp [diagonal, pair] at havg ⊢
  calc
    Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => pairCost (List.ofFn fun job =>
          effectiveLength u (binaryProcessing u input job))) =
      ((n : ℝ) ^ 2 * (1 + (u - 1) * b ^ 2) +
        n * (1 + (u - 1) * b - (1 + (u - 1) * b ^ 2)) +
        n * (1 + (u - 1) * b)) / 2 := by linarith [havg]
    _ = (n : ℝ) ^ 2 / 2 * (1 + (u - 1) * b ^ 2) +
        n / 2 *
          (2 * (1 + (u - 1) * b) - (1 + (u - 1) * b ^ 2)) := by ring

/-- Averaging first over an exact Bernoulli input and then over an arbitrary
finite private seed still satisfies the adaptive operational lower bound. -/
theorem operational_binary_finiteSeed_expected_lower
    {n : ℕ} {u b : ℝ} (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Strategy n)
    (hcomplete : ∀ seed, CompletesAll u (strategy seed)) :
    triangularCount n * min u (1 + b * u) ≤
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n) := by
  rw [show Randomized.finiteExpectation (bernoulliWeight n b)
      (fun input => Randomized.uniformAverage fun seed =>
        runCost u (binaryProcessing u input) (strategy seed) n) =
    Randomized.uniformAverage (fun seed =>
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => runCost u (binaryProcessing u input) (strategy seed) n)) by
      unfold Randomized.finiteExpectation Randomized.uniformAverage
      calc
        (∑ input, bernoulliWeight n b input *
            ((∑ seed, runCost u (binaryProcessing u input) (strategy seed) n) /
              Fintype.card Seeds)) =
            (∑ input, ∑ seed, bernoulliWeight n b input *
              runCost u (binaryProcessing u input) (strategy seed) n) /
                Fintype.card Seeds := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro input _
              rw [← Finset.mul_sum, mul_div_assoc]
        _ = (∑ seed, ∑ input, bernoulliWeight n b input *
              runCost u (binaryProcessing u input) (strategy seed) n) /
                Fintype.card Seeds := by rw [Finset.sum_comm]]
  calc
    triangularCount n * min u (1 + b * u) =
        Randomized.uniformAverage
          (fun _seed : Seeds => triangularCount n * min u (1 + b * u)) :=
      (Randomized.uniformAverage_const _).symm
    _ ≤ Randomized.uniformAverage (fun seed =>
        Randomized.finiteExpectation (bernoulliWeight n b)
          (fun input => runCost u (binaryProcessing u input) (strategy seed) n)) := by
      apply Randomized.uniformAverage_mono
      intro seed
      exact operational_binary_finiteExpectation_lower (strategy seed)
        hu0 hb0 hb1 (hcomplete seed)

/-- Exact finite operational Yao ratio.  The adversarial labelled input is
chosen once, before the algorithm's private seed, and the denominator is its
literal clairvoyant offline cost. -/
theorem operational_binary_yao_ratio
    {n : ℕ} (hn : 0 < n) {u b : ℝ} (hu : 1 < u)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Strategy n)
    (hcomplete : ∀ seed, CompletesAll u (strategy seed)) :
    ∃ input : BinaryInput n,
      binaryFiniteYaoRatio n u b *
          offlineCost u (binaryProcessing u input) ≤
        Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n := by
  let numerator := triangularCount n * min u (1 + b * u)
  let denominator := binaryExpectedOfflineCost n u b
  let ratio := binaryFiniteYaoRatio n u b
  let pair := 1 + (u - 1) * b ^ 2
  let diagonal := 1 + (u - 1) * b
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hpair : 0 < pair := by
    dsimp [pair]
    have hnonneg : 0 ≤ (u - 1) * b ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg b)
    linarith
  have hdiagonal : 0 < diagonal := by
    dsimp [diagonal]
    have hnonneg : 0 ≤ (u - 1) * b :=
      mul_nonneg (by linarith) hb0
    linarith
  have hdenRewrite : denominator =
      (n : ℝ) * ((n : ℝ) - 1) / 2 * pair + (n : ℝ) * diagonal := by
    dsimp [denominator, pair, diagonal]
    unfold binaryExpectedOfflineCost
    ring
  have hcoefficient : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    positivity
  have hden : 0 < denominator := by
    rw [hdenRewrite]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hcoefficient hpair.le) (mul_pos hnR hdiagonal)
  have hratioDen : ratio * denominator = numerator := by
    dsimp [ratio, numerator, denominator]
    unfold binaryFiniteYaoRatio
    exact div_mul_cancel₀ _ hden.ne'
  have honline : numerator ≤
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n) := by
    exact operational_binary_finiteSeed_expected_lower
      (by linarith) hb0 hb1 strategy hcomplete
  have hjoint : (0 : ℝ) ≤
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n -
            ratio * offlineCost u (binaryProcessing u input)) := by
    have hsplit : Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n -
            ratio * offlineCost u (binaryProcessing u input)) =
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => Randomized.uniformAverage (fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n)) +
      (-ratio) * Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => offlineCost u (binaryProcessing u input)) := by
      calc
        Randomized.finiteExpectation (bernoulliWeight n b)
            (fun input => Randomized.uniformAverage fun seed =>
              runCost u (binaryProcessing u input) (strategy seed) n -
                ratio * offlineCost u (binaryProcessing u input)) =
          Randomized.finiteExpectation (bernoulliWeight n b)
            (fun input =>
              Randomized.uniformAverage (fun seed =>
                runCost u (binaryProcessing u input) (strategy seed) n) +
              (-ratio) * offlineCost u (binaryProcessing u input)) := by
                congr 1
                funext input
                rw [show (fun seed =>
                    runCost u (binaryProcessing u input) (strategy seed) n -
                      ratio * offlineCost u (binaryProcessing u input)) =
                  (fun seed =>
                    runCost u (binaryProcessing u input) (strategy seed) n +
                      (-(ratio * offlineCost u (binaryProcessing u input)))) by
                    funext seed
                    ring,
                  Randomized.uniformAverage_add,
                  Randomized.uniformAverage_const]
                ring
        _ = Randomized.finiteExpectation (bernoulliWeight n b)
              (fun input => Randomized.uniformAverage (fun seed =>
                runCost u (binaryProcessing u input) (strategy seed) n)) +
            Randomized.finiteExpectation (bernoulliWeight n b)
              (fun input => (-ratio) *
                offlineCost u (binaryProcessing u input)) := by
              rw [Randomized.finiteExpectation_add]
        _ = _ := by rw [Randomized.finiteExpectation_smul]
    rw [hsplit, finiteExpectation_binary_offlineCost hu]
    dsimp [denominator] at hratioDen ⊢
    linarith
  obtain ⟨input, hinput⟩ := bernoulli_yao_select_fixed_input
    (n := n) (b := b) hb0 hb1
    (fun input seed =>
      runCost u (binaryProcessing u input) (strategy seed) n -
        ratio * offlineCost u (binaryProcessing u input)) hjoint
  refine ⟨input, ?_⟩
  have hsplit : Randomized.uniformAverage (fun seed =>
      runCost u (binaryProcessing u input) (strategy seed) n -
        ratio * offlineCost u (binaryProcessing u input)) =
    Randomized.uniformAverage (fun seed =>
      runCost u (binaryProcessing u input) (strategy seed) n) -
        ratio * offlineCost u (binaryProcessing u input) := by
    rw [show (fun seed =>
        runCost u (binaryProcessing u input) (strategy seed) n -
          ratio * offlineCost u (binaryProcessing u input)) =
      (fun seed =>
        runCost u (binaryProcessing u input) (strategy seed) n +
          (-(ratio * offlineCost u (binaryProcessing u input)))) by
        funext seed
        ring,
      Randomized.uniformAverage_add,
      Randomized.uniformAverage_const]
    ring
  rw [hsplit] at hinput
  dsimp [ratio] at hinput ⊢
  linarith

/-- At one curve-maximizing Bernoulli mass, the literal finite operational
ratios above converge to the advertised randomized curve. -/
theorem exists_binary_mass_operational_ratio_tendsto_curve
    {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => binaryFiniteYaoRatio n u b)
        Filter.atTop (nhds (randomizedCurve u)) ∧
      ∀ (n : ℕ) (Seeds : Type) [Fintype Seeds] [Nonempty Seeds],
        0 < n →
        ∀ (strategy : Seeds → Strategy n),
          (∀ seed, CompletesAll u (strategy seed)) →
          ∃ input : BinaryInput n,
            binaryFiniteYaoRatio n u b *
                offlineCost u (binaryProcessing u input) ≤
              Randomized.uniformAverage fun seed =>
                runCost u (binaryProcessing u input) (strategy seed) n := by
  obtain ⟨b, hb, hlimit⟩ := exists_binary_mass_finite_ratio_tendsto_curve hu
  refine ⟨b, hb, hlimit, ?_⟩
  intro n Seeds _ _ hn strategy hcomplete
  exact operational_binary_yao_ratio hn hu hb.1 hb.2 strategy hcomplete

/-- Exact operational Yao selection for any finite family of completing
private-seed strategies.  The selected labelled input is fixed before the
private seed is drawn. -/
theorem operational_bernoulli_yao_select
    {n : ℕ} {u b : ℝ} (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (strategy : Seeds → Strategy n)
    (hcomplete : ∀ seed, CompletesAll u (strategy seed)) :
    ∃ input : BinaryInput n,
      triangularCount n * min u (1 + b * u) ≤
        Randomized.uniformAverage fun seed =>
          runCost u (binaryProcessing u input) (strategy seed) n := by
  apply bernoulli_yao_select_fixed_input hb0 hb1
  rw [show Randomized.finiteExpectation (bernoulliWeight n b)
      (fun input => Randomized.uniformAverage fun seed =>
        runCost u (binaryProcessing u input) (strategy seed) n) =
    Randomized.uniformAverage (fun seed =>
      Randomized.finiteExpectation (bernoulliWeight n b)
        (fun input => runCost u (binaryProcessing u input) (strategy seed) n)) by
      unfold Randomized.finiteExpectation Randomized.uniformAverage
      calc
        (∑ input, bernoulliWeight n b input *
            ((∑ seed, runCost u (binaryProcessing u input) (strategy seed) n) /
              Fintype.card Seeds)) =
            (∑ input, ∑ seed, bernoulliWeight n b input *
              runCost u (binaryProcessing u input) (strategy seed) n) /
                Fintype.card Seeds := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro input _
              rw [← Finset.mul_sum, mul_div_assoc]
        _ = (∑ seed, ∑ input, bernoulliWeight n b input *
              runCost u (binaryProcessing u input) (strategy seed) n) /
                Fintype.card Seeds := by rw [Finset.sum_comm]]
  calc
    triangularCount n * min u (1 + b * u) =
        Randomized.uniformAverage
          (fun _seed : Seeds => triangularCount n * min u (1 + b * u)) :=
      (Randomized.uniformAverage_const _).symm
    _ ≤ Randomized.uniformAverage (fun seed =>
        Randomized.finiteExpectation (bernoulliWeight n b)
          (fun input => runCost u (binaryProcessing u input) (strategy seed) n)) := by
      apply Randomized.uniformAverage_mono
      intro seed
      exact operational_binary_finiteExpectation_lower (strategy seed)
        hu0 hb0 hb1 (hcomplete seed)

end

end RandomizedCompiler
end BlindOptimization
end SchedulingPaper
