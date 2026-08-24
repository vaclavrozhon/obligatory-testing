import SchedulingPaper.RevealingOptimizationBinaryLower
import SchedulingPaper.BlindOptimizationRandomizedCompiler
import Mathlib.Tactic

/-!
# Label-preserving finite Yao bridge for revealing optimization

The scalar Bellman tree proves the hard adaptive inequality.  Here labels
are retained, the structural expectation is identified with the exact
finite iid Bernoulli law on fixed labelled inputs, and finite Yao selects one
oblivious input against a finite private-seed family.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace RandomizedYao

open Randomized
open RandomizedLower

noncomputable section

abbrev BinaryInput (n : ℕ) :=
  BlindOptimization.RandomizedLower.BinaryInput n

abbrev bernoulliWeight (n : ℕ) (x : ℝ) (input : BinaryInput n) : ℝ :=
  BlindOptimization.RandomizedLower.bernoulliWeight n x input

/-- A completing labelled revealing decision tree.  `fresh` contains
untouched labels and `known` contains tested positive labels. -/
inductive LabelledPolicy (n : ℕ) :
    Finset (Fin n) → Finset (Fin n) → Type
  | done : LabelledPolicy n ∅ ∅
  | raw {fresh known : Finset (Fin n)}
      (job : Fin n) (hjob : job ∈ fresh)
      (next : LabelledPolicy n (fresh.erase job) known) :
      LabelledPolicy n fresh known
  | process {fresh known : Finset (Fin n)}
      (job : Fin n) (hjob : job ∈ known)
      (next : LabelledPolicy n fresh (known.erase job)) :
      LabelledPolicy n fresh known
  | test {fresh known : Finset (Fin n)}
      (job : Fin n) (hfresh : job ∈ fresh) (hknown : job ∉ known)
      (zeroBranch : LabelledPolicy n (fresh.erase job) known)
      (positiveBranch :
        LabelledPolicy n (fresh.erase job) (insert job known)) :
      LabelledPolicy n fresh known

def LabelledPolicy.cost
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known)
    (rawDuration processDuration : ℝ) (input : BinaryInput n) : ℝ :=
  match policy with
  | .done => 0
  | .raw (fresh := fresh) (known := known) _ _ next =>
      rawDuration * (fresh.card + known.card) +
        next.cost rawDuration processDuration input
  | .process (fresh := fresh) (known := known) _ _ next =>
      processDuration * (fresh.card + known.card) +
        next.cost rawDuration processDuration input
  | .test (fresh := fresh) (known := known) job _ _
      zeroBranch positiveBranch =>
      (fresh.card + known.card) +
        if input job then
          positiveBranch.cost rawDuration processDuration input
        else zeroBranch.cost rawDuration processDuration input

def LabelledPolicy.expectedCost
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known)
    (rawDuration processDuration x : ℝ) : ℝ :=
  match policy with
  | .done => 0
  | .raw (fresh := fresh) (known := known) _ _ next =>
      rawDuration * (fresh.card + known.card) +
        next.expectedCost rawDuration processDuration x
  | .process (fresh := fresh) (known := known) _ _ next =>
      processDuration * (fresh.card + known.card) +
        next.expectedCost rawDuration processDuration x
  | .test (fresh := fresh) (known := known) _ _ _
      zeroBranch positiveBranch =>
      (fresh.card + known.card) +
        (1 - x) * zeroBranch.expectedCost rawDuration processDuration x +
        x * positiveBranch.expectedCost rawDuration processDuration x

/-- Flipping a coordinate that is no longer fresh cannot change any future
branch of the labelled tree. -/
theorem LabelledPolicy.cost_flip_of_not_fresh
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known)
    (rawDuration processDuration : ℝ) (input : BinaryInput n)
    {job : Fin n} (hjob : job ∉ fresh) :
    policy.cost rawDuration processDuration
        (RandomizedObligatory.flipAt job input) =
      policy.cost rawDuration processDuration input := by
  induction policy with
  | done => rfl
  | @raw fresh known selected hselected next ih =>
      simp only [LabelledPolicy.cost]
      have hnot : job ∉ fresh.erase selected := by
        intro hmem
        exact hjob (Finset.mem_of_mem_erase hmem)
      rw [ih hnot]
  | @process fresh known selected hselected next ih =>
      simp only [LabelledPolicy.cost]
      rw [ih hjob]
  | @test fresh known selected hselected hknown
      zeroBranch positiveBranch ihZero ihPositive =>
      have hne : job ≠ selected := by
        intro heq
        subst job
        exact hjob hselected
      simp only [LabelledPolicy.cost]
      rw [RandomizedObligatory.flipAt_apply_other input hne]
      cases hbit : input selected
      · simp only [Bool.false_eq_true, if_false]
        have hnot : job ∉ fresh.erase selected := by
          intro hmem
          exact hjob (Finset.mem_of_mem_erase hmem)
        rw [ihZero hnot]
      · simp only [if_true]
        have hnot : job ∉ fresh.erase selected := by
          intro hmem
          exact hjob (Finset.mem_of_mem_erase hmem)
        rw [ihPositive hnot]

/-- Structural expectation equals the exact weighted expectation over all
fixed labelled Bernoulli inputs. -/
theorem LabelledPolicy.finiteExpectation_cost_eq_expectedCost
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known)
    (rawDuration processDuration x : ℝ) :
    finiteExpectation (bernoulliWeight n x)
        (policy.cost rawDuration processDuration) =
      policy.expectedCost rawDuration processDuration x := by
  induction policy with
  | done =>
      exact finiteExpectation_const _
        (BlindOptimization.RandomizedLower.bernoulliWeight_mass n x) _
  | @raw fresh known job hjob next ih =>
      simp only [LabelledPolicy.cost, LabelledPolicy.expectedCost]
      rw [show (fun input : BinaryInput n =>
          rawDuration * (fresh.card + known.card) +
            next.cost rawDuration processDuration input) =
        (fun input =>
          (fun _ : BinaryInput n =>
            rawDuration * (fresh.card + known.card)) input +
          next.cost rawDuration processDuration input) by rfl,
        finiteExpectation_add,
        finiteExpectation_const _
          (BlindOptimization.RandomizedLower.bernoulliWeight_mass n x), ih]
  | @process fresh known job hjob next ih =>
      simp only [LabelledPolicy.cost, LabelledPolicy.expectedCost]
      rw [show (fun input : BinaryInput n =>
          processDuration * (fresh.card + known.card) +
            next.cost rawDuration processDuration input) =
        (fun input =>
          (fun _ : BinaryInput n =>
            processDuration * (fresh.card + known.card)) input +
          next.cost rawDuration processDuration input) by rfl,
        finiteExpectation_add,
        finiteExpectation_const _
          (BlindOptimization.RandomizedLower.bernoulliWeight_mass n x), ih]
  | @test fresh known job hfresh hknown zeroBranch positiveBranch
      ihZero ihPositive =>
      simp only [LabelledPolicy.cost, LabelledPolicy.expectedCost]
      rw [show (fun input : BinaryInput n =>
          (fresh.card : ℝ) + known.card +
            (if input job then
              positiveBranch.cost rawDuration processDuration input
            else zeroBranch.cost rawDuration processDuration input)) =
        (fun input =>
          (fun _ : BinaryInput n =>
            (fresh.card : ℝ) + known.card) input +
          (if input job then
            positiveBranch.cost rawDuration processDuration input
          else zeroBranch.cost rawDuration processDuration input)) by rfl,
        finiteExpectation_add,
        finiteExpectation_const _
          (BlindOptimization.RandomizedLower.bernoulliWeight_mass n x)]
      rw [SchedulingPaper.BlindOptimization.RandomizedCompiler.
          finiteExpectation_fresh_bernoulli_branch x job
          (zeroBranch.cost rawDuration processDuration)
          (positiveBranch.cost rawDuration processDuration)
          (fun input => zeroBranch.cost_flip_of_not_fresh
            rawDuration processDuration input (by simp))
          (fun input => positiveBranch.cost_flip_of_not_fresh
            rawDuration processDuration input (by simp)),
        ihZero, ihPositive]
      ring

/-- Erase labels while preserving every adaptive branch and both state
counts. -/
def LabelledPolicy.eraseLabels
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known) :
    BinaryPolicy fresh.card known.card :=
  match policy with
  | .done => .done
  | .raw (fresh := fresh) _ hjob next =>
      (Finset.card_erase_add_one hjob) ▸
        BinaryPolicy.raw next.eraseLabels
  | .process (known := known) _ hjob next =>
      (Finset.card_erase_add_one hjob) ▸
        BinaryPolicy.process next.eraseLabels
  | .test (fresh := fresh) (known := known) job hfresh hknown
      zeroBranch positiveBranch =>
      let positive :
          BinaryPolicy (fresh.erase job).card (known.card + 1) :=
        (Finset.card_insert_of_notMem hknown) ▸
          positiveBranch.eraseLabels
      (Finset.card_erase_add_one hfresh) ▸
        BinaryPolicy.test zeroBranch.eraseLabels positive

private theorem BinaryPolicy.expectedCost_cast_fresh
    {fresh fresh' known : ℕ} (h : fresh = fresh')
    (policy : BinaryPolicy fresh known)
    (rawDuration processDuration x : ℝ) :
    (h ▸ policy).expectedCost rawDuration processDuration x =
      policy.expectedCost rawDuration processDuration x := by
  subst fresh'
  rfl

private theorem BinaryPolicy.expectedCost_cast_known
    {fresh known known' : ℕ} (h : known = known')
    (policy : BinaryPolicy fresh known)
    (rawDuration processDuration x : ℝ) :
    (h ▸ policy).expectedCost rawDuration processDuration x =
      policy.expectedCost rawDuration processDuration x := by
  subst known'
  rfl

theorem LabelledPolicy.eraseLabels_expectedCost
    {n : ℕ} {fresh known : Finset (Fin n)}
    (policy : LabelledPolicy n fresh known)
    (rawDuration processDuration x : ℝ) :
    policy.eraseLabels.expectedCost rawDuration processDuration x =
      policy.expectedCost rawDuration processDuration x := by
  induction policy with
  | done => rfl
  | @raw fresh known job hjob next ih =>
      have hcard := Finset.card_erase_add_one hjob
      rw [LabelledPolicy.eraseLabels,
        BinaryPolicy.expectedCost_cast_fresh hcard,
        BinaryPolicy.expectedCost]
      change rawDuration * ((fresh.erase job).card + known.card + 1) +
          next.eraseLabels.expectedCost rawDuration processDuration x =
        rawDuration * (fresh.card + known.card) +
          next.expectedCost rawDuration processDuration x
      rw [ih]
      have hcardR : ((fresh.erase job).card : ℝ) + 1 = fresh.card := by
        exact_mod_cast hcard
      have hsum : ((fresh.erase job).card : ℝ) + known.card + 1 =
          fresh.card + known.card := by linarith
      rw [hsum]
  | @process fresh known job hjob next ih =>
      have hcard := Finset.card_erase_add_one hjob
      rw [LabelledPolicy.eraseLabels,
        BinaryPolicy.expectedCost_cast_known hcard,
        BinaryPolicy.expectedCost]
      change processDuration * (fresh.card + (known.erase job).card + 1) +
          next.eraseLabels.expectedCost rawDuration processDuration x =
        processDuration * (fresh.card + known.card) +
          next.expectedCost rawDuration processDuration x
      rw [ih]
      have hcardR : ((known.erase job).card : ℝ) + 1 = known.card := by
        exact_mod_cast hcard
      have hsum : (fresh.card : ℝ) + (known.erase job).card + 1 =
          fresh.card + known.card := by linarith
      rw [hsum]
  | @test fresh known job hfresh hknown zeroBranch positiveBranch
      ihZero ihPositive =>
      have hfreshCard := Finset.card_erase_add_one hfresh
      have hknownCard : (insert job known).card = known.card + 1 :=
        Finset.card_insert_of_notMem hknown
      rw [LabelledPolicy.eraseLabels,
        BinaryPolicy.expectedCost_cast_fresh hfreshCard,
        BinaryPolicy.expectedCost,
        BinaryPolicy.expectedCost_cast_known hknownCard]
      change ((fresh.erase job).card + known.card + 1 : ℝ) +
          (1 - x) * zeroBranch.eraseLabels.expectedCost
            rawDuration processDuration x +
          x * positiveBranch.eraseLabels.expectedCost
            rawDuration processDuration x =
        (fresh.card + known.card : ℝ) +
          (1 - x) * zeroBranch.expectedCost rawDuration processDuration x +
          x * positiveBranch.expectedCost rawDuration processDuration x
      rw [ihZero, ihPositive]
      have hfreshCardR : ((fresh.erase job).card : ℝ) + 1 = fresh.card := by
        exact_mod_cast hfreshCard
      have hsum : ((fresh.erase job).card : ℝ) + known.card + 1 =
          fresh.card + known.card := by linarith
      rw [hsum]

/-- Labelled `familyB` lower bound, ready for finite Yao. -/
theorem LabelledPolicy.familyB_le_finiteExpectation
    {n : ℕ} (policy : LabelledPolicy n Finset.univ ∅)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    (n : ℝ) ^ 2 / 2 *
        (familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2)) ≤
      finiteExpectation (bernoulliWeight n (survivalMass τ))
        (policy.cost u u) := by
  rw [policy.finiteExpectation_cost_eq_expectedCost,
    ← policy.eraseLabels_expectedCost]
  simpa using policy.eraseLabels.familyB_le_expectedCost hu hτ hτu

/-- Labelled `familyA` lower bound, ready for finite Yao. -/
theorem LabelledPolicy.familyA_le_finiteExpectation
    {n : ℕ} (policy : LabelledPolicy n Finset.univ ∅)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    (n : ℝ) ^ 2 / 2 *
        (familyA τ * (1 + τ * survivalMass τ ^ 2)) ≤
      finiteExpectation (bernoulliWeight n (survivalMass τ))
        (policy.cost u τ) := by
  rw [policy.finiteExpectation_cost_eq_expectedCost,
    ← policy.eraseLabels_expectedCost]
  simpa using policy.eraseLabels.familyA_le_expectedCost hu hτ hτu

/-! ## Finite private seeds and an oblivious labelled input -/

private theorem finiteExpectation_uniformAverage_comm
    {Inputs Seeds : Type*} [Fintype Inputs]
    [Fintype Seeds] [Nonempty Seeds]
    (weight : Inputs → ℝ) (cost : Inputs → Seeds → ℝ) :
    finiteExpectation weight
        (fun input => uniformAverage fun seed => cost input seed) =
      uniformAverage fun seed =>
        finiteExpectation weight fun input => cost input seed := by
  unfold finiteExpectation uniformAverage
  calc
    (∑ input, weight input *
        ((∑ seed, cost input seed) / Fintype.card Seeds)) =
        (∑ input, ∑ seed, weight input * cost input seed) /
          Fintype.card Seeds := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro input _
      rw [← Finset.mul_sum, mul_div_assoc]
    _ = (∑ seed, ∑ input, weight input * cost input seed) /
          Fintype.card Seeds := by
      rw [Finset.sum_comm]

/-- For the `familyB` law, averaging an arbitrary finite collection of
label-preserving adaptive trees over private seeds still leaves one fixed
labelled input with at least the Bellman lower bound. -/
theorem familyB_finiteSeed_select_fixed_input
    {n : ℕ} {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policy : Seeds → LabelledPolicy n Finset.univ ∅)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2)) ≤
        uniformAverage fun seed => (policy seed).cost u u input := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  apply _root_.SchedulingPaper.BlindOptimization.RandomizedLower.bernoulli_yao_select_fixed_input
    hx0 hx1
  rw [finiteExpectation_uniformAverage_comm]
  calc
    (n : ℝ) ^ 2 / 2 *
          (familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2)) =
        uniformAverage (fun _seed : Seeds =>
          (n : ℝ) ^ 2 / 2 *
            (familyB u τ *
              (1 + (u - 1) * survivalMass τ ^ 2))) :=
      (uniformAverage_const _).symm
    _ ≤ uniformAverage (fun seed =>
        finiteExpectation (bernoulliWeight n (survivalMass τ))
          ((policy seed).cost u u)) := by
      apply uniformAverage_mono
      intro seed
      exact (policy seed).familyB_le_finiteExpectation hu hτ hτu

/-- The analogous finite-Yao selection for the `familyA` law. -/
theorem familyA_finiteSeed_select_fixed_input
    {n : ℕ} {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policy : Seeds → LabelledPolicy n Finset.univ ∅)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (familyA τ * (1 + τ * survivalMass τ ^ 2)) ≤
        uniformAverage fun seed => (policy seed).cost u τ input := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  apply _root_.SchedulingPaper.BlindOptimization.RandomizedLower.bernoulli_yao_select_fixed_input
    hx0 hx1
  rw [finiteExpectation_uniformAverage_comm]
  calc
    (n : ℝ) ^ 2 / 2 *
          (familyA τ * (1 + τ * survivalMass τ ^ 2)) =
        uniformAverage (fun _seed : Seeds =>
          (n : ℝ) ^ 2 / 2 *
            (familyA τ * (1 + τ * survivalMass τ ^ 2))) :=
      (uniformAverage_const _).symm
    _ ≤ uniformAverage (fun seed =>
        finiteExpectation (bernoulliWeight n (survivalMass τ))
          ((policy seed).cost u τ)) := by
      apply uniformAverage_mono
      intro seed
      exact (policy seed).familyA_le_finiteExpectation hu hτ hτu

/-- The scalar maximization and finite Yao now produce a single fixed
labelled binary input against every finite private-seed family of fully
adaptive revealing trees. -/
theorem finiteSeed_binary_families_attain_curve
    {n : ℕ} {u : ℝ} (hu : 1 < u)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policyB policyA :
      Seeds → ℝ → LabelledPolicy n Finset.univ ∅) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u, ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + (u - 1) * survivalMass τ ^ 2)) ≤
        uniformAverage fun seed => (policyB seed τ).cost u u input) ∨
    (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1), ∃ input : BinaryInput n,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + τ * survivalMass τ ^ 2)) ≤
        uniformAverage fun seed => (policyA seed τ).cost u τ input) := by
  rcases binaryFamilies_attain_curve hu with hB | hA
  · rcases hB with ⟨τ, hτ, hattain⟩
    obtain ⟨input, hinput⟩ :=
      familyB_finiteSeed_select_fixed_input
        (fun seed => policyB seed τ) hu hτ.1 hτ.2
    left
    exact ⟨τ, hτ, input, by simpa only [hattain] using hinput⟩
  · rcases hA with ⟨τ, hτ, hattain⟩
    obtain ⟨input, hinput⟩ :=
      familyA_finiteSeed_select_fixed_input
        (fun seed => policyA seed τ) hu hτ.1
          (hτ.2.trans (by linarith))
    right
    exact ⟨τ, hτ, input, by simpa only [hattain] using hinput⟩

end

end RandomizedYao
end RevealingOptimization
end SchedulingPaper
