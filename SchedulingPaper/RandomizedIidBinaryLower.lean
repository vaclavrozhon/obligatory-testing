import SchedulingPaper.RandomizedObligatoryLower
import SchedulingPaper.RandomizedFiniteObjective
import SchedulingPaper.RandomizedHypergeometric
import SchedulingPaper.RandomPermutation
import SchedulingPaper.UnifiedOffline
import Mathlib.Tactic

/-!
# An independent-binary Yao lower bound

The paper uses a uniformly labelled balanced `0/2` multiset.  For the sharp
asymptotic ratio, an independent fair `0/2` input distribution is even
cleaner: a potential argument gives expected online cost at least `n²`, while
the expected clairvoyant cost is exactly `(3n²+5n)/4`.  This yields the same
oblivious lower limit and avoids a maximal bridge-discrepancy theorem.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized
open RandomizedAnnounced

noncomputable section

abbrev BinaryInput (n : ℕ) := Fin n → Bool

/-- Toggle one coordinate of a binary input. -/
def flipAt {n : ℕ} (i : Fin n) : Equiv.Perm (BinaryInput n) where
  toFun x := Function.update x i (!x i)
  invFun x := Function.update x i (!x i)
  left_inv x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  right_inv x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]

@[simp] theorem flipAt_apply_same {n : ℕ}
    (input : BinaryInput n) (i : Fin n) :
    flipAt i input i = !input i := by
  simp [flipAt, Function.update]

theorem flipAt_apply_other {n : ℕ}
    (input : BinaryInput n) {i j : Fin n} (hij : i ≠ j) :
    flipAt i input j = input j := by
  simp [flipAt, Function.update, Ne.symm hij]

/-- Real indicator that coordinate `i` is a processing-time-two job. -/
def positiveIndicator {n : ℕ} (input : BinaryInput n) (i : Fin n) : ℝ :=
  if input i then 1 else 0

theorem positiveIndicator_flip_same {n : ℕ}
    (input : BinaryInput n) (i : Fin n) :
    positiveIndicator (flipAt i input) i = 1 - positiveIndicator input i := by
  cases h : input i <;> simp [positiveIndicator, flipAt, h, Function.update]

theorem positiveIndicator_flip_other {n : ℕ}
    (input : BinaryInput n) {i j : Fin n} (hij : i ≠ j) :
    positiveIndicator (flipAt i input) j = positiveIndicator input j := by
  simp [positiveIndicator, flipAt, Function.update, Ne.symm hij]

/-- One coordinate of a uniform binary input is fair. -/
theorem uniformAverage_positiveIndicator (n : ℕ) (i : Fin n) :
    uniformAverage (fun input : BinaryInput n => positiveIndicator input i) = 1 / 2 := by
  let f : BinaryInput n → ℝ := fun input => positiveIndicator input i
  have hreparam := uniformAverage_comp_equiv (flipAt i) f
  have hcomp : (f ∘ flipAt i) = fun input => 1 - f input := by
    funext input
    exact positiveIndicator_flip_same input i
  rw [hcomp] at hreparam
  have hcomplement :
      uniformAverage (fun input => 1 - f input) = 1 - uniformAverage f := by
    calc
      uniformAverage (fun input => 1 - f input) =
          uniformAverage (fun _input : BinaryInput n => (1 : ℝ)) +
            uniformAverage (fun input => (-1) * f input) := by
              simpa [sub_eq_add_neg] using
                (uniformAverage_add
                  (fun _input : BinaryInput n => (1 : ℝ))
                  (fun input => (-1) * f input))
      _ = 1 + (-1) * uniformAverage f := by
        rw [uniformAverage_const, uniformAverage_smul]
      _ = 1 - uniformAverage f := by ring
  rw [hcomplement] at hreparam
  dsimp [f] at hreparam ⊢
  linarith

/-- Two distinct coordinates of a uniform binary input are independent. -/
theorem uniformAverage_positiveIndicator_mul
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    uniformAverage (fun input : BinaryInput n =>
      positiveIndicator input i * positiveIndicator input j) = 1 / 4 := by
  let f : BinaryInput n → ℝ := fun input =>
    positiveIndicator input i * positiveIndicator input j
  have hreparam := uniformAverage_comp_equiv (flipAt i) f
  have hcomp : (f ∘ flipAt i) = fun input =>
      positiveIndicator input j - f input := by
    funext input
    dsimp [f, Function.comp_def]
    rw [positiveIndicator_flip_same,
      positiveIndicator_flip_other input hij]
    ring
  rw [hcomp] at hreparam
  have havg :
      uniformAverage (fun input : BinaryInput n =>
        positiveIndicator input j - f input) =
      uniformAverage (fun input : BinaryInput n => positiveIndicator input j) -
        uniformAverage f := by
    calc
      uniformAverage (fun input : BinaryInput n =>
          positiveIndicator input j - f input) =
        uniformAverage (fun input : BinaryInput n => positiveIndicator input j) +
          uniformAverage (fun input => (-1) * f input) := by
            simpa [sub_eq_add_neg] using
              (uniformAverage_add
                (fun input : BinaryInput n => positiveIndicator input j)
                (fun input => (-1) * f input))
      _ = uniformAverage (fun input : BinaryInput n => positiveIndicator input j) -
          uniformAverage f := by
            rw [uniformAverage_smul]
            ring
  rw [havg, uniformAverage_positiveIndicator n j] at hreparam
  dsimp [f] at hreparam ⊢
  linarith

/-! ## Labelled nonanticipating binary policies -/

/-- A deterministic decision tree whose untested labels are exactly `U` and
which currently has `r` unfinished jobs.

The `process` constructor intentionally does not track which positive job is
known.  This grants the policy extra power, so its lower bound applies a
fortiori to every legal obligatory-testing scheduler.  A `test` chooses one
previously untested label; its zero branch completes that job, while its
positive branch leaves it unfinished. -/
inductive LabelledBinaryPolicy (n : ℕ) : Finset (Fin n) → ℕ → Type
  | done : LabelledBinaryPolicy n ∅ 0
  | process {U : Finset (Fin n)} {r : ℕ} :
      LabelledBinaryPolicy n U r → LabelledBinaryPolicy n U (r + 1)
  | test {U : Finset (Fin n)} {r : ℕ}
      (i : Fin n) (hi : i ∉ U) :
      LabelledBinaryPolicy n U r →
      LabelledBinaryPolicy n U (r + 1) →
      LabelledBinaryPolicy n (insert i U) (r + 1)

/-- Area under the unfinished-jobs curve on one fixed binary input. -/
def LabelledBinaryPolicy.cost
    {n : ℕ} {U : Finset (Fin n)} {r : ℕ}
    (policy : LabelledBinaryPolicy n U r) (input : BinaryInput n) : ℝ :=
  match policy with
  | .done => 0
  | .process (r := r) next =>
      2 * ((r + 1 : ℕ) : ℝ) + next.cost input
  | .test (r := r) i _ zeroBranch positiveBranch =>
      ((r + 1 : ℕ) : ℝ) +
        if input i then positiveBranch.cost input else zeroBranch.cost input

/-- Forgetting labels produces the scalar policy used by the potential
proof. -/
def LabelledBinaryPolicy.forget
    {n : ℕ} {U : Finset (Fin n)} {r : ℕ}
    (policy : LabelledBinaryPolicy n U r) : BinaryPolicy r :=
  match policy with
  | .done => .done
  | .process next => .process next.forget
  | .test _ _ zeroBranch positiveBranch =>
      .test zeroBranch.forget positiveBranch.forget

/-- A policy whose untested set does not contain `i` is insensitive to
flipping coordinate `i`. -/
theorem LabelledBinaryPolicy.cost_flip_of_not_mem
    {n : ℕ} {U : Finset (Fin n)} {r : ℕ}
    (policy : LabelledBinaryPolicy n U r)
    (input : BinaryInput n) {i : Fin n} (hi : i ∉ U) :
    policy.cost (flipAt i input) = policy.cost input := by
  induction policy with
  | done => rfl
  | @process U r next ih =>
      simp only [LabelledBinaryPolicy.cost]
      rw [ih hi]
  | @test U r j hj zeroBranch positiveBranch ihZero ihPositive =>
      have hij : i ≠ j := by
        intro h
        subst i
        exact hi (by simp)
      have hiU : i ∉ U := by
        intro hiMem
        exact hi (by simp [hiMem])
      simp only [LabelledBinaryPolicy.cost]
      rw [flipAt_apply_other input hij]
      cases hbit : input j
      · simp [hbit, ihZero hiU]
      · simp [hbit, ihPositive hiU]

/-- Averaging a branch on one fresh fair coordinate gives the arithmetic
mean of its two continuation averages. -/
theorem uniformAverage_fresh_binary_branch
    {n : ℕ} (i : Fin n) (zero positive : BinaryInput n → ℝ)
    (hzero : ∀ input, zero (flipAt i input) = zero input)
    (hpositive : ∀ input, positive (flipAt i input) = positive input) :
    uniformAverage (fun input : BinaryInput n =>
      if input i then positive input else zero input) =
      (uniformAverage zero + uniformAverage positive) / 2 := by
  let branch : BinaryInput n → ℝ := fun input =>
    if input i then positive input else zero input
  have hreparam := uniformAverage_comp_equiv (flipAt i) branch
  have hpair : ∀ input,
      branch input + branch (flipAt i input) = zero input + positive input := by
    intro input
    cases hbit : input i <;>
      simp [branch, hbit, hzero, hpositive] <;> ring
  have hdouble :
      2 * uniformAverage branch =
        uniformAverage zero + uniformAverage positive := by
    calc
      2 * uniformAverage branch =
          uniformAverage branch + uniformAverage (branch ∘ flipAt i) := by
        rw [hreparam]
        ring
      _ = uniformAverage (fun input =>
          branch input + branch (flipAt i input)) := by
        simpa [Function.comp_apply] using
          (uniformAverage_add branch (branch ∘ flipAt i)).symm
      _ = uniformAverage (fun input => zero input + positive input) := by
        congr 1
        funext input
        exact hpair input
      _ = uniformAverage zero + uniformAverage positive :=
        uniformAverage_add zero positive
  dsimp [branch] at hdouble ⊢
  linarith

/-- Exact equality between the uniform fixed-input average of a labelled
decision tree and its recursively defined fair-coin expected area. -/
theorem LabelledBinaryPolicy.uniformAverage_cost_eq_expectedArea
    {n : ℕ} {U : Finset (Fin n)} {r : ℕ}
    (policy : LabelledBinaryPolicy n U r) :
    uniformAverage (policy.cost : BinaryInput n → ℝ) =
      policy.forget.expectedArea := by
  induction policy with
  | done => simp [LabelledBinaryPolicy.cost, LabelledBinaryPolicy.forget,
      BinaryPolicy.expectedArea]
  | @process U r next ih =>
      simp only [LabelledBinaryPolicy.cost, LabelledBinaryPolicy.forget,
        BinaryPolicy.expectedArea]
      rw [show (fun input : BinaryInput n =>
          2 * ((r + 1 : ℕ) : ℝ) + next.cost input) =
        (fun input =>
          (fun _ : BinaryInput n => 2 * ((r + 1 : ℕ) : ℝ)) input +
            next.cost input) by rfl]
      rw [uniformAverage_add, uniformAverage_const, ih]
  | @test U r i hi zeroBranch positiveBranch ihZero ihPositive =>
      simp only [LabelledBinaryPolicy.cost, LabelledBinaryPolicy.forget,
        BinaryPolicy.expectedArea]
      rw [show (fun input : BinaryInput n =>
          ((r + 1 : ℕ) : ℝ) +
            (if input i then positiveBranch.cost input else zeroBranch.cost input)) =
        (fun input =>
          (fun _ : BinaryInput n => ((r + 1 : ℕ) : ℝ)) input +
            (if input i then positiveBranch.cost input else
              zeroBranch.cost input)) by rfl]
      rw [uniformAverage_add, uniformAverage_const]
      rw [uniformAverage_fresh_binary_branch i
        zeroBranch.cost positiveBranch.cost
        (fun input => zeroBranch.cost_flip_of_not_mem input hi)
        (fun input => positiveBranch.cost_flip_of_not_mem input hi),
        ihZero, ihPositive]

/-- The lower potential is unconditional for every labelled adaptive testing
tree. -/
theorem LabelledBinaryPolicy.sq_le_uniformAverage_cost
    {n : ℕ} {U : Finset (Fin n)} {r : ℕ}
    (policy : LabelledBinaryPolicy n U r) :
    (r : ℝ) ^ 2 ≤ uniformAverage (policy.cost : BinaryInput n → ℝ) := by
  rw [policy.uniformAverage_cost_eq_expectedArea]
  exact policy.forget.sq_le_expectedArea

/-- Clairvoyant objective for a binary input, in diagonal-plus-pairs form.

The ordered-distinct sum contributes two when both endpoints of an unordered
pair are positive, exactly matching `min(2,2)=2`. -/
def iidBinaryOfflineCost (n : ℕ) (input : BinaryInput n) : ℝ :=
  triangular n + 2 * ∑ i, positiveIndicator input i +
    ∑ z : OrderedDistinct (Fin n),
      positiveIndicator input z.val.1 * positiveIndicator input z.val.2

/-- The actual processing-time vector represented by a binary input. -/
def iidBinaryProcessingTime {n : ℕ} (input : BinaryInput n) (i : Fin n) : ℝ :=
  2 * positiveIndicator input i

theorem positiveIndicator_mul_self {n : ℕ}
    (input : BinaryInput n) (i : Fin n) :
    positiveIndicator input i * positiveIndicator input i =
      positiveIndicator input i := by
  cases h : input i <;> simp [positiveIndicator, h]

theorem min_iidBinaryProcessingTime {n : ℕ}
    (input : BinaryInput n) (i j : Fin n) :
    min (iidBinaryProcessingTime input i) (iidBinaryProcessingTime input j) =
      2 * positiveIndicator input i * positiveIndicator input j := by
  cases hi : input i <;> cases hj : input j <;>
    simp [iidBinaryProcessingTime, positiveIndicator, hi, hj]

/-- A full ordered pair sum splits into its diagonal and ordered-distinct
parts. -/
theorem sum_orderedDistinct_add_diagonal
    {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ z : OrderedDistinct (Fin n), f z.val.1 z.val.2) +
        ∑ i, f i i =
      ∑ i, ∑ j, f i j := by
  classical
  have hoff :
      (∑ z : OrderedDistinct (Fin n), f z.val.1 z.val.2) =
        ∑ z ∈ (Finset.univ : Finset (Fin n)).offDiag, f z.1 z.2 := by
    symm
    apply Finset.sum_subtype
    intro z
    simp [Finset.mem_offDiag]
  have hdiag :
      (∑ z ∈ (Finset.univ : Finset (Fin n)).diag, f z.1 z.2) =
        ∑ i, f i i := by
    rw [Finset.sum_diag]
  rw [hoff, ← hdiag, add_comm]
  rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ)]
  rw [Finset.diag_union_offDiag, Finset.sum_product]

/-- `iidBinaryOfflineCost` is not merely a comparison formula: it is exactly
the clairvoyant SPT optimum of the concrete compulsory-test vector
`p_i ∈ {0,2}`. -/
theorem iidBinaryOfflineCost_eq_finiteObligatoryOPT
    {n : ℕ} (hn : 0 < n) (input : BinaryInput n) :
    iidBinaryOfflineCost n input =
      finiteObligatoryOPT (iidBinaryProcessingTime input) := by
  let indicator : Fin n → ℝ := positiveIndicator input
  have hdecomp := sum_orderedDistinct_add_diagonal
    (fun i j => indicator i * indicator j)
  have hindicatorSelf : ∀ i, indicator i * indicator i = indicator i := by
    intro i
    exact positiveIndicator_mul_self input i
  simp_rw [hindicatorSelf] at hdecomp
  have hK :
      weightedMinPair (uniformJobWeight n) (iidBinaryProcessingTime input) =
        (2 * (∑ i, ∑ j, indicator i * indicator j)) / (n : ℝ) ^ 2 := by
    unfold weightedMinPair uniformJobWeight
    simp_rw [min_iidBinaryProcessingTime input]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [show (fun i => ∑ j,
        (1 / (n : ℝ)) * (1 / (n : ℝ)) *
          (2 * indicator i * indicator j)) =
      (fun i => (2 / (n : ℝ) ^ 2) * ∑ j, indicator i * indicator j) by
        funext i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp [hnR]]
    rw [← Finset.mul_sum]
    ring
  have hsumP :
      (∑ i, iidBinaryProcessingTime input i) = 2 * ∑ i, indicator i := by
    unfold iidBinaryProcessingTime indicator
    rw [Finset.mul_sum]
  unfold iidBinaryOfflineCost finiteObligatoryOPT finiteOfflineFluid
    finiteOfflineCorrection
  rw [hK, hsumP]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  rw [← hdecomp]
  simp [triangular]
  ring

/-- Exact expected clairvoyant value `(3n²+5n)/4`. -/
theorem uniformAverage_iidBinaryOfflineCost (n : ℕ) :
    uniformAverage (iidBinaryOfflineCost n) =
      (3 * (n : ℝ) ^ 2 + 5 * n) / 4 := by
  have hsingle :
      uniformAverage (fun input : BinaryInput n =>
        ∑ i, positiveIndicator input i) = (n : ℝ) / 2 := by
    rw [uniformAverage_fintype_sum]
    simp_rw [uniformAverage_positiveIndicator]
    simp
    ring
  have hpairs : ∀ z : OrderedDistinct (Fin n),
      uniformAverage (fun input : BinaryInput n =>
        positiveIndicator input z.val.1 * positiveIndicator input z.val.2) =
        1 / 4 := fun z => uniformAverage_positiveIndicator_mul z.property
  have hpairSum :
      uniformAverage (fun input : BinaryInput n =>
        ∑ z : OrderedDistinct (Fin n),
          positiveIndicator input z.val.1 * positiveIndicator input z.val.2) =
        (n : ℝ) * (n - 1) / 4 := by
    by_cases hn : n = 0
    · subst n
      simp [uniformAverage]
    rw [uniformAverage_fintype_sum]
    simp_rw [hpairs]
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [Finset.card_univ, orderedDistinct_card]
    simp
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]
    ring
  unfold iidBinaryOfflineCost
  calc
    uniformAverage (fun input : BinaryInput n =>
        triangular n + 2 * ∑ i, positiveIndicator input i +
          ∑ z : OrderedDistinct (Fin n),
            positiveIndicator input z.val.1 * positiveIndicator input z.val.2) =
        triangular n +
          2 * uniformAverage (fun input : BinaryInput n =>
            ∑ i, positiveIndicator input i) +
          uniformAverage (fun input : BinaryInput n =>
            ∑ z : OrderedDistinct (Fin n),
              positiveIndicator input z.val.1 * positiveIndicator input z.val.2) := by
      rw [show (fun input : BinaryInput n =>
          triangular n + 2 * ∑ i, positiveIndicator input i +
            ∑ z : OrderedDistinct (Fin n),
              positiveIndicator input z.val.1 * positiveIndicator input z.val.2) =
          (fun input =>
            ((fun _ : BinaryInput n => triangular n) input +
              (fun input => 2 * ∑ i, positiveIndicator input i) input) +
            (fun input => ∑ z : OrderedDistinct (Fin n),
              positiveIndicator input z.val.1 * positiveIndicator input z.val.2) input) by
            funext input
            rfl]
      rw [uniformAverage_add, uniformAverage_add, uniformAverage_const,
        uniformAverage_smul]
    _ = triangular n + 2 * ((n : ℝ) / 2) +
          (n : ℝ) * (n - 1) / 4 := by rw [hsingle, hpairSum]
    _ = (3 * (n : ℝ) ^ 2 + 5 * n) / 4 := by
      simp [triangular]
      push_cast
      ring

/-- If every deterministic private seed unfolds to a fair binary decision
tree, the joint input/seed average is at least `n²`. -/
theorem iid_jointCost_lower_of_policyTrees
    {n : ℕ} {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (cost : BinaryInput n → Seeds → ℝ)
    (htree : ∀ seed, ∃ policy : BinaryPolicy n,
      uniformAverage (fun input : BinaryInput n => cost input seed) =
        policy.expectedArea) :
    (n : ℝ) ^ 2 ≤
      uniformAverage (fun input : BinaryInput n =>
        uniformAverage fun seed => cost input seed) := by
  rw [uniformAverage_comm]
  calc
    (n : ℝ) ^ 2 = uniformAverage (fun _seed : Seeds => (n : ℝ) ^ 2) :=
      (uniformAverage_const _).symm
    _ ≤ uniformAverage (fun seed =>
        uniformAverage fun input : BinaryInput n => cost input seed) := by
      apply uniformAverage_mono
      intro seed
      obtain ⟨policy, hpolicy⟩ := htree seed
      rw [hpolicy]
      exact policy.sq_le_expectedArea

/-- Independent-binary Yao lower bound for randomized algorithms.

For each finite private seed, `htree` is the finite nonanticipating execution
tree obtained by unfolding the deterministic strategy on all binary inputs.
The conclusion selects one fixed oblivious input. -/
theorem iid_binary_yao_lower
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (cost : BinaryInput n → Seeds → ℝ)
    (htree : ∀ seed, ∃ policy : BinaryPolicy n,
      uniformAverage (fun input : BinaryInput n => cost input seed) =
        policy.expectedArea) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) * iidBinaryOfflineCost n input ≤
        uniformAverage fun seed => cost input seed := by
  apply finite_yao_select_ratio cost (iidBinaryOfflineCost n)
      (L := (n : ℝ) ^ 2)
      (O := (3 * (n : ℝ) ^ 2 + 5 * n) / 4)
  · exact iid_jointCost_lower_of_policyTrees cost htree
  · exact uniformAverage_iidBinaryOfflineCost n
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    field_simp
    norm_num

/-- Unconditional Yao lower bound for a finite-seed randomized family of
labelled adaptive policies.  The selected `input` is fixed before the private
seed and is therefore an oblivious adversarial instance. -/
theorem iid_binary_yao_lower_labelled
    {n : ℕ} (hn : 0 < n)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (policy : Seeds → LabelledBinaryPolicy n Finset.univ n) :
    ∃ input : BinaryInput n,
      (4 * n / (3 * n + 5)) * iidBinaryOfflineCost n input ≤
        uniformAverage fun seed => (policy seed).cost input := by
  apply iid_binary_yao_lower hn
  intro seed
  refine ⟨(policy seed).forget, ?_⟩
  exact (policy seed).uniformAverage_cost_eq_expectedArea

/-- The finite lower coefficient tends to `4/3`, with explicit `O(1/n)`
gap. -/
theorem iid_binary_coefficient_identity
    {n : ℝ} (hn : 3 * n + 5 ≠ 0) :
    4 / 3 - 4 * n / (3 * n + 5) = 20 / (3 * (3 * n + 5)) := by
  field_simp [hn]
  ring

end

end RandomizedObligatory
end SchedulingPaper
