import SchedulingPaper.RandomizedOptionalOnline
import SchedulingPaper.RandomizedOptionalPermutationUrn
import Mathlib.Tactic

/-!
# Optional testing: the first-touch trace bijection

This file isolates the combinatorial core of the adaptive-policy/urn bridge.
Distinct hidden occurrences are placed behind public labels by a permutation.
A deterministic policy produces a permutation of labels in first-touch order.
If its next label and test/blind choice depend only on values exposed earlier,
then the induced order of hidden occurrences is itself a permutation of the
finite placement space.  Uniformity is therefore just reindexing a finite
sum; no conditional probability or suffix-swap compiler is needed.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace TraceBijection

open Randomized

noncomputable section

abbrev Label (n : ℕ) := Fin n
abbrev Occurrence (n : ℕ) := Fin n
abbrev Placement (n : ℕ) := Equiv.Perm (Fin n)

inductive TouchKind where
  | test
  | blind
  deriving DecidableEq

structure TouchTrace (n : ℕ) where
  /-- Public labels in their order of first touch. -/
  label : Equiv.Perm (Fin n)
  /-- Whether that first touch was a test or a blind completion. -/
  kind : Fin n → TouchKind

/-- Hidden occurrences in the order in which the policy first exposes them. -/
def revealOrder {n : ℕ}
    (trace : Placement n → TouchTrace n) (σ : Placement n) : Placement n :=
  (trace σ).label.trans σ

/-- Equality of the visible values in the first `k` reveal positions.  Hidden
occurrence tokens themselves need not agree. -/
def ValuePrefixEq {n : ℕ} (p : Occurrence n → ℝ) (k : ℕ)
    (r s : Placement n) : Prop :=
  ∀ j : Fin n, j.val < k → p (r j) = p (s j)

theorem take_ofFn_eq_of_prefix {n k : ℕ} {X : Type*}
    (f g : Fin n → X) (h : ∀ j : Fin n, j.val < k → f j = g j) :
    (List.ofFn f).take k = (List.ofFn g).take k := by
  apply List.ext_getElem?
  intro i
  by_cases hik : i < k
  · by_cases hin : i < n
    · simp [hik, hin, h ⟨i, hin⟩ hik]
    · rw [List.getElem?_take, List.getElem?_take]
      simp only [hik, if_true]
      rw [List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by simp; omega)]
  · simp [hik]

theorem get_eq_of_take_succ_eq {X : Type*} {left right : List X} {k : ℕ}
    (hkLeft : k < left.length) (hkRight : k < right.length)
    (h : left.take (k + 1) = right.take (k + 1)) :
    left.get ⟨k, hkLeft⟩ = right.get ⟨k, hkRight⟩ := by
  have hget := congrArg (fun l : List X ↦ l[k]?) h
  change (left.take (k + 1))[k]? = (right.take (k + 1))[k]? at hget
  rw [List.getElem?_take, List.getElem?_take] at hget
  simp only [Nat.lt_add_one, if_true] at hget
  rw [List.getElem?_eq_getElem hkLeft,
    List.getElem?_eq_getElem hkRight] at hget
  exact Option.some.inj hget

/-- The sole scheduler-facing hypothesis: equal visible value histories force
the same next public label and the same test/blind decision. -/
def Causal {n : ℕ} (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) : Prop :=
  ∀ σ τ k,
    ValuePrefixEq p k.val (revealOrder trace σ) (revealOrder trace τ) →
      (trace σ).label k = (trace τ).label k ∧
      (trace σ).kind k = (trace τ).kind k

theorem valuePrefixEq_of_eq {n : ℕ} (p : Occurrence n → ℝ)
    {r s : Placement n} (h : r = s) (k : ℕ) :
    ValuePrefixEq p k r s := by
  subst s
  intro j hj
  rfl

/-- A causal adaptive first-touch order is an injective transformation of
the finite placement space. -/
theorem revealOrder_injective {n : ℕ} (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    Function.Injective (revealOrder trace) := by
  intro σ τ hreveal
  have hlabels : (trace σ).label = (trace τ).label := by
    apply Equiv.ext
    intro k
    exact (hcausal σ τ k (valuePrefixEq_of_eq p hreveal k.val)).1
  apply Equiv.ext
  intro label
  let k : Fin n := (trace σ).label.symm label
  have hat := congrArg (fun r : Placement n ↦ r k) hreveal
  change σ ((trace σ).label k) = τ ((trace τ).label k) at hat
  have hkσ : (trace σ).label k = label := by simp [k]
  have hkτ : (trace τ).label k = label := by
    rw [← hlabels]
    exact hkσ
  simpa [hkσ, hkτ] using hat

/-- On a finite type, injectivity already gives the desired reparameterizing
equivalence.  The inverse need not be implemented by a second simulator. -/
def revealEquiv {n : ℕ} (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    Placement n ≃ Placement n :=
  Equiv.ofBijective (revealOrder trace) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨revealOrder_injective p trace hcausal, rfl⟩

@[simp] theorem revealEquiv_apply {n : ℕ} (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (σ : Placement n) :
    revealEquiv p trace hcausal σ = revealOrder trace σ := rfl

/-- Reindexing by the adaptive reveal order preserves a uniform finite
average exactly. -/
theorem uniformAverage_revealOrder {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (f : Placement n → ℝ) :
    uniformAverage (fun σ ↦ f (revealOrder trace σ)) = uniformAverage f := by
  simpa [Function.comp_def] using
    uniformAverage_comp_equiv (revealEquiv p trace hcausal) f

/-- Test indicator after reparameterizing placements by reveal order. -/
def compiledTestSelector {n : ℕ} (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (k : Fin n) (r : Placement n) : ℝ :=
  if (trace ((revealEquiv p trace hcausal).symm r)).kind k = .test
    then 1 else 0

theorem compiledTestSelector_zero_one {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (k : Fin n) (r : Placement n) :
    compiledTestSelector p trace hcausal k r = 0 ∨
      compiledTestSelector p trace hcausal k r = 1 := by
  unfold compiledTestSelector
  split <;> simp

/-- The compiled test/blind decision is predictable in the exact sense used
by the existing random-permutation urn lemmas. -/
theorem compiledTestSelector_predictable {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    PredictableSelector (compiledTestSelector p trace hcausal) := by
  intro k r s hpref
  let σ := (revealEquiv p trace hcausal).symm r
  let τ := (revealEquiv p trace hcausal).symm s
  have hrevealσ : revealOrder trace σ = r := by
    change revealEquiv p trace hcausal σ = r
    simp [σ]
  have hrevealτ : revealOrder trace τ = s := by
    change revealEquiv p trace hcausal τ = s
    simp [τ]
  have hvalues :
      ValuePrefixEq p k.val (revealOrder trace σ) (revealOrder trace τ) := by
    intro j hj
    rw [hrevealσ, hrevealτ, hpref j hj]
  have hkind := (hcausal σ τ k hvalues).2
  unfold compiledTestSelector
  change (if (trace σ).kind k = .test then 1 else 0) =
    (if (trace τ).kind k = .test then 1 else 0)
  rw [hkind]

@[simp] theorem compiledTestSelector_on_revealOrder {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (k : Fin n) (σ : Placement n) :
    compiledTestSelector p trace hcausal k (revealOrder trace σ) =
      if (trace σ).kind k = .test then 1 else 0 := by
  unfold compiledTestSelector
  have hinv :
      (revealEquiv p trace hcausal).symm (revealOrder trace σ) = σ := by
    rw [← revealEquiv_apply]
    exact (revealEquiv p trace hcausal).symm_apply_apply σ
  rw [hinv]

/-- Exact pathwise tested-class identity after the reveal-order
reparameterization. -/
theorem compiled_test_selection_identity {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (value : Occurrence n → ℝ) (σ : Placement n) :
    (∑ k, compiledTestSelector p trace hcausal k (revealOrder trace σ) *
        value (revealOrder trace σ k)) =
      ∑ k, if (trace σ).kind k = .test then
        value (σ ((trace σ).label k)) else 0 := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [compiledTestSelector_on_revealOrder]
  unfold revealOrder
  split <;> simp_all

/-- Prefix form of `compiled_test_selection_identity`.  Restricting to
`positionsThrough cutoff` is exactly restricting the operational trace to
the first `cutoff.val + 1` first touches. -/
theorem compiled_test_selection_prefix_identity {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (value : Occurrence n → ℝ) (σ : Placement n) (cutoff : Fin n) :
    (∑ k ∈ positionsThrough cutoff,
        compiledTestSelector p trace hcausal k (revealOrder trace σ) *
          value (revealOrder trace σ k)) =
      ∑ k ∈ positionsThrough cutoff,
        if (trace σ).kind k = .test then
          value (σ ((trace σ).label k)) else 0 := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [compiledTestSelector_on_revealOrder]
  unfold revealOrder
  split <;> simp_all

/-- Exact pathwise blind-work identity.  In particular, taking `value=p`
recovers the total processing work of blindly completed first touches. -/
theorem compiled_blind_selection_identity {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (value : Occurrence n → ℝ) (σ : Placement n) :
    (∑ k, (1 - compiledTestSelector p trace hcausal k
        (revealOrder trace σ)) * value (revealOrder trace σ k)) =
      ∑ k, if (trace σ).kind k = .blind then
        value (σ ((trace σ).label k)) else 0 := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [compiledTestSelector_on_revealOrder]
  cases hkind : (trace σ).kind k <;>
    simp [revealOrder, hkind]

/-- Prefix form of `compiled_blind_selection_identity`. -/
theorem compiled_blind_selection_prefix_identity {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace)
    (value : Occurrence n → ℝ) (σ : Placement n) (cutoff : Fin n) :
    (∑ k ∈ positionsThrough cutoff,
        (1 - compiledTestSelector p trace hcausal k
          (revealOrder trace σ)) * value (revealOrder trace σ k)) =
      ∑ k ∈ positionsThrough cutoff,
        if (trace σ).kind k = .blind then
          value (σ ((trace σ).label k)) else 0 := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [compiledTestSelector_on_revealOrder]
  cases hkind : (trace σ).kind k <;>
    simp [revealOrder, hkind]

theorem compiledBlindSelector_predictable {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    PredictableSelector
      (fun k r ↦ 1 - compiledTestSelector p trace hcausal k r) :=
  (compiledTestSelector_predictable p trace hcausal).one_sub

theorem compiledTestSelector_nonneg {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    ∀ k r, 0 ≤ compiledTestSelector p trace hcausal k r := by
  intro k r
  rcases compiledTestSelector_zero_one p trace hcausal k r with h | h <;>
    rw [h] <;> norm_num

theorem compiledTestSelector_le_one {n : ℕ}
    (p : Occurrence n → ℝ)
    (trace : Placement n → TouchTrace n) (hcausal : Causal p trace) :
    ∀ k r, compiledTestSelector p trace hcausal k r ≤ 1 := by
  intro k r
  rcases compiledTestSelector_zero_one p trace hcausal k r with h | h <;>
    rw [h] <;> norm_num

end

end TraceBijection
end RandomizedOptional
end SchedulingPaper
