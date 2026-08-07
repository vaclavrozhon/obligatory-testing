import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Uniform finite permutations

Exact one- and two-position marginals for the finite uniform average on
permutations.  These are the basic probability identities needed by the
sampled obligatory-testing upper bound and its binary Yao lower bound.
-/

namespace SchedulingPaper.Randomized

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma uniformAverage_sum {β : Type*} [Fintype β]
    (f : Equiv.Perm α → β → ℝ) :
    uniformAverage (fun σ => ∑ b, f σ b) =
      ∑ b, uniformAverage (fun σ => f σ b) := by
  unfold uniformAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

lemma perm_image_average_eq [Nonempty α] (f : α → ℝ) (i j : α) :
    uniformAverage (fun σ : Equiv.Perm α => f (σ i)) =
      uniformAverage (fun σ : Equiv.Perm α => f (σ j)) := by
  let e : Equiv.Perm (Equiv.Perm α) := Equiv.mulRight (Equiv.swap i j)
  have h := uniformAverage_comp_equiv e (fun σ : Equiv.Perm α => f (σ i))
  have heval : ((fun σ : Equiv.Perm α => f (σ i)) ∘ e) =
      (fun σ : Equiv.Perm α => f (σ j)) := by
    funext σ
    simp [e, Equiv.Perm.mul_apply]
  rw [heval] at h
  exact h.symm

lemma sum_perm_image_average [Nonempty α] (f : α → ℝ) :
    (∑ i, uniformAverage (fun σ : Equiv.Perm α => f (σ i))) = ∑ i, f i := by
  rw [← uniformAverage_sum]
  calc
    uniformAverage (fun σ : Equiv.Perm α => ∑ i, f (σ i)) =
        uniformAverage (fun _σ : Equiv.Perm α => ∑ i, f i) := by
      congr 1
      funext σ
      exact Equiv.sum_comp σ f
    _ = ∑ i, f i := uniformAverage_const _

lemma card_mul_perm_image_average [Nonempty α] (f : α → ℝ) (i : α) :
    (Fintype.card α : ℝ) * uniformAverage (fun σ : Equiv.Perm α => f (σ i)) =
      ∑ j, f j := by
  rw [← sum_perm_image_average f]
  calc
    (Fintype.card α : ℝ) * uniformAverage (fun σ : Equiv.Perm α => f (σ i)) =
        ∑ _j : α, uniformAverage (fun σ : Equiv.Perm α => f (σ i)) := by simp
    _ = ∑ j : α, uniformAverage (fun σ : Equiv.Perm α => f (σ j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact perm_image_average_eq f i j

/-- The image of a fixed position under a uniform finite permutation is
uniform on the label set. -/
theorem uniformAverage_perm_apply [Nonempty α] (f : α → ℝ) (i : α) :
    uniformAverage (fun σ : Equiv.Perm α => f (σ i)) =
      (∑ j, f j) / Fintype.card α := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  apply (eq_div_iff hcard).2
  simpa [mul_comm] using card_mul_perm_image_average f i

omit [Fintype α] in
lemma exists_perm_map_ordered_pair {i j i' j' : α}
    (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ τ : Equiv.Perm α, τ i = i' ∧ τ j = j' := by
  let s₁ : Equiv.Perm α := Equiv.swap i i'
  let j₁ : α := s₁ j
  have hj₁i' : j₁ ≠ i' := by
    intro h
    have : s₁ j = s₁ i := by simpa [s₁] using h
    exact hij (s₁.injective this).symm
  let s₂ : Equiv.Perm α := Equiv.swap j₁ j'
  have hi'j₁ : i' ≠ j₁ := Ne.symm hj₁i'
  have hi'j' : i' ≠ j' := hij'
  let τ : Equiv.Perm α := s₁.trans s₂
  refine ⟨τ, ?_, ?_⟩
  · change s₂ (s₁ i) = i'
    rw [show s₁ i = i' by simp [s₁]]
    exact Equiv.swap_apply_of_ne_of_ne hi'j₁ hi'j'
  · change s₂ (s₁ j) = j'
    change s₂ j₁ = j'
    simp [s₂]

lemma perm_pair_average_eq [Nonempty α] (f : α → α → ℝ)
    {i j i' j' : α} (hij : i ≠ j) (hij' : i' ≠ j') :
    uniformAverage (fun σ : Equiv.Perm α => f (σ i) (σ j)) =
      uniformAverage (fun σ : Equiv.Perm α => f (σ i') (σ j')) := by
  obtain ⟨τ, hτi, hτj⟩ := exists_perm_map_ordered_pair hij hij'
  let e : Equiv.Perm (Equiv.Perm α) := Equiv.mulRight τ
  have h := uniformAverage_comp_equiv e
    (fun σ : Equiv.Perm α => f (σ i) (σ j))
  have heval : ((fun σ : Equiv.Perm α => f (σ i) (σ j)) ∘ e) =
      (fun σ : Equiv.Perm α => f (σ i') (σ j')) := by
    funext σ
    simp [e, Equiv.Perm.mul_apply, hτi, hτj]
  rw [heval] at h
  exact h.symm

/-- Ordered pairs of distinct labels. -/
abbrev OrderedDistinct (α : Type*) := {z : α × α // z.1 ≠ z.2}

instance orderedDistinctNonempty [Nonempty α] {i j : α} (hij : i ≠ j) :
    Nonempty (OrderedDistinct α) := ⟨⟨(i, j), hij⟩⟩

/-- A permutation acts bijectively on ordered pairs of distinct labels. -/
def orderedDistinctPerm (σ : Equiv.Perm α) :
    OrderedDistinct α ≃ OrderedDistinct α where
  toFun z := ⟨(σ z.val.1, σ z.val.2), fun h => z.property (σ.injective h)⟩
  invFun z :=
    ⟨(σ.symm z.val.1, σ.symm z.val.2), fun h => z.property (σ.symm.injective h)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> simp

lemma sum_perm_orderedDistinct (f : α → α → ℝ) (σ : Equiv.Perm α) :
    (∑ z : OrderedDistinct α, f (σ z.val.1) (σ z.val.2)) =
      ∑ z : OrderedDistinct α, f z.val.1 z.val.2 := by
  simpa [orderedDistinctPerm] using
    (Equiv.sum_comp (orderedDistinctPerm σ)
      (fun z : OrderedDistinct α => f z.val.1 z.val.2))

lemma card_mul_perm_pair_average [Nonempty α] (f : α → α → ℝ)
    {i j : α} (hij : i ≠ j) :
    (Fintype.card (OrderedDistinct α) : ℝ) *
        uniformAverage (fun σ : Equiv.Perm α => f (σ i) (σ j)) =
      ∑ z : OrderedDistinct α, f z.val.1 z.val.2 := by
  letI : Nonempty (OrderedDistinct α) := orderedDistinctNonempty hij
  calc
    (Fintype.card (OrderedDistinct α) : ℝ) *
        uniformAverage (fun σ : Equiv.Perm α => f (σ i) (σ j)) =
      ∑ _z : OrderedDistinct α,
        uniformAverage (fun σ : Equiv.Perm α => f (σ i) (σ j)) := by simp
    _ = ∑ z : OrderedDistinct α,
        uniformAverage (fun σ : Equiv.Perm α => f (σ z.val.1) (σ z.val.2)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact perm_pair_average_eq f hij z.property
    _ = uniformAverage (fun σ : Equiv.Perm α =>
        ∑ z : OrderedDistinct α, f (σ z.val.1) (σ z.val.2)) := by
      rw [uniformAverage_sum]
    _ = uniformAverage (fun _σ : Equiv.Perm α =>
        ∑ z : OrderedDistinct α, f z.val.1 z.val.2) := by
      congr 1
      funext σ
      exact sum_perm_orderedDistinct f σ
    _ = ∑ z : OrderedDistinct α, f z.val.1 z.val.2 := uniformAverage_const _

/-- Two distinct positions of a uniform permutation form a uniform ordered
pair of distinct labels. -/
theorem uniformAverage_perm_apply₂ [Nonempty α] (f : α → α → ℝ)
    {i j : α} (hij : i ≠ j) :
    uniformAverage (fun σ : Equiv.Perm α => f (σ i) (σ j)) =
      (∑ z : OrderedDistinct α, f z.val.1 z.val.2) /
        Fintype.card (OrderedDistinct α) := by
  letI : Nonempty (OrderedDistinct α) := orderedDistinctNonempty hij
  have hcard : (Fintype.card (OrderedDistinct α) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  apply (eq_div_iff hcard).2
  simpa [mul_comm] using card_mul_perm_pair_average f hij

end

end SchedulingPaper.Randomized
