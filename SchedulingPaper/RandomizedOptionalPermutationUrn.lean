import SchedulingPaper.RandomizedOptionalUrn
import SchedulingPaper.RandomPermutation
import Mathlib.Tactic

/-!
# Optional testing: centered draws from a random-permutation urn

The main lemma is a finite, combinatorial substitute for conditional
expectation.  Under a uniform random permutation, the next revealed value
minus the mean of the remaining suffix is orthogonal to every quantity that
is unchanged by permuting that suffix.  This is exactly the martingale-
difference fact needed for predictable test/blind selectors.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized

noncomputable section

def suffixPositions {n : ℕ} (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun r => j.val ≤ r.val

@[simp] theorem mem_suffixPositions {n : ℕ} {j r : Fin n} :
    r ∈ suffixPositions j ↔ j.val ≤ r.val := by
  simp [suffixPositions]

theorem self_mem_suffixPositions {n : ℕ} (j : Fin n) :
    j ∈ suffixPositions j := by simp

theorem suffixPositions_nonempty {n : ℕ} (j : Fin n) :
    (suffixPositions j).Nonempty :=
  ⟨j, self_mem_suffixPositions j⟩

@[simp] theorem suffixPositions_card {n : ℕ} (j : Fin n) :
    (suffixPositions j).card = n - j.val := by
  have hsuffix : suffixPositions j = Finset.Ici j := by
    ext r
    simp [suffixPositions]
  rw [hsuffix]
  simp

/-- Positions at or before a fixed cutoff.  These are precisely the touch
prefixes whose remaining urn still contains the suffix beginning at
`cutoff`. -/
def positionsThrough {n : ℕ} (cutoff : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.val ≤ cutoff.val

@[simp] theorem mem_positionsThrough {n : ℕ} {cutoff j : Fin n} :
    j ∈ positionsThrough cutoff ↔ j.val ≤ cutoff.val := by
  simp [positionsThrough]

/-- Checkpoints spaced backwards from the last relevant touch.  Backwards
spacing makes the endpoint exact and avoids a partially filled last block. -/
def backwardCheckpoints {n : ℕ} (step : ℕ) (cutoff : Fin n) :
    Finset (Fin n) :=
  (Finset.range (cutoff.val / step + 1)).image fun k =>
    ⟨cutoff.val - k * step,
      lt_of_le_of_lt (Nat.sub_le cutoff.val (k * step)) cutoff.isLt⟩

theorem backwardCheckpoints_card_le {n : ℕ} (step : ℕ) (cutoff : Fin n) :
    (backwardCheckpoints step cutoff).card ≤ cutoff.val / step + 1 := by
  unfold backwardCheckpoints
  exact (Finset.card_image_le.trans_eq (Finset.card_range _))

theorem backwardCheckpoints_mem_le_cutoff
    {n : ℕ} {step : ℕ} {cutoff c : Fin n}
    (hc : c ∈ backwardCheckpoints step cutoff) :
    c.val ≤ cutoff.val := by
  rw [backwardCheckpoints, Finset.mem_image] at hc
  obtain ⟨k, _hk, rfl⟩ := hc
  exact Nat.sub_le _ _

/-- Every relevant position is followed by a checkpoint at distance less
than `step`, and no checkpoint goes past the cutoff. -/
theorem backwardCheckpoints_cover
    {n : ℕ} {step : ℕ} (hstep : 0 < step)
    {cutoff j : Fin n} (hj : j ∈ positionsThrough cutoff) :
    ∃ c ∈ backwardCheckpoints step cutoff,
      j.val ≤ c.val ∧ c.val - j.val < step := by
  let k := (cutoff.val - j.val) / step
  let c : Fin n :=
    ⟨cutoff.val - k * step,
      lt_of_le_of_lt (Nat.sub_le cutoff.val (k * step)) cutoff.isLt⟩
  have hjcut : j.val ≤ cutoff.val := mem_positionsThrough.mp hj
  have hkle : k ≤ cutoff.val / step := by
    dsimp [k]
    exact Nat.div_le_div_right (Nat.sub_le cutoff.val j.val)
  have hklt : k < cutoff.val / step + 1 := by
    omega
  have hc : c ∈ backwardCheckpoints step cutoff := by
    rw [backwardCheckpoints, Finset.mem_image]
    exact ⟨k, Finset.mem_range.mpr hklt, rfl⟩
  have hdecomp := Nat.mod_add_div (cutoff.val - j.val) step
  have hmod := Nat.mod_lt (cutoff.val - j.val) hstep
  have hprod := Nat.div_mul_le_self (cutoff.val - j.val) step
  rw [Nat.mul_comm step] at hdecomp
  refine ⟨c, hc, ?_, ?_⟩ <;> dsimp [c, k]
  · omega
  · omega

/-- Empirical mean of the labels occupying positions `j,j+1,...` in a
permutation. -/
def permutationSuffixMean {n : ℕ}
    (value : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  (∑ r ∈ suffixPositions j, value (σ r)) / (suffixPositions j).card

/-- A random variable determined by the values revealed strictly before
position `j`. -/
def PrefixInvariant {n : ℕ} (j : Fin n)
    (F : Equiv.Perm (Fin n) → ℝ) : Prop :=
  ∀ σ τ, (∀ i, i.val < j.val → σ i = τ i) → F σ = F τ

/-- A suffix position chosen using only values already exposed before `j`.
This is the label-choice analogue of a predictable scalar selector. -/
def PrefixInvariantChoice {n : ℕ} (j : Fin n)
    (choose : Equiv.Perm (Fin n) → Fin n) : Prop :=
  ∀ σ τ, (∀ i, i.val < j.val → σ i = τ i) → choose σ = choose τ

/-- One adaptive without-replacement choice is a measure-preserving suffix
swap.  The chosen position may depend arbitrarily on the exposed prefix, but
must lie in the still-unexposed suffix. -/
def adaptiveSuffixSwapEquiv {n : ℕ} (j : Fin n)
    (choose : Equiv.Perm (Fin n) → Fin n)
    (hPrefix : PrefixInvariantChoice j choose)
    (hSuffix : ∀ σ, choose σ ∈ suffixPositions j) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun σ := σ * Equiv.swap j (choose σ)
  invFun σ := σ * Equiv.swap j (choose σ)
  left_inv σ := by
    have hchoice :
        choose (σ * Equiv.swap j (choose σ)) = choose σ := by
      apply hPrefix
      intro i hi
      have hij : i ≠ j := by
        intro h
        subst j
        simp at hi
      have hir : i ≠ choose σ := by
        intro h
        subst i
        have hs := mem_suffixPositions.mp (hSuffix σ)
        omega
      simp [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hij hir]
    rw [hchoice]
    ext i
    simp [Equiv.Perm.mul_apply]
  right_inv σ := by
    have hchoice :
        choose (σ * Equiv.swap j (choose σ)) = choose σ := by
      apply hPrefix
      intro i hi
      have hij : i ≠ j := by
        intro h
        subst j
        simp at hi
      have hir : i ≠ choose σ := by
        intro h
        subst i
        have hs := mem_suffixPositions.mp (hSuffix σ)
        omega
      simp [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hij hir]
    rw [hchoice]
    ext i
    simp [Equiv.Perm.mul_apply]

/-- Adaptive choice of one untouched position preserves the uniform law of
the entire permutation. -/
theorem uniformAverage_adaptiveSuffixSwap
    {n : ℕ} (j : Fin n)
    (choose : Equiv.Perm (Fin n) → Fin n)
    (hPrefix : PrefixInvariantChoice j choose)
    (hSuffix : ∀ σ, choose σ ∈ suffixPositions j)
    (f : Equiv.Perm (Fin n) → ℝ) :
    uniformAverage (fun σ =>
      f (σ * Equiv.swap j (choose σ))) = uniformAverage f := by
  simpa [Function.comp_def] using
    uniformAverage_comp_equiv
      (adaptiveSuffixSwapEquiv j choose hPrefix hSuffix) f

/-- A finite adaptive reordering program, built from predictable suffix
swaps.  In the strategy compiler the pivots are the successive first-touch
indices and `choose` locates the label selected by the policy among the
remaining positions. -/
structure AdaptiveSuffixSwap (n : ℕ) where
  pivot : Fin n
  choose : Equiv.Perm (Fin n) → Fin n
  prefixInvariant : PrefixInvariantChoice pivot choose
  choosesSuffix : ∀ σ, choose σ ∈ suffixPositions pivot

def AdaptiveSuffixSwap.equiv {n : ℕ} (step : AdaptiveSuffixSwap n) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
  adaptiveSuffixSwapEquiv step.pivot step.choose
    step.prefixInvariant step.choosesSuffix

def adaptiveReorderingEquiv {n : ℕ} :
    List (AdaptiveSuffixSwap n) → Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | step :: rest => step.equiv.trans (adaptiveReorderingEquiv rest)

/-- Any finite composition of predictable suffix choices preserves the
uniform permutation law. -/
theorem uniformAverage_adaptiveReordering
    {n : ℕ} (steps : List (AdaptiveSuffixSwap n))
    (f : Equiv.Perm (Fin n) → ℝ) :
    uniformAverage (fun σ => f (adaptiveReorderingEquiv steps σ)) =
      uniformAverage f := by
  simpa [Function.comp_def] using
    uniformAverage_comp_equiv (adaptiveReorderingEquiv steps) f

theorem PrefixInvariant.right_mul_suffix_swap
    {n : ℕ} {j : Fin n} {F : Equiv.Perm (Fin n) → ℝ}
    (hF : PrefixInvariant j F)
    (σ : Equiv.Perm (Fin n)) {r : Fin n}
    (hr : r ∈ suffixPositions j) :
    F (σ * Equiv.swap j r) = F σ := by
  apply hF
  intro i hi
  have hij : i ≠ j := by
    intro h
    subst j
    simp at hi
  have hir : i ≠ r := by
    intro h
    subst r
    have hjr := (mem_suffixPositions.mp hr)
    omega
  simp [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hij hir]

theorem PrefixInvariant.right_mul_swap_of_suffix
    {n : ℕ} {pivot : Fin n} {F : Equiv.Perm (Fin n) → ℝ}
    (hF : PrefixInvariant pivot F)
    (σ : Equiv.Perm (Fin n)) {j r : Fin n}
    (hj : j ∈ suffixPositions pivot)
    (hr : r ∈ suffixPositions pivot) :
    F (σ * Equiv.swap j r) = F σ := by
  apply hF
  intro i hi
  have hij : i ≠ j := by
    intro h
    subst j
    have := mem_suffixPositions.mp hj
    omega
  have hir : i ≠ r := by
    intro h
    subst r
    have := mem_suffixPositions.mp hr
    omega
  simp [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hij hir]

private def suffixSwapEquiv {n : ℕ} (pivot : Fin n) {j r : Fin n}
    (hj : j ∈ suffixPositions pivot) (hr : r ∈ suffixPositions pivot) :
    ↥(suffixPositions pivot) ≃ ↥(suffixPositions pivot) where
  toFun k := ⟨Equiv.swap j r k.val, by
    rw [mem_suffixPositions]
    by_cases hkj : k.val = j
    · simp [hkj, mem_suffixPositions.mp hr]
    by_cases hkr : k.val = r
    · simp [hkr, mem_suffixPositions.mp hj]
    simpa [Equiv.swap_apply_of_ne_of_ne hkj hkr] using
      (mem_suffixPositions.mp k.property)⟩
  invFun k := ⟨Equiv.swap j r k.val, by
    rw [mem_suffixPositions]
    by_cases hkj : k.val = j
    · simp [hkj, mem_suffixPositions.mp hr]
    by_cases hkr : k.val = r
    · simp [hkr, mem_suffixPositions.mp hj]
    simpa [Equiv.swap_apply_of_ne_of_ne hkj hkr] using
      (mem_suffixPositions.mp k.property)⟩
  left_inv k := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

/-- Swapping any two still-unrevealed positions preserves the empirical mean
of the remaining urn. -/
theorem permutationSuffixMean_right_mul_swap
    {n : ℕ} (value : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (pivot : Fin n) {j r : Fin n}
    (hj : j ∈ suffixPositions pivot) (hr : r ∈ suffixPositions pivot) :
    permutationSuffixMean value (σ * Equiv.swap j r) pivot =
      permutationSuffixMean value σ pivot := by
  unfold permutationSuffixMean
  congr 1
  conv_lhs => rw [← Finset.sum_attach]
  conv_rhs => rw [← Finset.sum_attach]
  simpa [Equiv.Perm.mul_apply, suffixSwapEquiv] using
    (Equiv.sum_comp (suffixSwapEquiv pivot hj hr)
      (fun k : ↥(suffixPositions pivot) => value (σ k.val)))

private theorem uniformAverage_finset_sum
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (S : Finset ι) (f : Ω → ι → ℝ) :
    uniformAverage (fun ω => ∑ i ∈ S, f ω i) =
      ∑ i ∈ S, uniformAverage (fun ω => f ω i) := by
  unfold uniformAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

/-- Right-multiplying a permutation by a swap sends its value at the first
swapped position to its old value at the second. -/
private theorem uniformAverage_weighted_swap
    {n : ℕ} (value : Fin n → ℝ) (F : Equiv.Perm (Fin n) → ℝ)
    (j r : Fin n)
    (hInvariant : ∀ σ,
      F (σ * Equiv.swap j r) = F σ) :
    uniformAverage (fun σ : Equiv.Perm (Fin n) => F σ * value (σ r)) =
      uniformAverage (fun σ : Equiv.Perm (Fin n) => F σ * value (σ j)) := by
  let e : Equiv.Perm (Equiv.Perm (Fin n)) :=
    Equiv.mulRight (Equiv.swap j r)
  have h := uniformAverage_comp_equiv e
    (fun σ : Equiv.Perm (Fin n) => F σ * value (σ j))
  have heval :
      ((fun σ : Equiv.Perm (Fin n) => F σ * value (σ j)) ∘ e) =
        (fun σ : Equiv.Perm (Fin n) => F σ * value (σ r)) := by
    funext σ
    simp [e, Equiv.Perm.mul_apply, hInvariant]
  rwa [heval] at h

/-- Weighted suffix averaging: a suffix-symmetric quantity sees every
remaining position with the same weighted expectation. -/
theorem uniformAverage_mul_suffixMean
    {n : ℕ} (value : Fin n → ℝ) (F : Equiv.Perm (Fin n) → ℝ)
    (j : Fin n)
    (hInvariant : ∀ σ r, r ∈ suffixPositions j →
      F (σ * Equiv.swap j r) = F σ) :
    uniformAverage (fun σ => F σ * permutationSuffixMean value σ j) =
      uniformAverage (fun σ => F σ * value (σ j)) := by
  let S := suffixPositions j
  have hSpos : 0 < S.card := (suffixPositions_nonempty j).card_pos
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hrewrite :
      (fun σ : Equiv.Perm (Fin n) =>
          F σ * permutationSuffixMean value σ j) =
        (fun σ => (∑ r ∈ S, F σ * value (σ r)) / S.card) := by
    funext σ
    unfold permutationSuffixMean
    change F σ * ((∑ r ∈ S, value (σ r)) / (S.card : ℝ)) =
      (∑ r ∈ S, F σ * value (σ r)) / (S.card : ℝ)
    field_simp [hcard]
    rw [Finset.mul_sum]
  rw [hrewrite]
  have hsum :
      uniformAverage (fun σ : Equiv.Perm (Fin n) =>
          ∑ r ∈ S, F σ * value (σ r)) =
        ∑ r ∈ S,
          uniformAverage (fun σ => F σ * value (σ r)) :=
    uniformAverage_finset_sum S _
  calc
    uniformAverage (fun σ : Equiv.Perm (Fin n) =>
        (∑ r ∈ S, F σ * value (σ r)) / S.card) =
        (∑ r ∈ S,
          uniformAverage (fun σ => F σ * value (σ r))) / S.card := by
      rw [show (fun σ : Equiv.Perm (Fin n) =>
          (∑ r ∈ S, F σ * value (σ r)) / S.card) =
        (fun σ => (S.card : ℝ)⁻¹ *
          ∑ r ∈ S, F σ * value (σ r)) by
            funext σ
            field_simp [hcard]]
      rw [uniformAverage_smul, hsum]
      field_simp [hcard]
    _ = (∑ _r ∈ S,
          uniformAverage (fun σ => F σ * value (σ j))) / S.card := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact uniformAverage_weighted_swap value F j r
        (fun σ => hInvariant σ r (by simpa [S] using hr))
    _ = uniformAverage (fun σ => F σ * value (σ j)) := by
      simp [hcard]

/-- The next centered urn draw is orthogonal to every suffix-symmetric
weight.  In applications the weight is a product of earlier increments and
the predictable `0/1` decision at position `j`. -/
theorem uniformAverage_mul_next_sub_suffixMean_eq_zero
    {n : ℕ} (value : Fin n → ℝ) (F : Equiv.Perm (Fin n) → ℝ)
    (j : Fin n)
    (hInvariant : ∀ σ r, r ∈ suffixPositions j →
      F (σ * Equiv.swap j r) = F σ) :
    uniformAverage (fun σ =>
      F σ * (value (σ j) - permutationSuffixMean value σ j)) = 0 := by
  have hmean := uniformAverage_mul_suffixMean value F j hInvariant
  rw [show (fun σ =>
      F σ * (value (σ j) - permutationSuffixMean value σ j)) =
    (fun σ => F σ * value (σ j) +
      -(F σ * permutationSuffixMean value σ j)) by
        funext σ
        ring]
  rw [uniformAverage_add]
  have hneg :
      uniformAverage (fun σ =>
          -(F σ * permutationSuffixMean value σ j)) =
        -uniformAverage (fun σ =>
          F σ * permutationSuffixMean value σ j) := by
    simpa using uniformAverage_smul (-1)
      (fun σ => F σ * permutationSuffixMean value σ j)
  rw [hneg, hmean]
  ring

/-- Prefix-measurable form of the centered-draw orthogonality theorem. -/
theorem PrefixInvariant.uniformAverage_mul_next_sub_suffixMean_eq_zero
    {n : ℕ} (value : Fin n → ℝ) (F : Equiv.Perm (Fin n) → ℝ)
    (j : Fin n) (hF : PrefixInvariant j F) :
    uniformAverage (fun σ =>
      F σ * (value (σ j) - permutationSuffixMean value σ j)) = 0 := by
  exact
    SchedulingPaper.RandomizedOptional.uniformAverage_mul_next_sub_suffixMean_eq_zero
      value F j
        (fun σ r hr => PrefixInvariant.right_mul_suffix_swap hF σ hr)

/-! ## Predictable increments -/

def PredictableSelector {n : ℕ}
    (select : Fin n → Equiv.Perm (Fin n) → ℝ) : Prop :=
  ∀ j, PrefixInvariant j (select j)

theorem PredictableSelector.one_sub
    {n : ℕ} {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hselect : PredictableSelector select) :
    PredictableSelector (fun j σ => 1 - select j σ) := by
  intro j σ τ hprefix
  change 1 - select j σ = 1 - select j τ
  rw [hselect j σ τ hprefix]

def centeredUrnIncrement {n : ℕ}
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) : ℝ :=
  select j σ * (value (σ j) - permutationSuffixMean value σ j)

theorem centeredUrnIncrement_right_mul_later_swap
    {n : ℕ} {value : Fin n → ℝ}
    {select : Fin n → Equiv.Perm (Fin n) → ℝ}
    (hselect : PredictableSelector select)
    {i j r : Fin n} (hij : i.val < j.val)
    (hr : r ∈ suffixPositions j) (σ : Equiv.Perm (Fin n)) :
    centeredUrnIncrement value select i (σ * Equiv.swap j r) =
      centeredUrnIncrement value select i σ := by
  have hji : j ∈ suffixPositions i := by simp; omega
  have hri : r ∈ suffixPositions i := by
    rw [mem_suffixPositions] at hr ⊢
    omega
  have hselectEq := PrefixInvariant.right_mul_swap_of_suffix
    (hselect i) σ hji hri
  have hmeanEq := permutationSuffixMean_right_mul_swap
    value σ i hji hri
  have hiJ : i ≠ j := by
    intro h
    subst j
    simp at hij
  have hiR : i ≠ r := by
    intro h
    subst r
    rw [mem_suffixPositions] at hr
    omega
  unfold centeredUrnIncrement
  rw [hselectEq, hmeanEq]
  simp [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hiJ hiR]

/-- Distinct predictable urn increments are pairwise orthogonal under the
uniform random permutation. -/
theorem centeredUrnIncrement_orthogonal
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hselect : PredictableSelector select)
    {i j : Fin n} (hij : i ≠ j) :
    uniformAverage (fun σ =>
      centeredUrnIncrement value select i σ *
        centeredUrnIncrement value select j σ) = 0 := by
  have hvalNe : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hvalNe with hlt | hgt
  · let F : Equiv.Perm (Fin n) → ℝ := fun σ =>
      centeredUrnIncrement value select i σ * select j σ
    have hF : PrefixInvariant j F := by
      intro σ τ hprefix
      -- It is enough to use the defining prefix invariance of both factors.
      have hselJ : select j σ = select j τ := hselect j σ τ hprefix
      have hselI : select i σ = select i τ := by
        apply hselect i σ τ
        intro k hki
        exact hprefix k (lt_trans hki hlt)
      have hvalueI : value (σ i) = value (τ i) := by
        rw [hprefix i hlt]
      have hsuffixI :
          permutationSuffixMean value σ i =
            permutationSuffixMean value τ i := by
        -- Equal prefixes leave the same multiset in the suffix.  Prove this
        -- by subtracting their equal prefix sums from the permutation-total.
        unfold permutationSuffixMean
        congr 1
        have htotalσ : (∑ k, value (σ k)) = ∑ k, value k :=
          Equiv.sum_comp σ value
        have htotalτ : (∑ k, value (τ k)) = ∑ k, value k :=
          Equiv.sum_comp τ value
        let pre : Finset (Fin n) :=
          Finset.univ.filter fun k => k.val < i.val
        have hpre :
            (∑ k ∈ pre, value (σ k)) =
              ∑ k ∈ pre, value (τ k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_filter] at hk
          rw [hprefix k (lt_trans hk.2 hlt)]
        have hpartitionσ :
            (∑ k ∈ pre, value (σ k)) +
                (∑ k ∈ suffixPositions i, value (σ k)) =
              ∑ k, value (σ k) := by
          rw [← Finset.sum_union]
          · apply Finset.sum_congr
            · ext k
              simp only [Finset.mem_union, Finset.mem_filter,
                Finset.mem_univ, true_and, pre, mem_suffixPositions]
              constructor
              · intro _h
                trivial
              · intro _h
                exact lt_or_ge k.val i.val
            · intro k _hk
              rfl
          · rw [Finset.disjoint_left]
            intro k hkpre hksuf
            simp [pre] at hkpre
            rw [mem_suffixPositions] at hksuf
            omega
        have hpartitionτ :
            (∑ k ∈ pre, value (τ k)) +
                (∑ k ∈ suffixPositions i, value (τ k)) =
              ∑ k, value (τ k) := by
          rw [← Finset.sum_union]
          · apply Finset.sum_congr
            · ext k
              simp only [Finset.mem_union, Finset.mem_filter,
                Finset.mem_univ, true_and, pre, mem_suffixPositions]
              constructor
              · intro _h
                trivial
              · intro _h
                exact lt_or_ge k.val i.val
            · intro k _hk
              rfl
          · rw [Finset.disjoint_left]
            intro k hkpre hksuf
            simp [pre] at hkpre
            rw [mem_suffixPositions] at hksuf
            omega
        linarith
      dsimp [F]
      unfold centeredUrnIncrement
      rw [hselI, hvalueI, hsuffixI, hselJ]
    have hzero := hF.uniformAverage_mul_next_sub_suffixMean_eq_zero
      value F j
    simpa [F, centeredUrnIncrement, mul_assoc] using hzero
  · have hswap := centeredUrnIncrement_orthogonal value select hselect
      (i := j) (j := i) (Ne.symm hij)
    simpa [mul_comm] using hswap

theorem permutationSuffixMean_mem_Icc
    {n : ℕ} (value : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : Fin n)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1) :
    permutationSuffixMean value σ j ∈ Set.Icc (0 : ℝ) 1 := by
  let S := suffixPositions j
  have hSpos : 0 < S.card := (suffixPositions_nonempty j).card_pos
  have hScast : 0 < (S.card : ℝ) := by exact_mod_cast hSpos
  have hsum0 : 0 ≤ ∑ r ∈ S, value (σ r) :=
    Finset.sum_nonneg fun r _hr => hvalue0 (σ r)
  have hsum1 : (∑ r ∈ S, value (σ r)) ≤ S.card := by
    calc
      (∑ r ∈ S, value (σ r)) ≤ ∑ _r ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun r _hr => hvalue1 (σ r)
      _ = S.card := by simp
  constructor
  · unfold permutationSuffixMean
    change 0 ≤ (∑ r ∈ S, value (σ r)) / (S.card : ℝ)
    exact div_nonneg hsum0 hScast.le
  · unfold permutationSuffixMean
    change (∑ r ∈ S, value (σ r)) / (S.card : ℝ) ≤ 1
    rw [div_le_one hScast]
    exact hsum1

/-- Exact finite-population variance of one remaining-suffix empirical mean. -/
theorem uniformAverage_permutationSuffixMean_sq
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ) (j : Fin n) :
    uniformAverage (fun σ =>
        (permutationSuffixMean value σ j - populationMean value) ^ 2) =
      (((suffixPositions j).card : ℝ) *
          ((n : ℝ) - (suffixPositions j).card) /
          ((n : ℝ) * ((n : ℝ) - 1))) *
        (∑ i, centeredPopulation value i ^ 2) /
          ((suffixPositions j).card : ℝ) ^ 2 := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  let S := suffixPositions j
  have hSpos : 0 < S.card := (suffixPositions_nonempty j).card_pos
  have hScast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hrepr :
      (fun σ : Equiv.Perm (Fin n) =>
          (permutationSuffixMean value σ j - populationMean value) ^ 2) =
        (fun σ => (S.card : ℝ)⁻¹ ^ 2 *
          (permutationSampleSum S value σ -
            (S.card : ℝ) * populationMean value) ^ 2) := by
    funext σ
    have hsample :
        permutationSampleSum S value σ =
          ∑ r ∈ S, value (σ r) := by
      unfold permutationSampleSum
      exact Finset.sum_attach S (fun r => value (σ r))
    unfold permutationSuffixMean permutationSampleSum
    change
      ((∑ r ∈ S, value (σ r)) / (S.card : ℝ) -
          populationMean value) ^ 2 =
        (S.card : ℝ)⁻¹ ^ 2 *
          ((∑ r : ↥S, value (σ r.val)) -
            (S.card : ℝ) * populationMean value) ^ 2
    rw [show (∑ r : ↥S, value (σ r.val)) =
        ∑ r ∈ S, value (σ r) by
      simpa [permutationSampleSum] using hsample]
    field_simp [hScast]
  rw [hrepr, uniformAverage_smul]
  rw [uniformAverage_permutationSampleSum_variance S value (by simpa using hn)]
  simp only [Fintype.card_fin]
  dsimp [S]
  field_simp [hScast]

/-- A bounded population has suffix-mean variance at most `2/k`, where `k`
is the number of labels still in the urn. -/
theorem uniformAverage_permutationSuffixMean_sq_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ) (j : Fin n)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1) :
    uniformAverage (fun σ =>
        (permutationSuffixMean value σ j - populationMean value) ^ 2) ≤
      2 / (suffixPositions j).card := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  let S := suffixPositions j
  let N : ℝ := n
  let K : ℝ := S.card
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 0 < N - 1 := by
    have hnReal : (1 : ℝ) < N := by
      dsimp [N]
      exact_mod_cast hn
    linarith
  have hK : 0 < K := by
    dsimp [K, S]
    exact_mod_cast (suffixPositions_nonempty j).card_pos
  have hmean : populationMean value ∈ Set.Icc (0 : ℝ) 1 := by
    unfold populationMean
    simp only [Fintype.card_fin]
    have hsum0 : 0 ≤ ∑ i, value i :=
      Finset.sum_nonneg fun i _ => hvalue0 i
    have hsum1 : (∑ i, value i) ≤ (n : ℝ) := by
      calc
        (∑ i, value i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hvalue1 i
        _ = n := by simp
    constructor
    · exact div_nonneg hsum0 hN.le
    · rw [div_le_one hN]
      exact hsum1
  have hcenteredSq :
      (∑ i, centeredPopulation value i ^ 2) ≤ N := by
    calc
      (∑ i, centeredPopulation value i ^ 2) ≤
          ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        have habs : |centeredPopulation value i| ≤ 1 := by
          unfold centeredPopulation
          rw [abs_le]
          constructor <;>
            linarith [hvalue0 i, hvalue1 i, hmean.1, hmean.2]
        have habs' : |centeredPopulation value i| ≤ |(1 : ℝ)| := by
          simpa using habs
        simpa using (sq_le_sq.mpr habs')
      _ = N := by simp [N]
  have hKleN : K ≤ N := by
    have hcardNat : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    dsimp [K, N]
    exact_mod_cast hcardNat
  rw [uniformAverage_permutationSuffixMean_sq hn value j]
  change (K * (N - K) / (N * (N - 1))) *
      (∑ i, centeredPopulation value i ^ 2) / K ^ 2 ≤ 2 / K
  have hNK0 : 0 ≤ N - K := sub_nonneg.mpr hKleN
  have hcoeff0 : 0 ≤ K * (N - K) / (N * (N - 1)) := by positivity
  have huseV :
      (K * (N - K) / (N * (N - 1))) *
          (∑ i, centeredPopulation value i ^ 2) ≤
        (K * (N - K) / (N * (N - 1))) * N :=
    mul_le_mul_of_nonneg_left hcenteredSq hcoeff0
  have hNratio : N ≤ 2 * (N - 1) := by
    have hnReal : (2 : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hn
    linarith
  rw [div_le_div_iff₀ (sq_pos_of_pos hK) hK]
  field_simp [hN.ne', hN1.ne', hK.ne'] at huseV ⊢
  nlinarith

theorem uniformProbability_permutationSuffixMean_abs_gt_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ) (j : Fin n)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    uniformProbability (fun σ =>
      r < |permutationSuffixMean value σ j - populationMean value|) ≤
      (2 / (suffixPositions j).card) / r ^ 2 := by
  exact uniformProbability_abs_gt_le_secondMoment _ hr
    (uniformAverage_permutationSuffixMean_sq_le hn value j hvalue0 hvalue1)

/-- Union bound over any chosen finite set of suffix checkpoints. -/
theorem uniformProbability_checkpoint_suffixMean_abs_gt_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ) (J : Finset (Fin n))
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    {K r : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hSuffixCard : ∀ j ∈ J, K ≤ (suffixPositions j).card) :
    uniformProbability (fun σ => ∃ j ∈ J,
      r < |permutationSuffixMean value σ j - populationMean value|) ≤
      J.card * ((2 / K) / r ^ 2) := by
  let P : ↥J → Equiv.Perm (Fin n) → Prop := fun j σ =>
    r < |permutationSuffixMean value σ j.val - populationMean value|
  have hpoint : ∀ j : ↥J,
      uniformProbability (P j) ≤ (2 / K) / r ^ 2 := by
    intro j
    have hfixed := uniformProbability_permutationSuffixMean_abs_gt_le
      hn value j.val hvalue0 hvalue1 hr
    have hcardPos : 0 < ((suffixPositions j.val).card : ℝ) := by
      exact_mod_cast (suffixPositions_nonempty j.val).card_pos
    have hdenom :
        2 / (suffixPositions j.val).card ≤ 2 / K := by
      exact div_le_div_of_nonneg_left (by norm_num) hK
        (hSuffixCard j.val j.property)
    exact hfixed.trans
      (div_le_div_of_nonneg_right hdenom (sq_nonneg r))
  have hunion := uniformProbability_exists_le_card_mul P hpoint
  simpa [P] using hunion

/-- Removing `d` bounded observations from a pool of size at least `K`
changes its empirical mean by at most `2d/K`.  The factor two is deliberately
loose and makes the checkpoint interpolation argument elementary. -/
theorem nested_average_abs_le_two_mul_removed_div
    {K k₁ k₂ s₁ s₂ d : ℝ}
    (hK : 0 < K) (hk₂ : K ≤ k₂) (hk₂k₁ : k₂ ≤ k₁)
    (hd : d = k₁ - k₂)
    (hs₂0 : 0 ≤ s₂) (hs₂k₂ : s₂ ≤ k₂)
    (hremoved0 : 0 ≤ s₁ - s₂) (hremovedD : s₁ - s₂ ≤ d) :
    |s₁ / k₁ - s₂ / k₂| ≤ 2 * d / K := by
  have hk₂0 : 0 < k₂ := hK.trans_le hk₂
  have hk₁0 : 0 < k₁ := hk₂0.trans_le hk₂k₁
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hKk₁ : K ≤ k₁ := hk₂.trans hk₂k₁
  have hremovedRatio :
      |(s₁ - s₂) / k₁| ≤ d / K := by
    rw [abs_of_nonneg (div_nonneg hremoved0 hk₁0.le)]
    exact div_le_div₀ hd0 hremovedD hK hKk₁
  have hs₂ratio0 : 0 ≤ s₂ / k₂ := div_nonneg hs₂0 hk₂0.le
  have hs₂ratio1 : s₂ / k₂ ≤ 1 := (div_le_one hk₂0).mpr hs₂k₂
  have hdRatio0 : 0 ≤ d / k₁ := div_nonneg hd0 hk₁0.le
  have hdRatio : d / k₁ ≤ d / K :=
    div_le_div₀ hd0 le_rfl hK hKk₁
  have hproduct0 : 0 ≤ (s₂ / k₂) * (d / k₁) :=
    mul_nonneg hs₂ratio0 hdRatio0
  have hproduct :
      |(s₂ / k₂) * (d / k₁)| ≤ d / K := by
    rw [abs_of_nonneg hproduct0]
    calc
      (s₂ / k₂) * (d / k₁) ≤ 1 * (d / k₁) :=
        mul_le_mul_of_nonneg_right hs₂ratio1 hdRatio0
      _ ≤ d / K := by simpa using hdRatio
  have hidentity :
      s₁ / k₁ - s₂ / k₂ =
        (s₁ - s₂) / k₁ - (s₂ / k₂) * (d / k₁) := by
    rw [hd]
    field_simp [hk₁0.ne', hk₂0.ne']
    ring
  rw [hidentity]
  calc
    |(s₁ - s₂) / k₁ - (s₂ / k₂) * (d / k₁)| ≤
        |(s₁ - s₂) / k₁| + |(s₂ / k₂) * (d / k₁)| :=
      abs_sub _ _
    _ ≤ d / K + d / K := add_le_add hremovedRatio hproduct
    _ = 2 * d / K := by ring

/-- Finset form of the checkpoint interpolation lemma. -/
theorem nested_finset_average_abs_le
    {α : Type*} [DecidableEq α]
    (value : α → ℝ) (S₂ S₁ : Finset α)
    (hsub : S₂ ⊆ S₁)
    (hvalue0 : ∀ i ∈ S₁, 0 ≤ value i)
    (hvalue1 : ∀ i ∈ S₁, value i ≤ 1)
    {K : ℝ} (hK : 0 < K) (hcard : K ≤ S₂.card) :
    |(∑ i ∈ S₁, value i) / S₁.card -
        (∑ i ∈ S₂, value i) / S₂.card| ≤
      2 * ((S₁.card : ℝ) - S₂.card) / K := by
  let s₁ : ℝ := ∑ i ∈ S₁, value i
  let s₂ : ℝ := ∑ i ∈ S₂, value i
  let k₁ : ℝ := S₁.card
  let k₂ : ℝ := S₂.card
  let d : ℝ := k₁ - k₂
  have hk₂k₁ : k₂ ≤ k₁ := by
    dsimp [k₁, k₂]
    exact_mod_cast Finset.card_le_card hsub
  have hs₂0 : 0 ≤ s₂ := by
    dsimp [s₂]
    exact Finset.sum_nonneg fun i hi => hvalue0 i (hsub hi)
  have hs₂k₂ : s₂ ≤ k₂ := by
    dsimp [s₂, k₂]
    calc
      (∑ i ∈ S₂, value i) ≤ ∑ _i ∈ S₂, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => hvalue1 i (hsub hi)
      _ = S₂.card := by simp
  have hdecomp :
      (∑ i ∈ S₂, value i) + (∑ i ∈ S₁ \ S₂, value i) =
        ∑ i ∈ S₁, value i :=
    by simpa [add_comm] using Finset.sum_sdiff hsub (f := value)
  have hremovedEq : s₁ - s₂ = ∑ i ∈ S₁ \ S₂, value i := by
    dsimp [s₁, s₂]
    linarith
  have hremoved0 : 0 ≤ s₁ - s₂ := by
    rw [hremovedEq]
    exact Finset.sum_nonneg fun i hi => hvalue0 i (Finset.sdiff_subset hi)
  have hremovedD : s₁ - s₂ ≤ d := by
    rw [hremovedEq]
    dsimp [d, k₁, k₂]
    calc
      (∑ i ∈ S₁ \ S₂, value i) ≤
          ∑ _i ∈ S₁ \ S₂, (1 : ℝ) :=
        Finset.sum_le_sum fun i hi => hvalue1 i (Finset.sdiff_subset hi)
      _ = ((S₁ \ S₂).card : ℝ) := by simp
      _ = (S₁.card : ℝ) - S₂.card := by
        rw [Finset.cast_card_sdiff hsub]
  exact nested_average_abs_le_two_mul_removed_div hK hcard hk₂k₁
    rfl hs₂0 hs₂k₂ hremoved0 hremovedD

/-- Two nested remaining suffixes have close empirical means when only a
small number of positions separates them. -/
theorem permutationSuffixMean_nested_abs_le
    {n : ℕ} (value : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    {j checkpoint : Fin n} (horder : j.val ≤ checkpoint.val)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    {K : ℝ} (hK : 0 < K)
    (hcard : K ≤ (suffixPositions checkpoint).card) :
    |permutationSuffixMean value σ j -
        permutationSuffixMean value σ checkpoint| ≤
      2 * (((suffixPositions j).card : ℝ) -
        (suffixPositions checkpoint).card) / K := by
  have hsub : suffixPositions checkpoint ⊆ suffixPositions j := by
    intro r hr
    rw [mem_suffixPositions] at hr ⊢
    omega
  have h := nested_finset_average_abs_le
    (fun r => value (σ r)) (suffixPositions checkpoint)
      (suffixPositions j) hsub
      (fun r _hr => hvalue0 (σ r))
      (fun r _hr => hvalue1 (σ r)) hK hcard
  simpa [permutationSuffixMean] using h

/-- A checkpoint cover upgrades fixed-checkpoint concentration to a
simultaneous bound on every relevant suffix.  This cleanly separates the
probability calculation from the later elementary choice of checkpoint
spacing. -/
theorem uniformProbability_relevant_suffixMean_abs_gt_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ) (relevant checkpoints : Finset (Fin n))
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    {K r D : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hcheckpointCard : ∀ c ∈ checkpoints,
      K ≤ (suffixPositions c).card)
    (hcover : ∀ j ∈ relevant, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧
      ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ D ∧
      K ≤ (suffixPositions c).card) :
    uniformProbability (fun σ => ∃ j ∈ relevant,
      r + 2 * D / K <
        |permutationSuffixMean value σ j - populationMean value|) ≤
      checkpoints.card * ((2 / K) / r ^ 2) := by
  have hcontain : ∀ σ,
      (∃ j ∈ relevant,
        r + 2 * D / K <
          |permutationSuffixMean value σ j - populationMean value|) →
      ∃ c ∈ checkpoints,
        r < |permutationSuffixMean value σ c - populationMean value| := by
    intro σ hbad
    obtain ⟨j, hj, hjbad⟩ := hbad
    obtain ⟨c, hc, horder, hdiff, hcap⟩ := hcover j hj
    refine ⟨c, hc, ?_⟩
    by_contra hcgood
    have hinterp := permutationSuffixMean_nested_abs_le
      value σ horder hvalue0 hvalue1 hK hcap
    have hdiffBound :
        2 * (((suffixPositions j).card : ℝ) -
            (suffixPositions c).card) / K ≤ 2 * D / K := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff (by norm_num)) hK.le
    have htriangle := abs_sub_le
      (permutationSuffixMean value σ j)
      (permutationSuffixMean value σ c) (populationMean value)
    have hcgood' :
        |permutationSuffixMean value σ c - populationMean value| ≤ r :=
      le_of_not_gt hcgood
    linarith
  calc
    uniformProbability (fun σ => ∃ j ∈ relevant,
        r + 2 * D / K <
          |permutationSuffixMean value σ j - populationMean value|) ≤
        uniformProbability (fun σ => ∃ c ∈ checkpoints,
          r < |permutationSuffixMean value σ c - populationMean value|) :=
      uniformProbability_mono hcontain
    _ ≤ checkpoints.card * ((2 / K) / r ^ 2) :=
      uniformProbability_checkpoint_suffixMean_abs_gt_le
        hn value checkpoints hvalue0 hvalue1 hK hr hcheckpointCard

/-- A predictable `0/1`-weighted centered urn increment has second moment at
most one. -/
theorem uniformAverage_centeredUrnIncrement_sq_le_one
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (j : Fin n) :
    uniformAverage (fun σ =>
      (centeredUrnIncrement value select j σ) ^ 2) ≤ 1 := by
  calc
    uniformAverage (fun σ =>
        (centeredUrnIncrement value select j σ) ^ 2) ≤
        uniformAverage (fun _σ : Equiv.Perm (Fin n) => (1 : ℝ)) := by
      apply uniformAverage_mono
      intro σ
      obtain ⟨hmean0, hmean1⟩ :=
        permutationSuffixMean_mem_Icc value σ j hvalue0 hvalue1
      have hdiff :
          |value (σ j) - permutationSuffixMean value σ j| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hvalue0 (σ j), hvalue1 (σ j)]
      have hselAbs : |select j σ| ≤ 1 := by
        rw [abs_of_nonneg (hselect0 j σ)]
        exact hselect1 j σ
      have hincAbs : |centeredUrnIncrement value select j σ| ≤ 1 := by
        unfold centeredUrnIncrement
        rw [abs_mul]
        nlinarith [mul_le_mul hselAbs hdiff (abs_nonneg _)
          (show 0 ≤ (1 : ℝ) by norm_num)]
      have hincAbs' :
          |centeredUrnIncrement value select j σ| ≤ |(1 : ℝ)| := by
        simpa using hincAbs
      simpa using (sq_le_sq.mpr hincAbs')
    _ = 1 := uniformAverage_const _

/-- Fixed-horizon concentration for an arbitrary predictable selector in a
random-permutation urn.  This is a complete finite Chebyshev bound, proved
without measure-theoretic conditional expectation. -/
theorem predictable_centeredUrnSum_probability_le
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {e : ℝ} (he : 0 < e) :
    uniformProbability (fun σ =>
      e < |∑ j, centeredUrnIncrement value select j σ|) ≤
      n / e ^ 2 := by
  simpa using uniformProbability_sum_abs_gt_le_of_orthogonal
    (fun j σ => centeredUrnIncrement value select j σ) he
    (fun j => uniformAverage_centeredUrnIncrement_sq_le_one
      value select hvalue0 hvalue1 hselect0 hselect1 j)
    (fun i j hij => centeredUrnIncrement_orthogonal
      value select hPredictable hij)

/-- Concentration transfer from the centered urn martingale and a simultaneous
remaining-urn mean event to the actual adaptively selected count. -/
theorem predictable_selected_count_probability_le
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    {populationMean e r suffixFailure : ℝ}
    (he : 0 < e) (hr : 0 ≤ r)
    (hSuffix :
      uniformProbability (fun σ => ∃ j,
        r < |permutationSuffixMean value σ j - populationMean|) ≤
        suffixFailure) :
    uniformProbability (fun σ =>
      e + r * n <
        |(∑ j, select j σ * value (σ j)) -
          populationMean * ∑ j, select j σ|) ≤
      n / e ^ 2 + suffixFailure := by
  let martingaleBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    e < |∑ j, centeredUrnIncrement value select j σ|
  let suffixBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∃ j, r < |permutationSuffixMean value σ j - populationMean|
  have hsumSelect : ∀ σ, (∑ j, select j σ) ≤ n := by
    intro σ
    calc
      (∑ j, select j σ) ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hselect1 j σ
      _ = n := by simp
  have hcontain : ∀ σ,
      e + r * n <
          |(∑ j, select j σ * value (σ j)) -
            populationMean * ∑ j, select j σ| →
        martingaleBad σ ∨ suffixBad σ := by
    intro σ hbad
    by_contra hnot
    rw [not_or] at hnot
    have hmart :
        |∑ j, centeredUrnIncrement value select j σ| ≤ e :=
      le_of_not_gt hnot.1
    have hsuffix : ∀ j,
        |permutationSuffixMean value σ j - populationMean| ≤ r := by
      intro j
      exact le_of_not_gt (fun hj => hnot.2 ⟨j, hj⟩)
    have htransfer := predictable_selection_discrepancy_abs_le
      (select := fun j => select j σ)
      (value := fun j => value (σ j))
      (remainingMean := fun j => permutationSuffixMean value σ j)
      (populationMean := populationMean)
      (martingaleError := e) (driftError := r)
      (fun j => hselect0 j σ)
      (by simpa [centeredUrnIncrement] using hmart) hsuffix
    have hdrift :
        r * (∑ j, select j σ) ≤ r * n :=
      mul_le_mul_of_nonneg_left (hsumSelect σ) hr
    linarith
  calc
    uniformProbability (fun σ =>
        e + r * n <
          |(∑ j, select j σ * value (σ j)) -
            populationMean * ∑ j, select j σ|) ≤
        uniformProbability (fun σ => martingaleBad σ ∨ suffixBad σ) :=
      uniformProbability_mono hcontain
    _ ≤ uniformProbability martingaleBad + uniformProbability suffixBad :=
      uniformProbability_or_le martingaleBad suffixBad
    _ ≤ n / e ^ 2 + suffixFailure := by
      exact add_le_add
        (predictable_centeredUrnSum_probability_le value select hPredictable
          hvalue0 hvalue1 hselect0 hselect1 he)
        hSuffix

/-- Relevant-prefix version: selectors vanish after the controlled part of
the urn, so no suffix-mean estimate is needed near the final depleted tail. -/
theorem predictable_selected_count_probability_le_relevant
    {n : ℕ} (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (relevant : Finset (Fin n))
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ relevant, ∀ σ, select j σ = 0)
    {populationMean e r suffixFailure : ℝ}
    (he : 0 < e) (hr : 0 ≤ r)
    (hSuffix :
      uniformProbability (fun σ => ∃ j ∈ relevant,
        r < |permutationSuffixMean value σ j - populationMean|) ≤
        suffixFailure) :
    uniformProbability (fun σ =>
      e + r * n <
        |(∑ j, select j σ * value (σ j)) -
          populationMean * ∑ j, select j σ|) ≤
      n / e ^ 2 + suffixFailure := by
  let martingaleBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    e < |∑ j, centeredUrnIncrement value select j σ|
  let suffixBad : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∃ j ∈ relevant,
      r < |permutationSuffixMean value σ j - populationMean|
  have hsumSelect : ∀ σ, (∑ j, select j σ) ≤ n := by
    intro σ
    calc
      (∑ j, select j σ) ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hselect1 j σ
      _ = n := by simp
  have hcontain : ∀ σ,
      e + r * n <
          |(∑ j, select j σ * value (σ j)) -
            populationMean * ∑ j, select j σ| →
        martingaleBad σ ∨ suffixBad σ := by
    intro σ hbad
    by_contra hnot
    rw [not_or] at hnot
    have hmart :
        |∑ j, centeredUrnIncrement value select j σ| ≤ e :=
      le_of_not_gt hnot.1
    let remainingMean : Fin n → ℝ := fun j =>
      if j ∈ relevant then permutationSuffixMean value σ j
      else populationMean
    have hremaining : ∀ j,
        |remainingMean j - populationMean| ≤ r := by
      intro j
      by_cases hj : j ∈ relevant
      · dsimp [remainingMean]
        rw [if_pos hj]
        exact le_of_not_gt (fun h => hnot.2 ⟨j, hj, h⟩)
      · simp [remainingMean, hj]
        exact hr
    have hmartRewrite :
        (∑ j, select j σ * (value (σ j) - remainingMean j)) =
          ∑ j, centeredUrnIncrement value select j σ := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j ∈ relevant
      · simp [remainingMean, hj, centeredUrnIncrement]
      · simp [remainingMean, hj, centeredUrnIncrement,
          hinactive j hj σ]
    have htransfer := predictable_selection_discrepancy_abs_le
      (select := fun j => select j σ)
      (value := fun j => value (σ j))
      (remainingMean := remainingMean)
      (populationMean := populationMean)
      (martingaleError := e) (driftError := r)
      (fun j => hselect0 j σ)
      (by rw [hmartRewrite]; exact hmart) hremaining
    have hdrift :
        r * (∑ j, select j σ) ≤ r * n :=
      mul_le_mul_of_nonneg_left (hsumSelect σ) hr
    linarith
  calc
    uniformProbability (fun σ =>
        e + r * n <
          |(∑ j, select j σ * value (σ j)) -
            populationMean * ∑ j, select j σ|) ≤
        uniformProbability (fun σ => martingaleBad σ ∨ suffixBad σ) :=
      uniformProbability_mono hcontain
    _ ≤ uniformProbability martingaleBad + uniformProbability suffixBad :=
      uniformProbability_or_le martingaleBad suffixBad
    _ ≤ n / e ^ 2 + suffixFailure := by
      exact add_le_add
        (predictable_centeredUrnSum_probability_le value select hPredictable
          hvalue0 hvalue1 hselect0 hselect1 he)
        hSuffix

/-- Complete checkpoint-based predictable-selection concentration theorem.
It is finite, policy-uniform, and uses only explicit uniform averages over
permutations. -/
theorem predictable_selected_count_checkpoint_probability_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (relevant checkpoints : Finset (Fin n))
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ relevant, ∀ σ, select j σ = 0)
    {e K r D : ℝ}
    (he : 0 < e) (hK : 0 < K) (hr : 0 < r) (hD : 0 ≤ D)
    (hcheckpointCard : ∀ c ∈ checkpoints,
      K ≤ (suffixPositions c).card)
    (hcover : ∀ j ∈ relevant, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧
      ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ D ∧
      K ≤ (suffixPositions c).card) :
    uniformProbability (fun σ =>
      e + (r + 2 * D / K) * n <
        |(∑ j, select j σ * value (σ j)) -
          Randomized.populationMean value * ∑ j, select j σ|) ≤
      n / e ^ 2 + checkpoints.card * ((2 / K) / r ^ 2) := by
  have hsuffix := uniformProbability_relevant_suffixMean_abs_gt_le
    hn value relevant checkpoints hvalue0 hvalue1 hK hr
      hcheckpointCard hcover
  exact predictable_selected_count_probability_le_relevant
    value select relevant hPredictable hvalue0 hvalue1
      hselect0 hselect1 hinactive he
      (by positivity) hsuffix

/-- Concrete regular-checkpoint form.  If the selector is inactive after
`cutoff`, checkpoints spaced `step` positions apart suffice.  The deviation
has martingale term `e`, suffix-mean term `r*n`, and interpolation term
`2*step*n/K`, where `K` is the number of jobs left at the cutoff. -/
theorem predictable_selected_count_regular_checkpoint_probability_le
    {n : ℕ} (hn : 1 < n)
    (value : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) {step : ℕ} (hstep : 0 < step)
    (hPredictable : PredictableSelector select)
    (hvalue0 : ∀ i, 0 ≤ value i)
    (hvalue1 : ∀ i, value i ≤ 1)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ positionsThrough cutoff, ∀ σ, select j σ = 0)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ =>
      e + (r + 2 * step / (suffixPositions cutoff).card) * n <
        |(∑ j, select j σ * value (σ j)) -
          Randomized.populationMean value * ∑ j, select j σ|) ≤
      n / e ^ 2 +
        ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
  let checkpoints := backwardCheckpoints step cutoff
  let K : ℝ := (suffixPositions cutoff).card
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (suffixPositions_nonempty cutoff).card_pos
  have hcheckpointCard : ∀ c ∈ checkpoints,
      K ≤ (suffixPositions c).card := by
    intro c hc
    have hcle := backwardCheckpoints_mem_le_cutoff (by simpa [checkpoints] using hc)
    dsimp [K]
    simp only [suffixPositions_card]
    exact_mod_cast (by omega : n - cutoff.val ≤ n - c.val)
  have hcover : ∀ j ∈ positionsThrough cutoff, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧
      ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ step ∧
      K ≤ (suffixPositions c).card := by
    intro j hj
    obtain ⟨c, hc, hjc, hdist⟩ := backwardCheckpoints_cover hstep hj
    refine ⟨c, by simpa [checkpoints] using hc, hjc, ?_,
      hcheckpointCard c (by simpa [checkpoints] using hc)⟩
    simp only [suffixPositions_card]
    norm_num at *
    exact_mod_cast (by omega : c.val ≤ step + j.val)
  have hbase := predictable_selected_count_checkpoint_probability_le
    hn value select (positionsThrough cutoff) checkpoints hPredictable
      hvalue0 hvalue1 hselect0 hselect1 hinactive
      he hK hr (show (0 : ℝ) ≤ step by positivity)
      hcheckpointCard hcover
  have hcard : (checkpoints.card : ℝ) ≤
      ((cutoff.val / step + 1 : ℕ) : ℝ) := by
    exact_mod_cast backwardCheckpoints_card_le step cutoff
  have hfactor0 : 0 ≤ (2 / K) / r ^ 2 := by positivity
  have hrhs :
      checkpoints.card * ((2 / K) / r ^ 2) ≤
        ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / K) / r ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hfactor0
  have htotal :
      (n : ℝ) / e ^ 2 + checkpoints.card * ((2 / K) / r ^ 2) ≤
        n / e ^ 2 + ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / K) / r ^ 2) :=
    add_le_add_right hrhs _
  simpa [K, checkpoints] using
    hbase.trans htotal

/-- Scaled version for processing work in `[0,L]`. -/
theorem predictable_selected_work_checkpoint_probability_le
    {n : ℕ} (hn : 1 < n)
    (processing : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (relevant checkpoints : Finset (Fin n))
    (hPredictable : PredictableSelector select)
    {L : ℝ} (hL : 0 < L)
    (hp0 : ∀ i, 0 ≤ processing i)
    (hpL : ∀ i, processing i ≤ L)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ relevant, ∀ σ, select j σ = 0)
    {e K r D : ℝ}
    (he : 0 < e) (hK : 0 < K) (hr : 0 < r) (hD : 0 ≤ D)
    (hcheckpointCard : ∀ c ∈ checkpoints,
      K ≤ (suffixPositions c).card)
    (hcover : ∀ j ∈ relevant, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧
      ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ D ∧
      K ≤ (suffixPositions c).card) :
    uniformProbability (fun σ =>
      L * (e + (r + 2 * D / K) * n) <
        |(∑ j, select j σ * processing (σ j)) -
          Randomized.populationMean processing * ∑ j, select j σ|) ≤
      n / e ^ 2 + checkpoints.card * ((2 / K) / r ^ 2) := by
  let normalized : Fin n → ℝ := fun i => processing i / L
  have hnorm0 : ∀ i, 0 ≤ normalized i := fun i =>
    div_nonneg (hp0 i) hL.le
  have hnorm1 : ∀ i, normalized i ≤ 1 := fun i =>
    (div_le_one hL).mpr (hpL i)
  have hbound := predictable_selected_count_checkpoint_probability_le
    hn normalized select relevant checkpoints hPredictable
      hnorm0 hnorm1 hselect0 hselect1 hinactive
      he hK hr hD hcheckpointCard hcover
  have hscale : ∀ σ,
      (∑ j, select j σ * processing (σ j)) -
          Randomized.populationMean processing * ∑ j, select j σ =
        L * ((∑ j, select j σ * normalized (σ j)) -
          Randomized.populationMean normalized * ∑ j, select j σ) := by
    intro σ
    have hsumNorm :
        (∑ j, select j σ * normalized (σ j)) =
          (∑ j, select j σ * processing (σ j)) / L := by
      dsimp [normalized]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hmeanNorm :
        Randomized.populationMean normalized =
          Randomized.populationMean processing / L := by
      unfold Randomized.populationMean
      simp only [Fintype.card_fin]
      dsimp [normalized]
      rw [Finset.sum_div]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      field_simp [hL.ne', hnR]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      field_simp [hL.ne', hnR]
    rw [hsumNorm, hmeanNorm]
    field_simp [hL.ne']
  have hevent :
      (fun σ =>
        L * (e + (r + 2 * D / K) * n) <
          |(∑ j, select j σ * processing (σ j)) -
            Randomized.populationMean processing * ∑ j, select j σ|) =
      (fun σ =>
        e + (r + 2 * D / K) * n <
          |(∑ j, select j σ * normalized (σ j)) -
            Randomized.populationMean normalized * ∑ j, select j σ|) := by
    funext σ
    apply propext
    rw [hscale σ, abs_mul, abs_of_pos hL]
    constructor <;> intro h <;> nlinarith
  have hindicator :
      (fun σ => if
        L * (e + (r + 2 * D / K) * n) <
          |(∑ j, select j σ * processing (σ j)) -
            Randomized.populationMean processing * ∑ j, select j σ|
        then (1 : ℝ) else 0) =
      (fun σ => if
        e + (r + 2 * D / K) * n <
          |(∑ j, select j σ * normalized (σ j)) -
            Randomized.populationMean normalized * ∑ j, select j σ|
        then (1 : ℝ) else 0) := by
    funext σ
    have hpq := congrFun hevent σ
    have hpqIff :
        (L * (e + (r + 2 * D / K) * n) <
          |(∑ j, select j σ * processing (σ j)) -
            Randomized.populationMean processing * ∑ j, select j σ|) ↔
        (e + (r + 2 * D / K) * n <
          |(∑ j, select j σ * normalized (σ j)) -
            Randomized.populationMean normalized * ∑ j, select j σ|) :=
      iff_of_eq hpq
    by_cases hleft :
        L * (e + (r + 2 * D / K) * n) <
          |(∑ j, select j σ * processing (σ j)) -
            Randomized.populationMean processing * ∑ j, select j σ|
    · have hright := hpqIff.mp hleft
      simp [hleft, hright]
    · have hright : ¬(e + (r + 2 * D / K) * n <
          |(∑ j, select j σ * normalized (σ j)) -
            Randomized.populationMean normalized * ∑ j, select j σ|) :=
        fun h => hleft (hpqIff.mpr h)
      simp [hleft, hright]
  unfold uniformProbability at hbound ⊢
  rw [hindicator]
  exact hbound

/-- Concrete regular-checkpoint processing-work bound. -/
theorem predictable_selected_work_regular_checkpoint_probability_le
    {n : ℕ} (hn : 1 < n)
    (processing : Fin n → ℝ)
    (select : Fin n → Equiv.Perm (Fin n) → ℝ)
    (cutoff : Fin n) {step : ℕ} (hstep : 0 < step)
    (hPredictable : PredictableSelector select)
    {L : ℝ} (hL : 0 < L)
    (hp0 : ∀ i, 0 ≤ processing i)
    (hpL : ∀ i, processing i ≤ L)
    (hselect0 : ∀ j σ, 0 ≤ select j σ)
    (hselect1 : ∀ j σ, select j σ ≤ 1)
    (hinactive : ∀ j ∉ positionsThrough cutoff, ∀ σ, select j σ = 0)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ =>
      L * (e + (r + 2 * step / (suffixPositions cutoff).card) * n) <
        |(∑ j, select j σ * processing (σ j)) -
          Randomized.populationMean processing * ∑ j, select j σ|) ≤
      n / e ^ 2 +
        ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
  let checkpoints := backwardCheckpoints step cutoff
  let K : ℝ := (suffixPositions cutoff).card
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (suffixPositions_nonempty cutoff).card_pos
  have hcheckpointCard : ∀ c ∈ checkpoints,
      K ≤ (suffixPositions c).card := by
    intro c hc
    have hcle := backwardCheckpoints_mem_le_cutoff
      (by simpa [checkpoints] using hc)
    dsimp [K]
    simp only [suffixPositions_card]
    exact_mod_cast (by omega : n - cutoff.val ≤ n - c.val)
  have hcover : ∀ j ∈ positionsThrough cutoff, ∃ c ∈ checkpoints,
      j.val ≤ c.val ∧
      ((suffixPositions j).card : ℝ) -
          (suffixPositions c).card ≤ step ∧
      K ≤ (suffixPositions c).card := by
    intro j hj
    obtain ⟨c, hc, hjc, hdist⟩ := backwardCheckpoints_cover hstep hj
    refine ⟨c, by simpa [checkpoints] using hc, hjc, ?_,
      hcheckpointCard c (by simpa [checkpoints] using hc)⟩
    simp only [suffixPositions_card]
    norm_num at *
    exact_mod_cast (by omega : c.val ≤ step + j.val)
  have hbase := predictable_selected_work_checkpoint_probability_le
    hn processing select (positionsThrough cutoff) checkpoints hPredictable
      hL hp0 hpL hselect0 hselect1 hinactive
      he hK hr (show (0 : ℝ) ≤ step by positivity)
      hcheckpointCard hcover
  have hcard : (checkpoints.card : ℝ) ≤
      ((cutoff.val / step + 1 : ℕ) : ℝ) := by
    exact_mod_cast backwardCheckpoints_card_le step cutoff
  have hfactor0 : 0 ≤ (2 / K) / r ^ 2 := by positivity
  have hrhs :
      checkpoints.card * ((2 / K) / r ^ 2) ≤
        ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / K) / r ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hfactor0
  have htotal :
      (n : ℝ) / e ^ 2 + checkpoints.card * ((2 / K) / r ^ 2) ≤
        n / e ^ 2 + ((cutoff.val / step + 1 : ℕ) : ℝ) *
          ((2 / K) / r ^ 2) :=
    add_le_add_right hrhs _
  simpa [K, checkpoints] using hbase.trans htotal

end

end RandomizedOptional
end SchedulingPaper
