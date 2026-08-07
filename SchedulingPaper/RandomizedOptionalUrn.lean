import SchedulingPaper.RandomizedOptionalKernel
import SchedulingPaper.RandomizedHistogramConcentration
import Mathlib.Tactic

/-!
# Optional testing: deterministic predictable-urn bookkeeping

This file isolates the pathwise algebra in the predictable sampling lemma.
The genuinely probabilistic input is a maximal bound for the centered
predictable increments.  Once that bound and an ordinary touch-prefix
discrepancy are available, the lemmas below transfer them to the adaptively
selected test and blind subsequences.
-/

namespace SchedulingPaper
namespace RandomizedOptional

noncomputable section

/-- Finite union bound for the project's explicit uniform-probability
semantics.  Applied to all touch-prefix lengths after a terminal Azuma bound,
this gives the simultaneous event required by the optional proof. -/
theorem uniformProbability_exists_le_sum
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (P : ι → Ω → Prop) [∀ i, DecidablePred (P i)] :
    Randomized.uniformProbability (fun ω => ∃ i, P i ω) ≤
      ∑ i, Randomized.uniformProbability (P i) := by
  classical
  calc
    Randomized.uniformProbability (fun ω => ∃ i, P i ω) ≤
        Randomized.uniformAverage (fun ω =>
          ∑ i, if P i ω then (1 : ℝ) else 0) := by
      apply Randomized.uniformAverage_mono
      intro ω
      by_cases h : ∃ i, P i ω
      · simp only [if_pos h]
        obtain ⟨i, hi⟩ := h
        have hone : (1 : ℝ) ≤ ∑ j, if P j ω then 1 else 0 := by
          calc
            (1 : ℝ) = (if P i ω then 1 else 0) := by simp [hi]
            _ ≤ ∑ j, if P j ω then 1 else 0 :=
              Finset.single_le_sum
                (f := fun j => if P j ω then (1 : ℝ) else 0)
                (fun j _hj => by positivity) (Finset.mem_univ i)
        exact hone
      · simp [h]
    _ = ∑ i, Randomized.uniformProbability (P i) := by
      rw [Randomized.uniformAverage_fintype_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl

/-- If every one of `K` prefix events has probability at most `r`, their
simultaneous failure probability is at most `K*r`. -/
theorem uniformProbability_exists_le_card_mul
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (P : ι → Ω → Prop) [∀ i, DecidablePred (P i)]
    {r : ℝ} (hP : ∀ i, Randomized.uniformProbability (P i) ≤ r) :
    Randomized.uniformProbability (fun ω => ∃ i, P i ω) ≤
      Fintype.card ι * r := by
  calc
    Randomized.uniformProbability (fun ω => ∃ i, P i ω) ≤
        ∑ i, Randomized.uniformProbability (P i) :=
      uniformProbability_exists_le_sum P
    _ ≤ ∑ _i : ι, r := Finset.sum_le_sum fun i _ => hP i
    _ = Fintype.card ι * r := by simp

theorem uniformProbability_mono
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ ω, P ω → Q ω) :
    Randomized.uniformProbability P ≤ Randomized.uniformProbability Q := by
  apply Randomized.uniformAverage_mono
  intro ω
  by_cases hP : P ω
  · simp [hP, hPQ ω hP]
  · by_cases hQ : Q ω <;> simp [hP, hQ]

theorem uniformProbability_or_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q] :
    Randomized.uniformProbability (fun ω => P ω ∨ Q ω) ≤
      Randomized.uniformProbability P + Randomized.uniformProbability Q := by
  unfold Randomized.uniformProbability
  rw [← Randomized.uniformAverage_add]
  apply Randomized.uniformAverage_mono
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

/-- `L²` identity for a finite family of pairwise orthogonal centered
increments.  This is the algebraic core of the fixed-prefix martingale
variance estimate. -/
theorem uniformAverage_sum_sq_le_of_orthogonal
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (Y : ι → Ω → ℝ) {v : ℝ}
    (hdiag : ∀ i,
      Randomized.uniformAverage (fun ω => (Y i ω) ^ 2) ≤ v)
    (hoff : ∀ i j, i ≠ j →
      Randomized.uniformAverage (fun ω => Y i ω * Y j ω) = 0) :
    Randomized.uniformAverage (fun ω => (∑ i, Y i ω) ^ 2) ≤
      Fintype.card ι * v := by
  have hrow : ∀ i,
      (∑ j, Randomized.uniformAverage (fun ω => Y i ω * Y j ω)) =
        Randomized.uniformAverage (fun ω => (Y i ω) ^ 2) := by
    intro i
    rw [Fintype.sum_eq_single i]
    · congr 1
      funext ω
      ring
    · intro j hji
      exact hoff i j (Ne.symm hji)
  calc
    Randomized.uniformAverage (fun ω => (∑ i, Y i ω) ^ 2) =
        ∑ i, ∑ j,
          Randomized.uniformAverage (fun ω => Y i ω * Y j ω) := by
      rw [show (fun ω => (∑ i, Y i ω) ^ 2) =
          (fun ω => ∑ i, ∑ j, Y i ω * Y j ω) by
        funext ω
        rw [pow_two, Fintype.sum_mul_sum]]
      rw [Randomized.uniformAverage_fintype_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Randomized.uniformAverage_fintype_sum]
    _ = ∑ i, Randomized.uniformAverage (fun ω => (Y i ω) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hrow i
    _ ≤ ∑ _i : ι, v := Finset.sum_le_sum fun i _ => hdiag i
    _ = Fintype.card ι * v := by simp

/-- Finite Chebyshev inequality specialized to a square-moment estimate. -/
theorem uniformProbability_abs_gt_le_secondMoment
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {e V : ℝ} (he : 0 < e)
    (hsecond : Randomized.uniformAverage (fun ω => (X ω) ^ 2) ≤ V) :
    Randomized.uniformProbability (fun ω => e < |X ω|) ≤ V / e ^ 2 := by
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  calc
    Randomized.uniformProbability (fun ω => e < |X ω|) ≤
        Randomized.uniformProbability (fun ω => e ^ 2 < (X ω) ^ 2) := by
      apply uniformProbability_mono
      intro ω hω
      nlinarith [sq_abs (X ω)]
    _ ≤ Randomized.uniformAverage (fun ω => (X ω) ^ 2) / e ^ 2 := by
      exact Randomized.uniformProbability_lt_le_average_div
        (fun ω => (X ω) ^ 2) (fun ω => sq_nonneg (X ω)) he2
    _ ≤ V / e ^ 2 := div_le_div_of_nonneg_right hsecond he2.le

/-- Fixed-prefix Chebyshev bound for pairwise orthogonal predictable
increments.  A dyadic/checkpoint union can turn this into a simultaneous
prefix event with a slower but still vanishing grid rate. -/
theorem uniformProbability_sum_abs_gt_le_of_orthogonal
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (Y : ι → Ω → ℝ) {e v : ℝ} (he : 0 < e)
    (hdiag : ∀ i,
      Randomized.uniformAverage (fun ω => (Y i ω) ^ 2) ≤ v)
    (hoff : ∀ i j, i ≠ j →
      Randomized.uniformAverage (fun ω => Y i ω * Y j ω) = 0) :
    Randomized.uniformProbability (fun ω => e < |∑ i, Y i ω|) ≤
      (Fintype.card ι * v) / e ^ 2 := by
  exact uniformProbability_abs_gt_le_secondMoment _ he
    (uniformAverage_sum_sq_le_of_orthogonal Y hdiag hoff)

/-- A prefix count error controls the empirical fraction in the remaining
urn.  This is the exact scalar calculation behind display (20b). -/
theorem remainingFraction_sub_population_abs_le
    {N k total prefixCount D e δ : ℝ}
    (hNk : 0 < N - k) (hδN : δ * N ≤ N - k)
    (hδN0 : 0 < δ * N)
    (htotal : total = N * D)
    (hprefix : |prefixCount - k * D| ≤ e)
    (he : 0 ≤ e) :
    |(total - prefixCount) / (N - k) - D| ≤ e / (δ * N) := by
  have hid :
      (total - prefixCount) / (N - k) - D =
        -(prefixCount - k * D) / (N - k) := by
    rw [htotal]
    field_simp [ne_of_gt hNk]
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hNk]
  have hdenom : 0 ≤ e / (N - k) := div_nonneg he hNk.le
  calc
    |prefixCount - k * D| / (N - k) ≤ e / (N - k) :=
      div_le_div_of_nonneg_right hprefix hNk.le
    _ ≤ e / (δ * N) := by
      exact div_le_div_of_nonneg_left he hδN0 hδN

/-- Algebraic decomposition of a predictably selected centered sum into
martingale increments around the current urn mean and the drift of that urn
mean from the original population mean. -/
theorem predictable_selection_decomposition
    {ι : Type*} [Fintype ι]
    (select value remainingMean : ι → ℝ) (populationMean : ℝ) :
    (∑ i, select i * value i) -
        populationMean * (∑ i, select i) =
      (∑ i, select i * (value i - remainingMean i)) +
        ∑ i, select i * (remainingMean i - populationMean) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The drift term in the predictable decomposition is at most total
selected mass times a uniform remaining-urn error. -/
theorem predictable_selection_drift_abs_le
    {ι : Type*} [Fintype ι]
    {select remainingMean : ι → ℝ} {populationMean r : ℝ}
    (hselect0 : ∀ i, 0 ≤ select i)
    (hremaining : ∀ i, |remainingMean i - populationMean| ≤ r) :
    |∑ i, select i * (remainingMean i - populationMean)| ≤
      r * ∑ i, select i := by
  calc
    |∑ i, select i * (remainingMean i - populationMean)| ≤
        ∑ i, |select i * (remainingMean i - populationMean)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, select i * |remainingMean i - populationMean| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, abs_of_nonneg (hselect0 i)]
    _ ≤ ∑ i, select i * r := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hremaining i) (hselect0 i)
    _ = r * ∑ i, select i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Deterministic transfer from a maximal centered-increment estimate to the
adaptively selected test-count discrepancy.  In the application `select` is
the predictable `0/1` test indicator. -/
theorem predictable_selection_discrepancy_abs_le
    {ι : Type*} [Fintype ι]
    {select value remainingMean : ι → ℝ}
    {populationMean martingaleError driftError : ℝ}
    (hselect0 : ∀ i, 0 ≤ select i)
    (hmartingale :
      |∑ i, select i * (value i - remainingMean i)| ≤ martingaleError)
    (hremaining :
      ∀ i, |remainingMean i - populationMean| ≤ driftError) :
    |(∑ i, select i * value i) -
        populationMean * (∑ i, select i)| ≤
      martingaleError + driftError * ∑ i, select i := by
  rw [predictable_selection_decomposition]
  calc
    |(∑ i, select i * (value i - remainingMean i)) +
        ∑ i, select i * (remainingMean i - populationMean)| ≤
        |∑ i, select i * (value i - remainingMean i)| +
          |∑ i, select i * (remainingMean i - populationMean)| :=
      abs_add_le _ _
    _ ≤ martingaleError + driftError * ∑ i, select i :=
      add_le_add hmartingale
        (predictable_selection_drift_abs_le hselect0 hremaining)

/-- The same pathwise transfer for the blind subsequence, whose predictable
selector is the complement of the test indicator. -/
theorem predictable_blind_discrepancy_abs_le
    {ι : Type*} [Fintype ι]
    {test value remainingMean : ι → ℝ}
    {populationMean martingaleError driftError : ℝ}
    (htest1 : ∀ i, test i ≤ 1)
    (hmartingale :
      |∑ i, (1 - test i) * (value i - remainingMean i)| ≤
        martingaleError)
    (hremaining :
      ∀ i, |remainingMean i - populationMean| ≤ driftError) :
    |(∑ i, (1 - test i) * value i) -
        populationMean * (∑ i, (1 - test i))| ≤
      martingaleError + driftError * ∑ i, (1 - test i) := by
  exact predictable_selection_discrepancy_abs_le
    (fun i => sub_nonneg.mpr (htest1 i)) hmartingale hremaining

end

end RandomizedOptional
end SchedulingPaper
