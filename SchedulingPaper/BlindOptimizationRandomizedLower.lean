import SchedulingPaper.BlindOptimizationAlgebra
import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Adaptive binary lower bound for randomized blind optimization

This is the decision-tree core of the announced-policy/Yao lower bound.
At every fresh job an adaptive deterministic policy may choose a raw block,
or an optimized block and branch after seeing whether the hidden binary
processing time is zero or `u`.  Independence makes the next fresh bit have
the same mass `b` after every observed history.  The checked induction shows
that branching cannot beat the cheaper expected block length.
-/

namespace SchedulingPaper
namespace BlindOptimization
namespace RandomizedLower

noncomputable section

abbrev BinaryInput (n : ℕ) := Fin n → Bool

/-- Exact finite iid Bernoulli law used by the Yao lower bound.  Real atom
weights let us use the curve-maximizing mass without a rational
approximation. -/
def bernoulliWeight (n : ℕ) (b : ℝ) (input : BinaryInput n) : ℝ :=
  ∏ job, if input job then b else 1 - b

theorem bernoulliWeight_nonneg {n : ℕ} {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (input : BinaryInput n) :
    0 ≤ bernoulliWeight n b input := by
  unfold bernoulliWeight
  apply Finset.prod_nonneg
  intro job hjob
  split <;> linarith

theorem bernoulliWeight_mass (n : ℕ) (b : ℝ) :
    ∑ input : BinaryInput n, bernoulliWeight n b input = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.piFinset_univ]
  have hfactor :
      (∑ input ∈ Fintype.piFinset
          (fun _job : Fin n => (Finset.univ : Finset Bool)),
        ∏ job, if input job then b else 1 - b) =
      ∏ job : Fin n, ∑ bit : Bool, if bit then b else 1 - b := by
    symm
    simpa using Finset.prod_univ_sum
      (fun _job : Fin n => (Finset.univ : Finset Bool))
      (fun _job bit => if bit then b else 1 - b)
  rw [hfactor]
  simp

/-- Weighted finite Yao selection specialized to the exact iid binary input
law. -/
theorem bernoulli_yao_select_fixed_input
    {n : ℕ} {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {Seeds : Type*} [Fintype Seeds] [Nonempty Seeds]
    (cost : BinaryInput n → Seeds → ℝ) {L : ℝ}
    (hjoint : L ≤ Randomized.finiteExpectation (bernoulliWeight n b)
      (fun input => Randomized.uniformAverage fun seed => cost input seed)) :
    ∃ input, L ≤ Randomized.uniformAverage fun seed => cost input seed := by
  exact Randomized.finite_yao_select_weighted
    (bernoulliWeight n b) cost
    (bernoulliWeight_nonneg hb0 hb1) (bernoulliWeight_mass n b) hjoint

/-- A deterministic adaptive policy with exactly `remaining` unfinished
jobs.  Both optimized outcomes complete the selected job and may lead to
different continuation trees. -/
inductive BinaryPolicy : ℕ → Type
  | done : BinaryPolicy 0
  | raw {remaining : ℕ} (next : BinaryPolicy remaining) :
      BinaryPolicy (remaining + 1)
  | optimized {remaining : ℕ}
      (zeroBranch longBranch : BinaryPolicy remaining) :
      BinaryPolicy (remaining + 1)

/-- Expected completion area under independent binary processing times:
`p=0` with mass `1-b`, and `p=u` with mass `b`. -/
def BinaryPolicy.expectedCost {remaining : ℕ}
    (policy : BinaryPolicy remaining) (u b : ℝ) : ℝ :=
  match policy with
  | .done => 0
  | .raw (remaining := r) next =>
      u * (r + 1) + next.expectedCost u b
  | .optimized (remaining := r) zeroBranch longBranch =>
      (1 - b) * ((r + 1 : ℕ) + zeroBranch.expectedCost u b) +
        b * ((1 + u) * (r + 1) + longBranch.expectedCost u b)

def triangularCount (n : ℕ) : ℝ := (n : ℝ) * (n + 1) / 2

@[simp] theorem triangularCount_zero : triangularCount 0 = 0 := by
  simp [triangularCount]

theorem triangularCount_succ (n : ℕ) :
    triangularCount (n + 1) = (n + 1 : ℕ) + triangularCount n := by
  unfold triangularCount
  push_cast
  ring

/-- No deterministic adaptive binary policy beats the cheaper of a raw
block and an optimized block in expectation.  This theorem already permits
different continuation policies after the two optimized outcomes. -/
theorem BinaryPolicy.expectedCost_lower
    {remaining : ℕ} (policy : BinaryPolicy remaining)
    {u b : ℝ} (hu0 : 0 ≤ u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    triangularCount remaining * min u (1 + b * u) ≤
      policy.expectedCost u b := by
  induction policy with
  | done => simp [BinaryPolicy.expectedCost]
  | @raw remaining next ih =>
      rw [triangularCount_succ]
      simp only [BinaryPolicy.expectedCost]
      have hblock : min u (1 + b * u) ≤ u := min_le_left _ _
      have hblock0 : 0 ≤ min u (1 + b * u) := by
        exact le_min hu0 (by positivity)
      have hstep := mul_le_mul_of_nonneg_left hblock
        (show (0 : ℝ) ≤ remaining + 1 by positivity)
      calc
        ((remaining + 1 : ℕ) + triangularCount remaining) *
            min u (1 + b * u) =
            (remaining + 1 : ℝ) * min u (1 + b * u) +
              triangularCount remaining * min u (1 + b * u) := by
                push_cast
                ring
        _ ≤ (remaining + 1 : ℝ) * u + next.expectedCost u b :=
          add_le_add hstep ih
        _ = u * (remaining + 1 : ℝ) + next.expectedCost u b := by ring
  | @optimized remaining zeroBranch longBranch ihZero ihLong =>
      rw [triangularCount_succ]
      simp only [BinaryPolicy.expectedCost]
      have hcast : ((remaining + 1 : ℕ) : ℝ) =
          (remaining : ℝ) + 1 := by norm_num
      rw [hcast]
      have hzeroWeight : 0 ≤ 1 - b := by linarith
      have hweightedZero := mul_le_mul_of_nonneg_left ihZero hzeroWeight
      have hweightedLong := mul_le_mul_of_nonneg_left ihLong hb0
      have hcontinuation :
          triangularCount remaining * min u (1 + b * u) ≤
            (1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b := by
        calc
          triangularCount remaining * min u (1 + b * u) =
              (1 - b) *
                  (triangularCount remaining * min u (1 + b * u)) +
                b * (triangularCount remaining * min u (1 + b * u)) := by ring
          _ ≤ (1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b :=
            add_le_add hweightedZero hweightedLong
      have hblock : min u (1 + b * u) ≤ 1 + b * u := min_le_right _ _
      have hstep := mul_le_mul_of_nonneg_left hblock
        (show (0 : ℝ) ≤ remaining + 1 by positivity)
      calc
        ((remaining : ℝ) + 1 + triangularCount remaining) *
            min u (1 + b * u) =
            (remaining + 1 : ℝ) * min u (1 + b * u) +
              triangularCount remaining * min u (1 + b * u) := by
                push_cast
                ring
        _ ≤ (remaining + 1 : ℝ) * (1 + b * u) +
            ((1 - b) * zeroBranch.expectedCost u b +
              b * longBranch.expectedCost u b) :=
          add_le_add hstep hcontinuation
        _ = (1 - b) *
              ((remaining : ℝ) + 1 + zeroBranch.expectedCost u b) +
            b * ((1 + u) * ((remaining : ℝ) + 1) +
              longBranch.expectedCost u b) := by
                ring

/-- Expected exact clairvoyant finite cost for independent binary effective
lengths `1` and `u`.  The first term is the ordered-pair leading coefficient;
the second is the exact diagonal correction. -/
def binaryExpectedOfflineCost (n : ℕ) (u b : ℝ) : ℝ :=
  (n : ℝ) ^ 2 / 2 * (1 + (u - 1) * b ^ 2) +
    n / 2 *
      (2 * (1 + (u - 1) * b) - (1 + (u - 1) * b ^ 2))

theorem randomizedBinaryEnvelope_mul_denominator
    {u b : ℝ} (hu : 1 < u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    randomizedBinaryEnvelope u b * (1 + (u - 1) * b ^ 2) =
      min u (1 + b * u) := by
  have hden : 0 < 1 + (u - 1) * b ^ 2 := by
    have : 0 ≤ (u - 1) * b ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg b)
    linarith
  unfold randomizedBinaryEnvelope
  rw [div_mul_cancel₀ _ hden.ne']
  congr 2 <;> ring

/-- The finite expected online/offline comparison before the final Yao
selection.  It is uniform over every adaptive decision tree. -/
theorem BinaryPolicy.expectedCost_ge_binary_leading
    {n : ℕ} (policy : BinaryPolicy n)
    {u b : ℝ} (hu : 1 < u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (n : ℝ) * (n + 1) / 2 * min u (1 + b * u) ≤
      policy.expectedCost u b := by
  simpa [triangularCount] using
    policy.expectedCost_lower (by linarith) hb0 hb1

/-- Selecting a maximizing binary mass turns the adaptive lower bound into
the exact advertised curve at the leading `n²` scale. -/
theorem exists_binary_mass_adaptive_curve_lower
    {n : ℕ} (policy : BinaryPolicy n) {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      (n : ℝ) * (n + 1) / 2 *
          (randomizedCurve u * (1 + (u - 1) * b ^ 2)) ≤
        policy.expectedCost u b := by
  obtain ⟨b, hb, hattain⟩ := randomizedBinaryEnvelope_attains_curve hu
  refine ⟨b, hb, ?_⟩
  have hlower := policy.expectedCost_ge_binary_leading hu hb.1 hb.2
  rw [← randomizedBinaryEnvelope_mul_denominator hu hb.1 hb.2,
    hattain] at hlower
  exact hlower

def binaryFiniteYaoRatio (n : ℕ) (u b : ℝ) : ℝ :=
  (triangularCount n * min u (1 + b * u)) /
    binaryExpectedOfflineCost n u b

/-- The exact finite diagonal correction vanishes, so the binary Yao ratio
converges to the binary envelope. -/
theorem binaryFiniteYaoRatio_tendsto_envelope
    {u b : ℝ} (hu : 1 < u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Filter.Tendsto (fun n : ℕ ↦ binaryFiniteYaoRatio n u b)
      Filter.atTop (nhds (randomizedBinaryEnvelope u b)) := by
  let block := min u (1 + b * u)
  let pair := 1 + (u - 1) * b ^ 2
  let correction :=
    2 * (1 + (u - 1) * b) - (1 + (u - 1) * b ^ 2)
  have hpair : 0 < pair := by
    dsimp [pair]
    have : 0 ≤ (u - 1) * b ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / n)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop : Filter.Tendsto
        (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop) 1
  have hnumerator : Filter.Tendsto
      (fun n : ℕ ↦ ((1 + (1 : ℝ) / n) / 2) * block)
      Filter.atTop (nhds ((1 / 2 : ℝ) * block)) := by
    have hone := (tendsto_const_nhds : Filter.Tendsto
      (fun _n : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1)).add hinv
    simpa using (hone.div_const 2).mul_const block
  have hdenominator : Filter.Tendsto
      (fun n : ℕ ↦ pair / 2 + ((1 : ℝ) / n) * correction / 2)
      Filter.atTop (nhds (pair / 2)) := by
    have hdiag : Filter.Tendsto
        (fun n : ℕ ↦ ((1 : ℝ) / n) * correction / 2)
        Filter.atTop (nhds 0) := by
      simpa using (hinv.mul_const correction).div_const 2
    simpa using (tendsto_const_nhds.add hdiag : Filter.Tendsto
      (fun n : ℕ ↦ pair / 2 + ((1 : ℝ) / n) * correction / 2)
      Filter.atTop (nhds (pair / 2 + 0)))
  have hnormalized : Filter.Tendsto
      (fun n : ℕ ↦
        (((1 + (1 : ℝ) / n) / 2) * block) /
          (pair / 2 + ((1 : ℝ) / n) * correction / 2))
      Filter.atTop (nhds (block / pair)) := by
    convert hnumerator.div hdenominator (by positivity : pair / 2 ≠ 0) using 1 <;>
      field_simp [hpair.ne'] <;> ring
  have heq : (fun n : ℕ ↦ binaryFiniteYaoRatio n u b) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦
        (((1 + (1 : ℝ) / n) / 2) * block) /
          (pair / 2 + ((1 : ℝ) / n) * correction / 2)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    unfold binaryFiniteYaoRatio triangularCount binaryExpectedOfflineCost
    dsimp [block, pair, correction]
    field_simp [hnR]
  have hlimit := hnormalized.congr' heq.symm
  have henvelope : block / pair = randomizedBinaryEnvelope u b := by
    dsimp [block, pair]
    unfold randomizedBinaryEnvelope
    ring_nf
  rwa [henvelope] at hlimit

/-- At a maximizing binary mass, the exact finite Yao coefficients converge
to the advertised randomized curve. -/
theorem exists_binary_mass_finite_ratio_tendsto_curve
    {u : ℝ} (hu : 1 < u) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ ↦ binaryFiniteYaoRatio n u b)
        Filter.atTop (nhds (randomizedCurve u)) := by
  obtain ⟨b, hb, hattain⟩ := randomizedBinaryEnvelope_attains_curve hu
  refine ⟨b, hb, ?_⟩
  simpa [hattain] using
    (binaryFiniteYaoRatio_tendsto_envelope hu hb.1 hb.2)

end

end RandomizedLower
end BlindOptimization
end SchedulingPaper
