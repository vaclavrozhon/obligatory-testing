import SchedulingPaper.BlindOptimizationRandomizedLower
import SchedulingPaper.RevealingOptimizationReduction
import Mathlib.Tactic

/-!
# Adaptive binary lower bound for revealing optimization

This is the finite Bellman core of the binary lower envelope.  A state has
`fresh` untouched jobs and `known` tested cap jobs.  A deterministic policy
may run a fresh job raw, process a known cap job, or test a fresh job and use
different continuations after observing zero or the cap.  Thus the tree
already permits every history-dependent choice relevant to the revealing
model.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace RandomizedLower

noncomputable section

/-- A finite completing adaptive decision tree. -/
inductive BinaryPolicy : ℕ → ℕ → Type
  | done : BinaryPolicy 0 0
  | raw {fresh known : ℕ} (next : BinaryPolicy fresh known) :
      BinaryPolicy (fresh + 1) known
  | process {fresh known : ℕ} (next : BinaryPolicy fresh known) :
      BinaryPolicy fresh (known + 1)
  | test {fresh known : ℕ}
      (zeroBranch : BinaryPolicy fresh known)
      (capBranch : BinaryPolicy fresh (known + 1)) :
      BinaryPolicy (fresh + 1) known

/-- Expected total completion cost under iid processing times: zero with
mass `1-x` and the public cap `u` with mass `x`. -/
def BinaryPolicy.expectedCost {fresh known : ℕ}
    (policy : BinaryPolicy fresh known) (rawDuration processDuration x : ℝ) : ℝ :=
  match policy with
  | .done => 0
  | .raw (fresh := a) (known := k) next =>
      rawDuration * (a + k + 1) +
        next.expectedCost rawDuration processDuration x
  | .process (fresh := a) (known := k) next =>
      processDuration * (a + k + 1) +
        next.expectedCost rawDuration processDuration x
  | .test (fresh := a) (known := k) zeroBranch capBranch =>
      (a + k + 1) +
        (1 - x) * zeroBranch.expectedCost rawDuration processDuration x +
        x * capBranch.expectedCost rawDuration processDuration x

/-- Cost potential of finishing every remaining job at the raw duration. -/
def rawPotential (remaining : ℕ) (u : ℝ) : ℝ :=
  u * remaining * (remaining + 1) / 2

/-- Exact expected cost of testing all fresh jobs, completing zeros at their
tests, and finally processing the known and newly discovered cap jobs. -/
def testAllPotential (fresh known : ℕ) (u x : ℝ) : ℝ :=
  let a : ℝ := fresh
  let k : ℝ := known
  a * (a + k) - (1 - x) * a * (a - 1) / 2 +
    u / 2 * ((k + a * x) ^ 2 + a * x * (1 - x) + k + a * x)

@[simp] theorem rawPotential_zero (u : ℝ) : rawPotential 0 u = 0 := by
  simp [rawPotential]

theorem rawPotential_succ (remaining : ℕ) (u : ℝ) :
    rawPotential (remaining + 1) u =
      u * (remaining + 1) + rawPotential remaining u := by
  unfold rawPotential
  push_cast
  ring

@[simp] theorem testAllPotential_zero_zero (u x : ℝ) :
    testAllPotential 0 0 u x = 0 := by
  simp [testAllPotential]

/-- Testing one fresh job is exactly the Bellman recurrence of the
test-everything potential. -/
theorem testAllPotential_test (fresh known : ℕ) (u x : ℝ) :
    testAllPotential (fresh + 1) known u x =
      (fresh + known + 1) +
        (1 - x) * testAllPotential fresh known u x +
        x * testAllPotential fresh (known + 1) u x := by
  unfold testAllPotential
  push_cast
  ring

/-- Slack of a raw action against the test-everything potential. -/
theorem testAllPotential_raw_slack (fresh known : ℕ) (u x : ℝ) :
    u * (fresh + known + 1) + testAllPotential fresh known u x -
        testAllPotential (fresh + 1) known u x =
      -(u * x - u + 1) *
        ((fresh : ℝ) * x + fresh + known + 1) := by
  unfold testAllPotential
  push_cast
  ring

/-- Slack of processing one known cap job against the test-everything
potential. -/
theorem testAllPotential_process_slack (fresh known : ℕ) (u x : ℝ) :
    u * (fresh + known + 1) + testAllPotential fresh known u x -
        testAllPotential fresh (known + 1) u x =
      -(fresh : ℝ) * (u * x - u + 1) := by
  unfold testAllPotential
  push_cast
  ring

/-- When zeros have mass at least `1/u`, no adaptive mixture of raw,
processing, and testing beats the test-everything policy. -/
theorem BinaryPolicy.testAllPotential_le_expectedCost
    {fresh known : ℕ} (policy : BinaryPolicy fresh known)
    {u x : ℝ} (_hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hdenseZero : u * x - u + 1 ≤ 0) :
    testAllPotential fresh known u x ≤ policy.expectedCost u u x := by
  induction policy with
  | done => simp [BinaryPolicy.expectedCost]
  | @raw fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      have hfactor : 0 ≤ (fresh : ℝ) * x + fresh + known + 1 := by
        positivity
      have hslack := testAllPotential_raw_slack fresh known u x
      have hnonneg :
          0 ≤ -(u * x - u + 1) *
            ((fresh : ℝ) * x + fresh + known + 1) :=
        mul_nonneg (neg_nonneg.mpr hdenseZero) hfactor
      linarith
  | @process fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      have hslack := testAllPotential_process_slack fresh known u x
      have hfresh0 : 0 ≤ (fresh : ℝ) := by positivity
      have hnonneg : 0 ≤ -(fresh : ℝ) * (u * x - u + 1) :=
        mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hfresh0) hdenseZero
      linarith
  | @test fresh known zeroBranch capBranch ihZero ihCap =>
      simp only [BinaryPolicy.expectedCost]
      rw [testAllPotential_test]
      have hz0 : 0 ≤ 1 - x := by linarith
      have hweighted := add_le_add
        (mul_le_mul_of_nonneg_left ihZero hz0)
        (mul_le_mul_of_nonneg_left ihCap hx0)
      linarith

/-- A test action's exact slack against the all-raw potential. -/
theorem rawPotential_test_slack (remaining : ℕ) (u x : ℝ) :
    (remaining + 1) +
        (1 - x) * rawPotential remaining u +
        x * rawPotential (remaining + 1) u -
        rawPotential (remaining + 1) u =
      (remaining + 1) * (u * x - u + 1) := by
  unfold rawPotential
  push_cast
  ring

/-- When zeros have mass at most `1/u`, every action has completion density
at most `1/u`; hence no adaptive policy beats running everything raw. -/
theorem BinaryPolicy.rawPotential_le_expectedCost
    {fresh known : ℕ} (policy : BinaryPolicy fresh known)
    {u x : ℝ} (_hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hsparseZero : 0 ≤ u * x - u + 1) :
    rawPotential (fresh + known) u ≤ policy.expectedCost u u x := by
  induction policy with
  | done => simp [BinaryPolicy.expectedCost]
  | @raw fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      rw [show fresh + 1 + known = (fresh + known) + 1 by omega,
        rawPotential_succ]
      norm_num at ih ⊢
      linarith
  | @process fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      rw [show fresh + (known + 1) = (fresh + known) + 1 by omega,
        rawPotential_succ]
      norm_num at ih ⊢
      linarith
  | @test fresh known zeroBranch capBranch ihZero ihCap =>
      simp only [BinaryPolicy.expectedCost]
      rw [show fresh + 1 + known = fresh + known + 1 by omega]
      have hz0 : 0 ≤ 1 - x := by linarith
      have hweighted :
          (1 - x) * rawPotential (fresh + known) u +
              x * rawPotential (fresh + known + 1) u ≤
            (1 - x) * zeroBranch.expectedCost u u x +
              x * capBranch.expectedCost u u x :=
        add_le_add
          (mul_le_mul_of_nonneg_left ihZero hz0)
          (mul_le_mul_of_nonneg_left (by
            simpa [Nat.add_assoc] using ihCap) hx0)
      have hslack := rawPotential_test_slack (fresh + known) u x
      have hnonneg :
          0 ≤ ((fresh : ℝ) + known + 1) * (u * x - u + 1) :=
        mul_nonneg (by positivity) hsparseZero
      have hbase :
          rawPotential (fresh + known + 1) u ≤
            (fresh + known + 1) +
              (1 - x) * rawPotential (fresh + known) u +
              x * rawPotential (fresh + known + 1) u := by
        norm_num at hslack
        linarith
      norm_num at hweighted ⊢
      linarith

/-- At the initial state, the test-everything potential has the exact
finite leading term and diagonal correction. -/
theorem testAllPotential_initial (n : ℕ) (u x : ℝ) :
    testAllPotential n 0 u x =
      (n : ℝ) ^ 2 / 2 * (1 + x + u * x ^ 2) +
        n / 2 * (1 - x - u * x ^ 2 + 2 * u * x) := by
  unfold testAllPotential
  push_cast
  ring

/-- Dropping the nonnegative finite diagonal from the exact initial
test-everything potential. -/
theorem testAllPotential_initial_ge_leading
    (n : ℕ) {u x : ℝ} (hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (n : ℝ) ^ 2 / 2 * (1 + x + u * x ^ 2) ≤
      testAllPotential n 0 u x := by
  rw [testAllPotential_initial]
  have htwo : 0 ≤ 2 - x := by linarith
  have hcorrection : 0 ≤ 1 - x - u * x ^ 2 + 2 * u * x := by
    have hproduct : 0 ≤ u * x * (2 - x) :=
      mul_nonneg (mul_nonneg hu0 hx0) htwo
    nlinarith
  have hn0 : 0 ≤ (n : ℝ) / 2 := by positivity
  nlinarith [mul_nonneg hn0 hcorrection]

/-- The two exact adaptive lower branches, assembled at the initial state. -/
theorem BinaryPolicy.expectedCost_ge_binaryEnvelope
    {n : ℕ} (policy : BinaryPolicy n 0)
    {u x : ℝ} (hu0 : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (if u * x - u + 1 ≤ 0 then testAllPotential n 0 u x
      else rawPotential n u) ≤ policy.expectedCost u u x := by
  by_cases hbranch : u * x - u + 1 ≤ 0
  · rw [if_pos hbranch]
    exact policy.testAllPotential_le_expectedCost hu0 hx0 hx1 hbranch
  · rw [if_neg hbranch]
    exact policy.rawPotential_le_expectedCost hu0 hx0 hx1
      (le_of_not_ge hbranch)

/-! ## The second binary family -/

/-- With cap-job processing time equal to the density threshold, the slack
of a raw action is exactly `(u-τ)` times the unfinished population. -/
theorem testAllPotential_threshold_raw_slack
    (fresh known : ℕ) {u τ : ℝ} (hτ0 : 0 < τ) :
    u * (fresh + known + 1) +
        testAllPotential fresh known τ (survivalMass τ) -
        testAllPotential (fresh + 1) known τ (survivalMass τ) =
      (u - τ) * (fresh + known + 1) := by
  unfold testAllPotential survivalMass
  push_cast
  field_simp [hτ0.ne']
  ring

/-- Processing a known threshold job has zero Bellman slack. -/
theorem testAllPotential_threshold_process
    (fresh known : ℕ) {τ : ℝ} (hτ0 : 0 < τ) :
    testAllPotential fresh (known + 1) τ (survivalMass τ) =
      τ * (fresh + known + 1) +
        testAllPotential fresh known τ (survivalMass τ) := by
  unfold testAllPotential survivalMass
  push_cast
  field_simp [hτ0.ne']
  ring

/-- If `1 ≤ τ ≤ u`, an adaptive revealing policy cannot beat the
test-everything threshold template on the binary law with cap-job processing
time `τ` and positive mass `(τ-1)/τ`.  This is the decision-tree lower bound
for the paper's `familyA`. -/
theorem BinaryPolicy.thresholdPotential_le_expectedCost
    {fresh known : ℕ} (policy : BinaryPolicy fresh known)
    {u τ : ℝ} (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    testAllPotential fresh known τ (survivalMass τ) ≤
      policy.expectedCost u τ (survivalMass τ) := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  induction policy with
  | done => simp [BinaryPolicy.expectedCost]
  | @raw fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      have hslack := testAllPotential_threshold_raw_slack
        fresh known hτ0 (u := u)
      have hnonneg :
          0 ≤ (u - τ) * ((fresh : ℝ) + known + 1) :=
        mul_nonneg (sub_nonneg.mpr hτu) (by positivity)
      norm_num at hslack
      linarith
  | @process fresh known next ih =>
      simp only [BinaryPolicy.expectedCost]
      rw [testAllPotential_threshold_process fresh known hτ0]
      linarith
  | @test fresh known zeroBranch capBranch ihZero ihCap =>
      simp only [BinaryPolicy.expectedCost]
      rw [testAllPotential_test]
      have hz0 : 0 ≤ 1 - survivalMass τ := by linarith
      have hweighted := add_le_add
        (mul_le_mul_of_nonneg_left ihZero hz0)
        (mul_le_mul_of_nonneg_left ihCap hx0)
      linarith

/-- Initial leading coefficient of the threshold family is exactly the
`familyA` numerator times its binary offline pair coefficient. -/
theorem testAllPotential_threshold_initial_leading
    (n : ℕ) {τ : ℝ} (hτ0 : 0 < τ) :
    (n : ℝ) ^ 2 / 2 *
        (familyA τ * (1 + τ * survivalMass τ ^ 2)) =
      (n : ℝ) ^ 2 / 2 *
        (1 + survivalMass τ + τ * survivalMass τ ^ 2) := by
  rw [← survivalFamilyA_eq hτ0]
  have hden : 0 < 1 + τ * survivalMass τ ^ 2 := by positivity
  field_simp [hden.ne']
  unfold survivalMass
  field_simp [hτ0.ne']
  ring

/-- Binary offline pair coefficient for the `familyB` law. -/
theorem familyB_mul_binaryOfflinePair
    {u τ : ℝ} (hu : 1 ≤ u) (hτ0 : 0 < τ) :
    familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2) =
      1 + survivalMass τ + u * survivalMass τ ^ 2 := by
  rw [← survivalFamilyB_eq (u := u) hτ0]
  have hden : 0 < 1 + (u - 1) * survivalMass τ ^ 2 := by
    positivity
  unfold survivalFamilyB
  rw [div_mul_cancel₀ _ hden.ne']
  unfold survivalMass
  field_simp [hτ0.ne']
  ring

/-- Exact finite decision-tree lower bound for one member of `familyB`. -/
theorem BinaryPolicy.familyB_le_expectedCost
    {n : ℕ} (policy : BinaryPolicy n 0)
    {u τ : ℝ} (hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    (n : ℝ) ^ 2 / 2 *
        (familyB u τ * (1 + (u - 1) * survivalMass τ ^ 2)) ≤
      policy.expectedCost u u (survivalMass τ) := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  have hbranch : u * survivalMass τ - u + 1 ≤ 0 := by
    unfold survivalMass
    have hid : u * ((τ - 1) / τ) - u + 1 = (τ - u) / τ := by
      field_simp [hτ0.ne']
      ring
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτu) hτ0.le
  have hpotential := policy.testAllPotential_le_expectedCost
    (by linarith : 0 ≤ u) hx0 hx1 hbranch
  have hleading := testAllPotential_initial_ge_leading n
    (by linarith : 0 ≤ u) hx0 hx1
  rw [familyB_mul_binaryOfflinePair hu.le hτ0]
  exact hleading.trans hpotential

/-- Exact finite decision-tree lower bound for one member of `familyA`. -/
theorem BinaryPolicy.familyA_le_expectedCost
    {n : ℕ} (policy : BinaryPolicy n 0)
    {u τ : ℝ} (_hu : 1 < u) (hτ : 1 ≤ τ) (hτu : τ ≤ u) :
    (n : ℝ) ^ 2 / 2 *
        (familyA τ * (1 + τ * survivalMass τ ^ 2)) ≤
      policy.expectedCost u τ (survivalMass τ) := by
  have hτ0 : 0 < τ := by linarith
  have hx0 : 0 ≤ survivalMass τ := by
    unfold survivalMass
    positivity
  have hx1 : survivalMass τ ≤ 1 := by
    unfold survivalMass
    rw [div_le_one hτ0]
    linarith
  have hpotential := policy.thresholdPotential_le_expectedCost hτ hτu
  have hleading := testAllPotential_initial_ge_leading n hτ0.le hx0 hx1
  rw [testAllPotential_threshold_initial_leading n hτ0]
  exact hleading.trans hpotential

/-- For every cap `u>1`, the scalar maximization supplies a concrete binary
law on which every fully adaptive revealing decision tree pays the exact
advertised leading ratio.  The two policy families allow the unfolded
operational strategy to depend on the revealed positive value, as it must. -/
theorem adaptive_binary_families_attain_curve
    {n : ℕ} {u : ℝ} (hu : 1 < u)
    (policyB policyA : ℝ → BinaryPolicy n 0) :
    (∃ τ ∈ Set.Icc (1 : ℝ) u,
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + (u - 1) * survivalMass τ ^ 2)) ≤
        (policyB τ).expectedCost u u (survivalMass τ)) ∨
    (∃ τ ∈ Set.Icc (1 : ℝ) (u - 1),
      (n : ℝ) ^ 2 / 2 *
          (randomizedCurve u *
            (1 + τ * survivalMass τ ^ 2)) ≤
        (policyA τ).expectedCost u τ (survivalMass τ)) := by
  rcases binaryFamilies_attain_curve hu with hB | hA
  · rcases hB with ⟨τ, hτ, hattain⟩
    left
    refine ⟨τ, hτ, ?_⟩
    rw [← hattain]
    exact (policyB τ).familyB_le_expectedCost hu hτ.1 hτ.2
  · rcases hA with ⟨τ, hτ, hattain⟩
    right
    refine ⟨τ, hτ, ?_⟩
    rw [← hattain]
    exact (policyA τ).familyA_le_expectedCost hu hτ.1
      (hτ.2.trans (by linarith))

end

end RandomizedLower
end RevealingOptimization
end SchedulingPaper
