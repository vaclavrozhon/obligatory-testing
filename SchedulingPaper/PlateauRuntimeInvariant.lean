import SchedulingPaper.PlateauBank
import SchedulingPaper.ParameterizedAdaptiveStrategy
import SchedulingPaper.StrategyTermination

/-!
# Runtime counter invariants on the finite plateau

This file records the part of the finite-plateau transcript bridge that is
independent of pair accounting.  The executable parameterized strategy
reconstructs its state by folding the public test results.  We prove directly
that this fold has the expected test count, preserves nonnegativity and
`deferred ≤ positive`, and consequently always uses a threshold strictly
below the optional cap boundary when `u > zStar`.

In particular, a revealed value in `[u-1,u]` can never be selected for
immediate processing.  Thus every such runtime outcome belongs to the fifth
(`cap`) endpoint class used by the plateau bank.
-/

namespace SchedulingPaper.Online

noncomputable section

open SchedulingPaper

private theorem foldParameterized_tested
    (n : ℕ) (c : ℝ)
    (results : List (Label n × ℝ))
    (state : ParameterizedThresholdCounters) :
    (results.foldl
      (fun s result => s.observe n c result.2) state).tested =
        state.tested + results.length := by
  induction results generalizing state with
  | nil =>
      simp
  | cons result results ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [ParameterizedThresholdCounters.observe]
      omega

private theorem foldParameterized_positive_nonneg
    (n : ℕ) (c : ℝ)
    (results : List (Label n × ℝ))
    (state : ParameterizedThresholdCounters)
    (hpositive : 0 ≤ state.positive) :
    0 ≤
      (results.foldl
        (fun s result => s.observe n c result.2) state).positive := by
  induction results generalizing state with
  | nil =>
      simpa using hpositive
  | cons result results ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold ParameterizedThresholdCounters.observe
      dsimp only
      split_ifs <;> linarith

private theorem foldParameterized_deferred_nonneg
    (n : ℕ) (c : ℝ)
    (results : List (Label n × ℝ))
    (state : ParameterizedThresholdCounters)
    (hdeferred : 0 ≤ state.deferred) :
    0 ≤
      (results.foldl
        (fun s result => s.observe n c result.2) state).deferred := by
  induction results generalizing state with
  | nil =>
      simpa using hdeferred
  | cons result results ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold ParameterizedThresholdCounters.observe
      dsimp only
      split_ifs <;> linarith

private theorem foldParameterized_balance
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (results : List (Label n × ℝ))
    (state : ParameterizedThresholdCounters)
    (hlength : state.tested + results.length ≤ n)
    (hpositive : 0 ≤ state.positive)
    (hbalance : state.deferred ≤ state.positive) :
    let final :=
      results.foldl
        (fun s result => s.observe n c result.2) state
    final.deferred ≤ final.positive := by
  induction results generalizing state with
  | nil =>
      simpa using hbalance
  | cons result results ih =>
      simp only [List.length_cons] at hlength
      have htested : state.tested < n := by omega
      have hnextPositive :
          0 ≤ (state.observe n c result.2).positive := by
        unfold ParameterizedThresholdCounters.observe
        dsimp only
        split_ifs <;> linarith
      have hnextBalance :
          (state.observe n c result.2).deferred ≤
            (state.observe n c result.2).positive :=
        state.observe_deferred_le_positive hc htested
          hpositive hbalance
      have hnextLength :
          (state.observe n c result.2).tested + results.length ≤ n := by
        simp only [ParameterizedThresholdCounters.observe]
        omega
      simpa only [List.foldl_cons] using
        ih (state.observe n c result.2) hnextLength
          hnextPositive hnextBalance

@[simp] theorem parameterizedCountersFromResults_tested
    (n : ℕ) (c : ℝ) (results : List (Label n × ℝ)) :
    (parameterizedCountersFromResults n c results).tested =
      results.length := by
  unfold parameterizedCountersFromResults
  rw [foldParameterized_tested]
  simp [ParameterizedThresholdCounters.initial]

theorem parameterizedCountersFromResults_positive_nonneg
    (n : ℕ) (c : ℝ) (results : List (Label n × ℝ)) :
    0 ≤ (parameterizedCountersFromResults n c results).positive := by
  unfold parameterizedCountersFromResults
  exact foldParameterized_positive_nonneg n c results
    ParameterizedThresholdCounters.initial (by simp
      [ParameterizedThresholdCounters.initial])

theorem parameterizedCountersFromResults_deferred_nonneg
    (n : ℕ) (c : ℝ) (results : List (Label n × ℝ)) :
    0 ≤ (parameterizedCountersFromResults n c results).deferred := by
  unfold parameterizedCountersFromResults
  exact foldParameterized_deferred_nonneg n c results
    ParameterizedThresholdCounters.initial (by simp
      [ParameterizedThresholdCounters.initial])

theorem parameterizedCountersFromResults_balance
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (results : List (Label n × ℝ))
    (hlength : results.length ≤ n) :
    (parameterizedCountersFromResults n c results).deferred ≤
      (parameterizedCountersFromResults n c results).positive := by
  unfold parameterizedCountersFromResults
  apply foldParameterized_balance n hc results
    ParameterizedThresholdCounters.initial
  · simpa [ParameterizedThresholdCounters.initial] using hlength
  · simp [ParameterizedThresholdCounters.initial]
  · simp [ParameterizedThresholdCounters.initial]

/-- The normalized state reconstructed from any legal proper test prefix is
nonpositive. -/
theorem parameterizedCountersFromResults_y_nonpos
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (results : List (Label n × ℝ))
    (hlength : results.length < n) :
    (parameterizedCountersFromResults n c results).y n c ≤ 0 := by
  let state := parameterizedCountersFromResults n c results
  have htested : state.tested = results.length := by
    simp [state, parameterizedCountersFromResults_tested]
  have hremaining : 0 < (state.remaining n : ℝ) := by
    simp [ParameterizedThresholdCounters.remaining, htested, hlength]
  have hpositive : 0 ≤ state.positive := by
    simpa [state] using
      parameterizedCountersFromResults_positive_nonneg n c results
  have hbalance : state.deferred ≤ state.positive := by
    simpa [state] using
      parameterizedCountersFromResults_balance n hc results hlength.le
  have hscale : state.positive ≤ (1 + c) * state.positive := by
    nlinarith [mul_nonneg hc.le hpositive]
  unfold ParameterizedThresholdCounters.y
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hremaining.le

/-- Every threshold reconstructed from a proper test prefix at `rhoStar` is
at most its initial value `1 / rhoStar`. -/
theorem plateauCounters_threshold_le_inv
    (n : ℕ) (results : List (Label n × ℝ))
    (hlength : results.length < n) :
    (parameterizedCountersFromResults n rhoStar results).threshold
        n rhoStar ≤ 1 / rhoStar := by
  exact parameterizedAdaptiveThreshold_rhoStar_le_inv
    (parameterizedCountersFromResults_y_nonpos
      n rhoStar_pos results hlength)

/-- On the strict plateau, the optional cap breakpoint lies strictly above
every live threshold of the executable strategy. -/
theorem plateauCounters_threshold_lt_capBoundary
    {u : ℝ} (hu : zStar < u)
    (n : ℕ) (results : List (Label n × ℝ))
    (hlength : results.length < n) :
    (parameterizedCountersFromResults n rhoStar results).threshold
        n rhoStar < u - 1 := by
  have hthreshold :=
    plateauCounters_threshold_le_inv n results hlength
  have hinv :
      1 / rhoStar < 2 / rhoStar := by
    exact (div_lt_div_iff_of_pos_right rhoStar_pos).2 one_lt_two
  rw [two_div_rhoStar] at hinv
  linarith

/-- A value in the capped interval cannot satisfy the runtime immediate
test at any proper prefix. -/
theorem plateauCounters_capped_not_immediate
    {u p : ℝ} (hu : zStar < u) (hp : u - 1 ≤ p)
    (n : ℕ) (results : List (Label n × ℝ))
    (hlength : results.length < n) :
    ¬ p ≤
      (parameterizedCountersFromResults n rhoStar results).threshold
        n rhoStar := by
  have hthreshold :=
    plateauCounters_threshold_lt_capBoundary hu n results hlength
  linarith

/-- Transcript form: if the most recent observation is a capped test and
its preceding test-result prefix is proper, the actual executable selector
returns no immediate job. -/
theorem plateau_parameterizedPendingImmediate_eq_none
    {u p : ℝ} (hu : zStar < u) (hp : u - 1 ≤ p)
    (n : ℕ) (transcript : Transcript n) (job : Label n)
    (hlast :
      transcript.getLast? = some (.testResult job p))
    (hbefore : transcript.testResults.dropLast.length < n) :
    transcript.parameterizedPendingImmediate? n rhoStar = none := by
  unfold Transcript.parameterizedPendingImmediate?
  rw [hlast]
  simp only
  rw [if_neg]
  exact plateauCounters_capped_not_immediate hu hp n
    transcript.testResults.dropLast hbefore

end

end SchedulingPaper.Online
