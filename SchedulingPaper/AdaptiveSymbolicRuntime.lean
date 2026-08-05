import SchedulingPaper.AdaptiveCanonicalTrace
import SchedulingPaper.PlateauRuntimeInvariant

/-!
# Equality of the symbolic and executable AdaptiveThreshold states

`AnalysisState` is the state used by the endpoint bank, whereas the online
strategy reconstructs `ParameterizedThresholdCounters` from the public test
results.  This file proves that, at `c = rhoStar`, the two representations
have exactly the same live threshold and take exactly the same symbolic
transition on every nonnegative processing time.
-/

namespace SchedulingPaper.Online

noncomputable section

open SchedulingPaper

theorem AnalysisState.threshold_eq_adaptiveThreshold
    (s : AnalysisState) :
    s.threshold = adaptiveThreshold s.y := by
  unfold AnalysisState.threshold adaptiveThreshold
  by_cases hlower : -1 ≤ s.y
  · by_cases hupper : s.y ≤ -1
    · have hy : s.y = -1 := le_antisymm hupper hlower
      simp [hlower, hupper, hy, activeThreshold_at_neg_one]
    · simp [hlower, hupper]
  · have hupper : s.y ≤ -1 := le_of_lt (lt_of_not_ge hlower)
    simp [hlower, hupper]

/-- Coordinate equality between the bank state and the counters used by the
parameterized executable strategy. -/
def AnalysisStateMatchesParameterizedCounters
    (n : ℕ) (s : AnalysisState)
    (counters : ParameterizedThresholdCounters) : Prop :=
  s.x = counters.remaining n ∧
    s.substantive = counters.positive ∧
    s.epsilon = 0 ∧
    s.deferred = counters.deferred

theorem analysisStateMatchesParameterizedCounters_initial (n : ℕ) :
    AnalysisStateMatchesParameterizedCounters n
      (initialAnalysisState n)
      ParameterizedThresholdCounters.initial := by
  simp [AnalysisStateMatchesParameterizedCounters,
    initialAnalysisState, ParameterizedThresholdCounters.initial,
    ParameterizedThresholdCounters.remaining]

theorem AnalysisStateMatchesParameterizedCounters.y_eq
    {n : ℕ} {s : AnalysisState}
    {counters : ParameterizedThresholdCounters}
    (hmatch : AnalysisStateMatchesParameterizedCounters n s counters) :
    s.y = counters.y n rhoStar := by
  rcases hmatch with ⟨hx, hpositive, hepsilon, hdeferred⟩
  unfold AnalysisState.y AnalysisState.eta AnalysisState.b
    ParameterizedThresholdCounters.y
  rw [hx, hpositive, hepsilon, hdeferred]
  unfold RStar
  ring

theorem AnalysisStateMatchesParameterizedCounters.threshold_eq
    {n : ℕ} {s : AnalysisState}
    {counters : ParameterizedThresholdCounters}
    (hmatch : AnalysisStateMatchesParameterizedCounters n s counters) :
    s.threshold = counters.threshold n rhoStar := by
  rw [AnalysisState.threshold_eq_adaptiveThreshold,
    ParameterizedThresholdCounters.threshold,
    parameterizedAdaptiveThreshold_rhoStar,
    hmatch.y_eq]

theorem classifyAdaptive_outcome
    {threshold p : ℝ} (hp : 0 ≤ p) (hthreshold : 0 ≤ threshold) :
    let symbol := classifyAdaptive threshold p
    (symbol.outcome, (0 < p), (threshold < p)) =
      if p = 0 then
        (.zero, False, False)
      else if p ≤ threshold then
        (.immediate, True, False)
      else
        (.deferred, True, True) := by
  dsimp only
  by_cases hpzero : p = 0
  · subst p
    simp [classifyAdaptive, hthreshold,
      ObligatoryRuntimeClass.outcome]
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    by_cases himmediate : p ≤ threshold
    · simp [classifyAdaptive, hpzero, himmediate, hppos,
        not_lt_of_ge himmediate, ObligatoryRuntimeClass.outcome]
    · have hdeferred : threshold < p := lt_of_not_ge himmediate
      simp [classifyAdaptive, hpzero, himmediate, hppos, hdeferred,
        ObligatoryRuntimeClass.outcome]

theorem AnalysisStateMatchesParameterizedCounters.step_classify
    {n : ℕ} {s : AnalysisState}
    {counters : ParameterizedThresholdCounters}
    (hmatch : AnalysisStateMatchesParameterizedCounters n s counters)
    {p : ℝ} (hp : 0 ≤ p)
    (htested : counters.tested < n)
    (hthreshold : 0 ≤ counters.threshold n rhoStar) :
    let symbol := classifyAdaptive s.threshold p
    AnalysisStateMatchesParameterizedCounters n
      (s.step symbol.outcome) (counters.observe n rhoStar p) := by
  have hthresholdEq := hmatch.threshold_eq
  have hremaining :
      (↑(n - counters.tested) : ℝ) - 1 =
        ↑(n - (counters.tested + 1)) := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by omega :
      1 ≤ n - counters.tested)]
    congr 1
  rcases hmatch with ⟨hx, hpositive, hepsilon, hdeferred⟩
  dsimp only
  unfold classifyAdaptive
  by_cases hpzero : p = 0
  · subst p
    simp [AnalysisState.step, ObligatoryRuntimeClass.outcome,
      ParameterizedThresholdCounters.observe,
      AnalysisStateMatchesParameterizedCounters,
      hthresholdEq, hthreshold, hx, hpositive, hepsilon, hdeferred,
      ParameterizedThresholdCounters.remaining]
    exact hremaining
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    by_cases himmediate : p ≤ s.threshold
    · have hnotDeferred : ¬ counters.threshold n rhoStar < p := by
        rw [← hthresholdEq]
        exact not_lt_of_ge himmediate
      simp [hpzero, himmediate, hppos, hnotDeferred,
        AnalysisState.step, ObligatoryRuntimeClass.outcome,
        ParameterizedThresholdCounters.observe,
        AnalysisStateMatchesParameterizedCounters,
        hx, hpositive, hepsilon, hdeferred,
        ParameterizedThresholdCounters.remaining]
      exact hremaining
    · have hdeferS : s.threshold < p := lt_of_not_ge himmediate
      have hdeferC : counters.threshold n rhoStar < p := by
        rwa [← hthresholdEq]
      simp [hpzero, himmediate, hppos, hdeferS, hdeferC,
        AnalysisState.step, ObligatoryRuntimeClass.outcome,
        ParameterizedThresholdCounters.observe,
        AnalysisStateMatchesParameterizedCounters,
        hx, hpositive, hepsilon, hdeferred,
        ParameterizedThresholdCounters.remaining]
      exact hremaining

/-- The same job records as `buildAdaptiveJobs`, constructed directly from
the public counter fold of the executable strategy. -/
def buildParameterizedAdaptiveJobs
    (n : ℕ) :
    ParameterizedThresholdCounters →
      List (Label n × ℝ) → List (AdaptiveRuntimeJob n)
  | _, [] => []
  | counters, result :: results =>
      let threshold := counters.threshold n rhoStar
      let symbol := classifyAdaptive threshold result.2
      {
        label := result.1
        processing := result.2
        threshold := threshold
        symbol := symbol
      } ::
        buildParameterizedAdaptiveJobs n
          (counters.observe n rhoStar result.2) results

@[simp] theorem buildParameterizedAdaptiveJobs_length
    (n : ℕ) (counters : ParameterizedThresholdCounters)
    (results : List (Label n × ℝ)) :
    (buildParameterizedAdaptiveJobs n counters results).length =
      results.length := by
  induction results generalizing counters with
  | nil => rfl
  | cons result results ih =>
      simp [buildParameterizedAdaptiveJobs, ih]

theorem ParameterizedThresholdCounters.threshold_nonneg_of_invariant
    {n : ℕ} {counters : ParameterizedThresholdCounters}
    (htested : counters.tested < n)
    (hpositive : 0 ≤ counters.positive)
    (hbalance : counters.deferred ≤ counters.positive) :
    0 ≤ counters.threshold n rhoStar := by
  have hremaining :
      0 < (counters.remaining n : ℝ) := by
    simp [ParameterizedThresholdCounters.remaining, htested]
  have hscale :
      counters.positive ≤ (1 + rhoStar) * counters.positive := by
    nlinarith [mul_nonneg rhoStar_pos.le hpositive]
  have hy : counters.y n rhoStar ≤ 0 := by
    unfold ParameterizedThresholdCounters.y
    exact div_nonpos_of_nonpos_of_nonneg
      (by linarith) hremaining.le
  have hone :=
    parameterizedAdaptiveThreshold_ge_one_of_nonpos rhoStar_pos hy
  exact le_trans zero_le_one hone

/-- Folding a nonnegative result list through the symbolic bank state gives
the same records as folding it through the executable counters. -/
theorem buildAdaptiveJobs_eq_buildParameterizedAdaptiveJobs
    (n : ℕ) (results : List (Label n × ℝ))
    (state : AnalysisState)
    (counters : ParameterizedThresholdCounters)
    (hmatch :
      AnalysisStateMatchesParameterizedCounters n state counters)
    (htotal : counters.tested + results.length = n)
    (hpositive : 0 ≤ counters.positive)
    (hbalance : counters.deferred ≤ counters.positive)
    (hnonneg : ∀ result ∈ results, 0 ≤ result.2) :
    buildAdaptiveJobs state results =
      buildParameterizedAdaptiveJobs n counters results := by
  induction results generalizing state counters with
  | nil =>
      simp [buildAdaptiveJobs, buildParameterizedAdaptiveJobs]
  | cons result results ih =>
      have htested : counters.tested < n := by
        simp only [List.length_cons] at htotal
        omega
      have hp : 0 ≤ result.2 :=
        hnonneg result (by simp)
      have hthreshold :
          0 ≤ counters.threshold n rhoStar :=
        counters.threshold_nonneg_of_invariant
          htested hpositive hbalance
      have hnextMatch :
          AnalysisStateMatchesParameterizedCounters n
            (state.step
              (classifyAdaptive state.threshold result.2).outcome)
            (counters.observe n rhoStar result.2) :=
        hmatch.step_classify hp htested hthreshold
      have hnextPositive :
          0 ≤ (counters.observe n rhoStar result.2).positive := by
        unfold ParameterizedThresholdCounters.observe
        dsimp only
        split_ifs <;> linarith
      have hnextBalance :
          (counters.observe n rhoStar result.2).deferred ≤
            (counters.observe n rhoStar result.2).positive :=
        counters.observe_deferred_le_positive rhoStar_pos
          htested hpositive hbalance
      have hnextTotal :
          (counters.observe n rhoStar result.2).tested +
              results.length = n := by
        simp only [ParameterizedThresholdCounters.observe,
          List.length_cons] at htotal ⊢
        omega
      have htailNonneg :
          ∀ tailResult ∈ results, 0 ≤ tailResult.2 := by
        intro tailResult hmem
        exact hnonneg tailResult (by simp [hmem])
      have htail :=
        ih
          (state.step
            (classifyAdaptive state.threshold result.2).outcome)
          (counters.observe n rhoStar result.2)
          hnextMatch hnextTotal hnextPositive hnextBalance
          htailNonneg
      have hthresholdEq := hmatch.threshold_eq
      rw [hthresholdEq] at htail
      simp only [buildAdaptiveJobs,
        buildParameterizedAdaptiveJobs]
      rw [hthresholdEq]
      exact congrArg
        (fun tail =>
          {
            label := result.1
            processing := result.2
            threshold := counters.threshold n rhoStar
            symbol :=
              classifyAdaptive
                (counters.threshold n rhoStar) result.2
          } :: tail)
        htail

theorem adaptiveRuntimeJobs_eq_buildParameterizedAdaptiveJobs
    (processingTime : Label n → ℝ)
    (hnonneg : ∀ job, 0 ≤ processingTime job) :
    adaptiveRuntimeJobs processingTime =
      buildParameterizedAdaptiveJobs n
        ParameterizedThresholdCounters.initial
        (fixedTestResults processingTime) := by
  apply buildAdaptiveJobs_eq_buildParameterizedAdaptiveJobs
  · exact analysisStateMatchesParameterizedCounters_initial n
  · simp [ParameterizedThresholdCounters.initial]
  · simp [ParameterizedThresholdCounters.initial]
  · simp [ParameterizedThresholdCounters.initial]
  · intro result hmem
    simp only [fixedTestResults, List.mem_ofFn] at hmem
    rcases hmem with ⟨job, rfl⟩
    exact hnonneg job

/-! ## The obligatory and parameterized executable presentations coincide -/

def ThresholdCountersEquivalent
    (ordinary : ThresholdCounters)
    (parameterized : ParameterizedThresholdCounters) : Prop :=
  ordinary.tested = parameterized.tested ∧
    ordinary.positive = parameterized.positive ∧
    ordinary.deferred = parameterized.deferred

theorem thresholdCountersEquivalent_initial :
    ThresholdCountersEquivalent ThresholdCounters.initial
      ParameterizedThresholdCounters.initial := by
  simp [ThresholdCountersEquivalent, ThresholdCounters.initial,
    ParameterizedThresholdCounters.initial]

theorem ThresholdCountersEquivalent.remaining_eq
    {ordinary : ThresholdCounters}
    {parameterized : ParameterizedThresholdCounters}
    (heq : ThresholdCountersEquivalent ordinary parameterized)
    (n : ℕ) :
    ordinary.remaining n = parameterized.remaining n := by
  rcases heq with ⟨htested, _, _⟩
  simp [ThresholdCounters.remaining,
    ParameterizedThresholdCounters.remaining, htested]

theorem ThresholdCountersEquivalent.threshold_eq
    {ordinary : ThresholdCounters}
    {parameterized : ParameterizedThresholdCounters}
    (heq : ThresholdCountersEquivalent ordinary parameterized)
    (n : ℕ) :
    ordinary.threshold n =
      parameterized.threshold n rhoStar := by
  have hremaining := heq.remaining_eq n
  rcases heq with ⟨htested, hpositive, hdeferred⟩
  unfold ThresholdCounters.threshold ThresholdCounters.y
    ParameterizedThresholdCounters.threshold
    ParameterizedThresholdCounters.y
  rw [parameterizedAdaptiveThreshold_rhoStar,
    hpositive, hdeferred, hremaining]
  rfl

theorem ThresholdCountersEquivalent.observe
    {ordinary : ThresholdCounters}
    {parameterized : ParameterizedThresholdCounters}
    (heq : ThresholdCountersEquivalent ordinary parameterized)
    (n : ℕ) (p : ℝ) :
    ThresholdCountersEquivalent
      (ordinary.observe n p)
      (parameterized.observe n rhoStar p) := by
  have hthreshold := heq.threshold_eq n
  rcases heq with ⟨htested, hpositive, hdeferred⟩
  simp [ThresholdCountersEquivalent, ThresholdCounters.observe,
    ParameterizedThresholdCounters.observe, htested, hpositive,
    hdeferred, hthreshold]

theorem countersFromResults_equivalent_parameterized
    (n : ℕ) (results : List (Label n × ℝ)) :
    ThresholdCountersEquivalent
      (countersFromResults n results)
      (parameterizedCountersFromResults n rhoStar results) := by
  unfold countersFromResults parameterizedCountersFromResults
  have hgeneral :
      ∀ (ordinary : ThresholdCounters)
        (parameterized : ParameterizedThresholdCounters),
        ThresholdCountersEquivalent ordinary parameterized →
        ThresholdCountersEquivalent
          (results.foldl
            (fun state result => state.observe n result.2) ordinary)
          (results.foldl
            (fun state result =>
              state.observe n rhoStar result.2) parameterized) := by
    intro ordinary parameterized heq
    induction results generalizing ordinary parameterized with
    | nil =>
        simpa using heq
    | cons result results ih =>
        simp only [List.foldl_cons]
        exact ih _ _ (heq.observe n result.2)
  exact hgeneral _ _ thresholdCountersEquivalent_initial

theorem Transcript.parameterizedPendingImmediate_rhoStar
    (n : ℕ) (transcript : Transcript n) :
    transcript.parameterizedPendingImmediate? n rhoStar =
      transcript.pendingImmediate? n := by
  unfold Transcript.parameterizedPendingImmediate?
    Transcript.pendingImmediate?
    Transcript.parameterizedCountersBeforeLastTest
    Transcript.countersBeforeLastTest
  cases hlast : transcript.getLast? with
  | none => rfl
  | some observation =>
      cases observation with
      | processed job => rfl
      | rawCompleted job => rfl
      | testResult job p =>
          have heq :=
            countersFromResults_equivalent_parameterized n
              transcript.testResults.dropLast
          rw [← heq.threshold_eq n]

theorem parameterizedAdaptiveThresholdStrategy_rhoStar
    (n : ℕ) :
    parameterizedAdaptiveThresholdStrategy n rhoStar =
      adaptiveThresholdStrategy n := by
  funext transcript
  unfold parameterizedAdaptiveThresholdStrategy
    adaptiveThresholdStrategy
  rw [Transcript.parameterizedPendingImmediate_rhoStar]
  cases hpending : transcript.pendingImmediate? n with
  | some job => simp [hpending]
  | none =>
      by_cases htest : transcript.testResults.length < n
      · simp [hpending, htest]
      · cases hshort : transcript.shortestRemaining? with
        | none => simp [hpending, htest, hshort]
        | some job => simp [hpending, htest, hshort]

end

end SchedulingPaper.Online
