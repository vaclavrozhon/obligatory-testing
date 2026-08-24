import SchedulingPaper.RevealingOptimizationAnnounced
import SchedulingPaper.RawExecution
import SchedulingPaper.TestProcessCanonicalTrace
import SchedulingPaper.RandomizedRelabelRun
import SchedulingPaper.TestProcessPolicyAccounting
import SchedulingPaper.RandomizedIdealSchedule
import Mathlib.Tactic

/-!
# Operational upper endpoints for revealing optimization

This file connects the finite announced formulas to executable public-
transcript strategies.  The low-cap endpoint is the literal all-raw strategy;
it is exact, not merely asymptotic.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace OperationalUpper

noncomputable section

/-! ## Literal stationary threshold policy -/

/-- Process the just-revealed job immediately exactly when it lies below the
fixed announced threshold. -/
def fixedThresholdPending (τ : ℝ) (transcript : Online.Transcript n) :
    Option (Online.Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) => if p < τ then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- Public-transcript implementation of the announced stationary endpoint:
test in canonical order, process short outcomes immediately, and drain the
deferred tail by SPT. -/
def fixedThresholdStrategy (n : ℕ) (τ : ℝ) : Online.Strategy n :=
  Online.testProcessStrategy (fixedThresholdPending τ)

theorem fixedThresholdPending_selectsLastTest (τ : ℝ) :
    Online.SelectsLastTest (fixedThresholdPending (n := n) τ) := by
  intro transcript job hpending
  unfold fixedThresholdPending at hpending
  cases hlast : transcript.getLast? with
  | none => simp [hlast] at hpending
  | some observation =>
      cases observation with
      | processed processedJob => simp [hlast] at hpending
      | rawCompleted rawJob => simp [hlast] at hpending
      | testResult testedJob p =>
          by_cases hp : p < τ
          · simp [hlast, hp] at hpending
            subst testedJob
            exact ⟨p, rfl⟩
          · simp [hlast, hp] at hpending

/-- Termination, truthfulness, exact completion labels, and canonical trace
shape of the fixed-threshold strategy. -/
theorem fixedThreshold_run_package
    (n : ℕ) (u τ : ℝ) (processing : Fin n → ℝ) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (fixedThresholdStrategy n τ) (2 * n + 1)
    result.reason = .strategyStopped ∧
      result.config.TestProcessInvariant ∧
      result.config.transcript.TestsMatch processing ∧
      result.config.FixedCompletionInvariant processing ∧
      Online.TestProcessTrace result.config.transcript ∧
      ∀ job, result.config.jobs job = .done := by
  unfold Online.run fixedThresholdStrategy
  simpa using
    Online.runFuel_testProcessStrategy_completed_with_canonicalTrace
      (.finite u) processing (fixedThresholdPending_selectsLastTest τ) 0

theorem fixedThresholdStrategy_completes
    (n : ℕ) (u τ : ℝ) (processing : Fin n → ℝ) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (fixedThresholdStrategy n τ) (2 * n + 1)).config.jobs job = .done := by
  exact (fixedThreshold_run_package n u τ processing).2.2.2.2.2

/-- Private uniform discovery order obtained by conjugating virtual labels. -/
def randomizedFixedThresholdStrategy (n : ℕ) (τ : ℝ) :
    Equiv.Perm (Fin n) → Online.Strategy n :=
  fun order =>
    (fixedThresholdStrategy n τ).relabel
      (RandomizedObligatory.linearizedFinOrder n order)

theorem randomizedFixedThresholdStrategy_completes
    (n : ℕ) (u τ : ℝ) (processing : Fin n → ℝ)
    (order : Equiv.Perm (Fin n)) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (randomizedFixedThresholdStrategy n τ order)
        (2 * n + 1)).config.jobs job = .done := by
  rw [randomizedFixedThresholdStrategy, Online.run_relabel_config]
  intro job
  exact fixedThresholdStrategy_completes n u τ
    (fun virtual => processing
      (RandomizedObligatory.linearizedFinOrder n order virtual))
    ((RandomizedObligatory.linearizedFinOrder n order).symm job)

/-- Status used by the generic policy-sensitive pair accounting. -/
def fixedThresholdOutcome (τ p : ℝ) : BoundaryOutcome :=
  if p = 0 then .zero else if p < τ then .immediate else .deferred

theorem fixedThresholdOutcome_ne_deferred_iff
    {τ p : ℝ} (hτ : 0 < τ) (hp0 : 0 ≤ p) :
    fixedThresholdOutcome τ p ≠ .deferred ↔ p < τ := by
  unfold fixedThresholdOutcome
  by_cases hp : p = 0
  · subst p
    simp [hτ]
  · by_cases hpτ : p < τ <;> simp [hp, hpτ]

theorem fixedThresholdOutcome_eq_deferred_iff
    {τ p : ℝ} (hτ : 0 < τ) (hp0 : 0 ≤ p) :
    fixedThresholdOutcome τ p = .deferred ↔ ¬p < τ := by
  rw [← not_congr (fixedThresholdOutcome_ne_deferred_iff hτ hp0)]
  simp

theorem fixedThresholdOutcome_deferred_ne_zero
    {τ p : ℝ} (hdeferred : fixedThresholdOutcome τ p = .deferred) :
    p ≠ 0 := by
  intro hp
  subst p
  simp [fixedThresholdOutcome] at hdeferred

/-- Under the threshold classification, the generic operational status-table
charge is exactly the ideal stationary pair charge. -/
theorem fixedThreshold_pairCharge_eq_ideal
    {τ p q : ℝ} (hτ : 0 < τ) :
    obligatoryALGPairCharge
        ⟨fixedThresholdOutcome τ p, p⟩
        ⟨fixedThresholdOutcome τ q, q⟩ =
      RandomizedObligatory.idealPairCharge
        (p, decide (p < τ)) (q, decide (q < τ)) := by
  unfold fixedThresholdOutcome
  by_cases hp0 : p = 0
  · subst p
    simp [hτ, obligatoryALGPairCharge,
      RandomizedObligatory.idealPairCharge]
  · by_cases hpτ : p < τ
    · simp [hp0, hpτ, obligatoryALGPairCharge,
        RandomizedObligatory.idealPairCharge]
    · by_cases hq0 : q = 0
      · subst q
        simp [hp0, hpτ, hτ, obligatoryALGPairCharge,
          RandomizedObligatory.idealPairCharge]
      · by_cases hqτ : q < τ <;>
          simp [hp0, hpτ, hq0, hqτ, obligatoryALGPairCharge,
            RandomizedObligatory.idealPairCharge]

/-- Exact pathwise cost identity for the canonical fixed-threshold run. -/
theorem fixedThreshold_runCost_eq_idealPairCost
    (n : ℕ) (u τ : ℝ) (hτ : 0 < τ)
    (processing : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ processing job) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (fixedThresholdStrategy n τ) (2 * n + 1)) =
      RandomizedObligatory.finiteIdealPairCost processing
        (fun job => decide (processing job < τ)) := by
  let result := Online.run (.finite u) (Online.fixedOracle processing)
    (fixedThresholdStrategy n τ) (2 * n + 1)
  have hrun := fixedThreshold_run_package n u τ processing
  have hallTests : result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed : ∀ job,
      job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  have hperm :
      (result.config.transcript.completionLabels processing).Perm
        (List.ofFn id) := by
    have hnodup := hrun.2.2.2.1.nodup
    apply (List.perm_ext_iff_of_nodup hnodup
      (List.nodup_ofFn.mpr Function.injective_id)).mpr
    intro job
    rw [hrun.2.2.2.1.mem_iff]
    simp [hrun.2.2.2.2.2 job, Online.JobState.completionRecorded]
  have hself : ∀ job : Fin n,
      Online.traceSelfCharge (.finite u) processing
          result.config.transcript job = 1 + processing job := by
    intro job
    apply Online.traceSelfCharge_eq_one_add_of_projection
    · exact hrun.2.2.2.2.1.terminal_selfProjection hrun.2.2.1
        hallTests hallProcessed job
    · rfl
  have hfollow : result.config.transcript.FollowsStrategy
      (Online.testProcessStrategy (fixedThresholdPending τ)) := by
    simpa [result, fixedThresholdStrategy] using
      Online.run_followsStrategy (.finite u) (Online.fixedOracle processing)
        (fixedThresholdStrategy n τ) (2 * n + 1)
  let outcome : Fin n → BoundaryOutcome :=
    fun job => fixedThresholdOutcome τ (processing job)
  have himmediate : ∀ job, outcome job ≠ .deferred →
      result.config.transcript.ImmediateFor (fixedThresholdPending τ) job := by
    intro job hnotDeferred before after p hdecomp
    have hlt : processing job < τ :=
      (fixedThresholdOutcome_ne_deferred_iff hτ (hp0 job)).mp hnotDeferred
    have hp : p = processing job := by
      apply hrun.2.2.1 job p
      apply (Online.testResult_mem_iff_observation_mem
        result.config.transcript job p).2
      rw [hdecomp]
      simp
    subst p
    simp [fixedThresholdPending, hlt]
  have hdeferred : ∀ job, outcome job = .deferred →
      result.config.transcript.DeferredFor (fixedThresholdPending τ) job := by
    intro job hDeferred before after p hdecomp
    have hnlt : ¬processing job < τ :=
      (fixedThresholdOutcome_eq_deferred_iff hτ (hp0 job)).mp hDeferred
    have hp : p = processing job := by
      apply hrun.2.2.1 job p
      apply (Online.testResult_mem_iff_observation_mem
        result.config.transcript job p).2
      rw [hdecomp]
      simp
    subst p
    simp [fixedThresholdPending, hnlt]
  have hpair : ∀ left right : Fin n, left < right →
      Online.tracePairCharge (.finite u) processing
          result.config.transcript left right =
        RandomizedObligatory.idealPairCharge
          (processing left, decide (processing left < τ))
          (processing right, decide (processing right < τ)) := by
    intro left right hlr
    rw [hrun.2.2.2.2.1.tracePairCharge_eq_obligatoryALGPairCharge
      hrun.2.2.1 hallTests hallProcessed hfollow
      (fixedThresholdPending_selectsLastTest τ) outcome himmediate hdeferred
      (fun job hjob => fixedThresholdOutcome_deferred_ne_zero hjob)
      (.finite u) hlr]
    exact fixedThreshold_pairCharge_eq_ideal hτ
  unfold Online.runCompletionCost
  change Online.completionCost (.finite u) processing
      result.config.transcript = _
  rw [Online.completionCost_eq_traceSelf_add_pairs
    (.finite u) processing result.config.transcript hperm]
  unfold RandomizedObligatory.finiteIdealPairCost
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro job _
    exact hself job
  · apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right hright
    exact hpair left right (Finset.mem_filter.mp hright).2

/-- A relabelled path is exactly the classified stationary word indexed by
the corresponding discovery permutation. -/
theorem randomizedFixedThreshold_runCost_eq_classifiedPairCost
    (n : ℕ) (u τ : ℝ) (hτ : 0 < τ)
    (processing : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ processing job)
    (order : Equiv.Perm (Fin n)) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (randomizedFixedThresholdStrategy n τ order) (2 * n + 1)) =
      RandomizedObligatory.classifiedPairCost
        (RandomizedObligatory.orderedClassifiedJobs processing
          (ObligatoryInstance.empiricalThresholdEarly processing τ) order) := by
  rw [randomizedFixedThresholdStrategy,
    Online.runCompletionCost_relabel,
    fixedThreshold_runCost_eq_idealPairCost n u τ hτ
      (fun virtual => processing
        (RandomizedObligatory.linearizedFinOrder n order virtual))
      (fun virtual => hp0 _)]
  rw [← RandomizedObligatory.classifiedPairCost_ofFn]
  rfl

/-- Uniform expected cost of the literal randomized strategy is the exact
announced stationary-template formula already used by the curve proof. -/
theorem randomizedFixedThreshold_average_eq_stationaryTemplate
    (n : ℕ) (u τ : ℝ) (hτ : 0 < τ)
    (processing : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ processing job) :
    Randomized.uniformAverage (fun order : Equiv.Perm (Fin n) =>
      Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (randomizedFixedThresholdStrategy n τ order) (2 * n + 1))) =
      ObligatoryInstance.empiricalStationaryTemplateAverage processing τ := by
  unfold ObligatoryInstance.empiricalStationaryTemplateAverage
  apply congrArg Randomized.uniformAverage
  funext order
  exact randomizedFixedThreshold_runCost_eq_classifiedPairCost
    n u τ hτ processing hp0 order

/-- With the common `2n+1` analysis fuel, the public all-raw strategy has
exactly the finite raw endpoint cost. -/
theorem rawStrategy_runCost_eq_empiricalRawCost
    (n : ℕ) (u : ℝ) (processing : Fin n → ℝ) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (Online.rawStrategy n) (2 * n + 1)) =
      empiricalRawCost n u := by
  rw [show 2 * n + 1 = n + 1 + n by omega,
    Online.raw_runCompletionCost]
  unfold empiricalRawCost triangular
  ring

/-- The same run completes every job within the common analysis fuel. -/
theorem rawStrategy_completes (n : ℕ) (u : ℝ)
    (processing : Fin n → ℝ) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (Online.rawStrategy n) (2 * n + 1)).config.jobs job = .done := by
  rw [show 2 * n + 1 = n + 1 + n by omega]
  exact Online.raw_run_completed n n u
    (Online.fixedOracle processing)

/-- For `u ≤ 1`, Raw is an executable exact optimum on every nonempty
revealing instance. -/
theorem rawStrategy_runCost_eq_offline_of_cap_le_one
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hp0 : ∀ job, 0 ≤ processing job) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (Online.rawStrategy n) (2 * n + 1)) =
      empiricalRevealingOfflineCost u processing := by
  rw [rawStrategy_runCost_eq_empiricalRawCost,
    empiricalRawCost_eq_revealingOfflineCost_of_cap_le_one
      hn processing hu0 hu1 hp0]

/-- Literal operational upper half of the randomized curve in the low-cap
regime.  Since the curve equals one here, the inequality is an equality. -/
theorem rawStrategy_operational_curve_upper_of_cap_le_one
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hp0 : ∀ job, 0 ≤ processing job) :
    Online.runCompletionCost (.finite u) processing
        (Online.run (.finite u) (Online.fixedOracle processing)
          (Online.rawStrategy n) (2 * n + 1)) ≤
      randomizedCurve u * empiricalRevealingOfflineCost u processing := by
  rw [rawStrategy_runCost_eq_offline_of_cap_le_one
    hn processing hu0 hu1 hp0]
  unfold randomizedCurve
  rw [if_pos hu1]
  simp

/-- End-to-end announced upper endpoint.  For each concrete multiset, the
chosen threshold determines a finite private-seed family of literal
transcript-only strategies.  Every seed completes, and its expected timed
cost obeys the checked curve bound with the exact linear diagonal remainder. -/
theorem exists_announced_operational_curve_upper
    {n : ℕ} (hn : 0 < n) (processing : Fin n → ℝ)
    {u : ℝ} (hu : 1 < u)
    (hp0 : ∀ job, 0 ≤ processing job)
    (hpu : ∀ job, processing job ≤ u) :
    ∃ (τ : ℝ) (strategy : Equiv.Perm (Fin n) → Online.Strategy n),
      1 ≤ τ ∧
      (∑ job, max (τ - processing job) 0 = n) ∧
      (∀ seed job,
        (Online.run (.finite u) (Online.fixedOracle processing)
          (strategy seed) (2 * n + 1)).config.jobs job = .done) ∧
      Randomized.uniformAverage (fun seed =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (strategy seed) (2 * n + 1))) ≤
        randomizedCurve u * empiricalRevealingOfflineCost u processing +
          (n : ℝ) * (1 + u) / 2 := by
  obtain ⟨τ, hτ, hthreshold, hcost⟩ :=
    announcedTemplate_curve_upper hn processing hu hp0 hpu
  by_cases hτu : τ ≤ u
  · let strategy := randomizedFixedThresholdStrategy n τ
    refine ⟨τ, strategy, hτ, hthreshold, ?_, ?_⟩
    · intro seed job
      exact randomizedFixedThresholdStrategy_completes
        n u τ processing seed job
    · rw [show Randomized.uniformAverage (fun seed =>
          Online.runCompletionCost (.finite u) processing
            (Online.run (.finite u) (Online.fixedOracle processing)
              (strategy seed) (2 * n + 1))) =
          ObligatoryInstance.empiricalStationaryTemplateAverage
            processing τ by
          exact randomizedFixedThreshold_average_eq_stationaryTemplate
            n u τ (by linarith) processing hp0]
      simpa [empiricalAnnouncedTemplateAverage, hτu] using hcost
  · let strategy : Equiv.Perm (Fin n) → Online.Strategy n :=
      fun _seed => Online.rawStrategy n
    refine ⟨τ, strategy, hτ, hthreshold, ?_, ?_⟩
    · intro seed job
      exact rawStrategy_completes n u processing job
    · have hpoint : (fun _seed : Equiv.Perm (Fin n) =>
          Online.runCompletionCost (.finite u) processing
            (Online.run (.finite u) (Online.fixedOracle processing)
              (Online.rawStrategy n) (2 * n + 1))) =
          (fun _seed => empiricalRawCost n u) := by
          funext seed
          exact rawStrategy_runCost_eq_empiricalRawCost n u processing
      change Randomized.uniformAverage (fun seed =>
        Online.runCompletionCost (.finite u) processing
          (Online.run (.finite u) (Online.fixedOracle processing)
            (Online.rawStrategy n) (2 * n + 1))) ≤ _
      rw [hpoint, Randomized.uniformAverage_const]
      simpa [empiricalAnnouncedTemplateAverage, hτu] using hcost

end

end OperationalUpper
end RevealingOptimization
end SchedulingPaper
