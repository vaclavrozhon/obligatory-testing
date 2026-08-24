import SchedulingPaper.RevealingOptimizationQuotaRounding
import Mathlib.Tactic

/-!
# Transcript-adaptive quota strategies for revealing optimization

The learned policy uses one selector during its pilot block and a selector
computed from the public pilot transcript afterwards.  This file generalizes
the fixed-selector quota runtime just enough to express that literal policy,
while retaining the exact `2n+1` termination bound.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace PilotStrategy

open Online
open QuotaStrategy

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A quota policy whose low selector may be recomputed from the current
public transcript. -/
def adaptiveQuotaStrategy
    (n q : ℕ) (selector : Online.Transcript n → ℝ → Bool) :
    Online.Strategy n := fun transcript =>
  match safeLastLowPending? (selector transcript) transcript with
  | some job => some (.process job)
  | none =>
      if transcript.testResults.length < q then
        (RandomizedOptional.nextCanonicalTouch? n transcript).map
          Online.Action.test
      else
        match transcript.shortestRemaining? with
        | some job => some (.process job)
        | none =>
            (RandomizedOptional.nextCanonicalTouch? n transcript).map
              Online.Action.raw

def StrictAdaptiveWorkStep
    (u : ℝ) (processing : Online.Label n → ℝ) (q : ℕ)
    (strategy : Online.Strategy n) (config : Online.Config n) : Prop :=
  ∃ (action : Online.Action n) (next : Online.Config n),
    strategy config.transcript = some action ∧
      config.step (.finite u) (Online.fixedOracle processing) action =
        some next ∧
      QuotaStrategy.Config.Invariant processing q next ∧
      next.remainingWork < config.remainingWork

theorem adaptiveQuotaStrategy_progress
    {processing : Online.Label n → ℝ} {q : ℕ} (hq : q ≤ n)
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing q config)
    (hpos : 0 < config.remainingWork) (u : ℝ)
    (selector : Online.Transcript n → ℝ → Bool) :
    StrictAdaptiveWorkStep u processing q
      (adaptiveQuotaStrategy n q selector) config := by
  unfold adaptiveQuotaStrategy
  cases hlow : safeLastLowPending? (selector config.transcript)
      config.transcript with
  | some job =>
      obtain ⟨p, hstate⟩ := hgood.safeLastLowPending_tested hlow
      let next : Online.Config n := {
        jobs := Function.update config.jobs job .done
        transcript := config.transcript ++ [.processed job] }
      have hstep : config.step (.finite u) (Online.fixedOracle processing)
          (.process job) = some next := by
        simp [Online.Config.step, hstate, next]
      exact ⟨.process job, next, by simp [hlow], hstep,
        hgood.afterProcess hstate hstep,
        Online.Config.remainingWork_step_lt hstep⟩
  | none =>
      by_cases htest : config.transcript.testResults.length < q
      · have hstarted := hgood.beforeQuota htest
        have hstartedLt : config.transcript.startedLabels.length < n := by
          omega
        let job : Online.Label n :=
          ⟨config.transcript.startedLabels.length, hstartedLt⟩
        have hnext : RandomizedOptional.nextCanonicalTouch? n
            config.transcript = some job :=
          nextCanonicalTouch_some_iff.mpr ⟨hstartedLt, rfl⟩
        have hstate := hgood.nextTouch_untouched hnext
        let next : Online.Config n := {
          jobs := Function.update config.jobs job (.tested (processing job))
          transcript := config.transcript ++
            [.testResult job (processing job)] }
        have hstep : config.step (.finite u) (Online.fixedOracle processing)
            (.test job) = some next := by
          simp [Online.Config.step, hstate, Online.fixedOracle, next]
        exact ⟨.test job, next, by simp [hlow, htest, hnext], hstep,
          hgood.afterTest htest hnext hstep,
          Online.Config.remainingWork_step_lt hstep⟩
      · have hreached : q ≤ config.transcript.testResults.length :=
          Nat.le_of_not_gt htest
        cases hshort : config.transcript.shortestRemaining? with
        | some job =>
            obtain ⟨p, hstate⟩ := hgood.shortestRemaining_tested hshort
            let next : Online.Config n := {
              jobs := Function.update config.jobs job .done
              transcript := config.transcript ++ [.processed job] }
            have hstep : config.step (.finite u)
                (Online.fixedOracle processing) (.process job) = some next := by
              simp [Online.Config.step, hstate, next]
            exact ⟨.process job, next,
              by simp [hlow, htest, hshort], hstep,
              hgood.afterProcess hstate hstep,
              Online.Config.remainingWork_step_lt hstep⟩
        | none =>
            cases hnext : RandomizedOptional.nextCanonicalTouch? n
                config.transcript with
            | some job =>
                have hstate := hgood.nextTouch_untouched hnext
                let next : Online.Config n := {
                  jobs := Function.update config.jobs job .done
                  transcript := config.transcript ++ [.rawCompleted job] }
                have hstep : config.step (.finite u)
                    (Online.fixedOracle processing) (.raw job) = some next := by
                  simp [Online.Config.step, hstate, next]
                exact ⟨.raw job, next,
                  by simp [hlow, htest, hshort, hnext], hstep,
                  hgood.afterRaw hreached hnext hstep,
                  Online.Config.remainingWork_step_lt hstep⟩
            | none =>
                have hdone := hgood.done_of_no_next_no_remaining hnext hshort
                have hzero :=
                  (Online.Config.remainingWork_eq_zero_iff config).mpr hdone
                omega

theorem adaptiveQuotaStrategy_stop_of_zero
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing q config)
    (hzero : config.remainingWork = 0)
    (selector : Online.Transcript n → ℝ → Bool) :
    adaptiveQuotaStrategy n q selector config.transcript = none := by
  have hdone := (Online.Config.remainingWork_eq_zero_iff config).mp hzero
  have hsafe : safeLastLowPending? (selector config.transcript)
      config.transcript = none := by
    cases hs : safeLastLowPending? (selector config.transcript)
        config.transcript with
    | none => rfl
    | some job =>
        obtain ⟨p, htested⟩ := hgood.safeLastLowPending_tested hs
        rw [hdone job] at htested
        contradiction
  have hshort : config.transcript.shortestRemaining? = none := by
    cases hs : config.transcript.shortestRemaining? with
    | none => rfl
    | some job =>
        obtain ⟨p, htested⟩ := hgood.shortestRemaining_tested hs
        rw [hdone job] at htested
        contradiction
  have hnext : RandomizedOptional.nextCanonicalTouch? n
      config.transcript = none := by
    cases hnxt : RandomizedOptional.nextCanonicalTouch? n
        config.transcript with
    | none => rfl
    | some job =>
        have huntouched := hgood.nextTouch_untouched hnxt
        rw [hdone job] at huntouched
        contradiction
  simp [adaptiveQuotaStrategy, hsafe, hshort, hnext]

/-- Generic strict-rank recursion.  Raw execution can lower the work rank by
two, so this version only assumes a strict decrease rather than equality. -/
theorem runFuel_adaptiveQuotaStrategy_completed
    {processing : Online.Label n → ℝ} {q : ℕ} (hq : q ≤ n)
    (u : ℝ) (selector : Online.Transcript n → ℝ → Bool)
    (fuel : ℕ) (config : Online.Config n)
    (hgood : QuotaStrategy.Config.Invariant processing q config)
    (hfuel : config.remainingWork < fuel) :
    let result := Online.runFuel (.finite u) (Online.fixedOracle processing)
      (adaptiveQuotaStrategy n q selector) fuel config
    result.reason = .strategyStopped ∧
      QuotaStrategy.Config.Invariant processing q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  induction fuel generalizing config with
  | zero => omega
  | succ fuel ih =>
      by_cases hzero : config.remainingWork = 0
      · have hstop := adaptiveQuotaStrategy_stop_of_zero
          hgood hzero selector
        simp only [Online.runFuel, hstop]
        exact ⟨trivial, hgood,
          (Online.Config.remainingWork_eq_zero_iff config).mp hzero⟩
      · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
        obtain ⟨action, next, hchosen, hlegal, hnextGood, hdec⟩ :=
          adaptiveQuotaStrategy_progress hq hgood hpos u selector
        simp only [Online.runFuel, hchosen, hlegal]
        apply ih next hnextGood
        omega

theorem adaptiveQuotaStrategy_completes
    {n q : ℕ} (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ)
    (selector : Online.Transcript n → ℝ → Bool) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (adaptiveQuotaStrategy n q selector) (2 * n + 1)
    result.reason = .strategyStopped ∧
      QuotaStrategy.Config.Invariant processing q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  unfold Online.run
  apply runFuel_adaptiveQuotaStrategy_completed hq u selector
  · exact QuotaStrategy.Config.initial_invariant processing q
  · rw [Online.Config.initial_remainingWork]
    omega

/-- During the first `k` tests every outcome is completed immediately;
afterwards the supplied learned selector is used. -/
def pilotPhaseSelector
    (k : ℕ) (low : ℝ → Bool) (transcript : Online.Transcript n) :
    ℝ → Bool :=
  if transcript.testResults.length ≤ k then fun _ => true else low

/-- The literal pilot/quota policy.  It must test at least the `k` pilot
jobs, hence the total quota is `max k q`. -/
def pilotQuotaStrategy
    (n k q : ℕ) (low : ℝ → Bool) : Online.Strategy n :=
  adaptiveQuotaStrategy n (max k q) (pilotPhaseSelector k low)

theorem pilotQuotaStrategy_completes
    {n k q : ℕ} (hk : k ≤ n) (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool) :
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (pilotQuotaStrategy n k q low) (2 * n + 1)
    result.reason = .strategyStopped ∧
      QuotaStrategy.Config.Invariant processing (max k q) result.config ∧
      ∀ job, result.config.jobs job = .done := by
  exact adaptiveQuotaStrategy_completes (max_le hk hq) u processing
    (pilotPhaseSelector k low)

def randomizedPilotQuotaStrategy
    (n k q : ℕ) (low : ℝ → Bool) (order : Equiv.Perm (Fin n)) :
    Online.Strategy n :=
  (pilotQuotaStrategy n k q low).relabel order

theorem randomizedPilotQuotaStrategy_completes
    {n k q : ℕ} (hk : k ≤ n) (hq : q ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (low : ℝ → Bool)
    (order : Equiv.Perm (Fin n)) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (randomizedPilotQuotaStrategy n k q low order)
        (2 * n + 1)).config.jobs job = .done := by
  rw [randomizedPilotQuotaStrategy, Online.run_relabel_config]
  intro job
  exact (pilotQuotaStrategy_completes hk hq u
    (fun virtual => processing (order virtual)) low).2.2
      (order.symm job)

end

end PilotStrategy
end RevealingOptimization
end SchedulingPaper
