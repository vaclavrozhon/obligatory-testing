import SchedulingPaper.RevealingOptimizationPilotStrategy
import SchedulingPaper.RevealingOptimizationQuotaFluid
import SchedulingPaper.AdaptiveCanonicalTrace
import Mathlib.Tactic

/-!
# A literal learned pilot/quota strategy

The strategy below computes both its quota and low selector from the first
`k` public test results.  The fixed input appears only in the proof, where
the canonical test-order invariant identifies that public sample with the
first `k` entries of `fixedTestResults`.
-/

namespace SchedulingPaper
namespace RevealingOptimization
namespace LearnedPilot

open Online
open QuotaStrategy
open PilotStrategy
open InstanceLearning
open RandomizedOptional
open QuotaFluid

noncomputable section
attribute [local instance] Classical.propDecidable

theorem invariant_testResults_eq_fixed_take
    {processing : Online.Label n → ℝ} {q : ℕ}
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing q config)
    (hq : q ≤ n) :
    config.transcript.testResults =
      (Online.fixedTestResults processing).take
        config.transcript.testResults.length := by
  apply List.ext_get
  · simp [Online.fixedTestResults_length, hgood.testBound.trans hq]
  · intro index hleft hright
    let result := config.transcript.testResults.get ⟨index, hleft⟩
    have hmapIndex : index <
        (config.transcript.testResults.map fun entry => entry.1.val).length := by
      simpa using hleft
    have horder := List.getElem_of_eq hgood.testOrder hmapIndex
    have hlabelVal : result.1.val = index := by
      simpa [result, List.get_eq_getElem] using horder
    have hindexN : index < n := by
      exact lt_of_lt_of_le hleft (hgood.testBound.trans hq)
    have hlabel : result.1 = ⟨index, hindexN⟩ := Fin.ext hlabelVal
    have hvalue : result.2 = processing result.1 :=
      hgood.testsMatch result.1 result.2 (List.get_mem _ _)
    have htakeGet :
        ((Online.fixedTestResults processing).take
          config.transcript.testResults.length).get ⟨index, hright⟩ =
          (⟨index, hindexN⟩, processing ⟨index, hindexN⟩) := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_take]
      simp [Online.fixedTestResults]
    rw [htakeGet]
    exact Prod.ext hlabel (by simpa [hlabel] using hvalue)

/-- The output of an arbitrary public pilot learner: an integral quota and
a value selector. -/
abbrev PilotRule (n : ℕ) :=
  List (Online.Label n × ℝ) → ℕ × (ℝ → Bool)

/-- Recompute the rule from the first `k` public tests at every query.  Before
the sample is complete, `max k quota` and `pilotPhaseSelector` make the rule's
provisional output irrelevant. -/
def learnedPilotQuotaStrategy
    (n k : ℕ) (rule : PilotRule n) : Online.Strategy n := fun transcript =>
  let learned := rule (transcript.testResults.take k)
  adaptiveQuotaStrategy n (max k learned.1)
    (pilotPhaseSelector k learned.2) transcript

theorem learnedPilotQuotaStrategy_eq_fixed_of_invariant
    {processing : Online.Label n → ℝ} {Q k : ℕ}
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing Q config)
    (hQ : Q ≤ n) (rule : PilotRule n)
    (hQdef : Q = max k
      (rule ((Online.fixedTestResults processing).take k)).1) :
    learnedPilotQuotaStrategy n k rule config.transcript =
      adaptiveQuotaStrategy n Q
        (pilotPhaseSelector k
          (rule ((Online.fixedTestResults processing).take k)).2)
        config.transcript := by
  unfold learnedPilotQuotaStrategy
  by_cases hsample : config.transcript.testResults.length < k
  · have hphase : config.transcript.testResults.length ≤ k := hsample.le
    have hprovisional : config.transcript.testResults.length <
        max k (rule (config.transcript.testResults.take k)).1 :=
      hsample.trans_le (Nat.le_max_left _ _)
    have hfixed : config.transcript.testResults.length < Q := by
      rw [hQdef]
      exact hsample.trans_le (Nat.le_max_left _ _)
    simp [adaptiveQuotaStrategy, pilotPhaseSelector, hphase,
      hprovisional, hfixed]
  · have hklen : k ≤ config.transcript.testResults.length :=
      Nat.le_of_not_gt hsample
    have hall := invariant_testResults_eq_fixed_take hgood hQ
    have hsampleEq : config.transcript.testResults.take k =
        (Online.fixedTestResults processing).take k := by
      rw [hall, List.take_take, Nat.min_eq_left hklen]
    rw [hsampleEq]
    dsimp only
    rw [← hQdef]

theorem learnedPilotQuotaStrategy_stop_of_zero
    {processing : Online.Label n → ℝ} {Q k : ℕ}
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing Q config)
    (hQ : Q ≤ n) (hzero : config.remainingWork = 0)
    (rule : PilotRule n)
    (hQdef : Q = max k
      (rule ((Online.fixedTestResults processing).take k)).1) :
    learnedPilotQuotaStrategy n k rule config.transcript = none := by
  rw [learnedPilotQuotaStrategy_eq_fixed_of_invariant
    hgood hQ rule hQdef]
  exact adaptiveQuotaStrategy_stop_of_zero hgood hzero _

theorem learnedPilotQuotaStrategy_progress
    {processing : Online.Label n → ℝ} {Q k : ℕ}
    {config : Online.Config n}
    (hgood : QuotaStrategy.Config.Invariant processing Q config)
    (hQ : Q ≤ n) (hpos : 0 < config.remainingWork)
    (u : ℝ) (rule : PilotRule n)
    (hQdef : Q = max k
      (rule ((Online.fixedTestResults processing).take k)).1) :
    StrictAdaptiveWorkStep u processing Q
      (learnedPilotQuotaStrategy n k rule) config := by
  unfold StrictAdaptiveWorkStep
  rw [learnedPilotQuotaStrategy_eq_fixed_of_invariant
    hgood hQ rule hQdef]
  exact adaptiveQuotaStrategy_progress hQ hgood hpos u _

theorem runFuel_learnedPilotQuotaStrategy_completed
    {processing : Online.Label n → ℝ} {Q k : ℕ}
    (hQ : Q ≤ n) (u : ℝ) (rule : PilotRule n)
    (hQdef : Q = max k
      (rule ((Online.fixedTestResults processing).take k)).1)
    (fuel : ℕ) (config : Online.Config n)
    (hgood : QuotaStrategy.Config.Invariant processing Q config)
    (hfuel : config.remainingWork < fuel) :
    let result := Online.runFuel (.finite u) (Online.fixedOracle processing)
      (learnedPilotQuotaStrategy n k rule) fuel config
    result.reason = .strategyStopped ∧
      QuotaStrategy.Config.Invariant processing Q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  induction fuel generalizing config with
  | zero => omega
  | succ fuel ih =>
      by_cases hzero : config.remainingWork = 0
      · have hstop := learnedPilotQuotaStrategy_stop_of_zero
          hgood hQ hzero rule hQdef
        simp only [Online.runFuel, hstop]
        exact ⟨trivial, hgood,
          (Online.Config.remainingWork_eq_zero_iff config).mp hzero⟩
      · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
        obtain ⟨action, next, hchosen, hlegal, hnextGood, hdec⟩ :=
          learnedPilotQuotaStrategy_progress hgood hQ hpos u rule hQdef
        simp only [Online.runFuel, hchosen, hlegal]
        apply ih next hnextGood
        omega

theorem learnedPilotQuotaStrategy_completes
    {n k : ℕ} (hk : k ≤ n) (u : ℝ)
    (processing : Fin n → ℝ) (rule : PilotRule n)
    (hrule : (rule ((Online.fixedTestResults processing).take k)).1 ≤ n) :
    let Q := max k
      (rule ((Online.fixedTestResults processing).take k)).1
    let result := Online.run (.finite u) (Online.fixedOracle processing)
      (learnedPilotQuotaStrategy n k rule) (2 * n + 1)
    result.reason = .strategyStopped ∧
      QuotaStrategy.Config.Invariant processing Q result.config ∧
      ∀ job, result.config.jobs job = .done := by
  let Q := max k (rule ((Online.fixedTestResults processing).take k)).1
  have hQ : Q ≤ n := max_le hk hrule
  unfold Online.run
  apply runFuel_learnedPilotQuotaStrategy_completed hQ u rule rfl
  · exact QuotaStrategy.Config.initial_invariant processing Q
  · rw [Online.Config.initial_remainingWork]
    omega

/-! ## Histogram learner -/

def resultHistogram
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (category : ℝ → Option ι)
    (results : List (Online.Label n × ℝ)) : Option ι → ℝ := fun cell =>
  ((results.filter fun result => category result.2 = cell).length : ℝ) / k

def gridPilotRule
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (category : ℝ → Option ι) (price : ι → ℝ) (u : ℝ) :
    PilotRule n := fun results =>
  let T := InstanceLearning.minimizingTemplate (n := n)
    (resultHistogram k category results) price u
  (T.quota.val, templateLowSelector price T)

theorem gridPilotRule_quota_le
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (category : ℝ → Option ι) (price : ι → ℝ) (u : ℝ)
    (results : List (Online.Label n × ℝ)) :
    (gridPilotRule k category price u results).1 ≤ n := by
  exact InstanceLearning.Template.quota_le _

theorem learnedGridPilotQuotaStrategy_completes
    {n k : ℕ} (hk : k ≤ n) (u : ℝ)
    (processing : Fin n → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (category : ℝ → Option ι) (price : ι → ℝ) :
    ∀ job,
      (Online.run (.finite u) (Online.fixedOracle processing)
        (learnedPilotQuotaStrategy n k
          (gridPilotRule k category price u))
        (2 * n + 1)).config.jobs job = .done := by
  exact (learnedPilotQuotaStrategy_completes hk u processing
    (gridPilotRule k category price u)
    (gridPilotRule_quota_le k category price u _)).2.2

end

end LearnedPilot
end RevealingOptimization
end SchedulingPaper
