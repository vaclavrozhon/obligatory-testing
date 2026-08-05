import SchedulingPaper.LowBaseline

/-!
# Global cost interface for the hidden-stopping oracle

This file removes fuel management and semantic termination from the remaining
hidden-stopping premise.  The universal work rank proves that the adaptive
experiment is settled at the fixed fuel `2n+1`; replay transfers that fact
from the ordinary fixed-oracle run.

Consequently the only remaining global premise is a finite cost inequality
for a *completed* result.  An equivalent formulation splits this one premise
into the crossed and no-crossing branches of the explicit stopping line.
The final section records the two literal objectives of that premise:
completion cost of the public transcript and the unordered-pair formula for
the offline optimum of the frozen binary vector.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

open HiddenStoppingOracle

/-! ## Fixed fuel and the terminal dichotomy -/

/-- The explicit adaptive hidden-stopping experiment is always semantically
settled at the universal analysis fuel. -/
theorem hiddenStopping_analysisFuel_settled
    {n : ℕ} (u α : ℝ) (strategy : Online.Strategy n) :
    let fuel := 2 * n + 1
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u α) strategy fuel).result
    resultSettled result := by
  dsimp only
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (oracle n u α) strategy (fun _ => 0) (2 * n + 1)
  have hfixed :
      (Online.run (.finite u) (Online.fixedOracle frozen)
        strategy (2 * n + 1)).reason ≠ .outOfFuel :=
    Online.run_reason_ne_outOfFuel_analysisFuel
      (.finite u) (Online.fixedOracle frozen) strategy
  have hreplay :
      Online.run (.finite u) (Online.fixedOracle frozen)
          strategy (2 * n + 1) =
        (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy (2 * n + 1)).result := by
    simpa [frozen] using
      replay_fixed_binary u α strategy (2 * n + 1)
  unfold resultSettled
  rw [← hreplay]
  exact hfixed

/-- At analysis fuel there are exactly three semantically relevant cases:
incomplete, completed below the stopping line, or completed after crossing.
Fuel exhaustion is excluded independently of this case split. -/
theorem hiddenStopping_terminal_crossing_dichotomy
    {n : ℕ} (u α : ℝ) (strategy : Online.Strategy n) :
    let fuel := 2 * n + 1
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u α) strategy fuel).result
    resultSettled result ∧
      (¬ resultCompleted result ∨
        (resultCompleted result ∧
          ¬ Crossed n u α result.config.transcript) ∨
        (resultCompleted result ∧
          Crossed n u α result.config.transcript)) := by
  dsimp only
  refine ⟨hiddenStopping_analysisFuel_settled u α strategy, ?_⟩
  by_cases hcompleted :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy (2 * n + 1)).result
  · by_cases hcross :
        Crossed n u α
          (Online.adaptiveRun (.finite u)
            (oracle n u α) strategy
              (2 * n + 1)).result.config.transcript
    · exact Or.inr (Or.inr ⟨hcompleted, hcross⟩)
    · exact Or.inr (Or.inl ⟨hcompleted, hcross⟩)
  · exact Or.inl hcompleted

/-! ## The exact remaining completed-run premise -/

/-- The trace-global statement still needed after termination has been
discharged: only completed executions must satisfy the finite cost estimate.
The oracle, default, result, frozen input, and fuel are all fixed here. -/
def HiddenStoppingCompletedCostEstimate
    (u ratio : ℝ) (certificate : BinaryStoppingCertificate u ratio)
    (remainder : ℝ) : Prop :=
  ∀ n (strategy : Online.Strategy n),
    let fuel := 2 * n + 1
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u certificate.alpha)
        strategy (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u certificate.alpha) strategy fuel).result
    resultCompleted result →
      ratio * vectorOfflineCost (.finite u) frozen ≤
        Online.runCompletionCost (.finite u) frozen result +
          remainder * n

/-- The same remaining premise, explicitly separated into the no-crossing
and crossed branches.  This is the natural target for the two scheduling
exchange arguments. -/
def HiddenStoppingCrossingCostEstimate
    (u ratio : ℝ) (certificate : BinaryStoppingCertificate u ratio)
    (remainder : ℝ) : Prop :=
  ∀ n (strategy : Online.Strategy n),
    let fuel := 2 * n + 1
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u certificate.alpha)
        strategy (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u certificate.alpha) strategy fuel).result
    resultCompleted result →
      (¬ Crossed n u certificate.alpha result.config.transcript →
        ratio * vectorOfflineCost (.finite u) frozen ≤
          Online.runCompletionCost (.finite u) frozen result +
            remainder * n) ∧
      (Crossed n u certificate.alpha result.config.transcript →
        ratio * vectorOfflineCost (.finite u) frozen ≤
          Online.runCompletionCost (.finite u) frozen result +
            remainder * n)

theorem hiddenStoppingCompletedCostEstimate_iff_crossing
    {u ratio remainder : ℝ}
    {certificate : BinaryStoppingCertificate u ratio} :
    HiddenStoppingCompletedCostEstimate u ratio certificate remainder ↔
      HiddenStoppingCrossingCostEstimate
        u ratio certificate remainder := by
  constructor
  · intro hcost n strategy
    dsimp only
    intro hcompleted
    exact
      ⟨fun _ => hcost n strategy hcompleted,
        fun _ => hcost n strategy hcompleted⟩
  · intro hcost n strategy
    dsimp only
    intro hcompleted
    have hbranches := hcost n strategy hcompleted
    by_cases hcross :
        Crossed n u certificate.alpha
          (Online.adaptiveRun (.finite u)
            (oracle n u certificate.alpha) strategy
              (2 * n + 1)).result.config.transcript
    · exact hbranches.2 hcross
    · exact hbranches.1 hcross

/-- A size-independent remainder for the completed-run estimate. -/
def HiddenStoppingCompletedCostBridge : Prop :=
  ∀ {u ratio : ℝ} (_hu : 1 < u)
      (certificate : BinaryStoppingCertificate u ratio),
    ∃ remainder : ℝ, 0 ≤ remainder ∧
      HiddenStoppingCompletedCostEstimate
        u ratio certificate remainder

/-- This is the promised narrowing of `HiddenStoppingFiniteCostBridge`:
fixed analysis fuel plus the work-rank/replay theorem handle settledness and
the incomplete branch automatically. -/
theorem hiddenStoppingFiniteCostBridge_of_completedCost
    (bridge : HiddenStoppingCompletedCostBridge) :
    HiddenStoppingFiniteCostBridge := by
  intro u ratio hu certificate
  obtain ⟨remainder, hrem, hcost⟩ := bridge hu certificate
  refine ⟨remainder, hrem, ?_⟩
  intro n strategy
  let fuel := 2 * n + 1
  refine ⟨fuel, ?_⟩
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (oracle n u certificate.alpha)
      strategy (fun _ => 0) fuel
  let result :=
    (Online.adaptiveRun (.finite u)
      (oracle n u certificate.alpha) strategy fuel).result
  change
    resultSettled result ∧
      (¬ resultCompleted result ∨
        ratio * vectorOfflineCost (.finite u) frozen ≤
          Online.runCompletionCost (.finite u) frozen result +
            remainder * n)
  have hsettled : resultSettled result := by
    simpa [result, fuel] using
      hiddenStopping_analysisFuel_settled
        u certificate.alpha strategy
  refine ⟨hsettled, ?_⟩
  by_cases hcompleted : resultCompleted result
  · exact Or.inr (hcost n strategy hcompleted)
  · exact Or.inl hcompleted

/-! ## Literal completion and offline pair objectives -/

/-- Removing the canonical sort from the offline objective leaves the exact
unordered-pair functional, with no relaxation. -/
theorem vectorOfflineCost_eq_pairCost
    (cap : Cap) (processingTime : Online.Label n → ℝ) :
    vectorOfflineCost cap processingTime =
      pairCost (vectorEffectiveLengths cap processingTime) := by
  exact shortestFirst_pair_formula _

/-- For `u ≥ 1`, every effective length in the frozen hidden-stopping input
is literally either `1` (a zero job) or `u` (a long job). -/
theorem hiddenStopping_frozen_effectiveLength_binary
    {n : ℕ} {u : ℝ} (hu : 1 ≤ u) (α : ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (job : Online.Label n) :
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u α) strategy (fun _ => 0) fuel
    effectiveLength (.finite u) (frozen job) = 1 ∨
      effectiveLength (.finite u) (frozen job) = u := by
  dsimp only
  rcases frozenProcessingTimes_binary n u α strategy fuel job with
    hzero | hlong
  · left
    rw [hzero]
    simp [effectiveLength, min_eq_right hu]
  · right
    rw [hlong]
    simp only [effectiveLength_finite]
    exact min_eq_left (by linarith)

/-- Both objectives appearing in the completed cost premise are now literal:
the online side is `completionCost` of the observed trace, and the offline
side is the symmetric pair objective of its binary effective-length vector. -/
theorem hiddenStopping_literal_cost_objectives
    {n : ℕ} (u α : ℝ) (strategy : Online.Strategy n) (fuel : ℕ) :
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u α) strategy (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u α) strategy fuel).result
    Online.runCompletionCost (.finite u) frozen result =
        Online.completionCost (.finite u) frozen
          result.config.transcript ∧
      vectorOfflineCost (.finite u) frozen =
        pairCost (vectorEffectiveLengths (.finite u) frozen) := by
  dsimp only
  exact ⟨rfl, vectorOfflineCost_eq_pairCost _ _⟩

end LowerBound

end

end SchedulingPaper
