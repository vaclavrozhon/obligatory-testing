import SchedulingPaper.TestProcessRuntimeAccounting
import SchedulingPaper.UTEPairAccounting
import Mathlib.Tactic

/-!
# A fixed UTE pair word extracted from an operational transcript

The three chronological pair shapes, together with the special completion
semantics of zero-length jobs, determine a UTE pair symbol for every ordered
label pair.  This file evaluates the literal transcript charges against that
fixed word.
-/

namespace SchedulingPaper

noncomputable section

namespace Online

/-- Pair symbol selected by a completed canonical transcript.  Zero values
are treated by their actual completion observation (the test), independently
of the later administrative process observation. -/
def transcriptUTEPairSymbol
    (processingTime : Label n → ℝ) (transcript : Transcript n)
    (left right : Label n) : UTEPairSymbol :=
  if processingTime left = 0 then
    .leftAfterOneTest
  else if transcript.pairProjection left right =
      [.testResult left (processingTime left),
        .processed left,
        .testResult right (processingTime right),
        .processed right] then
    .leftAfterOneTest
  else if processingTime right = 0 then
    .rightAfterTwoTests
  else if transcript.pairProjection left right =
      [.testResult left (processingTime left),
        .testResult right (processingTime right),
        .processed left, .processed right] then
    .leftAfterTwoTests
  else
    .rightAfterTwoTests

def transcriptUTEFixedSymbolicWord
    (processingTime : Label n → ℝ) (transcript : Transcript n) :
    UTEFixedSymbolicWord n where
  pairSymbol :=
    transcriptUTEPairSymbol processingTime transcript

private theorem tracePairCharge_of_projection
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n)
    (hne : left ≠ right)
    (projection : Transcript n)
    (hprojection :
      transcript.pairProjection left right = projection) :
    tracePairCharge cap processingTime transcript left right =
      ownedDurationUntilCompletion cap processingTime
          left right projection +
        ownedDurationUntilCompletion cap processingTime
          right left projection := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl),
    hprojection]

/-- On any completed canonical test/process trace, its literal pair charge
is exactly the charge selected by the extracted fixed UTE word. -/
theorem TestProcessTrace.tracePairCharge_eq_uteFixedALGPairCharge
    {processingTime : Label n → ℝ}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed :
      ∀ job, job ∈ transcript.processedLabels)
    (cap : Cap) {left right : Label n} (horder : left < right) :
    tracePairCharge cap processingTime transcript left right =
      uteFixedALGPairCharge
        (transcriptUTEPairSymbol processingTime transcript left right)
        (processingTime left) (processingTime right) := by
  have hne : left ≠ right := ne_of_lt horder
  have hne' : right ≠ left := Ne.symm hne
  rcases htrace.terminal_pairProjection_shapes
      hmatch hallTests hallProcessed horder with
    hshape | hshape | hshape
  · rw [tracePairCharge_eq_leftAfterOneTest cap processingTime
      transcript left right (processingTime left)
      (processingTime right) hshape hne rfl rfl]
    simp [transcriptUTEPairSymbol, hshape,
      uteFixedALGPairCharge]
  · rw [tracePairCharge_of_projection cap processingTime
      transcript left right hne _ hshape]
    by_cases hp : processingTime left = 0 <;>
      by_cases hq : processingTime right = 0
    all_goals
      simp [ownedDurationUntilCompletion,
        Observation.ownerLabel, Observation.duration,
        Observation.completionLabel,
        transcriptUTEPairSymbol, hshape, hp, hq,
        uteFixedALGPairCharge, hne, hne'] <;>
      ring
  · rw [tracePairCharge_of_projection cap processingTime
      transcript left right hne _ hshape]
    by_cases hp : processingTime left = 0 <;>
      by_cases hq : processingTime right = 0
    all_goals
      simp [ownedDurationUntilCompletion,
        Observation.ownerLabel, Observation.duration,
        Observation.completionLabel,
        transcriptUTEPairSymbol, hshape, hp, hq,
        uteFixedALGPairCharge, hne, hne'] <;>
      ring

end Online

/-- Diagonal-plus-pair online value of a fixed UTE word. -/
def uteFixedWordALG {n : ℕ}
    (word : UTEFixedSymbolicWord n)
    (processing : Fin n → ℝ) : ℝ :=
  Finset.univ.sum
      (fun i : Fin n => (1 : ℝ) + processing i) +
    Finset.univ.sum (fun i : Fin n =>
      (Finset.univ.filter (fun j : Fin n => i < j)).sum
        (fun j =>
          uteFixedALGPairCharge
            (word.pairSymbol i j) (processing i) (processing j)))

namespace Online

/-- Exact equality between the cost of a completed ForcedPrefixUTE
execution and its extracted fixed-word online objective. -/
theorem run_forcedPrefixUTEStrategy_completionCost_eq_uteFixedWordALG
    (n : ℕ) (u b : ℝ) (cap : Cap)
    (processingTime : Label n → ℝ) :
    let result :=
      run cap (fixedOracle processingTime)
        (forcedPrefixUTEStrategy n u b) (2 * n + 1)
    runCompletionCost cap processingTime result =
      uteFixedWordALG
        (transcriptUTEFixedSymbolicWord processingTime
          result.config.transcript)
        processingTime := by
  dsimp only
  let result :=
    run cap (fixedOracle processingTime)
      (forcedPrefixUTEStrategy n u b) (2 * n + 1)
  have hrun :=
    run_forcedPrefixUTEStrategy_canonicalTrace
      n u b cap processingTime
  have hallTests :
      result.config.transcript.testResults.length = n :=
    hrun.2.1.testResults_length_eq hrun.2.2.2.2.2
  have hallProcessed :
      ∀ job, job ∈ result.config.transcript.processedLabels := by
    intro job
    rw [← hrun.2.1.done_iff job]
    exact hrun.2.2.2.2.2 job
  rw [run_forcedPrefixUTEStrategy_completionCost_eq_self_add_pairs]
  unfold uteFixedWordALG transcriptUTEFixedSymbolicWord
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro left _hleft
    apply Finset.sum_congr rfl
    intro right hright
    have horder :
        left < right :=
      (Finset.mem_filter.mp hright).2
    exact
      hrun.2.2.2.2.1.tracePairCharge_eq_uteFixedALGPairCharge
        hrun.2.2.1 hallTests hallProcessed cap horder

end Online

end

end SchedulingPaper
