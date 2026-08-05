import SchedulingPaper.MixedTailOperational
import Mathlib.Tactic

/-!
# Comparing the physical mixed tail with its virtual harmonic replay

The mixed oracle executes an untested tail job by one finite-cap raw
operation.  Its virtual harmonic transcript replaces that operation by a
unit test followed by processing.  This file proves that the replacement
can only decrease total completion cost whenever its total duration is at
most the cap.
-/

namespace SchedulingPaper

noncomputable section

open Online

namespace LowerBound
namespace MixedQuotaOracle

/-- Appending the same test observation preserves a simultaneous
completion-cost and elapsed-time comparison between the virtual and
physical transcripts. -/
private theorem append_testResult_dominates
    {n : ℕ} {u p : ℝ}
    (processingTime : Online.Label n → ℝ)
    (virtual physical : Online.Transcript n)
    (job : Online.Label n)
    (hcost :
      Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical)
    (htime :
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical) :
    Online.completionCost .infinite processingTime
        (virtual ++ [.testResult job p]) ≤
          Online.completionCost (.finite u) processingTime
            (physical ++ [.testResult job p]) ∧
      Online.transcriptElapsed .infinite processingTime
          (virtual ++ [.testResult job p]) ≤
        Online.transcriptElapsed (.finite u) processingTime
          (physical ++ [.testResult job p]) := by
  rw [completionCost_append_singleton,
    completionCost_append_singleton,
    transcriptElapsed_append_singleton,
    transcriptElapsed_append_singleton]
  simp only [Online.Observation.completionLabel,
    Online.Observation.duration]
  by_cases hp : p = 0
  · simp [hp]
    exact ⟨add_le_add hcost
      (add_le_add htime (le_refl 1)), htime⟩
  · simp [hp]
    exact ⟨hcost, htime⟩

/-- Appending the same tested processing observation preserves the two
comparisons. -/
private theorem append_processed_dominates
    {n : ℕ} {u : ℝ}
    (processingTime : Online.Label n → ℝ)
    (virtual physical : Online.Transcript n)
    (job : Online.Label n)
    (hcost :
      Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical)
    (htime :
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical) :
    Online.completionCost .infinite processingTime
        (virtual ++ [.processed job]) ≤
          Online.completionCost (.finite u) processingTime
            (physical ++ [.processed job]) ∧
      Online.transcriptElapsed .infinite processingTime
          (virtual ++ [.processed job]) ≤
        Online.transcriptElapsed (.finite u) processingTime
          (physical ++ [.processed job]) := by
  rw [completionCost_append_singleton,
    completionCost_append_singleton,
    transcriptElapsed_append_singleton,
    transcriptElapsed_append_singleton]
  simp only [Online.Observation.completionLabel,
    Online.Observation.duration]
  by_cases hp : processingTime job = 0
  · simp [hp]
    exact ⟨hcost, htime⟩
  · simp [hp]
    constructor
    · exact add_le_add hcost
        (add_le_add htime (le_refl (processingTime job)))
    · exact htime

/-- A physical observation which is omitted by the virtual replay can only
increase physical cost and time. -/
private theorem append_physical_dominates
    {n : ℕ} {u : ℝ}
    (processingTime : Online.Label n → ℝ)
    (virtual physical : Online.Transcript n)
    (observation : Online.Observation n)
    (hu : 0 < u)
    (hadmissible :
      ∀ job, Online.ValueAdmissible (.finite u) (processingTime job))
    (hcost :
      Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical)
    (htime :
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical) :
    Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime
          (physical ++ [observation]) ∧
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime
          (physical ++ [observation]) := by
  have hvalid : Cap.Valid (.finite u) := hu
  have helapsed :=
    Online.transcriptElapsed_nonneg hvalid hadmissible physical
  have hduration :=
    observation.duration_nonneg hvalid hadmissible
  rw [completionCost_append_singleton,
    transcriptElapsed_append_singleton]
  constructor
  · split_ifs
    · exact le_trans hcost
        (le_add_of_nonneg_right (add_nonneg helapsed hduration))
    · simpa using hcost
  · exact le_trans htime
      (le_add_of_nonneg_right hduration)

/-- The virtual test/process block for a raw completion costs no more than
the physical raw completion when `1 + p ≤ u`. -/
private theorem append_rawCompleted_dominates
    {n : ℕ} {u p : ℝ}
    (processingTime : Online.Label n → ℝ)
    (virtual physical : Online.Transcript n)
    (job : Online.Label n)
    (hprocessing : processingTime job = p)
    (hsafe : 1 + p ≤ u)
    (hcost :
      Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical)
    (htime :
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical) :
    Online.completionCost .infinite processingTime
        (virtual ++ [.testResult job p, .processed job]) ≤
          Online.completionCost (.finite u) processingTime
            (physical ++ [.rawCompleted job]) ∧
      Online.transcriptElapsed .infinite processingTime
          (virtual ++ [.testResult job p, .processed job]) ≤
        Online.transcriptElapsed (.finite u) processingTime
          (physical ++ [.rawCompleted job]) := by
  rw [show virtual ++ [.testResult job p, .processed job] =
      (virtual ++ [.testResult job p]) ++ [.processed job] by
        simp [List.append_assoc]]
  simp only [completionCost_append_singleton,
    transcriptElapsed_append_singleton,
    Online.Observation.completionLabel,
    Online.Observation.duration, Online.rawDuration]
  simp only [hprocessing]
  by_cases hpzero : p = 0
  · simp [hpzero] at hsafe ⊢
    constructor <;> linarith
  · simp [hpzero]
    constructor <;> linarith

/-- Tests already present in the virtual accumulator remain present after
folding any further physical tail. -/
private theorem virtualTailFold_preserves_test_mem_physical
    (K Z : ℕ)
    (virtual tail : Online.Transcript n)
    {job : Online.Label n} {p : ℝ}
    (hmem : (job, p) ∈ virtual.testResults) :
    (job, p) ∈
      (tail.foldl (virtualTailStep K Z) virtual).testResults := by
  induction tail generalizing virtual with
  | nil =>
      simpa using hmem
  | cons observation tail ih =>
      rw [List.foldl_cons]
      apply ih
      cases observation with
      | testResult tested q =>
          simp [virtualTailStep, hmem]
      | processed processed =>
          simp only [virtualTailStep]
          split_ifs <;> simp_all
      | rawCompleted raw =>
          simp [virtualTailStep, hmem]

/-- Accumulator-strengthened simulation theorem.  The physical transcript
may already have an arbitrary prefix; this is what lets the final theorem
retain all nonnegative cap-prefix work rather than discarding it. -/
private theorem virtualTailFold_dominates
    {n : ℕ} {u : ℝ}
    (hu : 0 < u)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job, Online.ValueAdmissible (.finite u) (processingTime job))
    (K Z : ℕ)
    (virtual physical tail : Online.Transcript n)
    (hcost :
      Online.completionCost .infinite processingTime virtual ≤
        Online.completionCost (.finite u) processingTime physical)
    (htime :
      Online.transcriptElapsed .infinite processingTime virtual ≤
        Online.transcriptElapsed (.finite u) processingTime physical)
    (hmatch :
      HarmonicMatches processingTime
        (tail.foldl (virtualTailStep K Z) virtual))
    (hsafe :
      ∀ job p,
        (job, p) ∈
          (tail.foldl (virtualTailStep K Z) virtual).testResults →
        1 + p ≤ u) :
    Online.completionCost .infinite processingTime
        (tail.foldl (virtualTailStep K Z) virtual) ≤
          Online.completionCost (.finite u) processingTime
            (physical ++ tail) ∧
      Online.transcriptElapsed .infinite processingTime
          (tail.foldl (virtualTailStep K Z) virtual) ≤
        Online.transcriptElapsed (.finite u) processingTime
          (physical ++ tail) := by
  induction tail generalizing virtual physical with
  | nil =>
      simpa using And.intro hcost htime
  | cons observation rest ih =>
      rw [List.foldl_cons] at hmatch hsafe ⊢
      have hstep :
          Online.completionCost .infinite processingTime
              (virtualTailStep K Z virtual observation) ≤
                Online.completionCost (.finite u) processingTime
                  (physical ++ [observation]) ∧
            Online.transcriptElapsed .infinite processingTime
                (virtualTailStep K Z virtual observation) ≤
              Online.transcriptElapsed (.finite u) processingTime
                (physical ++ [observation]) := by
        cases observation with
        | testResult job p =>
            simpa [virtualTailStep] using
              append_testResult_dominates
                processingTime virtual physical job hcost htime
        | processed job =>
            simp only [virtualTailStep]
            split
            next htested =>
              exact append_processed_dominates
                processingTime virtual physical job hcost htime
            next hnotTested =>
              exact append_physical_dominates
                processingTime virtual physical (.processed job)
                hu hadmissible hcost htime
        | rawCompleted job =>
            let p :=
              harmonicRankValue K Z 0 virtual.testResults.length
            have hnew :
                (job, p) ∈
                  (virtualTailStep K Z virtual
                    (.rawCompleted job)).testResults := by
              simp [virtualTailStep, p]
            have hfinal :
                (job, p) ∈
                  (rest.foldl (virtualTailStep K Z)
                    (virtualTailStep K Z virtual
                      (.rawCompleted job))).testResults :=
              virtualTailFold_preserves_test_mem_physical
                K Z _ rest hnew
            have hprocessing : processingTime job = p :=
              hmatch job p hfinal
            have hrawSafe : 1 + p ≤ u :=
              hsafe job p hfinal
            simpa [virtualTailStep, p] using
              append_rawCompleted_dominates
                processingTime virtual physical job
                hprocessing hrawSafe hcost htime
      have htail :=
        ih (virtualTailStep K Z virtual observation)
          (physical ++ [observation])
          hstep.1 hstep.2 hmatch hsafe
      simpa [List.append_assoc] using htail

/-- Generic physical/virtual comparison for a tail starting from empty
virtual state. -/
theorem virtualTailFold_completionCost_le
    {n : ℕ} {u : ℝ}
    (hu : 0 < u)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job, Online.ValueAdmissible (.finite u) (processingTime job))
    (K Z : ℕ) (tail : Online.Transcript n)
    (hmatch :
      HarmonicMatches processingTime
        (tail.foldl (virtualTailStep K Z) []))
    (hsafe :
      ∀ job p,
        (job, p) ∈
          (tail.foldl (virtualTailStep K Z) []).testResults →
        1 + p ≤ u) :
    Online.completionCost .infinite processingTime
        (tail.foldl (virtualTailStep K Z) []) ≤
      Online.completionCost (.finite u) processingTime tail := by
  have hsim :=
    virtualTailFold_dominates hu processingTime hadmissible K Z
      ([] : Online.Transcript n) ([] : Online.Transcript n) tail
      (by simp [Online.completionCost, Online.completionCostFrom])
      (by simp)
      hmatch hsafe
  simpa using hsim.1

/-- Every post-crossing physical mixed transcript dominates its virtual
harmonic tail.  The theorem is deliberately stronger than the terminal
case: no assumption on the remaining tail counters is needed. -/
theorem MixedQuotaHistory.virtualTail_completionCost_le_physical
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hu : 0 < u) (hβ : 0 < β)
    {A B H L z : ℕ}
    {caps : MixedCapPending n}
    {pending : MixedTailPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H L z caps pending) config)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job, Online.ValueAdmissible (.finite u) (processingTime job))
    (hmatch :
      MixedTailMatches processingTime
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript))
    (hsafe :
      ∀ job p,
        (job, p) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults →
        1 + p ≤ u) :
    Online.completionCost .infinite processingTime
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript) ≤
      Online.completionCost (.finite u) processingTime
        config.transcript := by
  obtain ⟨headTranscript, hdecomp⟩ :=
    history.post_tail_decomposition hn hβ
  have hvalid : Cap.Valid (.finite u) := hu
  have hheadCost :=
    Online.completionCost_nonneg hvalid hadmissible headTranscript
  have hheadTime :=
    Online.transcriptElapsed_nonneg hvalid hadmissible headTranscript
  have hsim :=
    virtualTailFold_dominates hu processingTime hadmissible
      (tailPositiveCount A B H)
      (tailZeroCount A B H)
      ([] : Online.Transcript n) headTranscript
      (scan n u β config.transcript).tail
      (by
        simpa [Online.completionCost,
          Online.completionCostFrom] using hheadCost)
      (by simpa using hheadTime)
      (by
        simpa [virtualTail] using hmatch.1)
      (by
        simpa [virtualTail] using hsafe)
  change
    Online.completionCost .infinite processingTime
        ((scan n u β config.transcript).tail.foldl
          (virtualTailStep
            (tailPositiveCount A B H)
            (tailZeroCount A B H)) []) ≤
      Online.completionCost (.finite u) processingTime
        config.transcript
  calc
    _ ≤ Online.completionCost (.finite u) processingTime
        (headTranscript ++
          (scan n u β config.transcript).tail) := hsim.1
    _ = Online.completionCost (.finite u) processingTime
        config.transcript :=
      congrArg
        (Online.completionCost (.finite u) processingTime)
        hdecomp.symm

/-- Terminal operational bridge: the generalized harmonic lower bound on
the virtual tail is a lower bound on the actual finite-cap transcript. -/
theorem MixedQuotaHistory.terminal_harmonicOnline_le_physical
    {n : ℕ} (hn : 0 < n) {u β : ℝ}
    (hu : 0 < u) (hβ : 0 < β)
    {A B H : ℕ}
    {caps : MixedCapPending n}
    {config : Online.Config n}
    (history :
      MixedQuotaHistory n u β A B
        (.post H 0 0 caps []) config)
    (hZ : 0 < tailZeroCount A B H)
    (processingTime : Online.Label n → ℝ)
    (hadmissible :
      ∀ job, Online.ValueAdmissible (.finite u) (processingTime job))
    (hmatch :
      MixedTailMatches processingTime
        (virtualTail n u β
          (tailPositiveCount A B H)
          (tailZeroCount A B H)
          config.transcript))
    (hsafe :
      ∀ job p,
        (job, p) ∈
          (virtualTail n u β
            (tailPositiveCount A B H)
            (tailZeroCount A B H)
            config.transcript).testResults →
        1 + p ≤ u) :
    harmonicFiniteOnline
        (tailPositiveCount A B H)
        (tailZeroCount A B H) 0 ≤
      Online.completionCost (.finite u) processingTime
        config.transcript := by
  have hvirtual :=
    history.post_virtual_history hn hβ
  exact le_trans
    (hvirtual.terminal_online_lower hZ processingTime hmatch)
    (history.virtualTail_completionCost_le_physical
      hn hu hβ processingTime hadmissible hmatch hsafe)

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
