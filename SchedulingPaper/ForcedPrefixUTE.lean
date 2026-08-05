import SchedulingPaper.ParameterizedAdaptiveStrategy
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Executable ForcedPrefixUTE

This is the concrete transcript-only strategy used on the two middle
finite-cap branches.  The first `⌊bn⌋` tested jobs are forced to complete
immediately; later jobs complete immediately exactly when their revealed
value is at most `min 1 (u-1)`.  Deferred jobs are processed in increasing
revealed-value order after all tests.
-/

namespace SchedulingPaper.Online

noncomputable section

def forcedPrefixCount (n : ℕ) (b : ℝ) : ℕ :=
  ⌊b * n⌋₊

def uteThreshold (u : ℝ) : ℝ := min 1 (u - 1)

def Transcript.forcedPrefixPendingImmediate?
    (n k : ℕ) (threshold : ℝ)
    (transcript : Transcript n) : Option (Label n) :=
  match transcript.getLast? with
  | some (.testResult job p) =>
      let testedBefore := transcript.testResults.dropLast.length
      if testedBefore < k ∨ p ≤ threshold then some job else none
  | some (.processed _) | some (.rawCompleted _) | none => none

/-- `ForcedPrefixUTE(J,u,b)` from the paper. -/
def forcedPrefixUTEStrategy
    (n : ℕ) (u b : ℝ) : Strategy n :=
  fun transcript =>
    let k := forcedPrefixCount n b
    let threshold := uteThreshold u
    match transcript.forcedPrefixPendingImmediate? n k threshold with
    | some job => some (.process job)
    | none =>
        let tested := transcript.testResults.length
        if h : tested < n then
          some (.test ⟨tested, h⟩)
        else
          match transcript.shortestRemaining? with
          | some job => some (.process job)
          | none => none

theorem forcedPrefixUTEStrategy_ne_raw
    (n : ℕ) (u b : ℝ) (transcript : Transcript n) (job : Label n) :
    forcedPrefixUTEStrategy n u b transcript ≠ some (.raw job) := by
  unfold forcedPrefixUTEStrategy
  dsimp only
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem forcedPrefixCount_le
    {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    forcedPrefixCount n b ≤ n := by
  unfold forcedPrefixCount
  have hnonneg : 0 ≤ b * (n : ℝ) :=
    mul_nonneg hb (Nat.cast_nonneg n)
  have hupper : b * (n : ℝ) ≤ n :=
    calc
      b * (n : ℝ) ≤ 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg n)
      _ = n := one_mul _
  exact Nat.floor_le_of_le hupper

theorem forcedPrefixCount_cast_le
    {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    (forcedPrefixCount n b : ℝ) ≤ b * n := by
  unfold forcedPrefixCount
  have hnonneg : 0 ≤ b * (n : ℝ) :=
    mul_nonneg hb (Nat.cast_nonneg n)
  exact Nat.floor_le hnonneg

theorem forcedPrefixCount_lt_add_one
    (n : ℕ) (b : ℝ) :
    b * n < forcedPrefixCount n b + 1 := by
  unfold forcedPrefixCount
  exact Nat.lt_floor_add_one _

end

end SchedulingPaper.Online
