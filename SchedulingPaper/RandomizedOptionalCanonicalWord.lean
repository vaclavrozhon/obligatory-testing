import SchedulingPaper.RandomizedOptionalObservedPairAccounting
import Mathlib.Tactic

/-!
# The canonical four-block operation word

This file gives one- and two-label specifications of the canonical schedule.
The word will be used as the target of the operational trace projection.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

open Randomized

noncomputable section

def canonicalHigh (low medium : ℝ → Bool) (x : ℝ) : Bool :=
  !low x && !medium x

def canonicalTested {n : ℕ} (q : ℕ) (job : Label n) : Bool :=
  decide (job.val < q)

def canonicalTestLowWord
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low : ℝ → Bool) (job : Label n) : Transcript n :=
  if job.val < q then
    [.testResult job (processing job)] ++
      if low (processing job) then [.processed job] else []
  else []

def canonicalMediumEligible
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (job : Label n) : Bool :=
  decide (job.val < q) && !low (processing job) && medium (processing job)

def canonicalHighEligible
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (job : Label n) : Bool :=
  decide (job.val < q) && !low (processing job) && !medium (processing job)

def canonicalBlindWord
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (job : Label n) : Transcript n :=
  if q ≤ job.val then [.blindCompleted job (processing job)] else []

def canonicalProcessPair
    {n : ℕ} (processing : Label n → ℝ)
    (eligible : Label n → Bool) (first second : Label n) : Transcript n :=
  if eligible first then
    if eligible second then
      if processing first ≤ processing second then
        [.processed first, .processed second]
      else [.processed second, .processed first]
    else [.processed first]
  else if eligible second then [.processed second] else []

def canonicalPairWordOrdered
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (first second : Label n) : Transcript n :=
  canonicalTestLowWord q processing low first ++
  canonicalTestLowWord q processing low second ++
  canonicalProcessPair processing
    (canonicalMediumEligible q processing low medium) first second ++
  canonicalBlindWord q processing first ++
  canonicalBlindWord q processing second ++
  canonicalProcessPair processing
    (canonicalHighEligible q processing low medium) first second

def canonicalPairWord
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (left right : Label n) : Transcript n :=
  if left.val < right.val then
    canonicalPairWordOrdered q processing low medium left right
  else canonicalPairWordOrdered q processing low medium right left

theorem canonicalPairWord_comm
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {left right : Label n}
    (hne : left ≠ right) :
    canonicalPairWord q processing low medium left right =
      canonicalPairWord q processing low medium right left := by
  have hval : left.val ≠ right.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · simp [canonicalPairWord, hlt, not_lt_of_ge hlt.le]
  · simp [canonicalPairWord, hgt, not_lt_of_ge hgt.le]

def canonicalSelfWord
    {n : ℕ} (q : ℕ) (processing : Label n → ℝ)
    (job : Label n) : Transcript n :=
  if job.val < q then
    [.testResult job (processing job), .processed job]
  else [.blindCompleted job (processing job)]

theorem ownedDuration_canonicalSelfWord
    {n q : ℕ} (processing : Label n → ℝ) (job : Label n) :
    ownedDurationUntilCompletion processing job job
        (canonicalSelfWord q processing job) =
      if job.val < q then 1 + processing job else processing job := by
  by_cases ht : job.val < q <;>
    by_cases hp : processing job = 0 <;>
      simp [canonicalSelfWord, ht, hp, ownedDurationUntilCompletion,
        Observation.ownerLabel, Observation.actualDuration,
        Observation.completionLabel]

theorem canonicalSingleKernel_eq_selfWord
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (i : Fin n) :
    canonicalSingleKernel q processing low medium (canonicalHigh low medium)
        i i =
      ownedDurationUntilCompletion processing i i
        (canonicalSelfWord q processing i) := by
  by_cases ht : i.val < q
  · rw [ownedDuration_canonicalSelfWord]
    simp only [if_pos ht]
    cases hlow : low (processing i) with
    | false =>
        cases hmedium : medium (processing i) <;>
          simp [canonicalSingleKernel, testedPosition, ht, canonicalHigh,
            boolWeight, hlow, hmedium] <;> ring
    | true =>
        have hmedium := hdisjoint (processing i) hlow
        simp [canonicalSingleKernel, testedPosition, ht, canonicalHigh,
          boolWeight, hlow, hmedium]
  · rw [ownedDuration_canonicalSelfWord]
    simp [canonicalSingleKernel, testedPosition, ht]

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
