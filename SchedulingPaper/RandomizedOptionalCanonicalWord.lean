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

/-- The ordered two-label specification contains exactly the two lifecycle
words, merely interleaved according to the four canonical phases. -/
theorem canonicalPairWordOrdered_perm_self_append
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n} (hij : i.val < j.val) :
    (canonicalPairWordOrdered q processing low medium i j).Perm
      (canonicalSelfWord q processing i ++ canonicalSelfWord q processing j) := by
  classical
  rw [List.perm_iff_count]
  intro observation
  by_cases hti : i.val < q
  · have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
    by_cases htj : j.val < q
    · have hqj : ¬q ≤ j.val := Nat.not_le_of_lt htj
      cases hli : low (processing i) <;> cases hmi : medium (processing i) <;>
      cases hlj : low (processing j) <;> cases hmj : medium (processing j) <;>
      simp [canonicalPairWordOrdered, canonicalTestLowWord, canonicalProcessPair,
        canonicalMediumEligible, canonicalHighEligible, canonicalBlindWord,
        canonicalSelfWord, hti, htj, hqi, hqj, hli, hmi, hlj, hmj,
        List.count_cons, List.count_nil] <;> (try split) <;>
        simp_all [List.count_cons, List.count_nil] <;> try ac_rfl
    · have hqj : q ≤ j.val := Nat.le_of_not_gt htj
      cases hli : low (processing i) <;> cases hmi : medium (processing i) <;>
      cases hlj : low (processing j) <;> cases hmj : medium (processing j) <;>
      simp [canonicalPairWordOrdered, canonicalTestLowWord, canonicalProcessPair,
        canonicalMediumEligible, canonicalHighEligible, canonicalBlindWord,
        canonicalSelfWord, hti, htj, hqi, hqj, hli, hmi, hlj, hmj,
        List.count_cons, List.count_nil] <;> (try split) <;>
        simp_all [List.count_cons, List.count_nil] <;> try ac_rfl
  · have hqi : q ≤ i.val := Nat.le_of_not_gt hti
    have htj : ¬j.val < q := by omega
    have hqj : q ≤ j.val := by omega
    simp [canonicalPairWordOrdered, canonicalTestLowWord, canonicalProcessPair,
      canonicalMediumEligible, canonicalHighEligible, canonicalBlindWord,
      canonicalSelfWord, hti, htj, hqi, hqj]

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

def pairChargeAutomaton
    {n : ℕ} (processing : Label n → ℝ) (left right : Label n) :
    Bool → Bool → Transcript n → ℝ
  | _, _, [] => 0
  | leftActive, rightActive, observation :: rest =>
      (if rightActive && observation.ownerLabel = left then
          observation.actualDuration processing else 0) +
        (if leftActive && observation.ownerLabel = right then
          observation.actualDuration processing else 0) +
        pairChargeAutomaton processing left right
          (leftActive &&
            observation.completionLabel processing ≠ some left)
          (rightActive &&
            observation.completionLabel processing ≠ some right) rest

@[simp] theorem pairChargeAutomaton_false_false
    {n : ℕ} (processing : Label n → ℝ) (left right : Label n)
    (transcript : Transcript n) :
    pairChargeAutomaton processing left right false false transcript = 0 := by
  induction transcript with
  | nil => rfl
  | cons observation rest tail_ih =>
      simpa [pairChargeAutomaton] using tail_ih

/-- The two-active-state automaton is the symmetric pair charge.  This
forward formulation avoids repeatedly reducing two recursive scans of a
symbolic transcript. -/
theorem pairChargeAutomaton_eq
    {n : ℕ} (processing : Label n → ℝ) {left right : Label n}
    (hne : left ≠ right) (leftActive rightActive : Bool)
    (transcript : Transcript n) :
    pairChargeAutomaton processing left right leftActive rightActive transcript =
      (if leftActive then
        observedTraceOrientedCharge processing transcript right left else 0) +
      (if rightActive then
        observedTraceOrientedCharge processing transcript left right else 0) := by
  induction transcript generalizing leftActive rightActive with
  | nil => simp [pairChargeAutomaton, observedTraceOrientedCharge,
      ownedDurationUntilCompletion]
  | cons observation rest ih =>
      cases leftActive <;> cases rightActive <;> cases observation <;>
        simp [pairChargeAutomaton, observedTraceOrientedCharge,
          ownedDurationUntilCompletion, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hne, Ne.symm hne, ih] <;>
        split <;> simp_all [ih] <;> aesop <;> ring

/-- Pair-kernel/word identity after the testing quota, when both labels are
blind.  This is the first of the three quota-position blocks. -/
theorem canonicalPairKernel_symm_eq_pairAutomaton_blind_blind
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n}
    (hij : i.val < j.val) (hqi : q ≤ i.val) :
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(i, j), Fin.ne_of_lt hij⟩ i j +
      canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(j, i), Ne.symm (Fin.ne_of_lt hij)⟩ j i =
      pairChargeAutomaton processing i j true true
        (canonicalPairWordOrdered q processing low medium i j) := by
  have hqj : q ≤ j.val := le_trans hqi hij.le
  have hti : ¬i.val < q := Nat.not_lt_of_ge hqi
  have htj : ¬j.val < q := Nat.not_lt_of_ge hqj
  have hfin : i < j := hij
  have hne : i ≠ j := ne_of_lt hfin
  have hne' : j ≠ i := Ne.symm hne
  have hjfin : ¬j < i := not_lt_of_ge hfin.le
  simp [canonicalPairKernel, canonicalHigh, testedPosition,
    beforePosition, canonicalPairWordOrdered, canonicalTestLowWord,
    canonicalProcessPair, canonicalMediumEligible, canonicalHighEligible,
    canonicalBlindWord, boolWeight, pairChargeAutomaton,
    Observation.ownerLabel, Observation.actualDuration,
    Observation.completionLabel, hti, htj, hqi, hqj, hfin, hjfin,
    hne, hne']

private theorem canonicalClass_cases (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false) (x : ℝ) :
    (low x = true ∧ medium x = false) ∨
      (low x = false ∧ medium x = true) ∨
      (low x = false ∧ medium x = false) := by
  cases hl : low x <;> cases hm : medium x <;> simp_all

theorem canonicalPairWordOrdered_tested_blind
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n}
    (hti : i.val < q) (hqj : q ≤ j.val) :
    canonicalPairWordOrdered q processing low medium i j =
      [.testResult i (processing i)] ++
        (if low (processing i) then [.processed i] else []) ++
        (if !low (processing i) && medium (processing i) then
          [.processed i] else []) ++
        [.blindCompleted j (processing j)] ++
        (if !low (processing i) && !medium (processing i) then
          [.processed i] else []) := by
  have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
  have htj : ¬j.val < q := Nat.not_lt_of_ge hqj
  simp [canonicalPairWordOrdered, canonicalTestLowWord,
    canonicalProcessPair, canonicalMediumEligible, canonicalHighEligible,
    canonicalBlindWord, hti, htj, hqi, hqj]

/-- Pair-kernel/word identity across the quota boundary. -/
theorem canonicalPairKernel_symm_eq_pairAutomaton_tested_blind
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true)
    {i j : Fin n} (hij : i.val < j.val)
    (hti : i.val < q) (hqj : q ≤ j.val) :
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(i, j), Fin.ne_of_lt hij⟩ i j +
      canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(j, i), Ne.symm (Fin.ne_of_lt hij)⟩ j i =
      pairChargeAutomaton processing i j true true
        (canonicalPairWordOrdered q processing low medium i j) := by
  have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
  have htj : ¬j.val < q := Nat.not_lt_of_ge hqj
  have hfin : i < j := hij
  have hne : i ≠ j := ne_of_lt hfin
  have hne' : j ≠ i := Ne.symm hne
  have hjfin : ¬j < i := not_lt_of_ge hfin.le
  rw [canonicalPairWordOrdered_tested_blind processing low medium hti hqj]
  rcases canonicalClass_cases low medium hdisjoint (processing i) with
      ⟨hli, hmi⟩ | ⟨hli, hmi⟩ | ⟨hli, hmi⟩
  · by_cases hpzi : processing i = 0
    · have hl0 : low 0 = true := by simpa [hpzi] using hli
      simp [canonicalPairKernel, canonicalHigh, testedPosition,
        beforePosition, boolWeight, pairChargeAutomaton,
        Observation.ownerLabel, Observation.actualDuration,
        Observation.completionLabel, hti, htj, hqi, hqj, hfin, hjfin,
        hne, hne', hli, hmi, hpzi, hl0]
    · simp [canonicalPairKernel, canonicalHigh, testedPosition,
        beforePosition, boolWeight, pairChargeAutomaton,
        Observation.ownerLabel, Observation.actualDuration,
        Observation.completionLabel, hti, htj, hqi, hqj, hfin, hjfin,
        hne, hne', hli, hmi, hpzi] <;> ring
  · have hpzi : processing i ≠ 0 := by
      intro hz
      rw [hzeroLow i hz] at hli
      contradiction
    simp [canonicalPairKernel, canonicalHigh, testedPosition,
      beforePosition, boolWeight, pairChargeAutomaton,
      Observation.ownerLabel, Observation.actualDuration,
      Observation.completionLabel, hti, htj, hqi, hqj, hfin, hjfin,
      hne, hne', hli, hmi, hpzi] <;> ring
  · have hpzi : processing i ≠ 0 := by
      intro hz
      rw [hzeroLow i hz] at hli
      contradiction
    simp [canonicalPairKernel, canonicalHigh, testedPosition,
      beforePosition, boolWeight, pairChargeAutomaton,
      Observation.ownerLabel, Observation.actualDuration,
      Observation.completionLabel, hti, htj, hqi, hqj, hfin, hjfin,
      hne, hne', hli, hmi, hpzi] <;> ring

theorem canonicalPairWordOrdered_tested_tested
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool) {i j : Fin n}
    (hti : i.val < q) (htj : j.val < q) :
    canonicalPairWordOrdered q processing low medium i j =
      [.testResult i (processing i)] ++
        (if low (processing i) then [.processed i] else []) ++
        [.testResult j (processing j)] ++
        (if low (processing j) then [.processed j] else []) ++
        canonicalProcessPair processing
          (canonicalMediumEligible q processing low medium) i j ++
        canonicalProcessPair processing
          (canonicalHighEligible q processing low medium) i j := by
  have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
  have hqj : ¬q ≤ j.val := Nat.not_le_of_lt htj
  simp [canonicalPairWordOrdered, canonicalTestLowWord,
    canonicalBlindWord, hti, htj, hqi, hqj]

/-- Pair-kernel/word identity inside the testing quota.  The class split is
finite; the only remaining order decision is SPT inside one residual block. -/
theorem canonicalPairKernel_symm_eq_pairAutomaton_tested_tested
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true)
    {i j : Fin n} (hij : i.val < j.val)
    (hti : i.val < q) (htj : j.val < q) :
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(i, j), Fin.ne_of_lt hij⟩ i j +
      canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(j, i), Ne.symm (Fin.ne_of_lt hij)⟩ j i =
      pairChargeAutomaton processing i j true true
        (canonicalPairWordOrdered q processing low medium i j) := by
  have hqi : ¬q ≤ i.val := Nat.not_le_of_lt hti
  have hqj : ¬q ≤ j.val := Nat.not_le_of_lt htj
  have hfin : i < j := hij
  have hne : i ≠ j := ne_of_lt hfin
  have hne' : j ≠ i := Ne.symm hne
  have hjfin : ¬j < i := not_lt_of_ge hfin.le
  rw [canonicalPairWordOrdered_tested_tested processing low medium hti htj]
  rcases canonicalClass_cases low medium hdisjoint (processing i) with
      hiL | hiM | hiH
  · rcases canonicalClass_cases low medium hdisjoint (processing j) with
        hjL | hjM | hjH
    · rcases hiL with ⟨hli, hmi⟩
      rcases hjL with ⟨hlj, hmj⟩
      by_cases hpzi : processing i = 0 <;>
        by_cases hpzj : processing j = 0 <;>
        simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne',
          hli, hmi, hlj, hmj, hpzi, hpzj] <;> ring
    · rcases hiL with ⟨hli, hmi⟩
      rcases hjM with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      by_cases hpzi : processing i = 0 <;>
        simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne',
          hli, hmi, hlj, hmj, hpzi, hpzj] <;> ring
    · rcases hiL with ⟨hli, hmi⟩
      rcases hjH with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      by_cases hpzi : processing i = 0 <;>
        simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne',
          hli, hmi, hlj, hmj, hpzi, hpzj] <;> ring
  · rcases hiM with ⟨hli, hmi⟩
    have hpzi : processing i ≠ 0 := by
      intro hz
      rw [hzeroLow i hz] at hli
      contradiction
    rcases canonicalClass_cases low medium hdisjoint (processing j) with
        hjL | hjM | hjH
    · rcases hjL with ⟨hlj, hmj⟩
      by_cases hpzj : processing j = 0 <;>
        simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne',
          hli, hmi, hlj, hmj, hpzi, hpzj] <;> ring
    · rcases hjM with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      by_cases hpord : processing i ≤ processing j
      · simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
          hlj, hmj, hpzi, hpzj, hpord, min_eq_left] <;> ring
      · have hrev : processing j ≤ processing i := le_of_not_ge hpord
        simp [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
          hlj, hmj, hpzi, hpzj, hpord, hrev, min_eq_right] <;> ring

    · rcases hjH with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
        beforePosition, boolWeight, canonicalProcessPair,
        canonicalMediumEligible, canonicalHighEligible,
        pairChargeAutomaton, Observation.ownerLabel,
        Observation.actualDuration, Observation.completionLabel,
        hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
        hlj, hmj, hpzi, hpzj] <;> ring
  · rcases hiH with ⟨hli, hmi⟩
    have hpzi : processing i ≠ 0 := by
      intro hz
      rw [hzeroLow i hz] at hli
      contradiction
    rcases canonicalClass_cases low medium hdisjoint (processing j) with
        hjL | hjM | hjH
    · rcases hjL with ⟨hlj, hmj⟩
      by_cases hpzj : processing j = 0 <;>
        simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne',
          hli, hmi, hlj, hmj, hpzi, hpzj] <;> ring
    · rcases hjM with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
        beforePosition, boolWeight, canonicalProcessPair,
        canonicalMediumEligible, canonicalHighEligible,
        pairChargeAutomaton, Observation.ownerLabel,
        Observation.actualDuration, Observation.completionLabel,
        hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
        hlj, hmj, hpzi, hpzj] <;> ring
    · rcases hjH with ⟨hlj, hmj⟩
      have hpzj : processing j ≠ 0 := by
        intro hz
        rw [hzeroLow j hz] at hlj
        contradiction
      by_cases hpord : processing i ≤ processing j
      · simp_all [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
          hlj, hmj, hpzi, hpzj, hpord, min_eq_left] <;> ring
      · have hrev : processing j ≤ processing i := le_of_not_ge hpord
        simp [canonicalPairKernel, canonicalHigh, testedPosition,
          beforePosition, boolWeight, canonicalProcessPair,
          canonicalMediumEligible, canonicalHighEligible,
          pairChargeAutomaton, Observation.ownerLabel,
          Observation.actualDuration, Observation.completionLabel,
          hti, htj, hqi, hqj, hfin, hjfin, hne, hne', hli, hmi,
          hlj, hmj, hpzi, hpzj, hpord, hrev, min_eq_right] <;> ring

/-- The three quota-position calculations cover every ordered pair of
distinct virtual positions. -/
theorem canonicalPairKernel_symm_eq_pairAutomaton_ordered
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true)
    {i j : Fin n} (hij : i.val < j.val) :
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(i, j), Fin.ne_of_lt hij⟩ i j +
      canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(j, i), Ne.symm (Fin.ne_of_lt hij)⟩ j i =
      pairChargeAutomaton processing i j true true
        (canonicalPairWordOrdered q processing low medium i j) := by
  by_cases hti : i.val < q
  · by_cases htj : j.val < q
    · exact canonicalPairKernel_symm_eq_pairAutomaton_tested_tested
        processing low medium hdisjoint hzeroLow hij hti htj
    · exact canonicalPairKernel_symm_eq_pairAutomaton_tested_blind
        processing low medium hdisjoint hzeroLow hij hti
          (Nat.le_of_not_gt htj)
  · exact canonicalPairKernel_symm_eq_pairAutomaton_blind_blind
      processing low medium hij (Nat.le_of_not_gt hti)

/-- Equivalently, the symmetrized pair kernel is exactly the two oriented
completion charges of the canonical two-label word. -/
theorem canonicalPairKernel_symm_eq_pairWordCharges_ordered
    {n q : ℕ} (processing : Label n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true)
    {i j : Fin n} (hij : i.val < j.val) :
    canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(i, j), Fin.ne_of_lt hij⟩ i j +
      canonicalPairKernel q processing low medium (canonicalHigh low medium)
        ⟨(j, i), Ne.symm (Fin.ne_of_lt hij)⟩ j i =
      observedTraceOrientedCharge processing
          (canonicalPairWordOrdered q processing low medium i j) i j +
        observedTraceOrientedCharge processing
          (canonicalPairWordOrdered q processing low medium i j) j i := by
  rw [canonicalPairKernel_symm_eq_pairAutomaton_ordered
    processing low medium hdisjoint hzeroLow hij]
  rw [pairChargeAutomaton_eq processing (Fin.ne_of_lt hij) true true]
  simp [add_comm]

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
