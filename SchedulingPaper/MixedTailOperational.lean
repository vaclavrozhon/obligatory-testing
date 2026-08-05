import SchedulingPaper.MixedQuotaHistory
import Mathlib.Tactic

/-!
# Operational accounting for the generalized mixed harmonic tail

`MixedTailHistory` is the harmonic test/process state machine on an ambient
label type `Fin n`.  This module ports the potential argument used by
`HarmonicHistory` without imposing the definitional label equality
`n = K + Z`.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Online

namespace LowerBound
namespace MixedQuotaOracle

@[simp] theorem MixedTailPending.values_nil :
    MixedTailPending.values ([] : MixedTailPending n) = [] := rfl

@[simp] theorem MixedTailPending.values_append
    (left right : MixedTailPending n) :
    (left ++ right).values = left.values ++ right.values := by
  simp [MixedTailPending.values]

@[simp] theorem MixedTailPending.values_cons
    (entry : Online.Label n × ℝ) (rest : MixedTailPending n) :
    MixedTailPending.values (entry :: rest) =
      entry.2 :: MixedTailPending.values rest := rfl

@[simp] theorem MixedTailPending.values_length
    (pending : MixedTailPending n) :
    pending.values.length = pending.length := by
  simp [MixedTailPending.values]

/-- Every still-pending positive tail value is at least the next hidden
harmonic level. -/
theorem MixedTailHistory.pending_lower
    {K Z : ℕ} (hZ : 0 < Z)
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
    ∀ entry ∈ pending,
      harmonicLevel (Z : ℝ) 0 L ≤ entry.2 := by
  induction history with
  | initial =>
      simp
  | @testPositive L z pending transcript history hL job ih =>
      intro entry hentry
      rw [List.mem_append] at hentry
      rcases hentry with hold | hnew
      · exact
          (harmonicLevel_strictMono
            (γ := 0) (by exact_mod_cast hZ)
            (Nat.sub_lt (Nat.zero_lt_of_lt hL) (by omega))).le.trans
            (ih entry hold)
      · simp only [List.mem_singleton] at hnew
        rcases hnew with rfl
        rfl
  | testZero history hz job ih =>
      simpa using ih
  | @processPositive L z before after transcript job p history ih =>
      intro entry hentry
      apply ih entry
      rw [List.mem_append] at hentry ⊢
      rcases hentry with hbefore | hafter
      · exact Or.inl hbefore
      · exact Or.inr (by simp [hafter])
  | processZero history job ih =>
      exact ih

/-- At every reachable virtual-tail state, the values already revealed,
the hidden descending levels, and the hidden zeros form the fixed full
tail multiset. -/
theorem MixedTailHistory.testValues_append_remaining
    {K Z : ℕ} {L z : ℕ}
    {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript) :
    transcript.testResults.map Prod.snd ++
        harmonicDescendingLevels (Z : ℝ) 0 L ++
        List.replicate z 0 =
      harmonicDescendingLevels (Z : ℝ) 0 K ++
        List.replicate Z 0 := by
  induction history with
  | initial =>
      simp
  | @testPositive L z pending transcript history hL job ih =>
      obtain ⟨L, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
      rw [harmonicDescendingLevels_succ] at ih
      simpa only [Nat.succ_sub_one,
        Online.Transcript.testResults_append,
        List.map_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.map_singleton, Prod.snd, List.append_assoc] using ih
  | @testZero z pending transcript history hz job ih =>
      obtain ⟨z, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hz)
      simpa only [Nat.succ_sub_one,
        Online.Transcript.testResults_append,
        List.map_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil,
        List.map_singleton, Prod.snd,
        harmonicDescendingLevels_zero,
        List.nil_append, List.replicate_succ,
        List.append_assoc] using ih
  | processPositive history ih =>
      simpa using ih
  | processZero history job ih =>
      simpa using ih

/-- Terminal virtual tails have revealed exactly the prescribed harmonic
value multiset. -/
theorem MixedTailHistory.testValues_eq_of_terminal
    {K Z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z 0 0 pending transcript) :
    transcript.testResults.map Prod.snd =
      harmonicDescendingLevels (Z : ℝ) 0 K ++
        List.replicate Z 0 := by
  simpa using history.testValues_append_remaining

/-- A frozen processing map agrees with all virtual test answers.  Global
nonnegativity is included because the generalized history deliberately
forgets the ambient `Config` proof attached to administrative zero
processings. -/
def MixedTailMatches
    (processingTime : Online.Label n → ℝ)
    (transcript : Online.Transcript n) : Prop :=
  HarmonicMatches processingTime transcript ∧
    ∀ job, 0 ≤ processingTime job

theorem MixedTailMatches.of_append
    {processingTime : Online.Label n → ℝ}
    {transcript : Online.Transcript n}
    {observation : Online.Observation n}
    (hmatch :
      MixedTailMatches processingTime
        (transcript ++ [observation])) :
    MixedTailMatches processingTime transcript :=
  ⟨hmatch.1.of_append, hmatch.2⟩

/-- The harmonic potential lower bound on an arbitrary ambient-label
virtual tail. -/
theorem MixedTailHistory.amortized_lower
    {K Z : ℕ} (hZ : 0 < Z)
    {L z : ℕ} {pending : MixedTailPending n}
    {transcript : Online.Transcript n}
    (history : MixedTailHistory K Z L z pending transcript)
    (processingTime : Online.Label n → ℝ)
    (hmatch : MixedTailMatches processingTime transcript) :
    harmonicDynamicPotential (Z : ℝ) 0 K Z [] ≤
      Online.completionCost .infinite processingTime transcript +
        Online.transcriptElapsed .infinite processingTime transcript *
          harmonicUnfinished L z pending +
        harmonicDynamicPotential (Z : ℝ) 0 L z pending.values := by
  induction history with
  | initial =>
      simp [harmonicUnfinished, Online.completionCost,
        Online.completionCostFrom]
  | @testPositive L z pending transcript history hL job ih =>
      let p := harmonicLevel (Z : ℝ) 0 (L - 1)
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hmatch.1 job p
        simp [p]
      have hp1 : 1 ≤ p := by
        dsimp [p]
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) _
      have hp0 : p ≠ 0 := by
        linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.testResult job p)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.testResult job p)
      have hpot :=
        harmonicDynamicPotential_test_positive
          (Z : ℝ) 0 (z := z) pending.values hL
      simp only [MixedTailPending.values_append,
        MixedTailPending.values_cons, MixedTailPending.values_nil,
        List.append_nil, p] at hpot ⊢
      simp [Online.Observation.completionLabel, hp0,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_singleton]
      push_cast at hpot hold ⊢
      have hLcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hL))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hLcast]
      simp only [MixedTailPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @testZero z pending transcript history hz job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.testResult job 0)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.testResult job 0)
      have hpot :=
        harmonicDynamicPotential_test_zero
          (Z : ℝ) 0 pending.values hz
      simp [Online.Observation.completionLabel,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      push_cast at hpot hold ⊢
      have hzcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hz))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hzcast]
      simp only [MixedTailPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @processPositive L z before after transcript job p history ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hprefix.1 job p
        exact history.pending_mem_testResult (job, p) (by simp)
      have hpLower :
          harmonicLevel (Z : ℝ) 0 L ≤ p := by
        apply history.pending_lower hZ (job, p)
        simp
      have hp1 : 1 ≤ p :=
        (harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) L).trans hpLower
      have hp0 : p ≠ 0 := by
        linarith
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.processed job)
      have hpot :=
        harmonicDynamicPotential_process
          (ξ := (Z : ℝ)) (γ := 0)
          (by exact_mod_cast hZ) (le_refl 0)
          (L := L) (z := z)
          (before := before.values) (after := after.values)
          (p := p)
          (by
            rcases history.positive_phase with hzero | hzEq
            · exact Or.inl hzero
            · exact Or.inr (by exact_mod_cast hzEq))
          hpLower
      simp only [MixedTailPending.values_append,
        MixedTailPending.values_cons] at hpot hold ⊢
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap, hp0] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_cons,
        MixedTailPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      rw [hcost, htime]
      ring_nf at hpot hold ⊢
      nlinarith
  | @processZero L z pending transcript history job ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpnonneg : 0 ≤ processingTime job :=
        hprefix.2 job
      have htimeNonneg :
          0 ≤ Online.transcriptElapsed .infinite
            processingTime transcript := by
        exact Online.transcriptElapsed_nonneg
          (by simp [Cap.Valid]) hprefix.2 transcript
      have hcost :=
        completionCost_append_singleton .infinite processingTime
          transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton .infinite processingTime
          transcript (.processed job)
      by_cases hpzero : processingTime job = 0
      · simp [Online.Observation.completionLabel,
          Online.Observation.duration, hpzero] at hcost htime
        rw [hcost, htime]
        simpa [harmonicUnfinished] using hold
      · have hppos : 0 < processingTime job :=
          lt_of_le_of_ne hpnonneg (Ne.symm hpzero)
        simp [Online.Observation.completionLabel,
          Online.Observation.duration, hpzero] at hcost htime
        rw [hcost, htime]
        unfold harmonicUnfinished at *
        push_cast at hold ⊢
        ring_nf at hold ⊢
        nlinarith

/-- Once the virtual tail is terminal, the residual potential and unfinished
work vanish, leaving the exact finite harmonic online benchmark. -/
theorem MixedTailHistory.terminal_online_lower
    {K Z : ℕ} (hZ : 0 < Z)
    {transcript : Online.Transcript n}
    (history :
      MixedTailHistory K Z 0 0
        ([] : MixedTailPending n) transcript)
    (processingTime : Online.Label n → ℝ)
    (hmatch : MixedTailMatches processingTime transcript) :
    harmonicFiniteOnline K Z 0 ≤
      Online.completionCost .infinite processingTime transcript := by
  have hlower :=
    history.amortized_lower hZ processingTime hmatch
  simpa [harmonicFiniteOnline, harmonicUnfinished,
    harmonicDynamicPotential_terminal] using hlower

end MixedQuotaOracle
end LowerBound

end

end SchedulingPaper
