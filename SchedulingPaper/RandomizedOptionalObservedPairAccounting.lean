import SchedulingPaper.RandomizedOptionalCanonicalKernel
import SchedulingPaper.RandomizedOptionalCompletionInvariant
import Mathlib.Tactic

/-!
# Pair decomposition for observed optional-testing transcripts

For a completed legal transcript, total completion time is the sum of the
duration owned by every job before its own completion and all oriented
owner--target interactions.  This is the operational decomposition matched
by `canonicalSingleKernel` and `canonicalPairKernel`.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

open Randomized

noncomputable section

@[simp] theorem Transcript.completionLabels_nil
    (processing : Label n → ℝ) :
    Transcript.completionLabels processing [] = [] := rfl

@[simp] theorem Transcript.completionLabels_cons
    (processing : Label n → ℝ) (observation : Observation n)
    (rest : Transcript n) :
    Transcript.completionLabels processing (observation :: rest) =
      match observation.completionLabel processing with
      | some job => job :: Transcript.completionLabels processing rest
      | none => Transcript.completionLabels processing rest := by
  cases h : observation.completionLabel processing <;>
    simp [Transcript.completionLabels, h]

theorem CompletionInvariant.completionLabels_perm_of_done
    {processing : Label n → ℝ} {config : Config n}
    (hinv : CompletionInvariant processing config)
    (hdone : ∀ job, config.jobs job = .done) :
    (Transcript.completionLabels processing config.transcript).Perm
      (List.ofFn id) := by
  apply (List.perm_ext_iff_of_nodup hinv.nodup
    (List.nodup_ofFn.mpr Function.injective_id)).2
  intro job
  constructor
  · intro _
    simp
  · intro _
    apply (hinv.mem_iff job).mpr
    exact Or.inl (hdone job)

theorem run_completionLabels_perm_of_done
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (run processing strategy fuel).config.jobs job = .done) :
    (Transcript.completionLabels processing
      (run processing strategy fuel).config.transcript).Perm
        (List.ofFn id) :=
  (run_completionInvariant processing strategy fuel).completionLabels_perm_of_done
    hdone

theorem completionCount_eq_completionLabels_length
    (processing : Label n → ℝ) (transcript : Transcript n) :
    completionCount processing transcript =
      (Transcript.completionLabels processing transcript).length :=
  (Transcript.completionLabels_length processing transcript).symm

def timeUntilCompletion
    (processing : Label n → ℝ) (job : Label n) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.actualDuration processing +
        if observation.completionLabel processing = some job then 0
        else timeUntilCompletion processing job rest

private theorem sum_map_const_add
    {ι : Type*} (duration : ℝ) (labels : List ι) (f : ι → ℝ) :
    (labels.map fun job => duration + f job).sum =
      labels.length * duration + (labels.map f).sum := by
  induction labels with
  | nil => simp
  | cons job labels ih => simp [ih]; ring

theorem suffixWeightedDuration_eq_sum_timeUntilCompletion
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hnodup :
      (Transcript.completionLabels processing transcript).Nodup) :
    suffixWeightedDuration processing transcript =
      ((Transcript.completionLabels processing transcript).map
        fun job => timeUntilCompletion processing job transcript).sum := by
  induction transcript with
  | nil => simp [suffixWeightedDuration]
  | cons observation rest ih =>
      rw [suffixWeightedDuration, completionCount_eq_completionLabels_length,
        Transcript.completionLabels_cons]
      cases hcompletion : observation.completionLabel processing with
      | none =>
          have htail :
              (Transcript.completionLabels processing rest).Nodup := by
            simpa [hcompletion] using hnodup
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion, reduceCtorEq,
            ↓reduceIte]
          rw [sum_map_const_add]
          ring
      | some completed =>
          have hcons :
              (completed :: Transcript.completionLabels processing rest).Nodup := by
            simpa [hcompletion] using hnodup
          have htail := (List.nodup_cons.mp hcons).2
          have hnotmem := (List.nodup_cons.mp hcons).1
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion, List.map_cons,
            List.sum_cons]
          have hmap :
              ((Transcript.completionLabels processing rest).map fun job =>
                observation.actualDuration processing +
                  (if some completed = some job then 0
                    else timeUntilCompletion processing job rest)).sum =
                ((Transcript.completionLabels processing rest).map fun job =>
                  observation.actualDuration processing +
                    timeUntilCompletion processing job rest).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro job hjob
            rw [if_neg]
            intro heq
            have : completed = job := Option.some.inj heq
            subst job
            exact hnotmem hjob
          rw [hmap, sum_map_const_add]
          simp
          ring

theorem completionCost_eq_sum_timeUntilCompletion
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processing transcript).Perm
        (List.ofFn id)) :
    completionCost processing transcript =
      ∑ job : Label n, timeUntilCompletion processing job transcript := by
  rw [completionCost_eq_suffixWeightedDuration]
  have hnodup :
      (Transcript.completionLabels processing transcript).Nodup :=
    hperm.nodup_iff.mpr (List.nodup_ofFn.mpr Function.injective_id)
  rw [suffixWeightedDuration_eq_sum_timeUntilCompletion processing transcript hnodup]
  calc
    ((Transcript.completionLabels processing transcript).map fun job =>
        timeUntilCompletion processing job transcript).sum =
        (List.ofFn fun job =>
          timeUntilCompletion processing job transcript).sum := by
      simpa only [List.map_ofFn, Function.comp_id] using
        (hperm.map fun job =>
          timeUntilCompletion processing job transcript).sum_eq
    _ = ∑ job : Label n,
        timeUntilCompletion processing job transcript := Fin.sum_ofFn _

def Observation.ownerLabel : Observation n → Label n
  | .testResult job _ | .processed job | .blindCompleted job _ => job

theorem Observation.ownerLabel_eq_of_completionLabel_eq
    {processing : Label n → ℝ} {observation : Observation n}
    {job : Label n}
    (hcompletion : observation.completionLabel processing = some job) :
    observation.ownerLabel = job := by
  cases observation with
  | testResult observed p =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · simpa [Observation.ownerLabel] using Option.some.inj hcompletion
      · contradiction
  | processed observed =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · contradiction
      · simpa [Observation.ownerLabel] using Option.some.inj hcompletion
  | blindCompleted observed p =>
      simpa [Observation.completionLabel, Observation.ownerLabel] using
        Option.some.inj hcompletion

def Transcript.ownerProjection
    (owner target : Label n) (transcript : Transcript n) : Transcript n :=
  transcript.filter fun observation =>
    observation.ownerLabel = owner ∨ observation.ownerLabel = target

/-- For distinct labels the pair projection is the disjoint shuffle of the
two owner-only projections. -/
theorem Transcript.ownerProjection_perm_self_append
    {left right : Label n} (hne : left ≠ right)
    (transcript : Transcript n) :
    (transcript.ownerProjection left right).Perm
      (transcript.ownerProjection left left ++
        transcript.ownerProjection right right) := by
  induction transcript with
  | nil => simp [Transcript.ownerProjection]
  | cons observation rest ih =>
      by_cases hl : observation.ownerLabel = left
      · have hr : observation.ownerLabel ≠ right := by
          intro hright
          exact hne (hl.symm.trans hright)
        have hpair :
            Transcript.ownerProjection left right (observation :: rest) =
              observation :: Transcript.ownerProjection left right rest := by
          simp [Transcript.ownerProjection, hl]
        have hleft :
            Transcript.ownerProjection left left (observation :: rest) =
              observation :: Transcript.ownerProjection left left rest := by
          simp [Transcript.ownerProjection, hl]
        have hright :
            Transcript.ownerProjection right right (observation :: rest) =
              Transcript.ownerProjection right right rest := by
          simp [Transcript.ownerProjection, hr]
        rw [hpair, hleft, hright]
        exact ih.cons observation
      · by_cases hr : observation.ownerLabel = right
        · have hpair :
              Transcript.ownerProjection left right (observation :: rest) =
                observation :: Transcript.ownerProjection left right rest := by
            simp [Transcript.ownerProjection, hr]
          have hleft :
              Transcript.ownerProjection left left (observation :: rest) =
                Transcript.ownerProjection left left rest := by
            simp [Transcript.ownerProjection, hl]
          have hright :
              Transcript.ownerProjection right right (observation :: rest) =
                observation :: Transcript.ownerProjection right right rest := by
            simp [Transcript.ownerProjection, hr]
          rw [hpair, hleft, hright]
          exact (ih.cons observation).trans List.perm_middle.symm
        · have hpair :
              Transcript.ownerProjection left right (observation :: rest) =
                Transcript.ownerProjection left right rest := by
            simp [Transcript.ownerProjection, hl, hr]
          have hleft :
              Transcript.ownerProjection left left (observation :: rest) =
                Transcript.ownerProjection left left rest := by
            simp [Transcript.ownerProjection, hl]
          have hright :
              Transcript.ownerProjection right right (observation :: rest) =
                Transcript.ownerProjection right right rest := by
            simp [Transcript.ownerProjection, hr]
          rw [hpair, hleft, hright]
          exact ih

def ownedDurationUntilCompletion
    (processing : Label n → ℝ) (target owner : Label n) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      (if observation.ownerLabel = owner
        then observation.actualDuration processing else 0) +
      if observation.completionLabel processing = some target then 0
      else ownedDurationUntilCompletion processing target owner rest

theorem ownedDurationUntilCompletion_ownerProjection
    (processing : Label n → ℝ) (owner target : Label n)
    (transcript : Transcript n) :
    ownedDurationUntilCompletion processing target owner
        (transcript.ownerProjection owner target) =
      ownedDurationUntilCompletion processing target owner transcript := by
  induction transcript with
  | nil => simp [Transcript.ownerProjection, ownedDurationUntilCompletion]
  | cons observation rest ih =>
      by_cases hrel : observation.ownerLabel = owner ∨
          observation.ownerLabel = target
      · simp only [Transcript.ownerProjection, List.filter_cons]
        have hdec : decide (observation.ownerLabel = owner ∨
            observation.ownerLabel = target) = true := by simp [hrel]
        rw [if_pos hdec]
        simp only [ownedDurationUntilCompletion]
        rw [show (List.filter (fun observation =>
            decide (observation.ownerLabel = owner ∨
              observation.ownerLabel = target)) rest) =
            Transcript.ownerProjection owner target rest by rfl, ih]
      · have howner : observation.ownerLabel ≠ owner :=
          fun h => hrel (Or.inl h)
        have hcompletion :
            observation.completionLabel processing ≠ some target := by
          intro h
          exact hrel (Or.inr
            (observation.ownerLabel_eq_of_completionLabel_eq h))
        simp only [Transcript.ownerProjection, List.filter_cons]
        have hdec : decide (observation.ownerLabel = owner ∨
            observation.ownerLabel = target) ≠ true := by simp [hrel]
        rw [if_neg hdec]
        simp only [ownedDurationUntilCompletion, howner, ↓reduceIte,
          hcompletion]
        simpa [Transcript.ownerProjection] using ih

theorem timeUntilCompletion_eq_sum_owned
    (processing : Label n → ℝ) (target : Label n)
    (transcript : Transcript n) :
    timeUntilCompletion processing target transcript =
      ∑ owner : Label n,
        ownedDurationUntilCompletion processing target owner transcript := by
  induction transcript with
  | nil => simp [timeUntilCompletion, ownedDurationUntilCompletion]
  | cons observation rest ih =>
      simp only [timeUntilCompletion, ownedDurationUntilCompletion]
      by_cases hcompletion :
          observation.completionLabel processing = some target
      · simp [hcompletion]
      · simp only [if_neg hcompletion]
        rw [Finset.sum_add_distrib]
        simp [ih]

def observedTraceSelfCharge
    (processing : Label n → ℝ) (transcript : Transcript n)
    (job : Label n) : ℝ :=
  ownedDurationUntilCompletion processing job job transcript

def observedTraceOrientedCharge
    (processing : Label n → ℝ) (transcript : Transcript n)
    (owner target : Label n) : ℝ :=
  ownedDurationUntilCompletion processing target owner transcript

/-- Exact oriented decomposition, with no symmetry factors. -/
theorem completionCost_eq_self_add_orderedDistinct
    (processing : Label n → ℝ) (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processing transcript).Perm
        (List.ofFn id)) :
    completionCost processing transcript =
      (∑ job, observedTraceSelfCharge processing transcript job) +
        ∑ z : OrderedDistinct (Label n),
          observedTraceOrientedCharge processing transcript
            z.val.1 z.val.2 := by
  rw [completionCost_eq_sum_timeUntilCompletion processing transcript hperm]
  simp_rw [timeUntilCompletion_eq_sum_owned]
  have hsplit :
      (∑ target : Label n, ∑ owner : Label n,
        ownedDurationUntilCompletion processing target owner transcript) =
      (∑ job : Label n,
        ownedDurationUntilCompletion processing job job transcript) +
      ∑ z : OrderedDistinct (Label n),
        ownedDurationUntilCompletion processing z.val.2 z.val.1 transcript := by
    have h := orderedDistinct_add_diagonal fun owner target =>
      ownedDurationUntilCompletion processing target owner transcript
    rw [Finset.sum_comm] at h
    linarith
  simpa [observedTraceSelfCharge, observedTraceOrientedCharge] using hsplit

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
