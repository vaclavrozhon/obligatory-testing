import SchedulingPaper.TranscriptPairAccounting
import Mathlib.Tactic

/-!
# Completion-label decomposition of a timed transcript

This module rewrites the suffix-weighted operational cost as a sum of one
prefix duration for every completed label.  It is deliberately independent
of a particular strategy and is the common first step in the remaining
runtime-to-pair reductions.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- Completion labels, in chronological order. -/
def Transcript.completionLabels
    (processingTime : Label n → ℝ) (transcript : Transcript n) :
    List (Label n) :=
  transcript.filterMap
    (fun observation => observation.completionLabel processingTime)

@[simp] theorem Transcript.completionLabels_nil
    (processingTime : Label n → ℝ) :
    Transcript.completionLabels processingTime [] = [] := rfl

@[simp] theorem Transcript.completionLabels_cons
    (processingTime : Label n → ℝ)
    (observation : Observation n) (rest : Transcript n) :
    Transcript.completionLabels processingTime (observation :: rest) =
      match observation.completionLabel processingTime with
      | some job =>
          job :: Transcript.completionLabels processingTime rest
      | none =>
          Transcript.completionLabels processingTime rest := by
  cases h : observation.completionLabel processingTime <;>
    simp [Transcript.completionLabels, h]

@[simp] theorem Transcript.completionLabels_append
    (processingTime : Label n → ℝ)
    (left right : Transcript n) :
    Transcript.completionLabels processingTime (left ++ right) =
      Transcript.completionLabels processingTime left ++
        Transcript.completionLabels processingTime right := by
  simp [Transcript.completionLabels]

@[simp] theorem Transcript.completionLabels_append_testResult
    (processingTime : Label n → ℝ)
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    Transcript.completionLabels processingTime
        (transcript ++ [.testResult job p]) =
      Transcript.completionLabels processingTime transcript ++
        if p = 0 then [job] else [] := by
  by_cases hp : p = 0 <;>
    simp [Observation.completionLabel, hp]

@[simp] theorem Transcript.completionLabels_append_processed
    (processingTime : Label n → ℝ)
    (transcript : Transcript n) (job : Label n) :
    Transcript.completionLabels processingTime
        (transcript ++ [.processed job]) =
      Transcript.completionLabels processingTime transcript ++
        if processingTime job = 0 then [] else [job] := by
  by_cases hp : processingTime job = 0 <;>
    simp [Observation.completionLabel, hp]

theorem completionCount_eq_completionLabels_length
    (processingTime : Label n → ℝ) (transcript : Transcript n) :
    completionCount processingTime transcript =
      (Transcript.completionLabels processingTime transcript).length := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      rw [completionCount_cons,
        Transcript.completionLabels_cons]
      cases h : observation.completionLabel processingTime with
      | none =>
          simp [ih]
      | some job =>
          simp [ih]
          omega

/-- Elapsed duration through the first completion observation of `job`.
When `job` does not complete in the transcript, this is the whole elapsed
duration; the latter branch is never used in the permutation theorem below.
-/
def timeUntilCompletion
    (cap : Cap) (processingTime : Label n → ℝ) (job : Label n) :
    Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      observation.duration cap processingTime +
        if observation.completionLabel processingTime = some job
          then 0
          else timeUntilCompletion cap processingTime job rest

@[simp] theorem timeUntilCompletion_nil
    (cap : Cap) (processingTime : Label n → ℝ) (job : Label n) :
    timeUntilCompletion cap processingTime job [] = 0 := rfl

@[simp] theorem timeUntilCompletion_cons
    (cap : Cap) (processingTime : Label n → ℝ)
    (job : Label n) (observation : Observation n)
    (rest : Transcript n) :
    timeUntilCompletion cap processingTime job (observation :: rest) =
      observation.duration cap processingTime +
        if observation.completionLabel processingTime = some job
          then 0
          else timeUntilCompletion cap processingTime job rest := rfl

private theorem sum_map_const_add
    {ι : Type*} (duration : ℝ) (labels : List ι) (f : ι → ℝ) :
    (labels.map (fun job => duration + f job)).sum =
      labels.length * duration + (labels.map f).sum := by
  induction labels with
  | nil => simp
  | cons job labels ih =>
      simp [ih]
      ring

/-- If completion labels are unique, the suffix-weighted duration is the sum
of the prefix duration ending at each completion. -/
theorem suffixWeightedDuration_eq_sum_timeUntilCompletion
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n)
    (hnodup :
      (Transcript.completionLabels processingTime transcript).Nodup) :
    suffixWeightedDuration cap processingTime transcript =
      ((Transcript.completionLabels processingTime transcript).map
        (fun job =>
          timeUntilCompletion cap processingTime job transcript)).sum := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      rw [suffixWeightedDuration_cons,
        completionCount_eq_completionLabels_length,
        Transcript.completionLabels_cons]
      cases hcompletion :
          observation.completionLabel processingTime with
      | none =>
          have htail :
              (Transcript.completionLabels processingTime rest).Nodup := by
            simpa [hcompletion] using hnodup
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion_cons]
          simp only [reduceCtorEq, ↓reduceIte]
          rw [sum_map_const_add]
          ring
      | some completed =>
          have hcons :
              (completed ::
                Transcript.completionLabels processingTime rest).Nodup := by
            simpa [hcompletion] using hnodup
          have htail :
              (Transcript.completionLabels processingTime rest).Nodup :=
            (List.nodup_cons.mp hcons).2
          have hnotmem :
              completed ∉
                Transcript.completionLabels processingTime rest :=
            (List.nodup_cons.mp hcons).1
          rw [ih htail]
          simp only [hcompletion, timeUntilCompletion_cons]
          have hneq :
              ∀ job ∈
                  Transcript.completionLabels processingTime rest,
                some completed ≠ some job := by
            intro job hjob heq
            have : completed = job := Option.some.inj heq
            subst job
            exact hnotmem hjob
          simp only [List.map_cons, List.sum_cons]
          have hmap :
              ((Transcript.completionLabels processingTime rest).map
                (fun job =>
                  observation.duration cap processingTime +
                    (if some completed = some job then 0
                      else
                        timeUntilCompletion cap processingTime job rest))).sum =
                ((Transcript.completionLabels processingTime rest).map
                  (fun job =>
                    observation.duration cap processingTime +
                      timeUntilCompletion cap processingTime job rest)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro job hjob
            rw [if_neg (hneq job hjob)]
          rw [hmap, sum_map_const_add]
          simp
          ring

/-- When every label completes exactly once, total completion cost is the
sum of the label-indexed prefix durations. -/
theorem completionCost_eq_sum_timeUntilCompletion
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processingTime transcript).Perm
        (List.ofFn id)) :
    completionCost cap processingTime transcript =
      ∑ job : Label n,
        timeUntilCompletion cap processingTime job transcript := by
  rw [completionCost_eq_suffixWeightedDuration]
  have hnodup :
      (Transcript.completionLabels processingTime transcript).Nodup :=
    hperm.nodup_iff.mpr
      (List.nodup_ofFn.mpr Function.injective_id)
  rw [suffixWeightedDuration_eq_sum_timeUntilCompletion
    cap processingTime transcript hnodup]
  calc
    ((Transcript.completionLabels processingTime transcript).map
        (fun job =>
          timeUntilCompletion cap processingTime job transcript)).sum =
        (List.ofFn
          (fun job =>
            timeUntilCompletion cap processingTime job transcript)).sum :=
      by
        simpa only [List.map_ofFn, Function.comp_id] using
          (hperm.map
            (fun job =>
              timeUntilCompletion cap processingTime job transcript)).sum_eq
    _ = ∑ job : Label n,
          timeUntilCompletion cap processingTime job transcript :=
      Fin.sum_ofFn _

/-! ## Decomposition by the label owning each operation -/

def Observation.ownerLabel : Observation n → Label n
  | .testResult job _ | .processed job | .rawCompleted job => job

theorem Observation.ownerLabel_eq_of_completionLabel_eq
    {processingTime : Label n → ℝ}
    {observation : Observation n} {job : Label n}
    (hcompletion :
      observation.completionLabel processingTime = some job) :
    observation.ownerLabel = job := by
  cases observation with
  | testResult observed p =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · simpa [Observation.ownerLabel] using
          Option.some.inj hcompletion
      · contradiction
  | processed observed =>
      simp only [Observation.completionLabel] at hcompletion
      split at hcompletion
      · contradiction
      · simpa [Observation.ownerLabel] using
          Option.some.inj hcompletion
  | rawCompleted observed =>
      simpa [Observation.completionLabel,
        Observation.ownerLabel] using
        Option.some.inj hcompletion

/-- Erase all observations not owned by either of two labels. -/
def Transcript.pairProjection
    (left right : Label n) (transcript : Transcript n) :
    Transcript n :=
  transcript.filter
    (fun observation =>
      observation.ownerLabel = left ∨
        observation.ownerLabel = right)

/-- Duration owned by `owner` up to and including the first completion of
`target`. -/
def ownedDurationUntilCompletion
    (cap : Cap) (processingTime : Label n → ℝ)
    (target owner : Label n) : Transcript n → ℝ
  | [] => 0
  | observation :: rest =>
      (if observation.ownerLabel = owner
        then observation.duration cap processingTime else 0) +
      if observation.completionLabel processingTime = some target
        then 0
        else
          ownedDurationUntilCompletion cap processingTime
            target owner rest

@[simp] theorem ownedDurationUntilCompletion_nil
    (cap : Cap) (processingTime : Label n → ℝ)
    (target owner : Label n) :
    ownedDurationUntilCompletion cap processingTime
      target owner [] = 0 := rfl

theorem ownedDurationUntilCompletion_pairProjection
    (cap : Cap) (processingTime : Label n → ℝ)
    (left right target owner : Label n)
    (htarget : target = left ∨ target = right)
    (howner : owner = left ∨ owner = right)
    (transcript : Transcript n) :
    ownedDurationUntilCompletion cap processingTime
        target owner (transcript.pairProjection left right) =
      ownedDurationUntilCompletion cap processingTime
        target owner transcript := by
  induction transcript with
  | nil => simp [Transcript.pairProjection]
  | cons observation rest ih =>
      by_cases hrel :
          observation.ownerLabel = left ∨
            observation.ownerLabel = right
      · simp only [Transcript.pairProjection, List.filter_cons]
        have hdec :
            decide
              (observation.ownerLabel = left ∨
                observation.ownerLabel = right) = true := by
          simp [hrel]
        rw [if_pos hdec]
        simp only [ownedDurationUntilCompletion]
        have ih' :
            ownedDurationUntilCompletion cap processingTime target owner
                (List.filter
                  (fun observation =>
                    decide
                      (observation.ownerLabel = left ∨
                        observation.ownerLabel = right)) rest) =
              ownedDurationUntilCompletion cap processingTime
                target owner rest := by
          simpa [Transcript.pairProjection] using ih
        rw [ih']
      · have hownerNe :
            observation.ownerLabel ≠ owner := by
          intro heq
          rcases howner with rfl | rfl
          · exact hrel (Or.inl heq)
          · exact hrel (Or.inr heq)
        have hcompletionNe :
            observation.completionLabel processingTime ≠ some target := by
          intro hcompletion
          have heq :=
            observation.ownerLabel_eq_of_completionLabel_eq
              hcompletion
          rcases htarget with rfl | rfl
          · exact hrel (Or.inl heq)
          · exact hrel (Or.inr heq)
        simp only [Transcript.pairProjection, List.filter_cons]
        have hdec :
            decide
              (observation.ownerLabel = left ∨
                observation.ownerLabel = right) ≠ true := by
          simp [hrel]
        rw [if_neg hdec]
        simp only [ownedDurationUntilCompletion, hownerNe,
          ↓reduceIte, hcompletionNe]
        have ih' :
            ownedDurationUntilCompletion cap processingTime target owner
                (List.filter
                  (fun observation =>
                    decide
                      (observation.ownerLabel = left ∨
                        observation.ownerLabel = right)) rest) =
              ownedDurationUntilCompletion cap processingTime
                target owner rest := by
          simpa [Transcript.pairProjection] using ih
        simpa using ih'

theorem timeUntilCompletion_eq_sum_owned
    (cap : Cap) (processingTime : Label n → ℝ)
    (target : Label n) (transcript : Transcript n) :
    timeUntilCompletion cap processingTime target transcript =
      ∑ owner : Label n,
        ownedDurationUntilCompletion cap processingTime
          target owner transcript := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      simp only [timeUntilCompletion_cons,
        ownedDurationUntilCompletion]
      by_cases hcompletion :
          observation.completionLabel processingTime = some target
      · simp [hcompletion]
      · simp only [if_neg hcompletion]
        rw [Finset.sum_add_distrib]
        simp [ih]

/-- The self charge of a label in an operational transcript. -/
def traceSelfCharge
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (job : Label n) : ℝ :=
  ownedDurationUntilCompletion cap processingTime
    job job transcript

/-- The symmetric unordered-pair charge of two distinct labels. -/
def tracePairCharge
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n) : ℝ :=
  ownedDurationUntilCompletion cap processingTime
      left right transcript +
    ownedDurationUntilCompletion cap processingTime
      right left transcript

/-- A test and its administrative process observation contribute exactly
`1+p` to the job's diagonal charge. -/
theorem traceSelfCharge_eq_one_add_of_projection
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (job : Label n) (p : ℝ)
    (hprojection :
      transcript.pairProjection job job =
        [.testResult job p, .processed job])
    (hp : processingTime job = p) :
    traceSelfCharge cap processingTime transcript job = 1 + p := by
  unfold traceSelfCharge
  rw [← ownedDurationUntilCompletion_pairProjection
    cap processingTime job job job job (Or.inl rfl) (Or.inl rfl),
    hprojection]
  by_cases hp0 : p = 0
  · subst p
    simp [ownedDurationUntilCompletion,
      Observation.ownerLabel, Observation.duration,
      Observation.completionLabel, hp0]
  · simp [ownedDurationUntilCompletion,
      Observation.ownerLabel, Observation.duration,
      Observation.completionLabel, hp, hp0]

/-- Pair charge when the left label completes immediately before the right
label is tested. -/
theorem tracePairCharge_eq_leftAfterOneTest
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n)
    (p q : ℝ)
    (hprojection :
      transcript.pairProjection left right =
        [.testResult left p, .processed left,
          .testResult right q, .processed right])
    (hne : left ≠ right)
    (hp : processingTime left = p)
    (hq : processingTime right = q) :
    tracePairCharge cap processingTime transcript left right =
      1 + p := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl),
    hprojection]
  by_cases hp0 : p = 0 <;>
    by_cases hq0 : q = 0 <;>
      simp [ownedDurationUntilCompletion,
        Observation.ownerLabel, Observation.duration,
        Observation.completionLabel, hp, hq, hp0, hq0,
        hne, Ne.symm hne]

/-- Pair charge when both tests precede the right completion and the right
label completes first. -/
theorem tracePairCharge_eq_rightAfterTwoTests
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n)
    (p q : ℝ)
    (hprojection :
      transcript.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed right, .processed left])
    (hne : left ≠ right)
    (hp : processingTime left = p)
    (hq : processingTime right = q)
    (hp0 : p ≠ 0) :
    tracePairCharge cap processingTime transcript left right =
      2 + q := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl),
    hprojection]
  by_cases hq0 : q = 0 <;>
    simp [ownedDurationUntilCompletion,
      Observation.ownerLabel, Observation.duration,
      Observation.completionLabel, hp, hq, hp0, hq0,
      hne, Ne.symm hne] <;>
    ring

/-- Pair charge when both tests precede the left completion and the left
label completes first. -/
theorem tracePairCharge_eq_leftAfterTwoTests
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n) (left right : Label n)
    (p q : ℝ)
    (hprojection :
      transcript.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed left, .processed right])
    (hne : left ≠ right)
    (hp : processingTime left = p)
    (hq : processingTime right = q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    tracePairCharge cap processingTime transcript left right =
      2 + p := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      cap processingTime left right right left
        (Or.inr rfl) (Or.inl rfl),
    hprojection]
  simp [ownedDurationUntilCompletion,
    Observation.ownerLabel, Observation.duration,
    Observation.completionLabel, hp, hq, hp0, hq0,
    hne, Ne.symm hne]
  ring

private theorem sum_row_split_lt
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (i : ι) :
    (∑ j, f i j) =
      f i i +
        ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), f i j := by
  classical
  let upper := Finset.univ.filter (fun j : ι => i < j)
  let lower := Finset.univ.filter (fun j : ι => j < i)
  have hdisjoint : Disjoint upper lower := by
    apply Finset.disjoint_left.mpr
    intro j hjUpper hjLower
    simp only [upper, lower, Finset.mem_filter,
      Finset.mem_univ, true_and] at hjUpper hjLower
    exact (not_lt_of_ge hjUpper.le hjLower)
  have hunion : upper ∪ lower = Finset.univ.erase i := by
    ext j
    simp only [upper, lower, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro (hij | hji)
      · exact ⟨ne_of_gt hij, trivial⟩
      · exact ⟨ne_of_lt hji, trivial⟩
    · rintro ⟨hji, _⟩
      rcases lt_trichotomy i j with hij | heq | hji'
      · exact Or.inl hij
      · exact (hji heq.symm).elim
      · exact Or.inr hji'
  calc
    (∑ j, f i j) =
        f i i + ∑ j ∈ Finset.univ.erase i, f i j :=
      (Finset.add_sum_erase Finset.univ (fun j => f i j)
        (Finset.mem_univ i)).symm
    _ =
        f i i +
          ((∑ j ∈ upper, f i j) +
            ∑ j ∈ lower, f i j) := by
      rw [← Finset.sum_union hdisjoint, hunion]
    _ =
        f i i +
          ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j +
          ∑ j ∈ Finset.univ.filter (fun j => j < i), f i j := by
      dsimp [upper, lower]
      ring

private theorem sum_lower_triangle_transpose
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), f i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f j i := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Every completed transcript splits into its `n` diagonal charges and one
symmetric charge for each unordered pair of labels. -/
theorem completionCost_eq_traceSelf_add_pairs
    (cap : Cap) (processingTime : Label n → ℝ)
    (transcript : Transcript n)
    (hperm :
      (Transcript.completionLabels processingTime transcript).Perm
        (List.ofFn id)) :
    completionCost cap processingTime transcript =
      (∑ job, traceSelfCharge cap processingTime transcript job) +
        ∑ left, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            tracePairCharge cap processingTime transcript left right := by
  rw [completionCost_eq_sum_timeUntilCompletion
    cap processingTime transcript hperm]
  simp_rw [timeUntilCompletion_eq_sum_owned]
  have hrows :
      (∑ target : Label n, ∑ owner : Label n,
          ownedDurationUntilCompletion cap processingTime
            target owner transcript) =
        (∑ job : Label n,
          ownedDurationUntilCompletion cap processingTime
            job job transcript) +
          ∑ left : Label n, ∑ right ∈
            Finset.univ.filter (fun right => left < right),
              (ownedDurationUntilCompletion cap processingTime
                  left right transcript +
                ownedDurationUntilCompletion cap processingTime
                  right left transcript) := by
    calc
      (∑ target : Label n, ∑ owner : Label n,
          ownedDurationUntilCompletion cap processingTime
            target owner transcript) =
          ∑ target : Label n,
            (ownedDurationUntilCompletion cap processingTime
                target target transcript +
              ∑ owner ∈
                Finset.univ.filter (fun owner => target < owner),
                  ownedDurationUntilCompletion cap processingTime
                    target owner transcript +
              ∑ owner ∈
                Finset.univ.filter (fun owner => owner < target),
                  ownedDurationUntilCompletion cap processingTime
                    target owner transcript) := by
        apply Finset.sum_congr rfl
        intro target _htarget
        exact sum_row_split_lt
          (fun i j =>
            ownedDurationUntilCompletion cap processingTime
              i j transcript) target
      _ =
          (∑ job : Label n,
            ownedDurationUntilCompletion cap processingTime
              job job transcript) +
            (∑ left : Label n, ∑ right ∈
              Finset.univ.filter (fun right => left < right),
                ownedDurationUntilCompletion cap processingTime
                  left right transcript) +
            ∑ left : Label n, ∑ right ∈
              Finset.univ.filter (fun right => right < left),
                ownedDurationUntilCompletion cap processingTime
                  left right transcript := by
        simp_rw [Finset.sum_add_distrib]
      _ =
          (∑ job : Label n,
            ownedDurationUntilCompletion cap processingTime
              job job transcript) +
            (∑ left : Label n, ∑ right ∈
              Finset.univ.filter (fun right => left < right),
                ownedDurationUntilCompletion cap processingTime
                  left right transcript) +
            ∑ left : Label n, ∑ right ∈
              Finset.univ.filter (fun right => left < right),
                ownedDurationUntilCompletion cap processingTime
                  right left transcript := by
        rw [sum_lower_triangle_transpose]
      _ =
          (∑ job : Label n,
            ownedDurationUntilCompletion cap processingTime
              job job transcript) +
            ∑ left : Label n, ∑ right ∈
              Finset.univ.filter (fun right => left < right),
                (ownedDurationUntilCompletion cap processingTime
                    left right transcript +
                  ownedDurationUntilCompletion cap processingTime
                    right left transcript) := by
        simp_rw [Finset.sum_add_distrib]
        ring
  simpa [traceSelfCharge, tracePairCharge] using hrows

end

end SchedulingPaper.Online
