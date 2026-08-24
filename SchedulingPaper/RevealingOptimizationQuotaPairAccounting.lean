import SchedulingPaper.RevealingOptimizationQuotaKernel
import SchedulingPaper.TestProcessPairShape
import SchedulingPaper.FinPairObjective
import Mathlib.Tactic

/-!
# Operational pair accounting for revealing-optimization quotas

The finite position kernel is identified with completion-time charges of a
literal mixed test/process/raw transcript, once its canonical two-label
projection grammar is available.
-/

namespace SchedulingPaper

namespace Online

/-- For distinct labels the pair projection is the disjoint shuffle of the
two owner-only projections. -/
theorem Transcript.pairProjection_perm_self_append
    {left right : Label n} (hne : left ≠ right)
    (transcript : Transcript n) :
    (transcript.pairProjection left right).Perm
      (transcript.pairProjection left left ++
        transcript.pairProjection right right) := by
  induction transcript with
  | nil => simp [Transcript.pairProjection]
  | cons observation rest ih =>
      by_cases hl : observation.ownerLabel = left
      · have hr : observation.ownerLabel ≠ right := by
          intro hright
          exact hne (hl.symm.trans hright)
        have hpair :
            Transcript.pairProjection left right (observation :: rest) =
              observation :: Transcript.pairProjection left right rest := by
          simp [Transcript.pairProjection, hl]
        have hleft :
            Transcript.pairProjection left left (observation :: rest) =
              observation :: Transcript.pairProjection left left rest := by
          simp [Transcript.pairProjection, hl]
        have hright :
            Transcript.pairProjection right right (observation :: rest) =
              Transcript.pairProjection right right rest := by
          simp [Transcript.pairProjection, hr]
        rw [hpair, hleft, hright]
        exact ih.cons observation
      · by_cases hr : observation.ownerLabel = right
        · have hpair :
              Transcript.pairProjection left right (observation :: rest) =
                observation :: Transcript.pairProjection left right rest := by
            simp [Transcript.pairProjection, hr]
          have hleft :
              Transcript.pairProjection left left (observation :: rest) =
                Transcript.pairProjection left left rest := by
            simp [Transcript.pairProjection, hl]
          have hright :
              Transcript.pairProjection right right (observation :: rest) =
                observation :: Transcript.pairProjection right right rest := by
            simp [Transcript.pairProjection, hr]
          rw [hpair, hleft, hright]
          exact (ih.cons observation).trans List.perm_middle.symm
        · have hpair :
              Transcript.pairProjection left right (observation :: rest) =
                Transcript.pairProjection left right rest := by
            simp [Transcript.pairProjection, hl, hr]
          have hleft :
              Transcript.pairProjection left left (observation :: rest) =
                Transcript.pairProjection left left rest := by
            simp [Transcript.pairProjection, hl]
          have hright :
              Transcript.pairProjection right right (observation :: rest) =
                Transcript.pairProjection right right rest := by
            simp [Transcript.pairProjection, hr]
          rw [hpair, hleft, hright]
          exact ih

end Online

namespace RevealingOptimization
namespace QuotaPairAccounting

open Online
open Randomized
open RandomizedOptional
open QuotaKernel

noncomputable section

def testedPairWord
    (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    (left right : Online.Label n) : Online.Transcript n :=
  let p := processing left
  let r := processing right
  if low p then
    [.testResult left p, .processed left,
      .testResult right r, .processed right]
  else if low r then
    [.testResult left p, .testResult right r,
      .processed right, .processed left]
  else if p ≤ r then
    [.testResult left p, .testResult right r,
      .processed left, .processed right]
  else
    [.testResult left p, .testResult right r,
      .processed right, .processed left]

def testedRawWord
    (processing : Online.Label n → ℝ)
    (tested raw : Online.Label n) : Online.Transcript n :=
  [.testResult tested (processing tested), .processed tested,
    .rawCompleted raw]

def rawPairWord
    (left right : Online.Label n) : Online.Transcript n :=
  [.rawCompleted left, .rawCompleted right]

/-! ## Canonical order of quota observations -/

def quotaObservationKey
    {n : ℕ} (processing : Online.Label n → ℝ)
    (low : ℝ → Bool) : Online.Observation n → ℕ × (ℝ × (ℕ × ℝ))
  | .testResult job value => (0, (job.val, (0, value)))
  | .processed job =>
      if low (processing job) then (0, (job.val, (1, 0)))
      else (1, (processing job, (job.val, 0)))
  | .rawCompleted job => (2, (job.val, (0, 0)))

def quotaObservationLE
    {n : ℕ} (processing : Online.Label n → ℝ)
    (low : ℝ → Bool) (first second : Online.Observation n) : Prop :=
  Prod.Lex (fun x y : ℕ => x < y)
    (Prod.Lex (fun x y : ℝ => x < y)
      (Prod.Lex (fun x y : ℕ => x < y) (fun x y : ℝ => x ≤ y)))
    (quotaObservationKey processing low first)
    (quotaObservationKey processing low second)

theorem quotaObservationLE_trans
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool) :
    Transitive (quotaObservationLE processing low) := by
  intro first second third hfirst hsecond
  unfold quotaObservationLE at hfirst hsecond ⊢
  exact Prod.Lex.trans hfirst hsecond

theorem quotaObservationKey_injective
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool) :
    Function.Injective (quotaObservationKey processing low) := by
  intro first second heq
  cases first <;> cases second <;>
    simp only [quotaObservationKey] at heq ⊢
  all_goals
    repeat' split at heq
    all_goals simp_all [Fin.ext_iff]

theorem quotaObservationLE_antisymm
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    {first second : Online.Observation n}
    (hfirst : quotaObservationLE processing low first second)
    (hsecond : quotaObservationLE processing low second first) :
    first = second := by
  apply quotaObservationKey_injective processing low
  unfold quotaObservationLE at hfirst hsecond
  simp only [Prod.lex_iff] at hfirst hsecond
  rcases hfirst with hphase | ⟨hphase, hfirst⟩
  · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> omega
  · rcases hsecond with hreverse | ⟨hreverse, hsecond⟩
    · omega
    · apply Prod.ext hphase
      rcases hfirst with hvalue | ⟨hvalue, hfirst⟩
      · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> linarith
      · rcases hsecond with hreverse | ⟨hreverse, hsecond⟩
        · linarith
        · apply Prod.ext hvalue
          rcases hfirst with hlabel | ⟨hlabel, hpayload⟩
          · rcases hsecond with hreverse | ⟨hreverse, _⟩ <;> omega
          · rcases hsecond with hreverse | ⟨hreverse, hpayload'⟩
            · omega
            · apply Prod.ext hlabel
              exact le_antisymm hpayload hpayload'

set_option maxHeartbeats 1000000 in
theorem testedPairWord_pairwise
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    {left right : Online.Label n} (horder : left.val < right.val) :
    (testedPairWord processing low left right).Pairwise
      (quotaObservationLE processing low) := by
  cases hl : low (processing left) <;>
  cases hr : low (processing right) <;>
  simp [testedPairWord, quotaObservationLE, quotaObservationKey,
    hl, hr, horder, Prod.lex_iff] <;>
    (try split) <;>
    simp_all [quotaObservationLE, quotaObservationKey, Prod.lex_iff]
  all_goals
    rcases lt_or_eq_of_le ‹processing left ≤ processing right› with hlt | heq
    · exact Or.inl hlt
    · simp [heq, horder]

theorem testedRawWord_pairwise
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    (tested raw : Online.Label n) :
    (testedRawWord processing tested raw).Pairwise
      (quotaObservationLE processing low) := by
  cases hlow : low (processing tested) <;>
    simp [testedRawWord, quotaObservationLE, quotaObservationKey,
      hlow, Prod.lex_iff]

theorem rawPairWord_pairwise
    {n : ℕ} (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    {left right : Online.Label n} (horder : left.val < right.val) :
    (rawPairWord left right).Pairwise
      (quotaObservationLE processing low) := by
  simp [rawPairWord, quotaObservationLE, quotaObservationKey,
    horder, Prod.lex_iff]

theorem traceSelfCharge_eq_raw_of_projection
    (u : ℝ) (processing : Online.Label n → ℝ)
    (transcript : Online.Transcript n) (job : Online.Label n)
    (hprojection : transcript.pairProjection job job =
      [.rawCompleted job]) :
    traceSelfCharge (.finite u) processing transcript job = u := by
  unfold traceSelfCharge
  rw [← ownedDurationUntilCompletion_pairProjection
    (.finite u) processing job job job job (Or.inl rfl) (Or.inl rfl),
    hprojection]
  simp [ownedDurationUntilCompletion, Observation.ownerLabel,
    Observation.duration, Observation.completionLabel, rawDuration]

theorem tracePairCharge_eq_tested_raw_of_projection
    (u : ℝ) (processing : Online.Label n → ℝ)
    (transcript : Online.Transcript n) (tested raw : Online.Label n)
    (hne : tested ≠ raw)
    (hprojection : transcript.pairProjection tested raw =
      testedRawWord processing tested raw) :
    tracePairCharge (.finite u) processing transcript tested raw =
      1 + processing tested := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      (.finite u) processing tested raw tested raw
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      (.finite u) processing tested raw raw tested
        (Or.inr rfl) (Or.inl rfl),
    hprojection]
  by_cases hp : processing tested = 0 <;>
    simp [testedRawWord, ownedDurationUntilCompletion,
      Observation.ownerLabel, Observation.duration,
      Observation.completionLabel, hp, hne, Ne.symm hne] <;> ring

theorem tracePairCharge_eq_raw_raw_of_projection
    (u : ℝ) (processing : Online.Label n → ℝ)
    (transcript : Online.Transcript n) (left right : Online.Label n)
    (hne : left ≠ right)
    (hprojection : transcript.pairProjection left right =
      rawPairWord left right) :
    tracePairCharge (.finite u) processing transcript left right = u := by
  unfold tracePairCharge
  rw [← ownedDurationUntilCompletion_pairProjection
      (.finite u) processing left right left right
        (Or.inl rfl) (Or.inr rfl),
    ← ownedDurationUntilCompletion_pairProjection
      (.finite u) processing left right right left
        (Or.inr rfl) (Or.inl rfl),
    hprojection]
  simp [rawPairWord, ownedDurationUntilCompletion,
    Observation.ownerLabel, Observation.duration,
    Observation.completionLabel, rawDuration, hne, Ne.symm hne]

theorem tracePairCharge_eq_testedPairChargeOrdered
    (u : ℝ) (processing : Online.Label n → ℝ)
    (low : ℝ → Bool) (hzero : low 0 = true)
    (transcript : Online.Transcript n)
    (left right : Online.Label n) (hne : left ≠ right)
    (hprojection : transcript.pairProjection left right =
      testedPairWord processing low left right) :
    tracePairCharge (.finite u) processing transcript left right =
      testedPairChargeOrdered (low (processing left))
        (low (processing right)) (processing left) (processing right) := by
  let p := processing left
  let r := processing right
  have hpNonzero : low p = false → p ≠ 0 := by
    intro hp hp0
    have hpTrue : low p = true := by simpa [hp0] using hzero
    rw [hp] at hpTrue
    contradiction
  have hrNonzero : low r = false → r ≠ 0 := by
    intro hr hr0
    have hrTrue : low r = true := by simpa [hr0] using hzero
    rw [hr] at hrTrue
    contradiction
  cases hp : low p with
  | true =>
      have hword : transcript.pairProjection left right =
          [.testResult left p, .processed left,
            .testResult right r, .processed right] := by
        simpa [testedPairWord, p, r, hp] using hprojection
      rw [tracePairCharge_eq_leftAfterOneTest
        (.finite u) processing transcript left right p r hword hne
          (by simp [p]) (by simp [r])]
      simp [testedPairChargeOrdered, hp, p, r]
  | false =>
      cases hr : low r with
      | true =>
          have hword : transcript.pairProjection left right =
              [.testResult left p, .testResult right r,
                .processed right, .processed left] := by
            simpa [testedPairWord, p, r, hp, hr] using hprojection
          rw [tracePairCharge_eq_rightAfterTwoTests
            (.finite u) processing transcript left right p r hword hne
              (by simp [p]) (by simp [r]) (hpNonzero hp)]
          simp [testedPairChargeOrdered, hp, hr, p, r]
      | false =>
          by_cases hpr : p ≤ r
          · have hword : transcript.pairProjection left right =
                [.testResult left p, .testResult right r,
                  .processed left, .processed right] := by
              simpa [testedPairWord, p, r, hp, hr, hpr] using hprojection
            rw [tracePairCharge_eq_leftAfterTwoTests
              (.finite u) processing transcript left right p r hword hne
                (by simp [p]) (by simp [r])
                (hpNonzero hp) (hrNonzero hr)]
            simp [testedPairChargeOrdered, hp, hr, p, r, min_eq_left hpr]
          · have hrp : r < p := lt_of_not_ge hpr
            have hword : transcript.pairProjection left right =
                [.testResult left p, .testResult right r,
                  .processed right, .processed left] := by
              simpa [testedPairWord, p, r, hp, hr, hpr] using hprojection
            rw [tracePairCharge_eq_rightAfterTwoTests
              (.finite u) processing transcript left right p r hword hne
                (by simp [p]) (by simp [r]) (hpNonzero hp)]
            simp [testedPairChargeOrdered, hp, hr, p, r,
              min_eq_right hrp.le]

/-- Complete one- and two-label grammar expected from the canonical quota
policy.  This predicate is deliberately independent of how the transcript
was generated, so the accounting theorem below is reusable. -/
structure QuotaProjectionSpec
    (q : ℕ) (processing : Online.Label n → ℝ) (low : ℝ → Bool)
    (transcript : Online.Transcript n) : Prop where
  self : ∀ job,
    transcript.pairProjection job job =
      if job.val < q then
        [.testResult job (processing job), .processed job]
      else [.rawCompleted job]
  pair : ∀ {left right}, left < right →
    transcript.pairProjection left right =
      if right.val < q then testedPairWord processing low left right
      else if left.val < q then testedRawWord processing left right
      else rawPairWord left right

theorem QuotaProjectionSpec.selfCharge
    {q : ℕ} {processing : Online.Label n → ℝ} {low : ℝ → Bool}
    {transcript : Online.Transcript n}
    (hspec : QuotaProjectionSpec q processing low transcript)
    (u : ℝ) (job : Online.Label n) :
    traceSelfCharge (.finite u) processing transcript job =
      quotaSingleKernel q u processing job job := by
  by_cases ht : job.val < q
  · have hprojection := hspec.self job
    rw [if_pos ht] at hprojection
    rw [traceSelfCharge_eq_one_add_of_projection
      (.finite u) processing transcript job (processing job)
        hprojection rfl]
    simp [quotaSingleKernel, ht]
  · have hprojection := hspec.self job
    rw [if_neg ht] at hprojection
    rw [traceSelfCharge_eq_raw_of_projection u processing transcript job
      hprojection]
    simp [quotaSingleKernel, ht]

theorem QuotaProjectionSpec.pairCharge
    {q : ℕ} {processing : Online.Label n → ℝ} {low : ℝ → Bool}
    (hzero : low 0 = true) {transcript : Online.Transcript n}
    (hspec : QuotaProjectionSpec q processing low transcript)
    (u : ℝ) {left right : Online.Label n} (horder : left < right) :
    tracePairCharge (.finite u) processing transcript left right =
      quotaPairCharge q u low left right
        (processing left) (processing right) := by
  have hne : left ≠ right := ne_of_lt horder
  have hval : left.val < right.val := horder
  by_cases hright : right.val < q
  · have hleft : left.val < q := lt_trans hval hright
    have hprojection := hspec.pair horder
    simp only [if_pos hright] at hprojection
    rw [tracePairCharge_eq_testedPairChargeOrdered u processing low hzero
      transcript left right hne hprojection]
    simp [quotaPairCharge, hleft, hright, hval]
  · by_cases hleft : left.val < q
    · have hprojection := hspec.pair horder
      simp only [if_neg hright, if_pos hleft] at hprojection
      rw [tracePairCharge_eq_tested_raw_of_projection u processing
        transcript left right hne hprojection]
      simp [quotaPairCharge, hleft, hright]
    · have hprojection := hspec.pair horder
      simp only [if_neg hright, if_neg hleft] at hprojection
      rw [tracePairCharge_eq_raw_raw_of_projection u processing
        transcript left right hne hprojection]
      simp [quotaPairCharge, hleft, hright]

private theorem sum_orderedDistinct_add_diagonal
    {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ z : OrderedDistinct (Fin n), f z.val.1 z.val.2) +
        ∑ i, f i i =
      ∑ i, ∑ j, f i j := by
  have hoff :
      (∑ z : OrderedDistinct (Fin n), f z.val.1 z.val.2) =
        ∑ z ∈ (Finset.univ : Finset (Fin n)).offDiag, f z.1 z.2 := by
    symm
    apply Finset.sum_subtype
    intro z
    simp [Finset.mem_offDiag]
  have hdiag :
      (∑ z ∈ (Finset.univ : Finset (Fin n)).diag, f z.1 z.2) =
        ∑ i, f i i := by
    rw [Finset.sum_diag]
  rw [hoff, ← hdiag, add_comm]
  rw [← Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ)]
  rw [Finset.diag_union_offDiag, Finset.sum_product]

private theorem sum_quotaPairKernel_eq_upper
    {n q : ℕ} (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) :
    (∑ z : OrderedDistinct (Fin n),
        quotaPairKernel q u processing low z z.val.1 z.val.2) =
      ∑ left, ∑ right ∈
        Finset.univ.filter (fun right => left < right),
          quotaPairCharge q u low left right
            (processing left) (processing right) := by
  let g : Fin n → Fin n → ℝ := fun left right =>
    if left = right then 0 else
      quotaPairCharge q u low left right
        (processing left) (processing right) / 2
  have hsymm : ∀ left right, g left right = g right left := by
    intro left right
    by_cases hne : left = right
    · subst right
      rfl
    · simp only [g, if_neg hne, if_neg (Ne.symm hne)]
      rw [quotaPairCharge_comm u low hne]
  have hdecomp := sum_orderedDistinct_add_diagonal g
  have hdouble := symmetric_double_sum g hsymm
  have hordered :
      (∑ z : OrderedDistinct (Fin n), g z.val.1 z.val.2) =
        2 * ∑ left, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            g left right := by
    have hdiag : (∑ i : Fin n, g i i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [g]
    rw [hdiag, add_zero] at hdecomp
    linarith
  have hupper :
      2 * ∑ left, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            g left right =
        ∑ left, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            quotaPairCharge q u low left right
              (processing left) (processing right) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right hright
    have horder : left < right := by simpa using hright
    simp [g, ne_of_lt horder]
    ring
  rw [← hupper, ← hordered]
  apply Finset.sum_congr rfl
  intro z _
  simp [g, quotaPairKernel, z.property]

/-- Exact cost identity for every completed transcript satisfying the quota
projection grammar.  No asymptotics or probabilistic approximation enters
this theorem. -/
theorem completionCost_eq_quotaKernelCost
    {n q : ℕ} (u : ℝ) (processing : Fin n → ℝ)
    (low : ℝ → Bool) (hzero : low 0 = true)
    (transcript : Online.Transcript n)
    (hcompletion :
      (transcript.completionLabels processing).Perm (List.ofFn id))
    (hspec : QuotaProjectionSpec q processing low transcript) :
    Online.completionCost (.finite u) processing transcript =
      quotaKernelCost q u processing low (Equiv.refl (Fin n)) := by
  rw [Online.completionCost_eq_traceSelf_add_pairs
    (.finite u) processing transcript hcompletion]
  have hself :
      (∑ job, traceSelfCharge (.finite u) processing transcript job) =
        ∑ job, quotaSingleKernel q u processing job job := by
    apply Finset.sum_congr rfl
    intro job _
    exact hspec.selfCharge u job
  have hpairs :
      (∑ left, ∑ right ∈
          Finset.univ.filter (fun right => left < right),
            tracePairCharge (.finite u) processing transcript left right) =
        ∑ z : OrderedDistinct (Fin n),
          quotaPairKernel q u processing low z z.val.1 z.val.2 := by
    rw [sum_quotaPairKernel_eq_upper]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right hright
    have horder : left < right := by simpa using hright
    exact hspec.pairCharge hzero u horder
  rw [hself, hpairs]
  simp [quotaKernelCost, positionKernelCost]

end

end QuotaPairAccounting
end RevealingOptimization
end SchedulingPaper
