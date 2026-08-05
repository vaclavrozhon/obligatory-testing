import SchedulingPaper.BoundaryRelaxation
import SchedulingPaper.EndpointReduction

/-!
# Exact pair accounting for obligatory boundary words

This file connects the four formal endpoint outcomes used by the bank
argument to the actual pair objectives in the scheduling problem.  A boundary
word is evaluated at the successive adaptive thresholds.  We prove that these
thresholds are nonincreasing, use this fact to simplify every `min` in the
pair objective, and obtain the exact identity

`ALG - RStar * OPT =
  -rhoStar * n * (n + 1) / 2 + sum exactBoundaryReward`.

The definitions of `boundaryALG` and `boundaryOPT` below are the literal
pairwise formulas from the manuscript, not the already-relaxed bank rewards.
-/

namespace SchedulingPaper

noncomputable section

/-! ## Threshold-generated boundary jobs -/

/-- A formal endpoint outcome together with its limiting processing value.
`epsilon` and `deferred` retain their symbolic counter effects even though
their displayed values are one-sided limits. -/
structure ObligatoryBoundaryJob where
  outcome : BoundaryOutcome
  processing : ℝ

/-- The limiting value attached to the current endpoint outcome. -/
def obligatoryBoundaryValue
    (s : AnalysisState) : BoundaryOutcome → ℝ
  | .zero | .epsilon => 0
  | .immediate | .deferred => s.threshold

/-- Evaluate a word at the successive state-dependent thresholds. -/
def obligatoryBoundaryJobs :
    AnalysisState → List BoundaryOutcome → List ObligatoryBoundaryJob
  | _, [] => []
  | s, outcome :: outcomes =>
      ⟨outcome, obligatoryBoundaryValue s outcome⟩ ::
        obligatoryBoundaryJobs (s.step outcome) outcomes

@[simp] theorem obligatoryBoundaryJobs_nil (s : AnalysisState) :
    obligatoryBoundaryJobs s [] = [] := rfl

@[simp] theorem obligatoryBoundaryJobs_cons
    (s : AnalysisState) (outcome : BoundaryOutcome)
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryJobs s (outcome :: outcomes) =
      ⟨outcome, obligatoryBoundaryValue s outcome⟩ ::
        obligatoryBoundaryJobs (s.step outcome) outcomes := rfl

@[simp] theorem obligatoryBoundaryJobs_length
    (s : AnalysisState) (outcomes : List BoundaryOutcome) :
    (obligatoryBoundaryJobs s outcomes).length = outcomes.length := by
  induction outcomes generalizing s with
  | nil => rfl
  | cons outcome outcomes ih =>
      simp [obligatoryBoundaryJobs, ih]

/-- Processing mass that is visible in pairwise minima.  The two zero
endpoint types contribute no mass. -/
def ObligatoryBoundaryJob.substantiveProcessing
    (job : ObligatoryBoundaryJob) : ℝ :=
  match job.outcome with
  | .zero | .epsilon => 0
  | .immediate | .deferred => job.processing

def totalSubstantiveProcessing :
    List ObligatoryBoundaryJob → ℝ
  | [] => 0
  | job :: jobs =>
      job.substantiveProcessing + totalSubstantiveProcessing jobs

/-- Canonical sign/value condition for a formal boundary job. -/
def ObligatoryBoundaryJob.Canonical
    (job : ObligatoryBoundaryJob) : Prop :=
  match job.outcome with
  | .zero | .epsilon => job.processing = 0
  | .immediate | .deferred => 0 ≤ job.processing

/-- A canonical boundary job whose substantive value is at most `a`. -/
def ObligatoryBoundaryJob.BoundedBy
    (a : ℝ) (job : ObligatoryBoundaryJob) : Prop :=
  match job.outcome with
  | .zero | .epsilon => job.processing = 0
  | .immediate | .deferred =>
      0 ≤ job.processing ∧ job.processing ≤ a

theorem ObligatoryBoundaryJob.BoundedBy.canonical
    {a : ℝ} {job : ObligatoryBoundaryJob}
    (h : job.BoundedBy a) :
    job.Canonical := by
  cases job with
  | mk outcome processing =>
      cases outcome <;>
        simp [ObligatoryBoundaryJob.BoundedBy,
          ObligatoryBoundaryJob.Canonical] at h ⊢
      · exact h
      · exact h
      · exact h.1
      · exact h.1

theorem ObligatoryBoundaryJob.BoundedBy.mono
    {a b : ℝ} (hab : a ≤ b) {job : ObligatoryBoundaryJob}
    (h : job.BoundedBy a) :
    job.BoundedBy b := by
  cases job with
  | mk outcome processing =>
      cases outcome <;>
        simp [ObligatoryBoundaryJob.BoundedBy] at h ⊢
      · exact h
      · exact h
      · exact ⟨h.1, h.2.trans hab⟩
      · exact ⟨h.1, h.2.trans hab⟩

/-! ## Monotonicity of the successive thresholds -/

/-- The nonsaturated logarithmic threshold is monotone on the nonpositive
half-line. -/
theorem activeThreshold_mono_nonpos
    {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 0) :
    activeThreshold u ≤ activeThreshold v := by
  have hu : u ≤ 0 := huv.trans hv
  have hdenv : 0 < rhoStar - 2 * v :=
    active_denominator_pos hv
  have hden :
      rhoStar - 2 * v ≤ rhoStar - 2 * u := by
    linarith
  have hlog :
      Real.log (rhoStar - 2 * v) ≤
        Real.log (rhoStar - 2 * u) :=
    Real.log_le_log hdenv hden
  unfold activeThreshold
  linarith

/-- The saturated state threshold is monotone as a function of the normalized
state `y` throughout the reachable half-line `y ≤ 0`. -/
theorem AnalysisState.threshold_le_of_y_le
    {left right : AnalysisState}
    (hy : left.y ≤ right.y) (hzero : right.y ≤ 0) :
    left.threshold ≤ right.threshold := by
  unfold AnalysisState.threshold
  by_cases hleft : -1 ≤ left.y
  · rw [if_pos hleft]
    by_cases hright : -1 ≤ right.y
    · rw [if_pos hright]
      exact activeThreshold_mono_nonpos hy hzero
    · rw [if_neg hright]
      exact (hright (hleft.trans hy)).elim
  · rw [if_neg hleft]
    by_cases hright : -1 ≤ right.y
    · rw [if_pos hright]
      exact activeThreshold_ge_one hright hzero
    · rw [if_neg hright]

/-- Every nonterminal unit update weakly lowers the next threshold. -/
theorem AnalysisState.threshold_step_le
    {s : AnalysisState} (hs : s.Feasible) (hx : 2 ≤ s.x)
    (outcome : BoundaryOutcome) :
    (s.step outcome).threshold ≤ s.threshold :=
  AnalysisState.threshold_le_of_y_le
    (AnalysisState.y_step_le hs hx outcome)
    (AnalysisState.y_nonpos hs)

/-! ## States matching a remaining boundary word -/

/-- Raw counters agree with a word of unit countdown transitions.  Unlike
`Feasible`, this also makes sense at the terminal empty word where `x = 0`. -/
def BoundaryStateMatches
    (s : AnalysisState) (outcomes : List BoundaryOutcome) : Prop :=
  s.x = outcomes.length ∧
  0 ≤ s.substantive ∧
  0 ≤ s.epsilon ∧
  0 ≤ s.deferred ∧
  s.deferred ≤ s.substantive

theorem boundaryStateMatches_initial
    (outcomes : List BoundaryOutcome) :
    BoundaryStateMatches
      (initialAnalysisState outcomes.length) outcomes := by
  simp [BoundaryStateMatches, initialAnalysisState]

theorem BoundaryStateMatches.feasible_of_cons
    {s : AnalysisState} {outcome : BoundaryOutcome}
    {outcomes : List BoundaryOutcome}
    (h : BoundaryStateMatches s (outcome :: outcomes)) :
    s.Feasible := by
  rcases h with ⟨hx, hS, he, hd, hdS⟩
  refine ⟨?_, hS, he, hd, hdS⟩
  rw [hx]
  norm_num only [List.length_cons, Nat.cast_add, Nat.cast_one]
  exact_mod_cast Nat.succ_pos outcomes.length

theorem BoundaryStateMatches.step
    {s : AnalysisState} {outcome : BoundaryOutcome}
    {outcomes : List BoundaryOutcome}
    (h : BoundaryStateMatches s (outcome :: outcomes)) :
    BoundaryStateMatches (s.step outcome) outcomes := by
  rcases h with ⟨hx, hS, he, hd, hdS⟩
  cases outcome <;>
    simp only [AnalysisState.step, BoundaryStateMatches] <;>
    constructor
  · simpa using congrArg (fun z : ℝ => z - 1) hx
  · exact ⟨hS, he, hd, hdS⟩
  · simpa using congrArg (fun z : ℝ => z - 1) hx
  · exact ⟨hS, by linarith, hd, hdS⟩
  · simpa using congrArg (fun z : ℝ => z - 1) hx
  · exact ⟨by linarith, he, hd, by linarith⟩
  · simpa using congrArg (fun z : ℝ => z - 1) hx
  · exact ⟨by linarith, he, by linarith, by linarith⟩

theorem BoundaryStateMatches.x_ge_two_of_tail
    {s : AnalysisState} {outcome : BoundaryOutcome}
    {outcomes : List BoundaryOutcome}
    (h : BoundaryStateMatches s (outcome :: outcomes))
    (htail : outcomes ≠ []) :
    2 ≤ s.x := by
  have hlen : 1 ≤ outcomes.length :=
    List.length_pos_iff.mpr htail
  rw [h.1]
  norm_num only [List.length_cons, Nat.cast_add, Nat.cast_one]
  exact_mod_cast Nat.succ_le_succ hlen

/-- All threshold-generated jobs have their canonical zero/sign behavior. -/
theorem obligatoryBoundaryJobs_canonical
    {s : AnalysisState} {outcomes : List BoundaryOutcome}
    (hmatch : BoundaryStateMatches s outcomes) :
    ∀ job ∈ obligatoryBoundaryJobs s outcomes, job.Canonical := by
  induction outcomes generalizing s with
  | nil =>
      simp [obligatoryBoundaryJobs]
  | cons outcome outcomes ih =>
      have hs := hmatch.feasible_of_cons
      have hthreshold : 0 ≤ s.threshold :=
        (AnalysisState.threshold_ge_one hs).trans' zero_le_one
      intro job hjob
      simp only [obligatoryBoundaryJobs, List.mem_cons] at hjob
      rcases hjob with rfl | htail
      · cases outcome <;>
          simp [obligatoryBoundaryValue,
            ObligatoryBoundaryJob.Canonical, hthreshold]
      · exact ih hmatch.step job htail

/-- Every later nonzero boundary value is at most the current threshold. -/
theorem obligatoryBoundaryJobs_bounded
    {s : AnalysisState} {outcomes : List BoundaryOutcome}
    (hmatch : BoundaryStateMatches s outcomes) :
    ∀ job ∈ obligatoryBoundaryJobs s outcomes,
      job.BoundedBy s.threshold := by
  induction outcomes generalizing s with
  | nil =>
      simp [obligatoryBoundaryJobs]
  | cons outcome outcomes ih =>
      have hs := hmatch.feasible_of_cons
      have hthreshold : 0 ≤ s.threshold :=
        (AnalysisState.threshold_ge_one hs).trans' zero_le_one
      intro job hjob
      simp only [obligatoryBoundaryJobs, List.mem_cons] at hjob
      rcases hjob with rfl | htail
      · cases outcome <;>
          simp [obligatoryBoundaryValue,
            ObligatoryBoundaryJob.BoundedBy, hthreshold]
      · have htailBound := ih hmatch.step job htail
        by_cases hempty : outcomes = []
        · subst outcomes
          simp [obligatoryBoundaryJobs] at htail
        · exact htailBound.mono
            (AnalysisState.threshold_step_le hs
              (hmatch.x_ge_two_of_tail hempty) outcome)

/-! ## The literal ALG and OPT pair objectives -/

/-- Algorithmic charge of the unordered pair whose left job occurs first in
test order. -/
def obligatoryALGPairCharge
    (left right : ObligatoryBoundaryJob) : ℝ :=
  match left.outcome with
  | .zero | .epsilon | .immediate =>
      1 + left.processing
  | .deferred =>
      match right.outcome with
      | .zero | .epsilon | .immediate => 2 + right.processing
      | .deferred => 2 + min left.processing right.processing

/-- Offline shortest-first charge of an unordered pair. -/
def obligatoryOPTPairCharge
    (left right : ObligatoryBoundaryJob) : ℝ :=
  1 + min left.processing right.processing

/-- Literal pairwise algorithmic objective
`Σ_i (1+p_i) + Σ_{i<j} g_ij`. -/
def obligatoryALGPairObjective :
    List ObligatoryBoundaryJob → ℝ
  | [] => 0
  | job :: jobs =>
      (1 + job.processing) +
        (jobs.map (obligatoryALGPairCharge job)).sum +
        obligatoryALGPairObjective jobs

/-- Literal pairwise offline objective
`Σ_i (1+p_i) + Σ_{i<j} (1+min(p_i,p_j))`. -/
def obligatoryOPTPairObjective :
    List ObligatoryBoundaryJob → ℝ
  | [] => 0
  | job :: jobs =>
      (1 + job.processing) +
        (jobs.map (obligatoryOPTPairCharge job)).sum +
        obligatoryOPTPairObjective jobs

/-- The exact objectives of a threshold-generated word. -/
def obligatoryBoundaryALG (outcomes : List BoundaryOutcome) : ℝ :=
  obligatoryALGPairObjective
    (obligatoryBoundaryJobs
      (initialAnalysisState outcomes.length) outcomes)

def obligatoryBoundaryOPT (outcomes : List BoundaryOutcome) : ℝ :=
  obligatoryOPTPairObjective
    (obligatoryBoundaryJobs
      (initialAnalysisState outcomes.length) outcomes)

/-! ### Pair-row simplifications -/

theorem sum_obligatoryALGPairCharge_immediate
    (outcome : BoundaryOutcome)
    (hneq : outcome ≠ .deferred) (p : ℝ)
    (jobs : List ObligatoryBoundaryJob) :
    (jobs.map
      (obligatoryALGPairCharge ⟨outcome, p⟩)).sum =
        jobs.length * (1 + p) := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      cases outcome <;>
        simp_all [obligatoryALGPairCharge,
          Nat.cast_add, Nat.cast_one] <;>
        ring

theorem sum_obligatoryALGPairCharge_deferred
    (p : ℝ) (jobs : List ObligatoryBoundaryJob)
    (hbounded : ∀ job ∈ jobs, job.BoundedBy p) :
    (jobs.map
      (obligatoryALGPairCharge ⟨.deferred, p⟩)).sum =
        2 * jobs.length + totalSubstantiveProcessing jobs := by
  induction jobs with
  | nil => simp [totalSubstantiveProcessing]
  | cons job jobs ih =>
      have hjob := hbounded job (by simp)
      have htail :
          ∀ tailJob ∈ jobs, tailJob.BoundedBy p := by
        intro tailJob hmem
        exact hbounded tailJob (by simp [hmem])
      have hi := ih htail
      rcases job with ⟨outcome, processing⟩
      cases outcome <;>
        simp [obligatoryALGPairCharge,
          totalSubstantiveProcessing,
          ObligatoryBoundaryJob.substantiveProcessing,
          ObligatoryBoundaryJob.BoundedBy] at hjob hi ⊢
      · rw [hjob]
        linarith
      · rw [hjob]
        linarith
      · linarith
      · rw [min_eq_right hjob.2]
        linarith

theorem sum_obligatoryOPTPairCharge_zero
    (outcome : BoundaryOutcome) (jobs : List ObligatoryBoundaryJob)
    (hcanonical : ∀ job ∈ jobs, job.Canonical) :
    (jobs.map
      (obligatoryOPTPairCharge ⟨outcome, 0⟩)).sum =
        jobs.length := by
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
      have hjob := hcanonical job (by simp)
      have htail :
          ∀ tailJob ∈ jobs, tailJob.Canonical := by
        intro tailJob hmem
        exact hcanonical tailJob (by simp [hmem])
      have hi := ih htail
      rcases job with ⟨outcome, processing⟩
      cases outcome <;>
        simp [obligatoryOPTPairCharge,
          ObligatoryBoundaryJob.Canonical] at hjob hi ⊢
      · rw [hjob, hi]
        norm_num only [min_self, Nat.cast_add, Nat.cast_one]
        ring
      · rw [hjob, hi]
        norm_num only [min_self, Nat.cast_add, Nat.cast_one]
        ring
      · rw [min_eq_left hjob]
        linarith
      · rw [min_eq_left hjob]
        linarith

theorem sum_obligatoryOPTPairCharge_substantive
    (outcome : BoundaryOutcome)
    (p : ℝ) (hp : 0 ≤ p) (jobs : List ObligatoryBoundaryJob)
    (hbounded : ∀ job ∈ jobs, job.BoundedBy p) :
    (jobs.map
      (obligatoryOPTPairCharge ⟨outcome, p⟩)).sum =
        jobs.length + totalSubstantiveProcessing jobs := by
  induction jobs with
  | nil => simp [totalSubstantiveProcessing]
  | cons job jobs ih =>
      have hjob := hbounded job (by simp)
      have htail :
          ∀ tailJob ∈ jobs, tailJob.BoundedBy p := by
        intro tailJob hmem
        exact hbounded tailJob (by simp [hmem])
      have hi := ih htail
      rcases job with ⟨rightOutcome, processing⟩
      cases rightOutcome <;>
        simp [obligatoryOPTPairCharge,
          totalSubstantiveProcessing,
          ObligatoryBoundaryJob.substantiveProcessing,
          ObligatoryBoundaryJob.BoundedBy] at hjob hi ⊢
      · rw [hjob, min_eq_right]
        · linarith
        · exact hp
      · rw [hjob, min_eq_right]
        · linarith
        · exact hp
      · rw [min_eq_right hjob.2]
        linarith
      · rw [min_eq_right hjob.2]
        linarith

/-! ## Processing-time allocation normal forms -/

/-- The algorithmic pair objective with every processing term charged at the
endpoint where the manuscript accounts for it.  `past` is the number of
already exposed jobs. -/
def obligatoryAllocatedALG :
    ℝ → AnalysisState → List BoundaryOutcome → ℝ
  | _, _, [] => 0
  | past, s, outcome :: outcomes =>
      let p := obligatoryBoundaryValue s outcome
      (past + 1) + s.deferred +
        (match outcome with
        | .zero | .epsilon => 0
        | .immediate => p * (s.x + s.deferred)
        | .deferred => p * (s.deferred + 1)) +
        obligatoryAllocatedALG (past + 1) (s.step outcome) outcomes

/-- The analogous allocation of the offline shortest-first objective. -/
def obligatoryAllocatedOPT :
    ℝ → AnalysisState → List BoundaryOutcome → ℝ
  | _, _, [] => 0
  | past, s, outcome :: outcomes =>
      let p := obligatoryBoundaryValue s outcome
      (past + 1) +
        (match outcome with
        | .zero | .epsilon => 0
        | .immediate | .deferred =>
            p * (s.substantive + 1)) +
        obligatoryAllocatedOPT (past + 1) (s.step outcome) outcomes

/-- Reassigning processing terms does not change the literal algorithmic
pair objective.  The two correction terms record interaction with an
arbitrary already-processed prefix; they vanish at the initial state. -/
theorem obligatoryAllocatedALG_eq_pairObjective
    {s : AnalysisState} {outcomes : List BoundaryOutcome}
    (past : ℝ) (hmatch : BoundaryStateMatches s outcomes) :
    obligatoryAllocatedALG past s outcomes =
      obligatoryALGPairObjective (obligatoryBoundaryJobs s outcomes) +
        (past + s.deferred) * outcomes.length +
        s.deferred *
          totalSubstantiveProcessing
            (obligatoryBoundaryJobs s outcomes) := by
  induction outcomes generalizing s past with
  | nil =>
      simp [obligatoryAllocatedALG, obligatoryBoundaryJobs,
        obligatoryALGPairObjective, totalSubstantiveProcessing]
  | cons outcome outcomes ih =>
      have hstep := hmatch.step
      have hih :=
        ih (s := s.step outcome) (past := past + 1) hstep
      have htailBound :
          ∀ job ∈ obligatoryBoundaryJobs (s.step outcome) outcomes,
            job.BoundedBy s.threshold := by
        intro job hjob
        exact obligatoryBoundaryJobs_bounded hmatch job (by
          simp [obligatoryBoundaryJobs, hjob])
      cases outcome with
      | zero =>
          have hpairs :=
            sum_obligatoryALGPairCharge_immediate
              .zero (by simp) 0
              (obligatoryBoundaryJobs (s.step .zero) outcomes)
          rw [show obligatoryAllocatedALG past s (.zero :: outcomes) =
              (past + 1) + s.deferred +
                obligatoryAllocatedALG (past + 1)
                  (s.step .zero) outcomes by
                simp [obligatoryAllocatedALG],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryALGPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [
            ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | epsilon =>
          have hpairs :=
            sum_obligatoryALGPairCharge_immediate
              .epsilon (by simp) 0
              (obligatoryBoundaryJobs (s.step .epsilon) outcomes)
          rw [show obligatoryAllocatedALG past s (.epsilon :: outcomes) =
              (past + 1) + s.deferred +
                obligatoryAllocatedALG (past + 1)
                  (s.step .epsilon) outcomes by
                simp [obligatoryAllocatedALG],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryALGPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [
            ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | immediate =>
          have hpairs :=
            sum_obligatoryALGPairCharge_immediate
              .immediate (by simp) s.threshold
              (obligatoryBoundaryJobs (s.step .immediate) outcomes)
          rw [show obligatoryAllocatedALG past s (.immediate :: outcomes) =
              (past + 1) + s.deferred +
                s.threshold * (s.x + s.deferred) +
                obligatoryAllocatedALG (past + 1)
                  (s.step .immediate) outcomes by
                simp [obligatoryAllocatedALG,
                  obligatoryBoundaryValue],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryALGPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [
            ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          rw [hmatch.1]
          norm_num only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | deferred =>
          have hpairs :=
            sum_obligatoryALGPairCharge_deferred
              s.threshold
              (obligatoryBoundaryJobs (s.step .deferred) outcomes)
              htailBound
          rw [show obligatoryAllocatedALG past s (.deferred :: outcomes) =
              (past + 1) + s.deferred +
                s.threshold * (s.deferred + 1) +
                obligatoryAllocatedALG (past + 1)
                  (s.step .deferred) outcomes by
                simp [obligatoryAllocatedALG,
                  obligatoryBoundaryValue],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryALGPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [
            ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Reassigning minima to their later substantive endpoint does not change
the literal offline shortest-first pair objective. -/
theorem obligatoryAllocatedOPT_eq_pairObjective
    {s : AnalysisState} {outcomes : List BoundaryOutcome}
    (past : ℝ) (hmatch : BoundaryStateMatches s outcomes) :
    obligatoryAllocatedOPT past s outcomes =
      obligatoryOPTPairObjective (obligatoryBoundaryJobs s outcomes) +
        past * outcomes.length +
        s.substantive *
          totalSubstantiveProcessing
            (obligatoryBoundaryJobs s outcomes) := by
  induction outcomes generalizing s past with
  | nil =>
      simp [obligatoryAllocatedOPT, obligatoryBoundaryJobs,
        obligatoryOPTPairObjective, totalSubstantiveProcessing]
  | cons outcome outcomes ih =>
      have hstep := hmatch.step
      have hih :=
        ih (s := s.step outcome) (past := past + 1) hstep
      have htailCanonical :
          ∀ job ∈ obligatoryBoundaryJobs (s.step outcome) outcomes,
            job.Canonical := by
        intro job hjob
        exact obligatoryBoundaryJobs_canonical hmatch job (by
          simp [obligatoryBoundaryJobs, hjob])
      have htailBound :
          ∀ job ∈ obligatoryBoundaryJobs (s.step outcome) outcomes,
            job.BoundedBy s.threshold := by
        intro job hjob
        exact obligatoryBoundaryJobs_bounded hmatch job (by
          simp [obligatoryBoundaryJobs, hjob])
      have hs := hmatch.feasible_of_cons
      have hp : 0 ≤ s.threshold :=
        (AnalysisState.threshold_ge_one hs).trans' zero_le_one
      cases outcome with
      | zero =>
          have hpairs :=
            sum_obligatoryOPTPairCharge_zero .zero
              (obligatoryBoundaryJobs (s.step .zero) outcomes)
              htailCanonical
          rw [show obligatoryAllocatedOPT past s (.zero :: outcomes) =
              (past + 1) +
                obligatoryAllocatedOPT (past + 1)
                  (s.step .zero) outcomes by
                simp [obligatoryAllocatedOPT],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryOPTPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | epsilon =>
          have hpairs :=
            sum_obligatoryOPTPairCharge_zero .epsilon
              (obligatoryBoundaryJobs (s.step .epsilon) outcomes)
              htailCanonical
          rw [show obligatoryAllocatedOPT past s (.epsilon :: outcomes) =
              (past + 1) +
                obligatoryAllocatedOPT (past + 1)
                  (s.step .epsilon) outcomes by
                simp [obligatoryAllocatedOPT],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryOPTPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | immediate =>
          have hpairs :=
            sum_obligatoryOPTPairCharge_substantive
              .immediate s.threshold hp
              (obligatoryBoundaryJobs (s.step .immediate) outcomes)
              htailBound
          rw [show obligatoryAllocatedOPT past s (.immediate :: outcomes) =
              (past + 1) +
                s.threshold * (s.substantive + 1) +
                obligatoryAllocatedOPT (past + 1)
                  (s.step .immediate) outcomes by
                simp [obligatoryAllocatedOPT,
                  obligatoryBoundaryValue],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryOPTPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
      | deferred =>
          have hpairs :=
            sum_obligatoryOPTPairCharge_substantive
              .deferred s.threshold hp
              (obligatoryBoundaryJobs (s.step .deferred) outcomes)
              htailBound
          rw [show obligatoryAllocatedOPT past s (.deferred :: outcomes) =
              (past + 1) +
                s.threshold * (s.substantive + 1) +
                obligatoryAllocatedOPT (past + 1)
                  (s.step .deferred) outcomes by
                simp [obligatoryAllocatedOPT,
                  obligatoryBoundaryValue],
            hih]
          simp only [obligatoryBoundaryJobs,
            obligatoryOPTPairObjective, obligatoryBoundaryValue]
          rw [hpairs]
          simp only [ObligatoryBoundaryJob.substantiveProcessing,
            totalSubstantiveProcessing,
            AnalysisState.step,
            obligatoryBoundaryJobs_length,
            List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-! ## Exact excess decomposition -/

/-- The universal base contribution left by `k` remaining positions after
`past` jobs have already been exposed. -/
def obligatoryUniversalIndexSum (past : ℝ) (k : ℕ) : ℝ :=
  k * past + k * (k + 1) / 2

theorem obligatoryUniversalIndexSum_cons
    (past : ℝ) (k : ℕ) :
    obligatoryUniversalIndexSum past (k + 1) =
      (past + 1) + obligatoryUniversalIndexSum (past + 1) k := by
  unfold obligatoryUniversalIndexSum
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

/-- Before invoking any monotonicity or endpoint property, the two allocated
objectives differ locally by the exact reward plus the universal
`-rhoStar * (i+1)` term. -/
theorem obligatoryAllocatedExcess_eq_exact
    (past : ℝ) (s : AnalysisState)
    (outcomes : List BoundaryOutcome) :
    obligatoryAllocatedALG past s outcomes -
        RStar * obligatoryAllocatedOPT past s outcomes =
      -rhoStar *
          obligatoryUniversalIndexSum past outcomes.length +
        trajectoryReward AnalysisState.step exactBoundaryReward
          s outcomes := by
  induction outcomes generalizing s past with
  | nil =>
      simp [obligatoryAllocatedALG, obligatoryAllocatedOPT,
        obligatoryUniversalIndexSum, trajectoryReward]
  | cons outcome outcomes ih =>
      have hih :=
        ih (s := s.step outcome) (past := past + 1)
      cases outcome <;>
        simp only [obligatoryAllocatedALG,
          obligatoryAllocatedOPT, obligatoryBoundaryValue,
          trajectoryReward, exactBoundaryReward,
          List.length_cons] at hih ⊢
      · rw [obligatoryUniversalIndexSum_cons]
        unfold RStar at hih ⊢
        linear_combination hih
      · rw [obligatoryUniversalIndexSum_cons]
        unfold RStar at hih ⊢
        linear_combination hih
      · rw [obligatoryUniversalIndexSum_cons]
        unfold RStar at hih ⊢
        linear_combination hih
      · rw [obligatoryUniversalIndexSum_cons]
        unfold RStar at hih ⊢
        linear_combination hih

/-- At the empty-prefix initial state, the allocated algorithmic normal form
is exactly the literal pair objective. -/
theorem obligatoryBoundaryALG_eq_allocated
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryALG outcomes =
      obligatoryAllocatedALG 0
        (initialAnalysisState outcomes.length) outcomes := by
  have h :=
    obligatoryAllocatedALG_eq_pairObjective (s :=
      initialAnalysisState outcomes.length) 0
      (boundaryStateMatches_initial outcomes)
  simpa [obligatoryBoundaryALG, initialAnalysisState] using h.symm

/-- The same identification for the offline pair objective. -/
theorem obligatoryBoundaryOPT_eq_allocated
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryOPT outcomes =
      obligatoryAllocatedOPT 0
        (initialAnalysisState outcomes.length) outcomes := by
  have h :=
    obligatoryAllocatedOPT_eq_pairObjective (s :=
      initialAnalysisState outcomes.length) 0
      (boundaryStateMatches_initial outcomes)
  simpa [obligatoryBoundaryOPT, initialAnalysisState] using h.symm

/-- Equation `upper-exact-decomposition`: the literal pairwise objectives of
every threshold-generated four-letter word have exactly the local-reward
decomposition used by the bank. -/
theorem obligatory_boundary_pair_excess_exact
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryALG outcomes -
        RStar * obligatoryBoundaryOPT outcomes =
      -rhoStar * outcomes.length * (outcomes.length + 1) / 2 +
        trajectoryReward AnalysisState.step exactBoundaryReward
          (initialAnalysisState outcomes.length) outcomes := by
  rw [obligatoryBoundaryALG_eq_allocated,
    obligatoryBoundaryOPT_eq_allocated,
    obligatoryAllocatedExcess_eq_exact]
  unfold obligatoryUniversalIndexSum
  norm_num
  ring

/-- The already-bounded `obligatoryBoundaryExcess` is therefore not merely a
formal bank expression: it is the exact excess of the two pair objectives. -/
theorem obligatory_boundary_pair_excess_eq_boundaryExcess
    (outcomes : List BoundaryOutcome) :
    obligatoryBoundaryALG outcomes -
        RStar * obligatoryBoundaryOPT outcomes =
      obligatoryBoundaryExcess outcomes := by
  rw [obligatory_boundary_pair_excess_exact]
  rfl

/-! ## Coordinatewise endpoint reduction for arbitrary values

The exact identity above concerns the formal threshold vertices.  The next
block supplies the separate convexity mechanism used to move an arbitrary
processing vector, on any fixed symbolic decision word and finite box, to
some coordinatewise endpoint vertex.
-/

def obligatorySelfExcessAt (p : ℝ) : ℝ :=
  (1 + p) - RStar * (1 + p)

def obligatoryPairExcessAt
    (left right : BoundaryOutcome) (p q : ℝ) : ℝ :=
  obligatoryALGPairCharge ⟨left, p⟩ ⟨right, q⟩ -
    RStar * obligatoryOPTPairCharge ⟨left, p⟩ ⟨right, q⟩

theorem obligatorySelfExcessAt_convex :
    ConvexOn ℝ Set.univ obligatorySelfExcessAt := by
  have h :=
    convexOn_affine_sub_mul_min
      (-rhoStar) (-rhoStar) 0 0 (show (0 : ℝ) ≤ 0 by norm_num)
  refine h.congr ?_
  intro p _hp
  unfold obligatorySelfExcessAt RStar
  simp
  ring

theorem obligatoryPairExcessAt_convex_left
    (left right : BoundaryOutcome) (q : ℝ) :
    ConvexOn ℝ Set.univ
      (fun p => obligatoryPairExcessAt left right p q) := by
  have hR : 0 ≤ RStar :=
    (lt_trans zero_lt_one one_lt_RStar).le
  cases left with
  | zero =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (1 - RStar) RStar q hR
      refine h.congr ?_
      intro p _hp
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge]
      ring
  | epsilon =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (1 - RStar) RStar q hR
      refine h.congr ?_
      intro p _hp
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge]
      ring
  | immediate =>
      have h :=
        convexOn_affine_sub_mul_min
          1 (1 - RStar) RStar q hR
      refine h.congr ?_
      intro p _hp
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge]
      ring
  | deferred =>
      cases right with
      | zero =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (2 + q - RStar) RStar q hR
          refine h.congr ?_
          intro p _hp
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          ring
      | epsilon =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (2 + q - RStar) RStar q hR
          refine h.congr ?_
          intro p _hp
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          ring
      | immediate =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (2 + q - RStar) RStar q hR
          refine h.congr ?_
          intro p _hp
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          ring
      | deferred =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (2 - RStar) rhoStar q rhoStar_pos.le
          refine h.congr ?_
          intro p _hp
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge]
          unfold RStar
          ring

theorem obligatoryPairExcessAt_convex_right
    (left right : BoundaryOutcome) (p : ℝ) :
    ConvexOn ℝ Set.univ
      (fun q => obligatoryPairExcessAt left right p q) := by
  have hR : 0 ≤ RStar :=
    (lt_trans zero_lt_one one_lt_RStar).le
  cases left with
  | zero =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - RStar) RStar p hR
      refine h.congr ?_
      intro q _hq
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge,
        min_comm p q]
      ring
  | epsilon =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - RStar) RStar p hR
      refine h.congr ?_
      intro q _hq
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge,
        min_comm p q]
      ring
  | immediate =>
      have h :=
        convexOn_affine_sub_mul_min
          0 (1 + p - RStar) RStar p hR
      refine h.congr ?_
      intro q _hq
      simp [obligatoryPairExcessAt,
        obligatoryALGPairCharge, obligatoryOPTPairCharge,
        min_comm p q]
      ring
  | deferred =>
      cases right with
      | zero =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (2 - RStar) RStar p hR
          refine h.congr ?_
          intro q _hq
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge,
            min_comm p q]
          ring
      | epsilon =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (2 - RStar) RStar p hR
          refine h.congr ?_
          intro q _hq
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge,
            min_comm p q]
          ring
      | immediate =>
          have h :=
            convexOn_affine_sub_mul_min
              1 (2 - RStar) RStar p hR
          refine h.congr ?_
          intro q _hq
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge,
            min_comm p q]
          ring
      | deferred =>
          have h :=
            convexOn_affine_sub_mul_min
              0 (2 - RStar) rhoStar p rhoStar_pos.le
          refine h.congr ?_
          intro q _hq
          simp [obligatoryPairExcessAt,
            obligatoryALGPairCharge, obligatoryOPTPairCharge,
            min_comm p q]
          unfold RStar
          ring

private theorem convexOn_finset_sum
    {ι : Type*} {s : Set ℝ} (hs : Convex ℝ s)
    (indices : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ indices, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => ∑ i ∈ indices, f i x) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using (convexOn_const (𝕜 := ℝ) (β := ℝ) 0 hs)
  | @insert i indices hi ih =>
      have hhead := hf i (Finset.mem_insert_self i indices)
      have htail :
          ∀ j ∈ indices, ConvexOn ℝ s (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hsum := hhead.add (ih htail)
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hsum

/-- Exact excess of a fixed symbolic word at an arbitrary processing
vector.  The pair summation contains each `i<j` exactly once. -/
def obligatoryFixedWordExcess {n : ℕ}
    (outcome : Fin n → BoundaryOutcome)
    (processing : Fin n → ℝ) : ℝ :=
  (∑ i, obligatorySelfExcessAt (processing i)) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      obligatoryPairExcessAt
        (outcome i) (outcome j) (processing i) (processing j)

/-- On every finite box, the exact fixed-word excess is convex in each
processing coordinate separately. -/
theorem obligatoryFixedWordExcess_coordinatewiseConvex
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (lower upper : Fin n → ℝ) :
    CoordinatewiseConvexOnBox lower upper
      (obligatoryFixedWordExcess outcome) := by
  classical
  intro processing _hbox coordinate
  let interval : Set ℝ := Set.Icc (lower coordinate) (upper coordinate)
  have hinterval : Convex ℝ interval :=
    convex_Icc (lower coordinate) (upper coordinate)
  have hself (i : Fin n) :
      ConvexOn ℝ interval
        (fun t =>
          obligatorySelfExcessAt
            (Function.update processing coordinate t i)) := by
    by_cases hi : i = coordinate
    · subst i
      simpa [interval] using
        obligatorySelfExcessAt_convex.subset
          (Set.subset_univ _) hinterval
    · have hconst :
          (fun t =>
            obligatorySelfExcessAt
              (Function.update processing coordinate t i)) =
            (fun _ : ℝ => obligatorySelfExcessAt (processing i)) := by
          funext t
          simp [Function.update, hi]
      rw [hconst]
      exact convexOn_const _ hinterval
  have hpair (i j : Fin n) (hij : i < j) :
      ConvexOn ℝ interval
        (fun t =>
          obligatoryPairExcessAt
            (outcome i) (outcome j)
            (Function.update processing coordinate t i)
            (Function.update processing coordinate t j)) := by
    by_cases hi : i = coordinate
    · subst i
      have hj : j ≠ coordinate := ne_of_gt hij
      have hleft :=
        (obligatoryPairExcessAt_convex_left
          (outcome coordinate) (outcome j) (processing j)).subset
            (Set.subset_univ _) hinterval
      simpa [Function.update, hj] using hleft
    · by_cases hj : j = coordinate
      · subst j
        have hright :=
          (obligatoryPairExcessAt_convex_right
            (outcome i) (outcome coordinate) (processing i)).subset
              (Set.subset_univ _) hinterval
        simpa [Function.update, hi] using hright
      · have hconst :
            (fun t =>
              obligatoryPairExcessAt
                (outcome i) (outcome j)
                (Function.update processing coordinate t i)
                (Function.update processing coordinate t j)) =
              (fun _ : ℝ =>
                obligatoryPairExcessAt
                  (outcome i) (outcome j)
                  (processing i) (processing j)) := by
            funext t
            simp [Function.update, hi, hj]
        rw [hconst]
        exact convexOn_const _ hinterval
  have hselfSum :
      ConvexOn ℝ interval
        (fun t => ∑ i,
          obligatorySelfExcessAt
            (Function.update processing coordinate t i)) := by
    simpa using convexOn_finset_sum hinterval
      Finset.univ
      (fun i t => obligatorySelfExcessAt
        (Function.update processing coordinate t i))
      (fun i _hi => hself i)
  have hpairRow (i : Fin n) :
      ConvexOn ℝ interval
        (fun t => ∑ j ∈ Finset.univ.filter (fun j => i < j),
          obligatoryPairExcessAt
            (outcome i) (outcome j)
            (Function.update processing coordinate t i)
            (Function.update processing coordinate t j)) := by
    apply convexOn_finset_sum hinterval
    intro j hj
    exact hpair i j (Finset.mem_filter.mp hj).2
  have hpairSum :
      ConvexOn ℝ interval
        (fun t => ∑ i, ∑ j ∈
          Finset.univ.filter (fun j => i < j),
            obligatoryPairExcessAt
              (outcome i) (outcome j)
              (Function.update processing coordinate t i)
              (Function.update processing coordinate t j)) := by
    simpa using convexOn_finset_sum hinterval
      Finset.univ
      (fun i t => ∑ j ∈ Finset.univ.filter (fun j => i < j),
        obligatoryPairExcessAt
          (outcome i) (outcome j)
          (Function.update processing coordinate t i)
          (Function.update processing coordinate t j))
      (fun i _hi => hpairRow i)
  simpa [obligatoryFixedWordExcess, interval, Pi.add_apply] using
    hselfSum.add hpairSum

/-- Coordinatewise endpoint reduction for an arbitrary genuine processing
vector on a fixed symbolic word. -/
theorem exists_obligatoryFixedWord_endpoint_ge
    {n : ℕ} (outcome : Fin n → BoundaryOutcome)
    (lower upper processing : Fin n → ℝ)
    (horder : ∀ i, lower i ≤ upper i)
    (hprocessing : processing ∈ coordinateBox lower upper) :
    ∃ vertex,
      vertex ∈ coordinateBox lower upper ∧
      IsBoxVertex lower upper vertex ∧
      obligatoryFixedWordExcess outcome processing ≤
        obligatoryFixedWordExcess outcome vertex :=
  exists_boxVertex_ge horder
    (obligatoryFixedWordExcess_coordinatewiseConvex
      outcome lower upper)
    processing hprocessing

end

end SchedulingPaper
