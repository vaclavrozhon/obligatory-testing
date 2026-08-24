import SchedulingPaper.BlindOptimizationRandomizedUpper

/-!
# Operational realization of the blind-optimization pilot policy

The analytic upper bound uses two independent private permutations.  This
file turns each such seed into a literal transcript-only online strategy and
proves that its operational run is exactly the pilot/main schedule whose
cost was bounded in `BlindOptimizationRandomizedUpper`.
-/

namespace SchedulingPaper
namespace BlindOptimization

open Online

noncomputable section

def pilotJobList {n : ℕ} (positions : Finset (Fin n))
    (sampleOrder : Equiv.Perm (Fin n)) : List (Fin n) :=
  positions.toList.map sampleOrder

def mainJobList {n : ℕ} (positions : Finset (Fin n))
    (sampleOrder : Equiv.Perm (Fin n))
  (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    List (Fin n) :=
  (List.ofFn fun position : Fin (Fintype.card ↥(sampleJobs positions sampleOrder)ᶜ) ↦
    (mainOrder
      ((Fintype.equivFin ↥(sampleJobs positions sampleOrder)ᶜ).symm position)).val)

@[simp] theorem pilotJobList_length {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n)) :
    (pilotJobList positions sampleOrder).length = positions.card := by
  simp [pilotJobList]

@[simp] theorem mainJobList_length {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (mainJobList positions sampleOrder mainOrder).length =
      n - positions.card := by
  unfold mainJobList
  rw [List.length_ofFn, Fintype.card_coe, Finset.card_compl,
    sampleJobs_card, Fintype.card_fin]

theorem pilotJobList_nodup {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n)) :
    (pilotJobList positions sampleOrder).Nodup := by
  exact positions.nodup_toList.map sampleOrder.injective

theorem mainJobList_nodup {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (mainJobList positions sampleOrder mainOrder).Nodup := by
  unfold mainJobList
  rw [List.nodup_ofFn]
  intro i j hij
  apply (Fintype.equivFin ↥(sampleJobs positions sampleOrder)ᶜ).symm.injective
  apply mainOrder.injective
  exact Subtype.ext hij

theorem mem_pilotJobList_iff {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (job : Fin n) :
    job ∈ pilotJobList positions sampleOrder ↔
      job ∈ sampleJobs positions sampleOrder := by
  unfold pilotJobList sampleJobs
  simp

theorem mem_mainJobList_iff {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ)
    (job : Fin n) :
    job ∈ mainJobList positions sampleOrder mainOrder ↔
      job ∈ (sampleJobs positions sampleOrder)ᶜ := by
  unfold mainJobList
  constructor
  · intro hmem
    rw [List.mem_ofFn] at hmem
    obtain ⟨position, hposition⟩ := hmem
    rw [← hposition]
    exact (mainOrder
      ((Fintype.equivFin ↥(sampleJobs positions sampleOrder)ᶜ).symm position)).property
  · intro hmem
    let restJob : ↥(sampleJobs positions sampleOrder)ᶜ := ⟨job, hmem⟩
    let source := mainOrder.symm restJob
    let position := Fintype.equivFin ↥(sampleJobs positions sampleOrder)ᶜ source
    rw [List.mem_ofFn]
    refine ⟨position, ?_⟩
    change (mainOrder
      ((Fintype.equivFin ↥(sampleJobs positions sampleOrder)ᶜ).symm position)).val = job
    simp [position, source, restJob]

def pilotMainJobList {n : ℕ} (positions : Finset (Fin n))
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    List (Fin n) :=
  pilotJobList positions sampleOrder ++
    mainJobList positions sampleOrder mainOrder

@[simp] theorem pilotMainJobList_length {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotMainJobList positions sampleOrder mainOrder).length = n := by
  unfold pilotMainJobList
  simp
  have hcard : positions.card ≤ n := by
    rw [← sampleJobs_card positions sampleOrder]
    simpa using (sampleJobs positions sampleOrder).card_le_univ
  exact Nat.add_sub_of_le hcard

theorem pilotMainJobList_nodup {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotMainJobList positions sampleOrder mainOrder).Nodup := by
  rw [pilotMainJobList, List.nodup_append]
  refine ⟨pilotJobList_nodup positions sampleOrder,
    mainJobList_nodup positions sampleOrder mainOrder, ?_⟩
  intro job hp _job hm heq
  subst job
  have hsample := (mem_pilotJobList_iff positions sampleOrder _).mp hp
  have hcomplement :=
    (mem_mainJobList_iff positions sampleOrder mainOrder _).mp hm
  have hnot : _job ∉ sampleJobs positions sampleOrder := by
    simpa using hcomplement
  exact hnot hsample

theorem pilotMainJobList_toFinset {n : ℕ}
    (positions : Finset (Fin n)) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotMainJobList positions sampleOrder mainOrder).toFinset =
      Finset.univ := by
  ext job
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  rw [pilotMainJobList, List.mem_append]
  by_cases hsample : job ∈ sampleJobs positions sampleOrder
  · exact Or.inl ((mem_pilotJobList_iff positions sampleOrder job).mpr hsample)
  · exact Or.inr ((mem_mainJobList_iff positions sampleOrder mainOrder job).mpr
      (by simpa using hsample))

def decisionMode (decision : Bool) : Online.Mode :=
  if decision then Online.Mode.optimized else Online.Mode.raw

def observedPilotDecision {n : ℕ} (positions : Finset (Fin n))
    (u : ℝ) (transcript : Transcript n) : Bool :=
  decide (1 + observedPilotMean positions
    ((transcript.take positions.card).map (Observation.duration u)) < u)

/-- The actual online policy.  Its private seed fixes the job order.  Pilot
jobs are recognized by their public labels; on every other job the mode is
computed solely from the first `positions.card` observed durations. -/
def pilotOnlineStrategy {n : ℕ} (positions : Finset (Fin n)) (u : ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    Strategy n := fun transcript =>
  (pilotMainJobList positions sampleOrder mainOrder)[transcript.length]?.map
    fun job =>
      ⟨job, if job ∈ sampleJobs positions sampleOrder then .optimized
        else decisionMode (observedPilotDecision positions u transcript)⟩

def pilotOnlinePlan {n : ℕ} (positions : Finset (Fin n)) (u : ℝ)
    (processing : Fin n → ℝ) (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    List (Action n) :=
  (pilotMainJobList positions sampleOrder mainOrder).map fun job =>
    ⟨job, if job ∈ sampleJobs positions sampleOrder then .optimized
      else decisionMode (pilotUsesOptimized positions u processing sampleOrder)⟩

@[simp] theorem pilotOnlinePlan_length {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotOnlinePlan positions u processing sampleOrder mainOrder).length = n := by
  simp [pilotOnlinePlan]

theorem pilotOnlinePlan_jobs {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotOnlinePlan positions u processing sampleOrder mainOrder).map Action.job =
      pilotMainJobList positions sampleOrder mainOrder := by
  unfold pilotOnlinePlan
  rw [List.map_map]
  have hfun :
      (Action.job ∘ fun job : Fin n =>
        Action.mk job
          (if job ∈ sampleJobs positions sampleOrder then Online.Mode.optimized
            else decisionMode
              (pilotUsesOptimized positions u processing sampleOrder))) =
        id := by
    funext job
    rfl
  rw [hfun, List.map_id]

theorem pilotOnlinePlan_jobs_nodup {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    ((pilotOnlinePlan positions u processing sampleOrder mainOrder).map
      Action.job).Nodup := by
  rw [pilotOnlinePlan_jobs]
  exact pilotMainJobList_nodup positions sampleOrder mainOrder

theorem pilotOnlinePlan_jobs_toFinset {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    ((pilotOnlinePlan positions u processing sampleOrder mainOrder).map
      Action.job).toFinset = Finset.univ := by
  rw [pilotOnlinePlan_jobs]
  exact pilotMainJobList_toFinset positions sampleOrder mainOrder

/-- The first `k` planned actions are precisely the optimized pilot block. -/
theorem pilotOnlinePlan_take_pilot {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (pilotOnlinePlan positions u processing sampleOrder mainOrder).take
        positions.card =
      (pilotJobList positions sampleOrder).map fun job =>
        Action.mk job .optimized := by
  unfold pilotOnlinePlan pilotMainJobList
  rw [List.map_append]
  have hp : ∀ job ∈ pilotJobList positions sampleOrder,
      job ∈ sampleJobs positions sampleOrder := by
    intro job hjob
    exact (mem_pilotJobList_iff positions sampleOrder job).mp hjob
  have hlength :
      ((pilotJobList positions sampleOrder).map fun job =>
        Action.mk job
          (if job ∈ sampleJobs positions sampleOrder then Online.Mode.optimized
            else decisionMode
              (pilotUsesOptimized positions u processing sampleOrder))).length =
        positions.card := by simp
  rw [show positions.card =
      ((pilotJobList positions sampleOrder).map fun job =>
        Action.mk job
          (if job ∈ sampleJobs positions sampleOrder then Online.Mode.optimized
            else decisionMode
              (pilotUsesOptimized positions u processing sampleOrder))).length
    by exact hlength.symm]
  simp only [List.take_append_of_le_length (le_refl _), List.take_length]
  apply List.map_congr_left
  intro job hjob
  simp [hp job hjob]

theorem observedPilotDurations_of_plan_prefix {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ)
    (k : ℕ) (hk : positions.card ≤ k) :
    (((executePlan processing
        ((pilotOnlinePlan positions u processing sampleOrder mainOrder).take k)).take
          positions.card).map (Observation.duration u)) =
      pilotDurations positions processing sampleOrder := by
  have htake :
      ((pilotOnlinePlan positions u processing sampleOrder mainOrder).take k).take
          positions.card =
        (pilotOnlinePlan positions u processing sampleOrder mainOrder).take
          positions.card := by
    rw [List.take_take, Nat.min_eq_left hk]
  unfold executePlan
  rw [← List.map_take, htake, pilotOnlinePlan_take_pilot]
  unfold pilotDurations pilotJobList
  simp [Action.observation, Observation.duration]

theorem observedPilotDecision_of_plan_prefix {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ)
    (k : ℕ) (hk : positions.card ≤ k) :
    observedPilotDecision positions u
        (executePlan processing
          ((pilotOnlinePlan positions u processing sampleOrder mainOrder).take k)) =
      pilotUsesOptimized positions u processing sampleOrder := by
  unfold observedPilotDecision
  rw [observedPilotDurations_of_plan_prefix positions u processing sampleOrder
    mainOrder k hk]
  exact (pilotUsesOptimized_eq_observed positions u processing sampleOrder).symm

/-- For every fixed pair of private permutations, the transcript-only policy
agrees with its truthful processing-dependent proof plan.  The plan is not
an input to the strategy; it is only the certificate used by the execution
bridge. -/
theorem pilotOnlineStrategy_agrees {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    AgreesWithPlan processing
      (pilotOnlineStrategy positions u sampleOrder mainOrder)
      (pilotOnlinePlan positions u processing sampleOrder mainOrder) := by
  apply agreesWithPlan_of_indexed
  intro k hk
  have hlength :
      (executePlan processing
        ((pilotOnlinePlan positions u processing sampleOrder mainOrder).take k)).length =
        k := by
    rw [executePlan_length, List.length_take,
      Nat.min_eq_left hk]
  rw [List.head?_drop]
  unfold pilotOnlineStrategy
  rw [hlength]
  have hplanNext :
      (pilotOnlinePlan positions u processing sampleOrder mainOrder)[k]? =
        (pilotMainJobList positions sampleOrder mainOrder)[k]?.map
          (fun job => Action.mk job
            (if job ∈ sampleJobs positions sampleOrder then Online.Mode.optimized
              else decisionMode
                (pilotUsesOptimized positions u processing sampleOrder))) := by
    simp [pilotOnlinePlan]
  rw [hplanNext]
  cases hnext :
      (pilotMainJobList positions sampleOrder mainOrder)[k]? with
  | none => simp [hnext]
  | some job =>
      simp only [hnext, Option.map_some]
      by_cases hsample : job ∈ sampleJobs positions sampleOrder
      · simp [hsample]
      · have hkPilot : positions.card ≤ k := by
          by_contra hnot
          have hklt : k < positions.card := Nat.lt_of_not_ge hnot
          have hpilotGet :
              (pilotJobList positions sampleOrder)[k]? = some job := by
            rw [← hnext]
            unfold pilotMainJobList
            rw [List.getElem?_append_left]
            simpa using hklt
          have hmem : job ∈ pilotJobList positions sampleOrder :=
            List.mem_of_getElem? hpilotGet
          exact hsample
            ((mem_pilotJobList_iff positions sampleOrder job).mp hmem)
        rw [observedPilotDecision_of_plan_prefix positions u processing
          sampleOrder mainOrder k hkPilot]

/-- Every seeded pilot strategy is a completing operational strategy. -/
theorem pilotOnlineStrategy_completes {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    Completes processing (pilotOnlineStrategy positions u sampleOrder mainOrder) := by
  exact completes_of_agreesWithPlan processing
    (pilotOnlineStrategy positions u sampleOrder mainOrder)
    (pilotOnlinePlan positions u processing sampleOrder mainOrder)
    (pilotOnlinePlan_length positions u processing sampleOrder mainOrder)
    (pilotOnlinePlan_jobs_nodup positions u processing sampleOrder mainOrder)
    (pilotOnlinePlan_jobs_toFinset positions u processing sampleOrder mainOrder)
    (pilotOnlineStrategy_agrees positions u processing sampleOrder mainOrder)

/-- The operational plan has exactly the duration list used in the finite
cost calculation: optimized pilot observations followed by one random-order
raw or optimized main block. -/
theorem pilotOnlinePlan_duration_list {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    (executePlan processing
        (pilotOnlinePlan positions u processing sampleOrder mainOrder)).map
        (Observation.duration u) =
      pilotDurations positions processing sampleOrder ++
        randomOrderValues
          (if pilotUsesOptimized positions u processing sampleOrder then
            fun job : ↥(sampleJobs positions sampleOrder)ᶜ =>
              1 + processing job
          else fun _job : ↥(sampleJobs positions sampleOrder)ᶜ => u)
          mainOrder := by
  let use := pilotUsesOptimized positions u processing sampleOrder
  let sample := sampleJobs positions sampleOrder
  let planAction : Fin n → Action n := fun job =>
    ⟨job, if job ∈ sample then Online.Mode.optimized
      else decisionMode use⟩
  have hpilot :
      (((pilotJobList positions sampleOrder).map planAction).map
          (Action.observation processing)).map (Observation.duration u) =
        pilotDurations positions processing sampleOrder := by
    unfold pilotDurations pilotJobList
    simp only [List.map_map]
    apply List.map_congr_left
    intro job hjob
    have hsample : sampleOrder job ∈ sample := by
      dsimp [sample]
      exact Finset.mem_image.mpr ⟨job, by simpa using hjob, rfl⟩
    simp [planAction, hsample, Action.observation, Observation.duration]
  have hmain :
      (((mainJobList positions sampleOrder mainOrder).map planAction).map
          (Action.observation processing)).map (Observation.duration u) =
        randomOrderValues
          (if use then fun job : ↥sampleᶜ => 1 + processing job
            else fun _job : ↥sampleᶜ => u)
          mainOrder := by
    let durationJob : Fin n → ℝ :=
      if use then fun job => 1 + processing job else fun _job => u
    have hpoint :
        (((mainJobList positions sampleOrder mainOrder).map planAction).map
            (Action.observation processing)).map (Observation.duration u) =
          (mainJobList positions sampleOrder mainOrder).map durationJob := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro job hjob
      have hcomplement :=
        (mem_mainJobList_iff positions sampleOrder mainOrder job).mp hjob
      have hnot : job ∉ sample := by simpa [sample] using hcomplement
      cases huse : use <;>
        simp [planAction, durationJob, hnot, use, huse, decisionMode,
          Action.observation, Observation.duration, Function.comp_def]
    rw [hpoint]
    unfold mainJobList randomOrderValues
    rw [List.map_ofFn]
    cases huse : use <;>
      simp [durationJob, sample, use, huse, Function.comp_def]
  unfold executePlan pilotOnlinePlan pilotMainJobList
  change
    (((pilotJobList positions sampleOrder ++
        mainJobList positions sampleOrder mainOrder).map planAction).map
          (Action.observation processing)).map (Observation.duration u) = _
  rw [List.map_append, List.map_append, List.map_append, hpilot, hmain]

/-- The literal operational cost of one private seed is the previously
bounded `pilotMainCost`. -/
theorem pilotOnlineStrategy_runCost_eq_pilotMainCost {n : ℕ}
    (positions : Finset (Fin n)) (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n))
    (mainOrder : Equiv.Perm ↥(sampleJobs positions sampleOrder)ᶜ) :
    runCost u processing
        (pilotOnlineStrategy positions u sampleOrder mainOrder) n =
      pilotMainCost positions u processing sampleOrder mainOrder := by
  unfold runCost completionCost
  have hrun := run_transcript_eq_executePlan processing
    (pilotOnlineStrategy positions u sampleOrder mainOrder)
    (pilotOnlinePlan positions u processing sampleOrder mainOrder)
    (pilotOnlinePlan_jobs_nodup positions u processing sampleOrder mainOrder)
    (pilotOnlineStrategy_agrees positions u processing sampleOrder mainOrder)
  rw [pilotOnlinePlan_length positions u processing sampleOrder mainOrder] at hrun
  rw [hrun]
  rw [pilotOnlinePlan_duration_list]
  rfl

def conditionalExpectedPilotRunCost {n : ℕ}
    (positions : Finset (Fin n)) (hproper : positions.card < n)
    (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n)) : ℝ := by
  let Rest := ↥(sampleJobs positions sampleOrder)ᶜ
  have hcardRest : 0 < Fintype.card Rest := by
    dsimp [Rest]
    rw [Fintype.card_coe, Finset.card_compl, sampleJobs_card,
      Fintype.card_fin]
    omega
  letI : Nonempty Rest := Fintype.card_pos_iff.mp hcardRest
  exact Randomized.uniformAverage fun mainOrder : Equiv.Perm Rest =>
    runCost u processing
      (pilotOnlineStrategy positions u sampleOrder mainOrder) n

/-- Conditional expectation of the literal operational policy equals the
analytic conditional cost, seed by seed in the pilot permutation. -/
theorem conditionalExpectedPilotRunCost_eq {n : ℕ}
    (positions : Finset (Fin n)) (hproper : positions.card < n)
    (u : ℝ) (processing : Fin n → ℝ)
    (sampleOrder : Equiv.Perm (Fin n)) :
    conditionalExpectedPilotRunCost positions hproper u processing sampleOrder =
      conditionalExpectedPilotCost positions hproper u processing sampleOrder := by
  unfold conditionalExpectedPilotRunCost conditionalExpectedPilotCost
  dsimp only
  apply congrArg Randomized.uniformAverage
  funext mainOrder
  exact pilotOnlineStrategy_runCost_eq_pilotMainCost
    positions u processing sampleOrder mainOrder

/-- Fully operational finite randomized blind-optimization upper bound.
Every inner seed is a completing transcript-only strategy, and the normalized
error is the explicit quantity proved to vanish in
`pilotNormalizedError_tendsto_zero`. -/
theorem operationalPilot_expectedCost_le_curve_normalized
    {n : ℕ} (hn : 1 < n) {u : ℝ} (hu : 1 < u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (positions : Finset (Fin n)) (hpositions : positions.Nonempty)
    (hproper : positions.card < n) :
    Randomized.uniformAverage (fun sampleOrder : Equiv.Perm (Fin n) =>
      conditionalExpectedPilotRunCost positions hproper u processing sampleOrder) ≤
      randomizedCurve u * Online.offlineCost u processing +
        pilotNormalizedError u n positions.card * n ^ 2 := by
  have hanalytic := pilotPolicy_expectedCost_le_curve_normalized
    hn hu processing hp positions hpositions hproper
  have heq :
      (fun sampleOrder : Equiv.Perm (Fin n) =>
        conditionalExpectedPilotRunCost positions hproper u processing sampleOrder) =
      (fun sampleOrder : Equiv.Perm (Fin n) =>
        conditionalExpectedPilotCost positions hproper u processing sampleOrder) := by
    funext sampleOrder
    exact conditionalExpectedPilotRunCost_eq
      positions hproper u processing sampleOrder
  rwa [heq]

end

end BlindOptimization
end SchedulingPaper
