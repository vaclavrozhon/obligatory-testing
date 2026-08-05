import SchedulingPaper.LowerBoundAssembly
import SchedulingPaper.StrategyTermination

/-!
# The elementary finite-cap lower baseline

For `0 < u ≤ 1`, reveal the constant processing time `u` on every test and
use the same value as the replay default.  The frozen input is therefore the
all-`u` vector.  Any arbitrary deterministic strategy either settles without
completing every job, or its completed transcript costs at least
`u * triangular n`, exactly the offline value of that vector.

The termination argument is strategy-independent: the `2/1/0` work rank from
`StrategyTermination` strictly decreases after every successful action,
including raw execution.
-/

namespace SchedulingPaper

noncomputable section

namespace Online

/-! ## Strategy-independent settling after `2n+1` fuel -/

theorem remainingWork_update_raw
    (jobs : Label n → JobState) (job : Label n)
    (hjob : jobs job = .untouched) :
    (∑ i : Label n,
        jobWork ((Function.update jobs job .done) i)) + 2 =
      ∑ i : Label n, jobWork (jobs i) := by
  classical
  have hsum :
      (∑ i ∈ Finset.univ.erase job,
          jobWork ((Function.update jobs job .done) i)) =
        ∑ i ∈ Finset.univ.erase job, jobWork (jobs i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [Function.update, hi.1]
  calc
    (∑ i : Label n,
          jobWork ((Function.update jobs job .done) i)) + 2 =
        ((∑ i ∈ Finset.univ.erase job,
            jobWork ((Function.update jobs job .done) i)) +
          jobWork ((Function.update jobs job .done) job)) + 2 := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ job)]
    _ = ((∑ i ∈ Finset.univ.erase job, jobWork (jobs i)) +
          jobWork (jobs job)) := by
          rw [hsum]
          simp [Function.update, jobWork, hjob]
    _ = ∑ i : Label n, jobWork (jobs i) :=
      Finset.sum_erase_add _ _ (Finset.mem_univ job)

/-- Every successful operational step of an arbitrary strategy strictly
decreases the finite work rank. -/
theorem Config.remainingWork_step_lt
    {cap : Cap} {oracle : Oracle n} {config next : Config n}
    {action : Action n}
    (hstep : config.step cap oracle action = some next) :
    next.remainingWork < config.remainingWork := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
          subst next
          have hdrop :=
            remainingWork_update_test config.jobs job
              (oracle config.transcript job) hjob
          unfold Config.remainingWork
          change
            (∑ i : Label n,
                jobWork
                  ((Function.update config.jobs job
                    (.tested (oracle config.transcript job))) i)) <
              ∑ i : Label n, jobWork (config.jobs i)
          omega
      | tested p =>
          simp [Config.step, hjob] at hstep
      | done =>
          simp [Config.step, hjob] at hstep
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Config.step, hjob] at hstep
      | tested p =>
          simp [Config.step, hjob] at hstep
          subst next
          have hdrop :=
            remainingWork_update_process config.jobs job p hjob
          unfold Config.remainingWork
          change
            (∑ i : Label n,
                jobWork ((Function.update config.jobs job .done) i)) <
              ∑ i : Label n, jobWork (config.jobs i)
          omega
      | done =>
          simp [Config.step, hjob] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hjob : config.jobs job with
          | untouched =>
              simp [Config.step, hjob] at hstep
              subst next
              have hdrop :=
                remainingWork_update_raw config.jobs job hjob
              unfold Config.remainingWork
              change
                (∑ i : Label n,
                    jobWork ((Function.update config.jobs job .done) i)) <
                  ∑ i : Label n, jobWork (config.jobs i)
              omega
          | tested p =>
              simp [Config.step, hjob] at hstep
          | done =>
              simp [Config.step, hjob] at hstep

/-- Fuel strictly larger than the current work rank cannot be exhausted,
regardless of which deterministic strategy is used. -/
theorem runFuel_reason_ne_outOfFuel_of_remainingWork_lt
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hfuel : config.remainingWork < fuel) :
    (runFuel cap oracle strategy fuel config).reason ≠
      .outOfFuel := by
  induction fuel generalizing config with
  | zero =>
      omega
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simp
      | some action =>
          simp only
          cases hstep : config.step cap oracle action with
          | none =>
              simp
          | some next =>
              have hdrop : next.remainingWork < config.remainingWork :=
                Config.remainingWork_step_lt hstep
              have hnextFuel : next.remainingWork < fuel := by
                omega
              exact ih next hnextFuel

/-- In particular, every arbitrary strategy has a settled result after the
common analysis fuel `2n+1`.  Completion is not asserted. -/
theorem run_reason_ne_outOfFuel_analysisFuel
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n) :
    (run cap oracle strategy (2 * n + 1)).reason ≠ .outOfFuel := by
  unfold run
  apply runFuel_reason_ne_outOfFuel_of_remainingWork_lt
  rw [Config.initial_remainingWork]
  omega

/-! ## Freezing the constant adversary -/

/-- Every value already committed by the adaptive runner is the same
constant. -/
def AssignmentConstant (u : ℝ) (assignment : PartialAssignment n) : Prop :=
  ∀ job p, assignment job = some p → p = u

theorem emptyAssignment_constant (u : ℝ) :
    AssignmentConstant u (emptyAssignment : PartialAssignment n) := by
  intro job p h
  simp [emptyAssignment] at h

theorem adaptiveValue_constant
    (u : ℝ) (assignment : PartialAssignment n)
    (hassignment : AssignmentConstant u assignment)
    (transcript : Transcript n) (job : Label n) :
    adaptiveValue (fun _ _ => u) assignment transcript job = u := by
  cases hjob : assignment job with
  | none =>
      simp [adaptiveValue, hjob]
  | some p =>
      have hp : p = u := hassignment job p hjob
      simp [adaptiveValue, hjob, hp]

theorem assignmentAfter_constant
    (u : ℝ) (config : Config n) (assignment : PartialAssignment n)
    (action : Action n)
    (hassignment : AssignmentConstant u assignment) :
    AssignmentConstant u
      (assignmentAfter (fun _ _ => u) config assignment action) := by
  cases action with
  | process job =>
      exact hassignment
  | raw job =>
      exact hassignment
  | test testedJob =>
      intro job p hjob
      by_cases heq : job = testedJob
      · subst job
        have hvalue :=
          adaptiveValue_constant u assignment hassignment
            config.transcript testedJob
        have hup : u = p := by
          simpa [assignmentAfter, hvalue] using hjob
        exact hup.symm
      · apply hassignment job p
        simpa [assignmentAfter, Function.update, heq] using hjob

theorem adaptiveStep_constant
    (cap : Cap) (u : ℝ) (config next : Config n)
    (assignment nextAssignment : PartialAssignment n)
    (action : Action n)
    (hassignment : AssignmentConstant u assignment)
    (hstep :
      adaptiveStep cap (fun _ _ => u) config assignment action =
        some (next, nextAssignment)) :
    AssignmentConstant u nextAssignment := by
  unfold adaptiveStep at hstep
  cases hbase :
      config.step cap
        (adaptiveOracle (fun _ _ => u) assignment) action with
  | none =>
      simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact assignmentAfter_constant u config assignment action hassignment

theorem runAdaptiveFuel_assignment_constant
    (cap : Cap) (u : ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (assignment : PartialAssignment n)
    (hassignment : AssignmentConstant u assignment) :
    AssignmentConstant u
      (runAdaptiveFuel cap (fun _ _ => u) strategy fuel
        config assignment).assigned := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hassignment
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hassignment
      | some action =>
          cases hstep :
              adaptiveStep cap (fun _ _ => u) config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hassignment
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnext :=
                adaptiveStep_constant cap u config next assignment
                  nextAssignment action hassignment hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

/-- With constant revelations and the same constant default, replay freezes
exactly the all-`u` processing-time vector. -/
theorem frozenProcessingTimes_constant
    (cap : Cap) (u : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    frozenProcessingTimes cap (fun _ _ => u) strategy
        (fun _ => u) fuel =
      fun _ => u := by
  funext job
  have hconstant :
      AssignmentConstant u
        (adaptiveRun cap (fun _ _ => u) strategy fuel).assigned := by
    exact runAdaptiveFuel_assignment_constant cap u strategy fuel
      (Config.initial n) emptyAssignment (emptyAssignment_constant u)
  unfold frozenProcessingTimes completeAssignment
  cases hjob :
      (adaptiveRun cap (fun _ _ => u) strategy fuel).assigned job with
  | none =>
      simp
  | some p =>
      have hp : p = u := hconstant job p hjob
      simp [hp]

/-! ## A completion record for arbitrary strategies -/

/-- The subsequence of operations that can turn a positive constant job into
the state `done`.  Tests are deliberately omitted. -/
def Transcript.terminalLabels : Transcript n → List (Label n)
  | [] => []
  | .testResult _ _ :: rest => Transcript.terminalLabels rest
  | .processed job :: rest =>
      job :: Transcript.terminalLabels rest
  | .rawCompleted job :: rest =>
      job :: Transcript.terminalLabels rest

@[simp] theorem Transcript.terminalLabels_nil :
    (Transcript.terminalLabels ([] : Transcript n)) = [] := rfl

@[simp] theorem Transcript.terminalLabels_testResult_cons
    (job : Label n) (p : ℝ) (rest : Transcript n) :
    Transcript.terminalLabels (.testResult job p :: rest) =
      Transcript.terminalLabels rest := rfl

@[simp] theorem Transcript.terminalLabels_processed_cons
    (job : Label n) (rest : Transcript n) :
    Transcript.terminalLabels (.processed job :: rest) =
      job :: Transcript.terminalLabels rest := rfl

@[simp] theorem Transcript.terminalLabels_rawCompleted_cons
    (job : Label n) (rest : Transcript n) :
    Transcript.terminalLabels (.rawCompleted job :: rest) =
      job :: Transcript.terminalLabels rest := rfl

@[simp] theorem Transcript.terminalLabels_append
    (left right : Transcript n) :
    Transcript.terminalLabels (left ++ right) =
      Transcript.terminalLabels left ++
        Transcript.terminalLabels right := by
  induction left with
  | nil =>
      simp
  | cons observation rest ih =>
      cases observation <;> simp [ih]

@[simp] theorem Transcript.terminalLabels_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    Transcript.terminalLabels
        (transcript ++ [Observation.testResult job p]) =
      Transcript.terminalLabels transcript := by
  simp

@[simp] theorem Transcript.terminalLabels_append_processed
    (transcript : Transcript n) (job : Label n) :
    Transcript.terminalLabels
        (transcript ++ [Observation.processed job]) =
      Transcript.terminalLabels transcript ++ [job] := by
  simp

@[simp] theorem Transcript.terminalLabels_append_rawCompleted
    (transcript : Transcript n) (job : Label n) :
    Transcript.terminalLabels
        (transcript ++ [Observation.rawCompleted job]) =
      Transcript.terminalLabels transcript ++ [job] := by
  simp

/-- Every job marked done by a reachable configuration has a corresponding
process-or-raw observation in the public transcript. -/
def Config.DoneRecorded (config : Config n) : Prop :=
  ∀ job, config.jobs job = .done →
    job ∈ Transcript.terminalLabels config.transcript

theorem Config.initial_doneRecorded (n : ℕ) :
    (Config.initial n).DoneRecorded := by
  intro job hjob
  simp [Config.initial] at hjob

theorem Config.doneRecorded_step
    {cap : Cap} {oracle : Oracle n} {config next : Config n}
    {action : Action n}
    (hrecord : config.DoneRecorded)
    (hstep : config.step cap oracle action = some next) :
    next.DoneRecorded := by
  cases action with
  | test testedJob =>
      cases hstate : config.jobs testedJob with
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          intro job hdone
          rw [Transcript.terminalLabels_append_testResult]
          by_cases heq : job = testedJob
          · subst job
            simp [Function.update] at hdone
          · apply hrecord job
            simpa [Function.update, heq] using hdone
      | tested p =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
  | process processedJob =>
      cases hstate : config.jobs processedJob with
      | untouched =>
          simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          intro job hdone
          rw [Transcript.terminalLabels_append_processed]
          by_cases heq : job = processedJob
          · subst job
            simp
          · have hold : config.jobs job = .done := by
              simpa [Function.update, heq] using hdone
            simp [hrecord job hold, heq]
      | done =>
          simp [Config.step, hstate] at hstep
  | raw rawJob =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hstate : config.jobs rawJob with
          | untouched =>
              simp [Config.step, hstate] at hstep
              subst next
              intro job hdone
              rw [Transcript.terminalLabels_append_rawCompleted]
              by_cases heq : job = rawJob
              · subst job
                simp
              · have hold : config.jobs job = .done := by
                  simpa [Function.update, heq] using hdone
                simp [hrecord job hold, heq]
          | tested p =>
              simp [Config.step, hstate] at hstep
          | done =>
              simp [Config.step, hstate] at hstep

theorem runFuel_doneRecorded
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hrecord : config.DoneRecorded) :
    (runFuel cap oracle strategy fuel config).config.DoneRecorded := by
  induction fuel generalizing config with
  | zero =>
      simpa [runFuel] using hrecord
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runFuel, haction] using hrecord
      | some action =>
          cases hstep : config.step cap oracle action with
          | none =>
              simpa [runFuel, haction, hstep] using hrecord
          | some next =>
              have hnext := Config.doneRecorded_step hrecord hstep
              simpa [runFuel, haction, hstep] using ih next hnext

theorem run_doneRecorded
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) :
    (run cap oracle strategy fuel).config.DoneRecorded := by
  unfold run
  exact runFuel_doneRecorded cap oracle strategy fuel (Config.initial n)
    (Config.initial_doneRecorded n)

theorem Transcript.length_terminalLabels_ge_of_all_recorded
    (transcript : Transcript n)
    (hrecord :
      ∀ job : Label n, job ∈ Transcript.terminalLabels transcript) :
    n ≤ (Transcript.terminalLabels transcript).length := by
  classical
  have hsubset :
      (Finset.univ : Finset (Label n)) ⊆
        (Transcript.terminalLabels transcript).toFinset := by
    intro job _
    simpa using hrecord job
  have hcards :
      Finset.card (Finset.univ : Finset (Label n)) ≤
        (Transcript.terminalLabels transcript).toFinset.card :=
    Finset.card_le_card hsubset
  have hlist :
      (Transcript.terminalLabels transcript).toFinset.card ≤
        (Transcript.terminalLabels transcript).length :=
    List.toFinset_card_le (Transcript.terminalLabels transcript)
  simpa using hcards.trans hlist

theorem Config.terminalLabels_length_ge_of_completed
    (config : Config n) (hrecord : config.DoneRecorded)
    (hcompleted : ∀ job, config.jobs job = .done) :
    n ≤ (Transcript.terminalLabels config.transcript).length :=
  config.transcript.length_terminalLabels_ge_of_all_recorded
    (fun job => hrecord job (hcompleted job))

/-! ## Cost of the completion record -/

/-- For the all-`u` fixed instance, `k` process-or-raw observations cost at
least `k * time + u * triangular k` when the suffix begins at `time`.
Intervening tests only increase time (and a zero-valued test observation,
although unreachable for this oracle, can only add another completion). -/
theorem completionCostFrom_constant_lower
    {u time : ℝ} (hu : 0 < u) (htime : 0 ≤ time)
    (transcript : Transcript n) :
    let k := (Transcript.terminalLabels transcript).length
    (k : ℝ) * time + u * triangular k ≤
      completionCostFrom (.finite u) (fun _ => u) time transcript := by
  induction transcript generalizing time with
  | nil =>
      simp [completionCostFrom]
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          have hnextTime : 0 ≤ time + 1 := by linarith
          have htail := ih hnextTime
          have hk :
              0 ≤
                ((Transcript.terminalLabels rest).length : ℝ) := by
            positivity
          by_cases hp : p = 0
          · subst p
            simp only [Transcript.terminalLabels_testResult_cons]
            simp [completionCostFrom, Observation.duration,
              Observation.completionLabel] at *
            nlinarith
          · simp only [Transcript.terminalLabels_testResult_cons]
            simp [completionCostFrom, Observation.duration,
              Observation.completionLabel, hp] at *
            nlinarith
      | processed job =>
          have hnextTime : 0 ≤ time + u :=
            add_nonneg htime hu.le
          have htail := ih hnextTime
          simp only [Transcript.terminalLabels_processed_cons,
            List.length_cons]
          simp [completionCostFrom, Observation.duration,
            Observation.completionLabel, ne_of_gt hu, triangular_succ] at *
          nlinarith
      | rawCompleted job =>
          have hnextTime : 0 ≤ time + u :=
            add_nonneg htime hu.le
          have htail := ih hnextTime
          simp only [Transcript.terminalLabels_rawCompleted_cons,
            List.length_cons]
          simp [completionCostFrom, Observation.duration, rawDuration,
            Observation.completionLabel, triangular_succ] at *
          nlinarith

/-- The carried-time estimate at time zero. -/
theorem completionCost_constant_lower
    {u : ℝ} (hu : 0 < u) (transcript : Transcript n) :
    u * triangular (Transcript.terminalLabels transcript).length ≤
      completionCost (.finite u) (fun _ => u) transcript := by
  simpa [completionCost] using
    completionCostFrom_constant_lower (n := n) hu (le_refl 0) transcript

/-- The adaptive result is reachable by an ordinary fixed-oracle run, hence
it satisfies the same completion-record invariant. -/
theorem adaptiveRun_doneRecorded
    (cap : Cap) (adversary : Oracle n) (strategy : Strategy n)
    (default : Label n → ℝ) (fuel : ℕ) :
    (adaptiveRun cap adversary strategy fuel).result.config.DoneRecorded := by
  have hrecord :=
    run_doneRecorded cap
      (fixedOracle
        (frozenProcessingTimes cap adversary strategy default fuel))
      strategy fuel
  rw [replay cap adversary strategy default fuel] at hrecord
  exact hrecord

end Online

theorem triangular_mono {a b : ℕ} (hab : a ≤ b) :
    triangular a ≤ triangular b := by
  unfold triangular
  have ha : 0 ≤ (a : ℝ) := by positivity
  have hb : 0 ≤ (b : ℝ) := by positivity
  have habReal : (a : ℝ) ≤ (b : ℝ) :=
    Nat.cast_le.mpr hab
  nlinarith

namespace LowerBound

/-! ## The all-`u` offline benchmark -/

theorem vectorEffectiveLengths_constant_of_cap_le_one
    (n : ℕ) {u : ℝ} (_hu : u ≤ 1) :
    vectorEffectiveLengths (.finite u) (fun _ : Online.Label n => u) =
      List.replicate n u := by
  unfold vectorEffectiveLengths
  rw [List.ofFn_const]
  apply List.replicate_inj.mpr
  refine ⟨rfl, Or.inr ?_⟩
  simp only [effectiveLength_finite]
  exact min_eq_left (by linarith)

theorem vectorOfflineCost_constant_of_cap_le_one
    (n : ℕ) {u : ℝ} (hu : u ≤ 1) :
    vectorOfflineCost (.finite u) (fun _ : Online.Label n => u) =
      u * triangular n := by
  have heffective :=
    vectorEffectiveLengths_constant_of_cap_le_one n hu
  calc
    vectorOfflineCost (.finite u) (fun _ : Online.Label n => u) =
        pairCost
          (vectorEffectiveLengths (.finite u)
            (fun _ : Online.Label n => u)) := by
      exact shortestFirst_pair_formula _
    _ = pairCost (List.replicate n u) := by rw [heffective]
    _ = prefixCost (List.replicate n u) := by
      symm
      exact prefixCost_eq_pairCost_of_pairwise (by simp)
    _ = u * triangular n := prefixCost_replicate n u

/-! ## Elementary adaptive lower bound -/

/-- The operational lower interface on the entire low-cap interval. -/
theorem lowBaseline
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    AdaptiveSizeLowerBound (.finite u) 1 := by
  intro strategies ε hε N
  let adversary : Online.Oracle N := fun _ _ => u
  let default : Online.Label N → ℝ := fun _ => u
  let fuel : ℕ := 2 * N + 1
  refine ⟨N, le_rfl, adversary, default, fuel, ?_, ?_, ?_⟩
  · intro transcript job
    exact ⟨hu.le, le_rfl⟩
  · intro job
    exact ⟨hu.le, le_rfl⟩
  · let frozen :=
      Online.frozenProcessingTimes (.finite u) adversary
        (strategies N) default fuel
    let result :=
      (Online.adaptiveRun (.finite u) adversary
        (strategies N) fuel).result
    change
      resultSettled result ∧
        (¬ resultCompleted result ∨
          (1 - ε) * vectorOfflineCost (.finite u) frozen ≤
            Online.runCompletionCost (.finite u) frozen result)
    have hfrozen :
        frozen = (fun _ : Online.Label N => u) := by
      simpa [frozen, adversary, default] using
        Online.frozenProcessingTimes_constant
          (.finite u) u (strategies N) fuel
    have hreplay :
        Online.run (.finite u) (Online.fixedOracle frozen)
            (strategies N) fuel =
          result := by
      simpa [frozen, result, adversary, default] using
        Online.replay (.finite u) adversary
          (strategies N) default fuel
    have hsettledFixed :
        (Online.run (.finite u) (Online.fixedOracle frozen)
          (strategies N) fuel).reason ≠ .outOfFuel := by
      simpa [fuel] using
        Online.run_reason_ne_outOfFuel_analysisFuel
          (.finite u) (Online.fixedOracle frozen) (strategies N)
    have hsettled : resultSettled result := by
      unfold resultSettled
      rw [← hreplay]
      exact hsettledFixed
    refine ⟨hsettled, ?_⟩
    by_cases hcompleted : resultCompleted result
    · right
      have hrecord : result.config.DoneRecorded := by
        simpa [result, adversary, default] using
          Online.adaptiveRun_doneRecorded
            (.finite u) adversary (strategies N) default fuel
      have hcount :
          N ≤
            (Online.Transcript.terminalLabels
              result.config.transcript).length := by
        exact Online.Config.terminalLabels_length_ge_of_completed
          result.config hrecord hcompleted
      have htri :
          triangular N ≤
            triangular
              (Online.Transcript.terminalLabels
                result.config.transcript).length :=
        triangular_mono hcount
      have hcostConstant :
          u * triangular
              (Online.Transcript.terminalLabels
                result.config.transcript).length ≤
            Online.runCompletionCost (.finite u)
              (fun _ : Online.Label N => u) result := by
        simpa [Online.runCompletionCost] using
          Online.completionCost_constant_lower
            (n := N) hu result.config.transcript
      have hcost :
          u * triangular N ≤
            Online.runCompletionCost (.finite u) frozen result := by
        rw [hfrozen]
        exact
          (mul_le_mul_of_nonneg_left htri hu.le).trans hcostConstant
      have hoffline :
          vectorOfflineCost (.finite u) frozen =
            u * triangular N := by
        rw [hfrozen]
        exact vectorOfflineCost_constant_of_cap_le_one N huOne
      rw [hoffline]
      have htriNonneg : 0 ≤ triangular N := by
        unfold triangular
        positivity
      calc
        (1 - ε) * (u * triangular N) =
            u * triangular N - ε * (u * triangular N) := by ring
        _ ≤ u * triangular N := by
          apply sub_le_self
          exact mul_nonneg hε.le (mul_nonneg hu.le htriNonneg)
        _ ≤ Online.runCompletionCost (.finite u) frozen result := hcost
    · exact Or.inl hcompleted

/-- The theorem in exactly the field type expected by
`OperationalLowerInterfaces.baseline`. -/
theorem operationalLowerBaseline :
    ∀ {u : ℝ}, 0 < u → u ≤ 1 →
      AdaptiveSizeLowerBound (.finite u) 1 :=
  fun hu huOne => lowBaseline hu huOne

end LowerBound

end

end SchedulingPaper
