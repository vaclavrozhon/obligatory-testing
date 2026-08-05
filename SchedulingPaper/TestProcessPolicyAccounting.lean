import SchedulingPaper.TestProcessRuntimeAccounting
import SchedulingPaper.ObligatoryPairAccounting
import Mathlib.Tactic

/-!
# Policy-sensitive accounting for test/process traces

The canonical-trace grammar remembers the three possible shapes of a pair,
but deliberately forgets why a particular process operation was selected.
This file retains that small piece of operational information.  It is
generic in the strategy, so it can be reused by every policy built on the
test/process skeleton.
-/

namespace SchedulingPaper.Online

noncomputable section

/-- The request whose successful execution publishes an observation. -/
def Observation.requestedAction : Observation n → Action n
  | .testResult job _ => .test job
  | .processed job => .process job
  | .rawCompleted job => .raw job

/-- At every position of a public transcript, the observation there was
requested by the strategy on the preceding prefix. -/
def Transcript.FollowsStrategy
    (strategy : Strategy n) (transcript : Transcript n) : Prop :=
  ∀ index : Fin transcript.length,
    strategy (transcript.take index.val) =
      some (transcript.get index).requestedAction

@[simp] theorem Transcript.followsStrategy_nil
    (strategy : Strategy n) :
    Transcript.FollowsStrategy strategy [] := by
  intro index
  exact Fin.elim0 index

theorem Transcript.FollowsStrategy.append
    {strategy : Strategy n} {transcript : Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    (observation : Observation n)
    (haction :
      strategy transcript = some observation.requestedAction) :
    (transcript ++ [observation]).FollowsStrategy strategy := by
  intro index
  by_cases hindex : index.val < transcript.length
  · have hold :
        strategy (transcript.take index.val) =
          some
            ((transcript.get
              ⟨index.val, hindex⟩).requestedAction) :=
      hfollow ⟨index.val, hindex⟩
    have htake :
        (transcript ++ [observation]).take index.val =
          transcript.take index.val :=
      List.take_append_of_le_length hindex.le
    have hget :
        (transcript ++ [observation]).get index =
          transcript.get ⟨index.val, hindex⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left hindex
    rw [htake, hget]
    exact hold
  · have hvalue : index.val = transcript.length := by
      have hbound : index.val < transcript.length + 1 := by
        simpa using index.isLt
      omega
    have htake :
        (transcript ++ [observation]).take index.val =
          transcript := by
      rw [hvalue]
      exact List.take_left
    have hget :
        (transcript ++ [observation]).get index =
          observation := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hvalue]
    rw [htake, hget]
    exact haction

theorem Config.step_observation
    {cap : Cap} {oracle : Oracle n}
    {config next : Config n} {action : Action n}
    (hstep : config.step cap oracle action = some next) :
    ∃ observation,
      next.transcript = config.transcript ++ [observation] ∧
      observation.requestedAction = action := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          exact
            ⟨.testResult job (oracle config.transcript job),
              rfl, rfl⟩
      | tested p =>
          simp [Config.step, hstate] at hstep
      | done =>
          simp [Config.step, hstate] at hstep
  | process job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp [Config.step, hstate] at hstep
      | tested p =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          exact ⟨.processed job, rfl, rfl⟩
      | done =>
          simp [Config.step, hstate] at hstep
  | raw job =>
      cases cap with
      | infinite =>
          simp [Config.step] at hstep
      | finite u =>
          cases hstate : config.jobs job with
          | untouched =>
              simp only [Config.step, hstate,
                Option.some.injEq] at hstep
              subst next
              exact ⟨.rawCompleted job, rfl, rfl⟩
          | tested p =>
              simp [Config.step, hstate] at hstep
          | done =>
              simp [Config.step, hstate] at hstep

/-- A fuelled execution retains the strategy-consistency property. -/
theorem runFuel_followsStrategy
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hfollow : config.transcript.FollowsStrategy strategy) :
    (runFuel cap oracle strategy fuel config).config.transcript
      |>.FollowsStrategy strategy := by
  induction fuel generalizing config with
  | zero =>
      simpa [runFuel] using hfollow
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simp only
          exact hfollow
      | some action =>
          simp only
          cases hstep : config.step cap oracle action with
          | none =>
              simp only
              exact hfollow
          | some next =>
              simp only
              obtain ⟨observation, htranscript, hobservation⟩ :=
                Config.step_observation hstep
              apply ih
              rw [htranscript]
              apply hfollow.append
              rw [hobservation]
              exact haction

theorem run_followsStrategy
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) :
    (run cap oracle strategy fuel).config.transcript
      |>.FollowsStrategy strategy := by
  unfold run
  exact
    runFuel_followsStrategy cap oracle strategy fuel
      (Config.initial n)
      (Transcript.followsStrategy_nil strategy)

/-- Extract the policy request at an arbitrary displayed observation. -/
theorem Transcript.FollowsStrategy.action_at
    {strategy : Strategy n} {transcript : Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    {before after : Transcript n} {observation : Observation n}
    (hdecomp :
      transcript = before ++ observation :: after) :
    strategy before = some observation.requestedAction := by
  subst transcript
  let index : Fin (before ++ observation :: after).length :=
    ⟨before.length, by
      simp⟩
  have h := hfollow index
  simpa [index, List.get_eq_getElem] using h

/-- If the policy reports a pending immediate job after a displayed test,
the next observation in a completed transcript is its process operation. -/
theorem follows_testProcessStrategy_next_processed
    {pending : Transcript n → Option (Label n)}
    {transcript before after : Transcript n}
    {job : Label n} {p : ℝ}
    (hfollow :
      transcript.FollowsStrategy (testProcessStrategy pending))
    (hdecomp :
      transcript =
        before ++ Observation.testResult job p :: after)
    (hpending :
      pending (before ++ [.testResult job p]) = some job)
    (hnotBefore : job ∉ before.processedLabels)
    (hjobProcessed : job ∈ transcript.processedLabels) :
    ∃ rest, after = .processed job :: rest := by
  cases after with
  | nil =>
      rw [hdecomp] at hjobProcessed
      have heq :
          (before ++ [Observation.testResult job p]).processedLabels =
            before.processedLabels := by simp
      rw [heq] at hjobProcessed
      exact (hnotBefore hjobProcessed).elim
  | cons observation rest =>
      have haction :=
        hfollow.action_at
          (before := before ++ [.testResult job p])
          (after := rest) (observation := observation) (by
            simpa [List.append_assoc] using hdecomp)
      unfold testProcessStrategy at haction
      rw [hpending] at haction
      simp only [Option.some.injEq] at haction
      cases observation <;> simp [Observation.requestedAction] at haction
      next processedJob =>
        subst processedJob
        exact ⟨rest, rfl⟩

/-! ## The shortest-remaining suffix -/

private theorem shortestFold_minimal
    (best : Label n × ℝ) (rest : List (Label n × ℝ)) :
    let chosen :=
      rest.foldl
        (fun current candidate =>
          if candidate.2 < current.2 then candidate else current)
        best
    chosen.2 ≤ best.2 ∧
      ∀ candidate ∈ rest, chosen.2 ≤ candidate.2 := by
  induction rest generalizing best with
  | nil =>
      simp
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hlt : candidate.2 < best.2
      · simp only [if_pos hlt]
        have htail := ih candidate
        refine ⟨htail.1.trans hlt.le, ?_⟩
        intro other hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | htailMem
        · subst other
          exact htail.1
        · exact htail.2 other htailMem
      · simp only [if_neg hlt]
        have htail := ih best
        refine ⟨htail.1, ?_⟩
        intro other hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | htailMem
        · subst other
          exact htail.1.trans (le_of_not_gt hlt)
        · exact htail.2 other htailMem

/-- `shortestResult?` really selects a minimum revealed value. -/
theorem shortestResult?_processing_le
    {results : List (Label n × ℝ)}
    {chosen candidate : Label n × ℝ}
    (hchosen : shortestResult? results = some chosen)
    (hcandidate : candidate ∈ results) :
    chosen.2 ≤ candidate.2 := by
  cases results with
  | nil =>
      simp [shortestResult?] at hchosen
  | cons best rest =>
      simp only [shortestResult?, Option.some.injEq] at hchosen
      subst chosen
      have hminimal := shortestFold_minimal best rest
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with heq | htail
      · subst candidate
        exact hminimal.1
      · exact hminimal.2 candidate htail

/-- A selected remaining label has processing time no larger than any other
currently tested and unprocessed label. -/
theorem shortestRemaining_processing_le
    {processingTime : Label n → ℝ}
    {transcript : Transcript n} {chosen other : Label n}
    {q : ℝ}
    (hmatch : transcript.TestsMatch processingTime)
    (hshort : transcript.shortestRemaining? = some chosen)
    (hother :
      (other, q) ∈ transcript.remainingTestResults) :
    processingTime chosen ≤ q := by
  unfold Transcript.shortestRemaining? at hshort
  cases hresult :
      shortestResult? transcript.remainingTestResults with
  | none =>
      simp [hresult] at hshort
  | some result =>
      have hlabel : result.1 = chosen := by
        simpa [hresult] using hshort
      have hresultMem :
          result ∈ transcript.remainingTestResults :=
        shortestResult?_mem hresult
      have hvalue :
          result.2 = processingTime result.1 := by
        apply hmatch
        exact (List.mem_filter.mp hresultMem).1
      have hle :=
        shortestResult?_processing_le hresult hother
      rw [hvalue, hlabel] at hle
      exact hle

/-- A job for which the pending selector is false immediately after every
displayed test occurrence in the terminal transcript.  Canonical traces
have one such occurrence, but the definition is deliberately generic. -/
def Transcript.DeferredFor
    (pending : Transcript n → Option (Label n))
    (transcript : Transcript n) (job : Label n) : Prop :=
  ∀ before after p,
    transcript = before ++ .testResult job p :: after →
      pending (before ++ [.testResult job p]) = none

def Transcript.ImmediateFor
    (pending : Transcript n → Option (Label n))
    (transcript : Transcript n) (job : Label n) : Prop :=
  ∀ before after p,
    transcript = before ++ .testResult job p :: after →
      pending (before ++ [.testResult job p]) = some job

/-- In a completed policy-consistent test/process transcript, a deferred
job can only be processed in the all-tests-complete suffix, and its process
request is exactly the current shortest-remaining request. -/
theorem follows_deferred_process_is_shortest
    {pending : Transcript n → Option (Label n)}
    (hpending : SelectsLastTest pending)
    {transcript before after : Transcript n}
    {job : Label n}
    (hfollow :
      transcript.FollowsStrategy (testProcessStrategy pending))
    (hdeferred : transcript.DeferredFor pending job)
    (hprocess :
      transcript = before ++ .processed job :: after)
    (htestBound : before.testResults.length ≤ n) :
    pending before = none ∧
      before.testResults.length = n ∧
      before.shortestRemaining? = some job := by
  have haction :=
    hfollow.action_at
      (before := before) (after := after)
      (observation := .processed job) hprocess
  unfold testProcessStrategy at haction
  cases hp : pending before with
  | some selected =>
      simp only [hp, Option.some.injEq] at haction
      change Action.process selected = Action.process job at haction
      cases haction
      obtain ⟨p, hlast⟩ := hpending before job hp
      obtain ⟨prior, hbefore⟩ :=
        List.getLast?_eq_some_iff.mp hlast
      have hnone :
          pending (prior ++ [.testResult job p]) = none := by
        apply hdeferred prior (.processed job :: after) p
        rw [hprocess, hbefore]
        simp [List.append_assoc]
      rw [← hbefore] at hnone
      rw [hp] at hnone
      contradiction
  | none =>
      simp only [hp] at haction
      split at haction
      next hlt =>
        simp [Observation.requestedAction] at haction
      next hnotlt =>
        split at haction
        next selected hshort =>
          simp only [Option.some.injEq] at haction
          change Action.process selected = Action.process job at haction
          cases haction
          exact
            ⟨rfl, by omega, hshort⟩
        next hnone =>
          simp at haction

/-! ## Small list facts used by pair accounting -/

theorem processed_mem_iff_observation_mem
    (transcript : Transcript n) (job : Label n) :
    job ∈ transcript.processedLabels ↔
      .processed job ∈ transcript := by
  induction transcript with
  | nil => simp [Transcript.processedLabels]
  | cons observation transcript ih =>
      cases observation with
      | testResult observed q =>
          rw [show
            Transcript.processedLabels
                (.testResult observed q :: transcript) =
              Transcript.processedLabels transcript by rfl]
          simp only [List.mem_cons, reduceCtorEq, false_or]
          exact ih
      | processed observed =>
          rw [show
            Transcript.processedLabels
                (.processed observed :: transcript) =
              observed :: Transcript.processedLabels transcript by rfl]
          simp only [List.mem_cons, Observation.processed.injEq]
          rw [ih]
      | rawCompleted observed =>
          rw [show
            Transcript.processedLabels
                (.rawCompleted observed :: transcript) =
              Transcript.processedLabels transcript by rfl]
          simp only [List.mem_cons, reduceCtorEq, false_or]
          exact ih

theorem testResult_mem_iff_observation_mem
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    (job, p) ∈ transcript.testResults ↔
      .testResult job p ∈ transcript := by
  induction transcript with
  | nil => simp [Transcript.testResults]
  | cons observation transcript ih =>
      cases observation with
      | testResult observed q =>
          rw [show
            Transcript.testResults
                (.testResult observed q :: transcript) =
              (observed, q) :: Transcript.testResults transcript by rfl]
          simp only [List.mem_cons, Observation.testResult.injEq,
            Prod.mk.injEq]
          rw [ih]
      | processed observed =>
          rw [show
            Transcript.testResults (.processed observed :: transcript) =
              Transcript.testResults transcript by rfl]
          simp only [List.mem_cons, reduceCtorEq, false_or]
          exact ih
      | rawCompleted observed =>
          rw [show
            Transcript.testResults
                (.rawCompleted observed :: transcript) =
              Transcript.testResults transcript by rfl]
          simp only [List.mem_cons, reduceCtorEq, false_or]
          exact ih

private theorem split_at_third_of_four
    {α : Type*} {prior suffix : List α} {a b c d : α}
    (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d)
    (heq : prior ++ c :: suffix = [a, b, c, d]) :
    prior = [a, b] := by
  cases prior with
  | nil => simp_all
  | cons first prior =>
      cases prior with
      | nil => simp_all
      | cons second prior =>
          cases prior with
          | nil => simp_all
          | cons third prior =>
              cases prior with
              | nil => simp_all
              | cons fourth prior =>
                  have hlength := congrArg List.length heq
                  simp at hlength

private theorem split_at_second_of_four
    {α : Type*} {prior suffix : List α} {a b c d : α}
    (hba : b ≠ a) (hbc : b ≠ c) (hbd : b ≠ d)
    (heq : prior ++ b :: suffix = [a, b, c, d]) :
    prior = [a] ∧ suffix = [c, d] := by
  cases prior with
  | nil => simp_all
  | cons first prior =>
      cases prior with
      | nil => simp_all
      | cons second prior =>
          cases prior with
          | nil => simp_all
          | cons third prior =>
              cases prior with
              | nil => simp_all
              | cons fourth prior =>
                  have hlength := congrArg List.length heq
                  simp at hlength

private theorem split_at_first_of_two
    {α : Type*} {prior suffix : List α} {a b : α}
    (hab : a ≠ b)
    (heq : prior ++ a :: suffix = [a, b]) :
    prior = [] := by
  cases prior with
  | nil => rfl
  | cons first prior =>
      cases prior with
      | nil => simp_all
      | cons second prior =>
          have hlength := congrArg List.length heq
          simp at hlength

/-- In a terminal canonical test/process trace, a label has not yet been
processed at the prefix immediately preceding its unique test. -/
theorem TestProcessTrace.not_processed_before_test
    {processingTime : Label n → ℝ}
    {transcript before after : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed :
      ∀ job, job ∈ transcript.processedLabels)
    (job : Label n) (p : ℝ)
    (hdecomp :
      transcript = before ++ .testResult job p :: after) :
    job ∉ before.processedLabels := by
  have hp : p = processingTime job := by
    apply hmatch job p
    apply (testResult_mem_iff_observation_mem transcript job p).2
    rw [hdecomp]
    simp
  have hself :=
    htrace.terminal_selfProjection
      hmatch hallTests hallProcessed job
  have heq :
      before.pairProjection job job ++
          .testResult job p :: after.pairProjection job job =
        [.testResult job p, .processed job] := by
    rw [← hp] at hself
    rw [← hself, hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel]
  have hbefore :
      before.pairProjection job job = [] :=
    split_at_first_of_two (by simp) heq
  intro hprocessed
  have hobservation :
      Observation.processed job ∈ before :=
    (processed_mem_iff_observation_mem before job).1 hprocessed
  have hprojectionMem :
      Observation.processed job ∈
        before.pairProjection job job := by
    unfold Transcript.pairProjection
    exact List.mem_filter.mpr
      ⟨hobservation, by
        simp [Observation.ownerLabel]⟩
  rw [hbefore] at hprojectionMem
  simp at hprojectionMem

private theorem left_test_process_not_infix_rightFirst
    {left right : Label n} (hne : left ≠ right) (p q : ℝ) :
    ¬([.testResult left p, .processed left] : Transcript n) <:+:
      [.testResult left p, .testResult right q,
        .processed right, .processed left] := by
  rintro ⟨prior, suffix, heq⟩
  cases prior with
  | nil => simp at heq
  | cons first prior =>
      cases prior with
      | nil =>
          simp at heq
          exact hne heq.2.1.1
      | cons second prior =>
          cases prior with
          | nil => simp at heq
          | cons third prior =>
              have hlength := congrArg List.length heq
              simp at hlength
              omega

private theorem left_test_process_not_infix_leftFirst
    {left right : Label n} (hne : left ≠ right) (p q : ℝ) :
    ¬([.testResult left p, .processed left] : Transcript n) <:+:
      [.testResult left p, .testResult right q,
        .processed left, .processed right] := by
  rintro ⟨prior, suffix, heq⟩
  cases prior with
  | nil => simp at heq
  | cons first prior =>
      cases prior with
      | nil => simp [hne] at heq
      | cons second prior =>
          cases prior with
          | nil => simp at heq
          | cons third prior =>
              have hlength := congrArg List.length heq
              simp at hlength
              omega

private theorem right_test_process_not_infix_leftFirst
    {left right : Label n} (hne : left ≠ right) (p q : ℝ) :
    ¬([.testResult right q, .processed right] : Transcript n) <:+:
      [.testResult left p, .testResult right q,
        .processed left, .processed right] := by
  rintro ⟨prior, suffix, heq⟩
  cases prior with
  | nil => simp at heq
  | cons first prior =>
      cases prior with
      | nil =>
          simp at heq
          exact hne heq.2.1.symm
      | cons second prior =>
          cases prior with
          | nil => simp at heq
          | cons third prior =>
              have hlength := congrArg List.length heq
              simp at hlength
              omega

private theorem pairProjection_test_process_infix_left
    {transcript before rest : Transcript n}
    {left right : Label n} (hne : left ≠ right) (p : ℝ)
    (hdecomp :
      transcript =
        before ++ [.testResult left p, .processed left] ++ rest) :
    ([.testResult left p, .processed left] : Transcript n) <:+:
      transcript.pairProjection left right := by
  have hprojection :
      transcript.pairProjection left right =
        before.pairProjection left right ++
          [.testResult left p, .processed left] ++
          rest.pairProjection left right := by
    rw [hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel, hne]
  rw [hprojection]
  exact List.infix_append _ _ _

private theorem pairProjection_test_process_infix_right
    {transcript before rest : Transcript n}
    {left right : Label n} (hne : left ≠ right) (q : ℝ)
    (hdecomp :
      transcript =
        before ++ [.testResult right q, .processed right] ++ rest) :
    ([.testResult right q, .processed right] : Transcript n) <:+:
      transcript.pairProjection left right := by
  have hprojection :
      transcript.pairProjection left right =
        before.pairProjection left right ++
          [.testResult right q, .processed right] ++
          rest.pairProjection left right := by
    rw [hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel, hne]
  rw [hprojection]
  exact List.infix_append _ _ _

private theorem pairProjection_before_rightProcess
    {transcript before after : Transcript n}
    {left right : Label n} (hne : left ≠ right) (p q : ℝ)
    (hdecomp :
      transcript = before ++ .processed right :: after)
    (hshape :
      transcript.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed right, .processed left]) :
    before.pairProjection left right =
      [.testResult left p, .testResult right q] := by
  have heq :
      before.pairProjection left right ++
          .processed right :: after.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed right, .processed left] := by
    rw [← hshape, hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel]
  exact split_at_third_of_four
    (by simp) (by simp)
    (by simpa using hne.symm) heq

private theorem pairProjection_after_leftProcess_oneTest
    {transcript before after : Transcript n}
    {left right : Label n} (hne : left ≠ right) (p q : ℝ)
    (hdecomp :
      transcript = before ++ .processed left :: after)
    (hshape :
      transcript.pairProjection left right =
        [.testResult left p, .processed left,
          .testResult right q, .processed right]) :
    after.pairProjection left right =
      [.testResult right q, .processed right] := by
  have heq :
      before.pairProjection left right ++
          .processed left :: after.pairProjection left right =
        [.testResult left p, .processed left,
          .testResult right q, .processed right] := by
    rw [← hshape, hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel]
  exact
    (split_at_second_of_four
      (by simp) (by simp)
      (by simpa using hne) heq).2

private theorem pairProjection_before_leftProcess
    {transcript before after : Transcript n}
    {left right : Label n} (hne : left ≠ right) (p q : ℝ)
    (hdecomp :
      transcript = before ++ .processed left :: after)
    (hshape :
      transcript.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed left, .processed right]) :
    before.pairProjection left right =
      [.testResult left p, .testResult right q] := by
  have heq :
      before.pairProjection left right ++
          .processed left :: after.pairProjection left right =
        [.testResult left p, .testResult right q,
          .processed left, .processed right] := by
    rw [← hshape, hdecomp]
    simp [Transcript.pairProjection, Observation.ownerLabel]
  exact split_at_third_of_four
    (by simp) (by simp)
    (by simpa using hne) heq

private theorem left_remaining_of_pairProjection_tests
    {before : Transcript n} {left right : Label n}
    (hne : left ≠ right) (p q : ℝ)
    (hprojection :
      before.pairProjection left right =
        [.testResult left p, .testResult right q]) :
    (left, p) ∈ before.remainingTestResults := by
  unfold Transcript.remainingTestResults
  apply List.mem_filter.mpr
  constructor
  · apply (testResult_mem_iff_observation_mem before left p).2
    have hmem :
        Observation.testResult left p ∈
          before.pairProjection left right := by
      rw [hprojection]
      simp
    exact (List.mem_filter.mp hmem).1
  · simp only [decide_eq_true_eq]
    intro hprocessed
    have hobservation :
        Observation.processed left ∈ before :=
      (processed_mem_iff_observation_mem before left).1 hprocessed
    have hmem :
        Observation.processed left ∈
          before.pairProjection left right := by
      exact List.mem_filter.mpr
        ⟨hobservation, by
          simp [Observation.ownerLabel]⟩
    rw [hprojection] at hmem
    simp at hmem

private theorem right_remaining_of_pairProjection_tests
    {before : Transcript n} {left right : Label n}
    (hne : left ≠ right) (p q : ℝ)
    (hprojection :
      before.pairProjection left right =
        [.testResult left p, .testResult right q]) :
    (right, q) ∈ before.remainingTestResults := by
  unfold Transcript.remainingTestResults
  apply List.mem_filter.mpr
  constructor
  · apply (testResult_mem_iff_observation_mem before right q).2
    have hmem :
        Observation.testResult right q ∈
          before.pairProjection left right := by
      rw [hprojection]
      simp
    exact (List.mem_filter.mp hmem).1
  · simp only [decide_eq_true_eq]
    intro hprocessed
    have hobservation :
        Observation.processed right ∈ before :=
      (processed_mem_iff_observation_mem before right).1 hprocessed
    have hmem :
        Observation.processed right ∈
          before.pairProjection left right := by
      exact List.mem_filter.mpr
        ⟨hobservation, by
          simp [Observation.ownerLabel]⟩
    rw [hprojection] at hmem
    simp at hmem

/-! ## Exact status-table pair accounting -/

/-- The literal pair charge of a policy-consistent completed test/process
run is the obligatory status table.  The assumptions mention only the
pending-after-test decision and hence apply to any concrete threshold
policy; SPT ordering of two deferred jobs is derived operationally. -/
theorem TestProcessTrace.tracePairCharge_eq_obligatoryALGPairCharge
    {processingTime : Label n → ℝ}
    {pending : Transcript n → Option (Label n)}
    {transcript : Transcript n}
    (htrace : TestProcessTrace transcript)
    (hmatch : transcript.TestsMatch processingTime)
    (hallTests : transcript.testResults.length = n)
    (hallProcessed :
      ∀ job, job ∈ transcript.processedLabels)
    (hfollow :
      transcript.FollowsStrategy (testProcessStrategy pending))
    (hpending : SelectsLastTest pending)
    (outcome : Label n → BoundaryOutcome)
    (himmediate :
      ∀ job, outcome job ≠ .deferred →
        transcript.ImmediateFor pending job)
    (hdeferred :
      ∀ job, outcome job = .deferred →
        transcript.DeferredFor pending job)
    (hdeferredNonzero :
      ∀ job, outcome job = .deferred →
        processingTime job ≠ 0)
    (cap : Cap) {left right : Label n} (horder : left < right) :
    tracePairCharge cap processingTime transcript left right =
      obligatoryALGPairCharge
        ⟨outcome left, processingTime left⟩
        ⟨outcome right, processingTime right⟩ := by
  have hne : left ≠ right := ne_of_lt horder
  have hleftTest :
      Observation.testResult left (processingTime left) ∈ transcript := by
    have hself :=
      htrace.terminal_selfProjection
        hmatch hallTests hallProcessed left
    have hmem :
        Observation.testResult left (processingTime left) ∈
          transcript.pairProjection left left := by
      rw [hself]
      simp
    exact (List.mem_filter.mp hmem).1
  have hrightTest :
      Observation.testResult right (processingTime right) ∈ transcript := by
    have hself :=
      htrace.terminal_selfProjection
        hmatch hallTests hallProcessed right
    have hmem :
        Observation.testResult right (processingTime right) ∈
          transcript.pairProjection right right := by
      rw [hself]
      simp
    exact (List.mem_filter.mp hmem).1
  have hleftImmediateInfix
      (hleft : outcome left ≠ .deferred) :
      ([.testResult left (processingTime left),
          .processed left] : Transcript n) <:+:
        transcript.pairProjection left right := by
    obtain ⟨before, after, htest⟩ :=
      List.mem_iff_append.mp hleftTest
    have hpendingNow :=
      himmediate left hleft before after
        (processingTime left) htest
    have hnotBefore :=
      htrace.not_processed_before_test
        hmatch hallTests hallProcessed left
          (processingTime left) htest
    obtain ⟨rest, hafter⟩ :=
      follows_testProcessStrategy_next_processed
        hfollow htest hpendingNow hnotBefore
          (hallProcessed left)
    exact
      pairProjection_test_process_infix_left
        (before := before) (rest := rest)
        hne (processingTime left) (by
          rw [htest, hafter]
          simp [List.append_assoc])
  have hrightImmediateInfix
      (hright : outcome right ≠ .deferred) :
      ([.testResult right (processingTime right),
          .processed right] : Transcript n) <:+:
        transcript.pairProjection left right := by
    obtain ⟨before, after, htest⟩ :=
      List.mem_iff_append.mp hrightTest
    have hpendingNow :=
      himmediate right hright before after
        (processingTime right) htest
    have hnotBefore :=
      htrace.not_processed_before_test
        hmatch hallTests hallProcessed right
          (processingTime right) htest
    obtain ⟨rest, hafter⟩ :=
      follows_testProcessStrategy_next_processed
        hfollow htest hpendingNow hnotBefore
          (hallProcessed right)
    exact
      pairProjection_test_process_infix_right
        (before := before) (rest := rest)
        hne (processingTime right) (by
          rw [htest, hafter]
          simp [List.append_assoc])
  rcases htrace.terminal_pairProjection_shapes
      hmatch hallTests hallProcessed horder with
    hshape | hshape | hshape
  · by_cases hleft : outcome left = .deferred
    · have hleftProcess :
          Observation.processed left ∈ transcript := by
        exact
          (processed_mem_iff_observation_mem transcript left).1
            (hallProcessed left)
      obtain ⟨before, after, hprocess⟩ :=
        List.mem_iff_append.mp hleftProcess
      have htestBound :
          (Transcript.testResults before).length ≤ n := by
        rw [hprocess] at hallTests
        simp only [Transcript.testResults_append,
          Transcript.testResults_processed_cons,
          List.length_append] at hallTests
        omega
      have hallBefore :=
        (follows_deferred_process_is_shortest
          hpending hfollow (hdeferred left hleft)
            hprocess htestBound).2.1
      have hafterProjection :=
        pairProjection_after_leftProcess_oneTest
          hne (processingTime left) (processingTime right)
          hprocess hshape
      have hrightAfter :
          Observation.testResult right (processingTime right) ∈ after := by
        have hmem :
            Observation.testResult right (processingTime right) ∈
              Transcript.pairProjection left right after := by
          rw [hafterProjection]
          simp
        exact (List.mem_filter.mp hmem).1
      have hrightResult :
          (right, processingTime right) ∈
            Transcript.testResults after :=
        (testResult_mem_iff_observation_mem
          after right (processingTime right)).2 hrightAfter
      rw [hprocess] at hallTests
      simp only [Transcript.testResults_append,
        Transcript.testResults_processed_cons,
        List.length_append] at hallTests
      have : 0 < (Transcript.testResults after).length :=
        List.length_pos_of_mem hrightResult
      omega
    · rw [tracePairCharge_eq_leftAfterOneTest
        cap processingTime transcript left right
        (processingTime left) (processingTime right)
        hshape hne rfl rfl]
      cases hleftOutcome : outcome left with
      | zero =>
          simp [obligatoryALGPairCharge]
      | epsilon =>
          simp [obligatoryALGPairCharge]
      | immediate =>
          simp [obligatoryALGPairCharge]
      | deferred =>
          exact (hleft hleftOutcome).elim
  · by_cases hleft : outcome left = .deferred
    · rw [tracePairCharge_eq_rightAfterTwoTests
        cap processingTime transcript left right
        (processingTime left) (processingTime right)
        hshape hne rfl rfl
        (hdeferredNonzero left hleft)]
      by_cases hright : outcome right = .deferred
      · have hrightProcess :
            Observation.processed right ∈ transcript :=
          (processed_mem_iff_observation_mem transcript right).1
            (hallProcessed right)
        obtain ⟨before, after, hprocess⟩ :=
          List.mem_iff_append.mp hrightProcess
        have htestBound :
            (Transcript.testResults before).length ≤ n := by
          rw [hprocess] at hallTests
          simp only [Transcript.testResults_append,
            Transcript.testResults_processed_cons,
            List.length_append] at hallTests
          omega
        have hshort :=
          follows_deferred_process_is_shortest
            hpending hfollow (hdeferred right hright)
              hprocess htestBound
        have hbeforeProjection :=
          pairProjection_before_rightProcess
            hne (processingTime left) (processingTime right)
            hprocess hshape
        have hleftRemaining :=
          left_remaining_of_pairProjection_tests
            hne (processingTime left) (processingTime right)
            hbeforeProjection
        have hbeforeMatch :
            Transcript.TestsMatch processingTime before := by
          intro job p hmem
          apply hmatch job p
          apply
            (testResult_mem_iff_observation_mem transcript job p).2
          have hobservation :=
            (testResult_mem_iff_observation_mem before job p).1 hmem
          rw [hprocess]
          simp [hobservation]
        have hle :
            processingTime right ≤ processingTime left :=
          shortestRemaining_processing_le
            hbeforeMatch hshort.2.2 hleftRemaining
        simp [obligatoryALGPairCharge, hleft, hright,
          min_eq_right hle]
      · cases hrightOutcome : outcome right with
        | zero =>
            rw [hleft]
            rfl
        | epsilon =>
            rw [hleft]
            rfl
        | immediate =>
            rw [hleft]
            rfl
        | deferred =>
            exact (hright hrightOutcome).elim
    · have hinfix := hleftImmediateInfix hleft
      rw [hshape] at hinfix
      exact
        (left_test_process_not_infix_rightFirst
          hne (processingTime left) (processingTime right)
          hinfix).elim
  · by_cases hleft : outcome left = .deferred
    · by_cases hright : outcome right = .deferred
      · rw [tracePairCharge_eq_leftAfterTwoTests
          cap processingTime transcript left right
          (processingTime left) (processingTime right)
          hshape hne rfl rfl
          (hdeferredNonzero left hleft)
          (hdeferredNonzero right hright)]
        have hleftProcess :
            Observation.processed left ∈ transcript :=
          (processed_mem_iff_observation_mem transcript left).1
            (hallProcessed left)
        obtain ⟨before, after, hprocess⟩ :=
          List.mem_iff_append.mp hleftProcess
        have htestBound :
            (Transcript.testResults before).length ≤ n := by
          rw [hprocess] at hallTests
          simp only [Transcript.testResults_append,
            Transcript.testResults_processed_cons,
            List.length_append] at hallTests
          omega
        have hshort :=
          follows_deferred_process_is_shortest
            hpending hfollow (hdeferred left hleft)
              hprocess htestBound
        have hbeforeProjection :=
          pairProjection_before_leftProcess
            hne (processingTime left) (processingTime right)
            hprocess hshape
        have hrightRemaining :=
          right_remaining_of_pairProjection_tests
            hne (processingTime left) (processingTime right)
            hbeforeProjection
        have hbeforeMatch :
            Transcript.TestsMatch processingTime before := by
          intro job p hmem
          apply hmatch job p
          apply
            (testResult_mem_iff_observation_mem transcript job p).2
          have hobservation :=
            (testResult_mem_iff_observation_mem before job p).1 hmem
          rw [hprocess]
          simp [hobservation]
        have hle :
            processingTime left ≤ processingTime right :=
          shortestRemaining_processing_le
            hbeforeMatch hshort.2.2 hrightRemaining
        simp [obligatoryALGPairCharge, hleft, hright,
          min_eq_left hle]
      · have hinfix := hrightImmediateInfix hright
        rw [hshape] at hinfix
        exact
          (right_test_process_not_infix_leftFirst
            hne (processingTime left) (processingTime right)
            hinfix).elim
    · have hinfix := hleftImmediateInfix hleft
      rw [hshape] at hinfix
      exact
        (left_test_process_not_infix_leftFirst
          hne (processingTime left) (processingTime right)
          hinfix).elim

end

end SchedulingPaper.Online
