import SchedulingPaper.HiddenStoppingCostAccounting
import SchedulingPaper.TranscriptPairAccounting

/-!
# Pair-contribution accounting for hidden stopping

The online total completion cost admits the same kind of pair decomposition
as the offline objective.  Each operation duration is charged once for every
completion at or after that operation.  This file makes that statement
literal, proves its adjacent-swap identity, and gives a closed pair formula
for every binary effective-length vector.

The final bridge has no scheduling semantics hidden in either objective:
the remaining premise compares one explicit weighted transcript sum with one
explicit binary triangular expression.
-/

namespace SchedulingPaper

noncomputable section

namespace Online

/-! ## Unique first touches in every operational trace -/

/-- Labels first touched by either a successful test or a raw completion.
Processing a previously tested job is not another first touch. -/
def Transcript.startedLabels : Transcript n → List (Label n)
  | [] => []
  | .testResult job _ :: rest =>
      job :: Transcript.startedLabels rest
  | .processed _ :: rest => Transcript.startedLabels rest
  | .rawCompleted job :: rest =>
      job :: Transcript.startedLabels rest

@[simp] theorem Transcript.startedLabels_nil :
    Transcript.startedLabels ([] : Transcript n) = [] := rfl

@[simp] theorem Transcript.startedLabels_testResult_cons
    (job : Label n) (p : ℝ) (rest : Transcript n) :
    Transcript.startedLabels (.testResult job p :: rest) =
      job :: Transcript.startedLabels rest := rfl

@[simp] theorem Transcript.startedLabels_processed_cons
    (job : Label n) (rest : Transcript n) :
    Transcript.startedLabels (.processed job :: rest) =
      Transcript.startedLabels rest := rfl

@[simp] theorem Transcript.startedLabels_rawCompleted_cons
    (job : Label n) (rest : Transcript n) :
    Transcript.startedLabels (.rawCompleted job :: rest) =
      job :: Transcript.startedLabels rest := rfl

@[simp] theorem Transcript.startedLabels_append
    (left right : Transcript n) :
    Transcript.startedLabels (left ++ right) =
      Transcript.startedLabels left ++
        Transcript.startedLabels right := by
  induction left with
  | nil => simp
  | cons observation rest ih =>
      cases observation <;> simp [ih]

@[simp] theorem Transcript.startedLabels_append_testResult
    (transcript : Transcript n) (job : Label n) (p : ℝ) :
    Transcript.startedLabels
        (transcript ++ [Observation.testResult job p]) =
      Transcript.startedLabels transcript ++ [job] := by
  simp

@[simp] theorem Transcript.startedLabels_append_processed
    (transcript : Transcript n) (job : Label n) :
    Transcript.startedLabels
        (transcript ++ [Observation.processed job]) =
      Transcript.startedLabels transcript := by
  simp

@[simp] theorem Transcript.startedLabels_append_rawCompleted
    (transcript : Transcript n) (job : Label n) :
    Transcript.startedLabels
        (transcript ++ [Observation.rawCompleted job]) =
      Transcript.startedLabels transcript ++ [job] := by
  simp

/-- Reachable configurations have no repeated first touch; moreover an
untouched job has not yet appeared in that history. -/
structure Config.StartedHistoryInvariant (config : Config n) : Prop where
  nodup : (Transcript.startedLabels config.transcript).Nodup
  untouched_not_mem :
    ∀ job, config.jobs job = .untouched →
      job ∉ Transcript.startedLabels config.transcript

theorem Config.initial_startedHistoryInvariant (n : ℕ) :
    (Config.initial n).StartedHistoryInvariant := by
  constructor <;> simp [Config.initial]

theorem Config.startedHistoryInvariant_step
    {cap : Cap} {oracle : Oracle n} {config next : Config n}
    {action : Action n}
    (hgood : config.StartedHistoryInvariant)
    (hstep : config.step cap oracle action = some next) :
    next.StartedHistoryInvariant := by
  cases action with
  | test testedJob =>
      cases hstate : config.jobs testedJob with
      | untouched =>
          simp [Config.step, hstate] at hstep
          subst next
          constructor
          · change
              (Transcript.startedLabels
                (config.transcript ++
                  [Observation.testResult testedJob
                    (oracle config.transcript testedJob)])).Nodup
            rw [Transcript.startedLabels_append_testResult,
              List.nodup_append_comm]
            simp [hgood.nodup,
              hgood.untouched_not_mem testedJob hstate]
          · intro job hjob
            by_cases heq : job = testedJob
            · subst job
              simp [Function.update] at hjob
            · have hold : config.jobs job = .untouched := by
                simpa [Function.update, heq] using hjob
              simp [hgood.untouched_not_mem job hold, heq]
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
          constructor
          · simpa using hgood.nodup
          · intro job hjob
            by_cases heq : job = processedJob
            · subst job
              simp [Function.update] at hjob
            · rw [Transcript.startedLabels_append_processed]
              apply hgood.untouched_not_mem job
              simpa [Function.update, heq] using hjob
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
              constructor
              · change
                  (Transcript.startedLabels
                    (config.transcript ++
                      [Observation.rawCompleted rawJob])).Nodup
                rw [Transcript.startedLabels_append_rawCompleted,
                  List.nodup_append_comm]
                simp [hgood.nodup,
                  hgood.untouched_not_mem rawJob hstate]
              · intro job hjob
                by_cases heq : job = rawJob
                · subst job
                  simp [Function.update] at hjob
                · have hold : config.jobs job = .untouched := by
                    simpa [Function.update, heq] using hjob
                  simp [hgood.untouched_not_mem job hold, heq]
          | tested p =>
              simp [Config.step, hstate] at hstep
          | done =>
              simp [Config.step, hstate] at hstep

theorem runFuel_startedHistoryInvariant
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hgood : config.StartedHistoryInvariant) :
    (runFuel cap oracle strategy fuel config).config.StartedHistoryInvariant := by
  induction fuel generalizing config with
  | zero =>
      simpa [runFuel] using hgood
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runFuel, haction] using hgood
      | some action =>
          cases hstep : config.step cap oracle action with
          | none =>
              simpa [runFuel, haction, hstep] using hgood
          | some next =>
              have hnext :=
                Config.startedHistoryInvariant_step hgood hstep
              simpa [runFuel, haction, hstep] using ih next hnext

theorem run_startedHistoryInvariant
    (cap : Cap) (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) :
    (run cap oracle strategy fuel).config.StartedHistoryInvariant := by
  unfold run
  exact runFuel_startedHistoryInvariant cap oracle strategy fuel
    (Config.initial n) (Config.initial_startedHistoryInvariant n)

/-- Replay transfers the unique-first-touch invariant to every adaptive
hidden-stopping result. -/
theorem hiddenStopping_adaptiveRun_startedHistoryInvariant
    {n : ℕ} (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    (adaptiveRun (.finite u)
      (HiddenStoppingOracle.oracle n u α) strategy
        fuel).result.config.StartedHistoryInvariant := by
  let frozen :=
    frozenProcessingTimes (.finite u)
      (HiddenStoppingOracle.oracle n u α) strategy
        (fun _ => 0) fuel
  have hgood :=
    run_startedHistoryInvariant (.finite u)
      (fixedOracle frozen) strategy fuel
  rw [HiddenStoppingOracle.replay_fixed_binary
    u α strategy fuel] at hgood
  exact hgood

end Online

namespace HiddenStoppingOracle

/-- Raw completions and long tests are two disjoint subclasses of first
touches, so their total count is bounded by the first-touch history. -/
theorem rawCount_add_longCount_le_startedLabels_length
    (u : ℝ) (transcript : Online.Transcript n) :
    rawCount transcript + longCount u transcript ≤
      (Online.Transcript.startedLabels transcript).length := by
  induction transcript with
  | nil => simp
  | cons observation rest ih =>
      cases observation with
      | testResult job p =>
          by_cases hp : p = u
          · subst p
            simp [longCount]
            omega
          · simp [longCount, hp]
            omega
      | processed job =>
          simpa using ih
      | rawCompleted job =>
          simp
          omega

/-- Global feasibility of the public stopping counters on every adaptive
hidden-stopping run. -/
theorem adaptiveRun_rawCount_add_longCount_le
    {n : ℕ} (u α : ℝ) (strategy : Online.Strategy n) (fuel : ℕ) :
    let transcript :=
      (Online.adaptiveRun (.finite u)
        (oracle n u α) strategy fuel).result.config.transcript
    rawCount transcript + longCount u transcript ≤ n := by
  dsimp only
  have hgood :=
    Online.hiddenStopping_adaptiveRun_startedHistoryInvariant
      u α strategy fuel
  have hlength :
      (Online.Transcript.startedLabels
        (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy
            fuel).result.config.transcript).length ≤ n := by
    simpa using hgood.nodup.length_le_card
  exact
    (rawCount_add_longCount_le_startedLabels_length u _).trans hlength

/-! ## First crossing is a literal long-test or raw touch -/

def TestResultsBinary (u : ℝ) (transcript : Online.Transcript n) : Prop :=
  ∀ job p, (job, p) ∈ transcript.testResults → p = 0 ∨ p = u

theorem adaptiveRun_testResultsBinary
    {n : ℕ} (u α : ℝ) (strategy : Online.Strategy n) (fuel : ℕ) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u α) strategy fuel).result
    TestResultsBinary u result.config.transcript := by
  dsimp only
  intro job p hresult
  have hassigned :=
    Online.adaptiveRun_assigned_of_testResult
      (.finite u) (oracle n u α) strategy fuel hresult
  exact adaptiveRun_binary n u α strategy fuel
    job p hassigned

/-- For a binary trace, the first crossing observation cannot be a process
or a zero test, since those leave the surplus unchanged. -/
theorem exists_firstCrossing_long_or_raw_of_binary
    {n : ℕ} {u α : ℝ} (hu : u ≠ 0)
    (start rest : Online.Transcript n)
    (hstart : ¬ Crossed n u α start)
    (hfinal : Crossed n u α (start ++ rest))
    (hbinary : TestResultsBinary u (start ++ rest)) :
    (∃ before job after,
      start ++ rest =
        before ++ Online.Observation.testResult job u :: after ∧
      FirstCrossingAt n u α before
        (.testResult job u)) ∨
    (∃ before job after,
      start ++ rest =
        before ++ Online.Observation.rawCompleted job :: after ∧
      FirstCrossingAt n u α before
        (.rawCompleted job)) := by
  induction rest generalizing start with
  | nil =>
      simp only [List.append_nil] at hfinal
      exact (hstart hfinal).elim
  | cons observation rest ih =>
      let touched := start ++ [observation]
      by_cases htouched : Crossed n u α touched
      · have hfirst : FirstCrossingAt n u α start observation :=
          ⟨hstart, htouched⟩
        cases observation with
        | processed job =>
            exfalso
            apply hstart
            unfold touched at htouched
            unfold Crossed at *
            rwa [surplus_append_processed] at htouched
        | rawCompleted job =>
            exact Or.inr
              ⟨start, job, rest, by simp,
                by simpa [touched] using hfirst⟩
        | testResult job p =>
            have hp : p = 0 ∨ p = u := by
              apply hbinary job p
              rw [Online.Transcript.testResults_append]
              simp
            rcases hp with rfl | rfl
            · exfalso
              apply hstart
              unfold touched at htouched
              unfold Crossed at *
              rwa [surplus_append_testResult_ne n u α start job 0
                (Ne.symm hu)] at htouched
            · exact Or.inl
                ⟨start, job, rest, by simp,
                  by simpa [touched] using hfirst⟩
      · have hfinal' :
            Crossed n u α (touched ++ rest) := by
          simpa [touched, List.append_assoc] using hfinal
        have hbinary' :
            TestResultsBinary u (touched ++ rest) := by
          simpa [touched, List.append_assoc] using hbinary
        simpa [touched, List.append_assoc] using
          ih touched htouched hfinal' hbinary'

/-- The empty trace is strictly below the stopping line for positive size
and positive threshold. -/
theorem not_crossed_nil
    {n : ℕ} {u α : ℝ} (hn : 0 < n) (hα : 0 < α) :
    ¬ Crossed n u α ([] : Online.Transcript n) := by
  unfold Crossed surplus
  simp
  positivity

/-- Every crossed adaptive run of positive size contains a literal first
crossing long test or raw completion as a prefix of its public transcript. -/
theorem adaptiveRun_exists_firstCrossing_long_or_raw
    {n : ℕ} {u α : ℝ} (hn : 0 < n) (hu : 0 < u) (hα : 0 < α)
    (strategy : Online.Strategy n) (fuel : ℕ)
    (hcross :
      Crossed n u α
        (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy
            fuel).result.config.transcript) :
    (∃ before job after,
      (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy
            fuel).result.config.transcript =
        before ++ Online.Observation.testResult job u :: after ∧
      FirstCrossingAt n u α before
        (.testResult job u)) ∨
    (∃ before job after,
      (Online.adaptiveRun (.finite u)
          (oracle n u α) strategy
            fuel).result.config.transcript =
        before ++ Online.Observation.rawCompleted job :: after ∧
      FirstCrossingAt n u α before
        (.rawCompleted job)) := by
  apply exists_firstCrossing_long_or_raw_of_binary
    hu.ne' [] _ (not_crossed_nil hn hα)
  · simpa using hcross
  · exact adaptiveRun_testResultsBinary u α strategy fuel

end HiddenStoppingOracle

/-! ## Closed offline pair formula for binary vectors -/

/-- Number of occurrences of the long effective length `u`. -/
def binaryLongCount (u : ℝ) : List ℝ → ℕ
  | [] => 0
  | x :: xs => (if x = u then 1 else 0) + binaryLongCount u xs

@[simp] theorem binaryLongCount_nil (u : ℝ) :
    binaryLongCount u [] = 0 := rfl

@[simp] theorem binaryLongCount_cons
    (u x : ℝ) (xs : List ℝ) :
    binaryLongCount u (x :: xs) =
      (if x = u then 1 else 0) + binaryLongCount u xs := rfl

theorem binary_sum_exact
    {u : ℝ} (hu : 1 < u) (xs : List ℝ)
    (hbinary : ∀ x ∈ xs, x = 1 ∨ x = u) :
    xs.sum =
      (xs.length : ℝ) +
        (u - 1) * binaryLongCount u xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx := hbinary x (by simp)
      have htail : ∀ y ∈ xs, y = 1 ∨ y = u :=
        fun y hy => hbinary y (by simp [hy])
      have hi := ih htail
      rcases hx with hx | hx
      · subst x
        have hone : (1 : ℝ) ≠ u := ne_of_lt hu
        simp [binaryLongCount, hone, hi]
        ring
      · subst x
        simp [binaryLongCount, hi]
        ring

/-- Exact unordered-pair value of a list whose entries are all `1` or `u`.
It depends only on the number of long entries, not their order. -/
theorem pairCost_cons_eq (x : ℝ) (xs : List ℝ) :
    pairCost (x :: xs) =
      x + (xs.map (min x)).sum + pairCost xs := by
  simp [pairCost]
  ring

theorem pairCost_binary_exact
    {u : ℝ} (hu : 1 < u) (xs : List ℝ)
    (hbinary : ∀ x ∈ xs, x = 1 ∨ x = u) :
    pairCost xs =
      triangular xs.length +
        (u - 1) * triangular (binaryLongCount u xs) := by
  induction xs with
  | nil =>
      simp [pairCost, triangular]
  | cons x xs ih =>
      have hx := hbinary x (by simp)
      have htail : ∀ y ∈ xs, y = 1 ∨ y = u :=
        fun y hy => hbinary y (by simp [hy])
      have hi := ih htail
      have hsum := binary_sum_exact hu xs htail
      rcases hx with hx | hx
      · subst x
        have hone : (1 : ℝ) ≠ u := ne_of_lt hu
        have hmap :
            xs.map (min 1) = xs.map (fun _ => (1 : ℝ)) := by
          apply List.map_congr_left
          intro y hy
          rcases htail y hy with rfl | rfl
          · simp
          · simp [min_eq_left hu.le]
        rw [pairCost_cons_eq, hmap, List.map_const',
          List.sum_replicate]
        simp only [nsmul_eq_mul]
        rw [hi]
        simp [binaryLongCount, hone, triangular_succ]
        ring
      · subst x
        have hmap : xs.map (min u) = xs := by
          have hcongr :
              xs.map (min u) = xs.map (fun y => y) := by
            apply List.map_congr_left
            intro y hy
            rcases htail y hy with rfl | rfl
            · exact min_eq_right hu.le
            · simp
          simpa using hcongr
        rw [pairCost_cons_eq, hmap, hi, hsum]
        simp [binaryLongCount, triangular_succ]
        rw [show
          1 + binaryLongCount u xs =
            binaryLongCount u xs + 1 by omega]
        rw [triangular_succ]
        push_cast
        ring

namespace LowerBound

open HiddenStoppingOracle

/-- Exact closed offline value of every frozen hidden-stopping instance. -/
theorem hiddenStopping_frozen_offline_pair_exact
    {n : ℕ} {u : ℝ} (hu : 1 < u) (α : ℝ)
    (strategy : Online.Strategy n) (fuel : ℕ) :
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u α) strategy (fun _ => 0) fuel
    let effective := vectorEffectiveLengths (.finite u) frozen
    vectorOfflineCost (.finite u) frozen =
      triangular n +
        (u - 1) * triangular (binaryLongCount u effective) := by
  dsimp only
  rw [vectorOfflineCost_eq_pairCost]
  have hbinary :
      ∀ x ∈
          vectorEffectiveLengths (.finite u)
            (Online.frozenProcessingTimes (.finite u)
              (oracle n u α) strategy (fun _ => 0) fuel),
        x = 1 ∨ x = u := by
    intro x hx
    unfold vectorEffectiveLengths at hx
    rcases List.mem_ofFn.mp hx with ⟨job, rfl⟩
    exact hiddenStopping_frozen_effectiveLength_binary hu.le α
      strategy fuel job
  simpa [vectorEffectiveLengths] using
    pairCost_binary_exact hu _ hbinary

/-! ## A literal pair-exchange premise -/

/-- The sole remaining inequality after both objectives have been expanded:
an explicit binary triangular offline value is compared with the explicit
weighted sum of transcript operations. -/
def HiddenStoppingPairExchangeEstimate
    (u ratio : ℝ) (certificate : BinaryStoppingCertificate u ratio)
    (remainder : ℝ) : Prop :=
  ∀ n (strategy : Online.Strategy n),
    let fuel := 2 * n + 1
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (oracle n u certificate.alpha)
        strategy (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u certificate.alpha) strategy fuel).result
    let effective := vectorEffectiveLengths (.finite u) frozen
    resultCompleted result →
      ratio *
          (triangular n +
            (u - 1) * triangular (binaryLongCount u effective)) ≤
        Online.suffixWeightedDuration (.finite u) frozen
            result.config.transcript +
          remainder * n

def HiddenStoppingPairExchangeBridge : Prop :=
  ∀ {u ratio : ℝ} (_hu : 1 < u)
      (certificate : BinaryStoppingCertificate u ratio),
    ∃ remainder : ℝ, 0 ≤ remainder ∧
      HiddenStoppingPairExchangeEstimate
        u ratio certificate remainder

/-- Literal pair exchange is sufficient for the completed-cost bridge. -/
theorem hiddenStoppingCompletedCostBridge_of_pairExchange
    (bridge : HiddenStoppingPairExchangeBridge) :
    HiddenStoppingCompletedCostBridge := by
  intro u ratio hu certificate
  obtain ⟨remainder, hrem, hexchange⟩ :=
    bridge hu certificate
  refine ⟨remainder, hrem, ?_⟩
  intro n strategy
  dsimp only
  intro hcompleted
  let fuel := 2 * n + 1
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (oracle n u certificate.alpha)
      strategy (fun _ => 0) fuel
  let result :=
    (Online.adaptiveRun (.finite u)
      (oracle n u certificate.alpha) strategy fuel).result
  let effective := vectorEffectiveLengths (.finite u) frozen
  have hoffline :
      vectorOfflineCost (.finite u) frozen =
        triangular n +
          (u - 1) * triangular (binaryLongCount u effective) := by
    simpa [frozen, effective, fuel] using
      hiddenStopping_frozen_offline_pair_exact
        hu certificate.alpha strategy fuel
  have honline :
      Online.runCompletionCost (.finite u) frozen result =
        Online.suffixWeightedDuration (.finite u) frozen
          result.config.transcript := by
    exact Online.runCompletionCost_eq_suffixWeightedDuration
      (.finite u) frozen result
  rw [hoffline, honline]
  exact hexchange n strategy hcompleted

/-- Thus the original finite-cost bridge follows from only the literal
operation-pair exchange inequality. -/
theorem hiddenStoppingFiniteCostBridge_of_pairExchange
    (bridge : HiddenStoppingPairExchangeBridge) :
    HiddenStoppingFiniteCostBridge :=
  hiddenStoppingFiniteCostBridge_of_completedCost
    (hiddenStoppingCompletedCostBridge_of_pairExchange bridge)

end LowerBound

end

end SchedulingPaper
