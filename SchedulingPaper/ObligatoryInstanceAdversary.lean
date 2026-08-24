import SchedulingPaper.OnlineTestingInvariant
import SchedulingPaper.TimedOnline
import SchedulingPaper.BlindOptimizationAlgebra
import Mathlib.Tactic

/-!
# Fixed balanced adversary for obligatory instance optimality

The transcript-dependent oracle returns two on the first `m` successful
tests and zero afterwards.  The generic replay machinery freezes the run to
one ordinary labeled input.  This file checks that a completed run really
produces exactly `m` twos and `n-m` zeros; no assumption about the strategy's
test order is made.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Online

noncomputable section

def frontLoadedOracle (m : ℕ) : Oracle n := fun transcript _job =>
  if transcript.testResults.length < m then 2 else 0

theorem frontLoadedOracle_admissible (m : ℕ) :
    (frontLoadedOracle (n := n) m).Admissible .infinite := by
  intro transcript job
  change 0 ≤ if transcript.testResults.length < m then 2 else 0
  split <;> norm_num

def testValues (transcript : Transcript n) : List ℝ :=
  transcript.testResults.map Prod.snd

def frontLoadedValues (m k : ℕ) : List ℝ :=
  List.replicate (min m k) 2 ++ List.replicate (k - m) 0

structure FrontLoadedStats (m : ℕ) (transcript : Transcript n) : Prop where
  binary : ∀ p ∈ testValues transcript, p = 0 ∨ p = 2
  twos : (testValues transcript).count 2 = min m transcript.testResults.length
  ordered : testValues transcript =
    frontLoadedValues m transcript.testResults.length

theorem FrontLoadedStats.nil (m : ℕ) :
    FrontLoadedStats m ([] : Transcript n) := by
  constructor <;> simp [testValues, frontLoadedValues]

theorem FrontLoadedStats.afterProcess
    {m : ℕ} {transcript : Transcript n} (hstats : FrontLoadedStats m transcript)
    (job : Label n) :
    FrontLoadedStats m (transcript ++ [.processed job]) := by
  constructor
  · simpa [testValues, Transcript.testResults_append] using hstats.binary
  · simpa [testValues, Transcript.testResults_append] using hstats.twos
  · simpa [testValues, Transcript.testResults_append] using hstats.ordered

theorem FrontLoadedStats.afterTest
    {m : ℕ} {transcript : Transcript n} (hstats : FrontLoadedStats m transcript)
    (job : Label n) (p : ℝ)
    (hp : p = if transcript.testResults.length < m then 2 else 0) :
    FrontLoadedStats m (transcript ++ [.testResult job p]) := by
  have hvalues : testValues (transcript ++ [.testResult job p]) =
      testValues transcript ++ [p] := by
    simp [testValues, Transcript.testResults_append]
  constructor
  · intro q hq
    rw [hvalues] at hq
    rcases List.mem_append.mp hq with hold | hnew
    · exact hstats.binary q hold
    · have hqp : q = p := by simpa using hnew
      subst q
      rw [hp]
      split <;> simp
  · rw [hvalues, List.count_append]
    simp only [List.count_singleton]
    rw [hp]
    by_cases hlt : transcript.testResults.length < m
    · simp [hlt]
      rw [hstats.twos]
      omega
    · simp [hlt]
      rw [hstats.twos]
      omega
  · rw [hvalues, hp, hstats.ordered]
    by_cases hlt : transcript.testResults.length < m
    · have hmin : min m transcript.testResults.length =
          transcript.testResults.length := by omega
      have hminSucc : min m (transcript.testResults.length + 1) =
          transcript.testResults.length + 1 := by omega
      have hsub : transcript.testResults.length - m = 0 := by omega
      have hsubSucc : transcript.testResults.length + 1 - m = 0 := by omega
      simp [frontLoadedValues, hlt, hmin, hsub, hsubSucc,
        List.replicate_succ']
    · have hmin : min m transcript.testResults.length = m := by omega
      have hminSucc : min m (transcript.testResults.length + 1) = m := by omega
      have hsubSucc : transcript.testResults.length + 1 - m =
          (transcript.testResults.length - m) + 1 := by omega
      simp [frontLoadedValues, hlt, hmin, hminSucc, hsubSucc,
        List.replicate_succ', List.append_assoc]

/-- The adaptive replay execution preserves the exact front-loaded count.
The testing and assignment-support invariants are carried explicitly so a
successful fresh test cannot reuse an earlier commitment. -/
theorem runAdaptiveFuel_frontLoadedStats
    (m : ℕ) (strategy : Strategy n) (fuel : ℕ)
    (config : Config n) (assignment : PartialAssignment n)
    (hinv : config.TestingInvariant)
    (hsupported : SupportedByTranscript assignment config.transcript)
    (hstats : FrontLoadedStats m config.transcript) :
    FrontLoadedStats m
      (runAdaptiveFuel .infinite (frontLoadedOracle m) strategy fuel
        config assignment).result.config.transcript := by
  induction fuel generalizing config assignment with
  | zero => simpa [runAdaptiveFuel] using hstats
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runAdaptiveFuel, haction] using hstats
      | some action =>
          cases hstep : adaptiveStep .infinite (frontLoadedOracle m)
              config assignment action with
          | none => simpa [runAdaptiveFuel, haction, hstep] using hstats
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hnextInv : next.TestingInvariant := by
                unfold adaptiveStep at hstep
                cases hfixed : config.step .infinite
                    (adaptiveOracle (frontLoadedOracle m) assignment) action with
                | none => simp [hfixed] at hstep
                | some next' =>
                    simp only [hfixed, Option.some.injEq] at hstep
                    rcases hstep with ⟨rfl, rfl⟩
                    exact hinv.step hfixed
              have hnextSupported :
                  SupportedByTranscript nextAssignment next.transcript :=
                adaptiveStep_supportedByTranscript .infinite
                  (frontLoadedOracle m) config next assignment nextAssignment
                  action hsupported hstep
              have hnextStats : FrontLoadedStats m next.transcript := by
                cases action with
                | raw job => simp [adaptiveStep, Config.step] at hstep
                | process job =>
                    cases hstate : config.jobs job with
                    | untouched => simp [adaptiveStep, Config.step, hstate] at hstep
                    | tested p =>
                        simp [adaptiveStep, Config.step, hstate] at hstep
                        rcases hstep with ⟨rfl, rfl⟩
                        exact hstats.afterProcess job
                    | done => simp [adaptiveStep, Config.step, hstate] at hstep
                | test job =>
                    cases hstate : config.jobs job with
                    | tested p => simp [adaptiveStep, Config.step, hstate] at hstep
                    | done => simp [adaptiveStep, Config.step, hstate] at hstep
                    | untouched =>
                        have hnotTested : job ∉
                            config.transcript.testResults.map Prod.fst :=
                          (hinv.untouched_iff job).mp hstate
                        have hnone : assignment job = none := by
                          cases hassign : assignment job with
                          | none => rfl
                          | some p =>
                              have hmem := hsupported job p hassign
                              exact (hnotTested
                                (List.mem_map.mpr ⟨(job, p), hmem, rfl⟩)).elim
                        simp [adaptiveStep, Config.step, hstate,
                          adaptiveOracle, adaptiveValue, hnone,
                          assignmentAfter] at hstep
                        rcases hstep with ⟨rfl, rfl⟩
                        apply hstats.afterTest
                        rfl
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnextInv hnextSupported hnextStats

theorem adaptiveRun_frontLoadedStats (m : ℕ) (strategy : Strategy n) (fuel : ℕ) :
    FrontLoadedStats m
      (adaptiveRun .infinite (frontLoadedOracle m) strategy fuel).result.config.transcript := by
  unfold adaptiveRun
  exact runAdaptiveFuel_frontLoadedStats m strategy fuel
    (Config.initial n) emptyAssignment
    (Config.initial_testingInvariant n)
    (by simp [SupportedByTranscript, Config.initial, emptyAssignment])
    (FrontLoadedStats.nil m)

def frozenBalanced (m : ℕ) (strategy : Strategy n) (fuel : ℕ) : Label n → ℝ :=
  frozenProcessingTimes .infinite (frontLoadedOracle m) strategy (fun _ => 0) fuel

theorem count_ofFn_eq_sum_indicator
    {α : Type*} [DecidableEq α] (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let tail : Fin n → α := fun i => f i.succ
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
      have htail := ih tail
      dsimp [tail] at htail
      rw [htail]
      by_cases h : f 0 = a <;> simp [h, add_comm]

theorem frozenBalanced_nonneg (m : ℕ) (strategy : Strategy n) (fuel : ℕ) :
    ∀ job, 0 ≤ frozenBalanced m strategy fuel job := by
  exact frozenProcessingTimes_admissible .infinite (frontLoadedOracle m)
    strategy (fun _ => 0) fuel (frontLoadedOracle_admissible m)
      (by intro job; simp [ValueAdmissible])

theorem frozenBalanced_replay (m : ℕ) (strategy : Strategy n) (fuel : ℕ) :
    run .infinite (fixedOracle (frozenBalanced m strategy fuel)) strategy fuel =
      (adaptiveRun .infinite (frontLoadedOracle m) strategy fuel).result := by
  exact replay .infinite (frontLoadedOracle m) strategy (fun _ => 0) fuel

/-- A completing strategy is frozen to a genuine binary vector containing
exactly `m` twos (when `m ≤ n`). -/
theorem frozenBalanced_exact_count
    {m : ℕ} (hm : m ≤ n) (strategy : Strategy n) (fuel : ℕ)
    (hcomplete : ∀ processing : Label n → ℝ,
      (∀ job, 0 ≤ processing job) →
      ∀ job, (run .infinite (fixedOracle processing) strategy fuel).config.jobs job = .done) :
    (∀ job, frozenBalanced m strategy fuel job = 0 ∨
      frozenBalanced m strategy fuel job = 2) ∧
    (Finset.univ.filter fun job =>
      frozenBalanced m strategy fuel job = 2).card = m := by
  let processing := frozenBalanced m strategy fuel
  let adaptive := adaptiveRun .infinite (frontLoadedOracle m) strategy fuel
  have hp0 : ∀ job, 0 ≤ processing job := frozenBalanced_nonneg m strategy fuel
  have hdoneFixed := hcomplete processing hp0
  have hreplay := frozenBalanced_replay m strategy fuel
  have hdoneAdaptive : ∀ job, adaptive.result.config.jobs job = .done := by
    intro job
    dsimp [adaptive]
    rw [← hreplay]
    exact hdoneFixed job
  have hlengthFixed := testResults_length_eq_n_of_all_done
    (fixedOracle processing) strategy fuel hdoneFixed
  have hlength : adaptive.result.config.transcript.testResults.length = n := by
    dsimp [adaptive]
    rw [← hreplay]
    exact hlengthFixed
  have hstats := adaptiveRun_frontLoadedStats m strategy fuel
  have htwosValues :
      (testValues adaptive.result.config.transcript).count 2 = m := by
    dsimp [adaptive] at hstats ⊢
    rw [hstats.twos, hlength, min_eq_left hm]
  have hinvFixed := run_testingInvariant (fixedOracle processing) strategy fuel
  have hinv : adaptive.result.config.TestingInvariant := by
    dsimp [adaptive]
    rw [← hreplay]
    exact hinvFixed
  have htestPerm :
      (adaptive.result.config.transcript.testResults.map Prod.fst).Perm
        (List.ofFn fun job : Fin n => job) := by
    apply (List.perm_ext_iff_of_nodup hinv.testNodup
      (List.nodup_ofFn.mpr fun _ _ hij => hij)).2
    intro job
    constructor
    · intro _; simp
    · intro _
      by_contra hnot
      have huntouched := (hinv.untouched_iff job).mpr hnot
      rw [hdoneAdaptive job] at huntouched
      contradiction
  have hvalueMatch :
      testValues adaptive.result.config.transcript =
        (adaptive.result.config.transcript.testResults.map Prod.fst).map processing := by
    unfold testValues
    rw [List.map_map]
    apply List.map_congr_left
    intro result hresult
    dsimp
    symm
    exact frozenProcessingTimes_eq_of_testResult .infinite
      (frontLoadedOracle m) strategy (fun _ => 0) fuel hresult
  have hprocessingValuesPerm :
      (testValues adaptive.result.config.transcript).Perm
        (List.ofFn processing) := by
    rw [hvalueMatch]
    simpa [List.map_ofFn] using htestPerm.map processing
  constructor
  · intro job
    have hmem : processing job ∈ List.ofFn processing := by simp
    have hmemTest : processing job ∈ testValues adaptive.result.config.transcript :=
      hprocessingValuesPerm.symm.subset hmem
    exact hstats.binary _ hmemTest
  · have hcountPerm := hprocessingValuesPerm.count 2
    have hfilterSum :
        (Finset.univ.filter fun job => processing job = 2).card =
          (List.ofFn processing).count 2 := by
      rw [count_ofFn_eq_sum_indicator]
      simp
    change (Finset.univ.filter fun job => processing job = 2).card = m
    rw [hfilterSum]
    exact hcountPerm.symm.trans htwosValues

end

end ObligatoryInstance
end SchedulingPaper
