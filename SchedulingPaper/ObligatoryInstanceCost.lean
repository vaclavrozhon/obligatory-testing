import SchedulingPaper.ObligatoryInstanceAdversary
import SchedulingPaper.RandomizedOnlineBinaryCompiler
import Mathlib.Tactic

/-!
# Cost of the front-loaded obligatory adversary

This file proves the quantitative half of deterministic obligatory-testing
instance impossibility.  Along the branch on which the first `m` tests return
two and the next `m` return zero, every adaptive symbolic execution tree pays
at least `9 (2m)^2 / 8`.  The proof uses a two-phase continuation potential;
zero-duration administrative actions are harmless and arbitrary positive jobs
may be processed between tests.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open Online
open RandomizedObligatory

noncomputable section

def balancedSuffix (m a : ℕ) : List ℝ :=
  List.replicate (m - a) 2 ++
    List.replicate (2 * m - max m a) 0

@[simp] theorem balancedSuffix_zero (m : ℕ) :
    balancedSuffix m 0 = frontLoadedValues m (2 * m) := by
  have hm : m ≤ 2 * m := by omega
  simp [balancedSuffix, frontLoadedValues, hm]

theorem balancedSuffix_two_cons {m a : ℕ} (ha : a < m) :
    balancedSuffix m a = 2 :: balancedSuffix m (a + 1) := by
  unfold balancedSuffix
  have hsub : m - a = (m - (a + 1)) + 1 := by omega
  have hmax : max m a = m := max_eq_left (Nat.le_of_lt ha)
  have hmaxSucc : max m (a + 1) = m := by
    apply max_eq_left
    omega
  rw [hsub, List.replicate_succ, hmax, hmaxSucc]
  rfl

theorem balancedSuffix_zero_cons {m a : ℕ}
    (hma : m ≤ a) (ha : a < 2 * m) :
    balancedSuffix m a = 0 :: balancedSuffix m (a + 1) := by
  unfold balancedSuffix
  have hfirst : m - a = 0 := Nat.sub_eq_zero_of_le hma
  have hfirstSucc : m - (a + 1) = 0 := Nat.sub_eq_zero_of_le (by omega)
  have hmax : max m a = a := max_eq_right hma
  have hmaxSucc : max m (a + 1) = a + 1 := max_eq_right (by omega)
  have hsub : 2 * m - a = (2 * m - (a + 1)) + 1 := by omega
  simp only [hfirst, hfirstSucc, List.replicate_zero, List.nil_append,
    hmax, hmaxSucc]
  rw [hsub, List.replicate_succ]

def twoProcessCount
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) : ℕ :=
  match tree with
  | .stop _ => 0
  | .processZero _ _ next => twoProcessCount next input
  | .processTwo _ _ next => twoProcessCount next input + 1
  | .test job _ zeroBranch twoBranch =>
      if input job then twoProcessCount twoBranch input
      else twoProcessCount zeroBranch input

def doneTwoCount (config : SymbolicBinaryConfig n) : ℕ :=
  ∑ job, if config.jobs job = .doneTwo then 1 else 0

private theorem doneTwoCount_update
    (config : SymbolicBinaryConfig n) (job : Label n)
    (state : SymbolicBinaryJobState)
    (hold : config.jobs job ≠ .doneTwo) :
    doneTwoCount { config with jobs := Function.update config.jobs job state } =
      doneTwoCount config + if state = .doneTwo then 1 else 0 := by
  classical
  unfold doneTwoCount
  change (∑ i, if Function.update config.jobs job state i = .doneTwo then 1 else 0) = _
  have hfun :
      (fun i => if Function.update config.jobs job state i = .doneTwo then 1 else 0) =
        Function.update
          (fun i => if config.jobs i = .doneTwo then 1 else 0) job
          (if state = .doneTwo then 1 else 0) := by
    funext i
    by_cases hi : i = job
    · subst i
      simp [Function.update]
    · simp [Function.update, hi]
  rw [hfun]
  rw [Finset.sum_update_of_mem (Finset.mem_univ job)]
  have horiginal := Finset.sum_erase_add
    (Finset.univ : Finset (Label n))
    (fun i => if config.jobs i = .doneTwo then 1 else 0)
    (Finset.mem_univ job)
  rw [← horiginal]
  simp [hold, add_comm, Finset.sdiff_singleton_eq_erase]

theorem doneTwoCount_afterTestZero
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) :
    doneTwoCount (config.afterTestZero job) = doneTwoCount config := by
  change doneTwoCount
      { jobs := Function.update config.jobs job .testedZero
        transcript := config.transcript ++ [.testResult job 0] } = _
  simpa [doneTwoCount] using
    doneTwoCount_update config job .testedZero (by simp [hjob])

theorem doneTwoCount_afterTestTwo
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .untouched) :
    doneTwoCount (config.afterTestTwo job) = doneTwoCount config := by
  change doneTwoCount
      { jobs := Function.update config.jobs job .testedTwo
        transcript := config.transcript ++ [.testResult job 2] } = _
  simpa [doneTwoCount] using
    doneTwoCount_update config job .testedTwo (by simp [hjob])

theorem doneTwoCount_afterProcessZero
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedZero) :
    doneTwoCount (config.afterProcessZero job) = doneTwoCount config := by
  change doneTwoCount
      { jobs := Function.update config.jobs job .doneZero
        transcript := config.transcript ++ [.processed job] } = _
  simpa [doneTwoCount] using
    doneTwoCount_update config job .doneZero (by simp [hjob])

theorem doneTwoCount_afterProcessTwo
    (config : SymbolicBinaryConfig n) (job : Label n)
    (hjob : config.jobs job = .testedTwo) :
    doneTwoCount (config.afterProcessTwo job) = doneTwoCount config + 1 := by
  change doneTwoCount
      { jobs := Function.update config.jobs job .doneTwo
        transcript := config.transcript ++ [.processed job] } = _
  simpa [doneTwoCount] using
    doneTwoCount_update config job .doneTwo (by simp [hjob])

theorem OnlineBinaryTree.doneTwoCount_add_twoProcessCount
    {n : ℕ} {config : SymbolicBinaryConfig n}
    (tree : OnlineBinaryTree n config) (input : BinaryInput n) :
    doneTwoCount config + twoProcessCount tree input =
      doneTwoCount (tree.finalConfig input) := by
  induction tree with
  | stop => simp [twoProcessCount, OnlineBinaryTree.finalConfig]
  | @processZero config job hjob next ih =>
      simp only [twoProcessCount, OnlineBinaryTree.finalConfig]
      rw [← ih, doneTwoCount_afterProcessZero config job hjob]
  | @processTwo config job hjob next ih =>
      simp only [twoProcessCount, OnlineBinaryTree.finalConfig]
      rw [← ih, doneTwoCount_afterProcessTwo config job hjob]
      omega
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      cases hbit : input job
      · simp only [twoProcessCount, OnlineBinaryTree.finalConfig, hbit,
          Bool.false_eq_true, if_false]
        rw [← ihZero, doneTwoCount_afterTestZero config job hjob]
      · simp only [twoProcessCount, OnlineBinaryTree.finalConfig, hbit, if_true]
        rw [← ihTwo, doneTwoCount_afterTestTwo config job hjob]

theorem doneTwoCount_eq_trueCount_of_done
    (config : SymbolicBinaryConfig n) (input : BinaryInput n)
    (hconsistent : config.Consistent input)
    (hdone : ∀ job, config.toOnline.jobs job = .done) :
    doneTwoCount config = ∑ job, if input job then 1 else 0 := by
  classical
  unfold doneTwoCount
  apply Finset.sum_congr rfl
  intro job _
  have hc := hconsistent job
  have hd := hdone job
  cases hs : config.jobs job with
  | untouched =>
      simp [SymbolicBinaryConfig.toOnline, SymbolicBinaryJobState.toOnline, hs] at hd
  | testedZero =>
      simp [SymbolicBinaryConfig.toOnline, SymbolicBinaryJobState.toOnline, hs] at hd
  | testedTwo =>
      simp [SymbolicBinaryConfig.toOnline, SymbolicBinaryJobState.toOnline, hs] at hd
  | doneZero =>
      have hb : input job = false := by
        simpa [SymbolicBinaryConfig.Consistent, hs] using hc
      simp [hb]
  | doneTwo =>
      have hb : input job = true := by
        simpa [SymbolicBinaryConfig.Consistent, hs] using hc
      simp [hb]

def prePotential (m a h : ℝ) : ℝ :=
  (m - a) * (2 * m - h) +
    m * (m + 1) / 2 + (m - h) * m + (m - h) * (m - h + 1)

def postPotential (m a h : ℝ) : ℝ :=
  let z := a - m
  (m - z) * (m - z + 1) / 2 +
    (m - h) * (m - z) + (m - h) * (m - h + 1)

def balancedPotential (m a h : ℕ) : ℝ :=
  if a < m then prePotential m a h else postPotential m a h

def CountInvariant (m a h r : ℕ) : Prop :=
  if a < m then r + h = 2 * m else r + h + (a - m) = 2 * m

theorem balancedPotential_initial (m : ℕ) :
    balancedPotential m 0 0 = 9 * (m : ℝ) ^ 2 / 2 + 3 * m / 2 := by
  by_cases hm : m = 0
  · subst m
    norm_num [balancedPotential, postPotential]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    simp [balancedPotential, hmpos, prePotential]
    ring

theorem balancedPotential_testTwo
    {m a h r : ℕ} (ha : a < m) (hinv : CountInvariant m a h r) :
    (r : ℝ) + balancedPotential m (a + 1) h =
      balancedPotential m a h := by
  have hr : (r : ℝ) + h = 2 * m := by
    exact_mod_cast (by simpa [CountInvariant, ha] using hinv)
  by_cases hnext : a + 1 < m
  · simp [balancedPotential, ha, hnext, prePotential]
    nlinarith
  · have hae : a + 1 = m := by omega
    subst m
    simp [balancedPotential, postPotential, prePotential] at hr ⊢
    nlinarith

theorem balancedPotential_testZero
    {m a h r : ℕ} (hma : m ≤ a) (hinv : CountInvariant m a h r) :
    (r : ℝ) + balancedPotential m (a + 1) h =
      balancedPotential m a h := by
  have hphase : ¬ a < m := Nat.not_lt_of_ge hma
  have hrNat : r + h + (a - m) = 2 * m := by
    simpa [CountInvariant, hphase] using hinv
  have hr : (r : ℝ) + h + (a - m) = 2 * m := by
    exact_mod_cast hrNat
  have hsub : ((a + 1 - m : ℕ) : ℝ) = (a - m : ℕ) + 1 := by
    exact_mod_cast (by omega : a + 1 - m = (a - m) + 1)
  have hnext : ¬ a + 1 < m := by omega
  simp [balancedPotential, hphase, hnext, postPotential]
  push_cast at hr hsub ⊢
  nlinarith

theorem balancedPotential_processTwo
    {m a h r : ℕ} (ha : a ≤ 2 * m)
    (hinv : CountInvariant m a h r) :
    balancedPotential m a h ≤
      2 * (r : ℝ) + balancedPotential m a (h + 1) := by
  by_cases hphase : a < m
  · have hrNat : r + h = 2 * m := by
      simpa [CountInvariant, hphase] using hinv
    have hr : (r : ℝ) + h = 2 * m := by exact_mod_cast hrNat
    simp [balancedPotential, hphase, prePotential]
    push_cast at hr ⊢
    nlinarith
  · have hma : m ≤ a := Nat.le_of_not_gt hphase
    have hrNat : r + h + (a - m) = 2 * m := by
      simpa [CountInvariant, hphase] using hinv
    have hr : (r : ℝ) + h + (a - m) = 2 * m := by
      exact_mod_cast hrNat
    have hz : (a - m : ℕ) ≤ m := by omega
    have hzR : ((a - m : ℕ) : ℝ) ≤ m := by exact_mod_cast hz
    have hcast : ((a - m : ℕ) : ℝ) = (a : ℝ) - m := by
      exact Nat.cast_sub hma
    simp [balancedPotential, hphase, postPotential]
    rw [hcast] at hzR
    push_cast at hr ⊢
    nlinarith

theorem CountInvariant.processZero
    {m a h r r' : ℕ} (hinv : CountInvariant m a h r) (hr : r' = r) :
    CountInvariant m a h r' := by simpa [hr] using hinv

theorem CountInvariant.processTwo
    {m a h r r' : ℕ} (hinv : CountInvariant m a h r)
    (hr : r' + 1 = r) : CountInvariant m a (h + 1) r' := by
  by_cases hphase : a < m <;> simp [CountInvariant, hphase] at hinv ⊢ <;> omega

theorem CountInvariant.testTwo
    {m a h r r' : ℕ} (ha : a < m) (hinv : CountInvariant m a h r)
    (hr : r' = r) : CountInvariant m (a + 1) h r' := by
  by_cases hnext : a + 1 < m <;>
    simp [CountInvariant, ha, hnext] at hinv ⊢ <;> omega

theorem CountInvariant.testZero
    {m a h r r' : ℕ} (hma : m ≤ a) (hinv : CountInvariant m a h r)
    (hr : r' + 1 = r) : CountInvariant m (a + 1) h r' := by
  have hphase : ¬ a < m := Nat.not_lt_of_ge hma
  have hnext : ¬ a + 1 < m := by omega
  simp [CountInvariant, hphase, hnext] at hinv ⊢
  omega

/-- The front-loaded branch of any adaptive symbolic tree costs at least its
two-phase continuation potential.  The hypotheses describe precisely the
tests and positive processing operations still present in the selected
suffix. -/
theorem OnlineBinaryTree.balancedSuffix_cost_lower
    {m a h : ℕ} {config : SymbolicBinaryConfig (2 * m)}
    (tree : OnlineBinaryTree (2 * m) config) (input : BinaryInput (2 * m))
    (ha : a ≤ 2 * m) (hh : h ≤ m)
    (hinv : CountInvariant m a h config.unfinished)
    (htests : testValues (tree.observations input) = balancedSuffix m a)
    (hprocess : twoProcessCount tree input = m - h) :
    balancedPotential m a h ≤ tree.cost input := by
  induction tree generalizing a h with
  | stop config =>
      simp only [OnlineBinaryTree.observations, testValues, Transcript.testResults_nil,
        List.map_nil] at htests
      have hlength := congrArg List.length htests
      simp [balancedSuffix] at hlength
      have hae : a = 2 * m := by omega
      simp only [twoProcessCount] at hprocess
      have hhe : h = m := by omega
      subst a
      subst h
      have hr : config.unfinished = 0 := by
        unfold CountInvariant at hinv
        split at hinv <;> omega
      have hphase : ¬ 2 * m < m := by omega
      simp [balancedPotential, hphase, postPotential, OnlineBinaryTree.cost, hr]
      ring_nf
      exact le_rfl
  | @processZero config job hjob next ih =>
      simp only [OnlineBinaryTree.observations, testValues,
        Transcript.testResults_processed_cons] at htests
      simp only [twoProcessCount] at hprocess
      have hnextInv : CountInvariant m a h
          (config.afterProcessZero job).unfinished :=
        hinv.processZero (config.afterProcessZero_unfinished job hjob)
      simpa [OnlineBinaryTree.cost] using
        ih ha hh hnextInv htests hprocess
  | @processTwo config job hjob next ih =>
      simp only [OnlineBinaryTree.observations, testValues,
        Transcript.testResults_processed_cons] at htests
      simp only [twoProcessCount] at hprocess
      have hhlt : h < m := by omega
      have hnextInv : CountInvariant m a (h + 1)
          (config.afterProcessTwo job).unfinished :=
        hinv.processTwo (config.afterProcessTwo_unfinished job hjob)
      have hchildProcess : twoProcessCount next input = m - (h + 1) := by omega
      have hchild := ih ha (by omega) hnextInv htests hchildProcess
      have hstep := balancedPotential_processTwo ha hinv
      simp only [OnlineBinaryTree.cost]
      linarith
  | @test config job hjob zeroBranch twoBranch ihZero ihTwo =>
      have hremaining : 0 < (balancedSuffix m a).length := by
        rw [← htests]
        cases hbit : input job <;>
          simp [OnlineBinaryTree.observations, hbit, testValues]
      have halt : a < 2 * m := by
        simp [balancedSuffix] at hremaining
        omega
      cases hbit : input job
      · have hma : m ≤ a := by
          by_contra hnot
          have halow : a < m := Nat.lt_of_not_ge hnot
          simp only [OnlineBinaryTree.observations, hbit, Bool.false_eq_true,
            if_false, testValues, Transcript.testResults_testResult_cons,
            List.map_cons, balancedSuffix_two_cons halow] at htests
          simp at htests
        have hchildTests :
            testValues (zeroBranch.observations input) =
              balancedSuffix m (a + 1) := by
          simp only [OnlineBinaryTree.observations, hbit, Bool.false_eq_true,
            if_false, testValues, Transcript.testResults_testResult_cons,
            List.map_cons, balancedSuffix_zero_cons hma halt] at htests
          simpa using htests
        simp only [twoProcessCount, hbit,
          Bool.false_eq_true, if_false] at hprocess
        have hnextInv : CountInvariant m (a + 1) h
            (config.afterTestZero job).unfinished :=
          hinv.testZero hma (config.afterTestZero_unfinished job hjob)
        have hchild := ihZero (by omega) hh hnextInv
          hchildTests hprocess
        have hstep := balancedPotential_testZero hma hinv
        simp only [OnlineBinaryTree.cost, hbit, Bool.false_eq_true, if_false]
        linarith
      · have halow : a < m := by
          by_contra hnot
          have hma : m ≤ a := Nat.le_of_not_gt hnot
          simp only [OnlineBinaryTree.observations, hbit, if_true, testValues,
            Transcript.testResults_testResult_cons, List.map_cons,
            balancedSuffix_zero_cons hma halt] at htests
          simp at htests
        have hchildTests :
            testValues (twoBranch.observations input) =
              balancedSuffix m (a + 1) := by
          simp only [OnlineBinaryTree.observations, hbit, if_true, testValues,
            Transcript.testResults_testResult_cons, List.map_cons,
            balancedSuffix_two_cons halow] at htests
          simpa using htests
        simp only [twoProcessCount, hbit, if_true] at hprocess
        have hnextInv : CountInvariant m (a + 1) h
            (config.afterTestTwo job).unfinished :=
          hinv.testTwo halow (config.afterTestTwo_unfinished job hjob)
        have hchild := ihTwo (by omega) hh hnextInv
          hchildTests hprocess
        have hstep := balancedPotential_testTwo halow hinv
        simp only [OnlineBinaryTree.cost, hbit, if_true]
        linarith

def frozenBalancedInput (m : ℕ) (strategy : Strategy (2 * m)) (fuel : ℕ) :
    BinaryInput (2 * m) := fun job =>
  decide (frozenBalanced m strategy fuel job = 2)

theorem iidBinaryProcessingTime_frozenBalancedInput
    (m : ℕ) (strategy : Strategy (2 * m)) (fuel : ℕ)
    (hbinary : ∀ job, frozenBalanced m strategy fuel job = 0 ∨
      frozenBalanced m strategy fuel job = 2) :
    iidBinaryProcessingTime (frozenBalancedInput m strategy fuel) =
      frozenBalanced m strategy fuel := by
  funext job
  rcases hbinary job with hzero | htwo
  · simp [frozenBalancedInput, iidBinaryProcessingTime, positiveIndicator,
      hzero]
  · simp [frozenBalancedInput, iidBinaryProcessingTime, positiveIndicator,
      htwo]

theorem sum_bool_eq_filter_card (input : BinaryInput n) :
    (∑ job, if input job then 1 else 0) =
      (Finset.univ.filter fun job => input job = true).card := by
  classical
  rw [Finset.card_filter]

theorem compile_initial_observations_eq_run_transcript
    (strategy : Strategy n) (fuel : ℕ) (input : BinaryInput n) :
    (compileOnlineBinaryTree strategy fuel
        (SymbolicBinaryConfig.initial n)).observations input =
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel).config.transcript := by
  let tree := compileOnlineBinaryTree strategy fuel
    (SymbolicBinaryConfig.initial n)
  let result := run .infinite (fixedOracle (iidBinaryProcessingTime input))
    strategy fuel
  have hmirror : (tree.finalConfig input).toOnline = result.config := by
    simpa [tree, result, run] using
      compileOnlineBinaryTree_finalConfig_toOnline strategy fuel
        (SymbolicBinaryConfig.initial n) input
  have hfinal := tree.finalConfig_transcript input
  have hmirrorTranscript := congrArg (fun c : Config n => c.transcript) hmirror
  simpa [tree, result, SymbolicBinaryConfig.initial] using
    hfinal.symm.trans hmirrorTranscript

theorem compile_initial_twoProcessCount_eq_trueCount
    (strategy : Strategy n) (fuel : ℕ) (input : BinaryInput n)
    (hdone : ∀ job,
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel).config.jobs job = .done) :
    twoProcessCount
        (compileOnlineBinaryTree strategy fuel (SymbolicBinaryConfig.initial n))
        input = ∑ job, if input job then 1 else 0 := by
  let tree := compileOnlineBinaryTree strategy fuel
    (SymbolicBinaryConfig.initial n)
  let result := run .infinite (fixedOracle (iidBinaryProcessingTime input))
    strategy fuel
  have hmirror : (tree.finalConfig input).toOnline = result.config := by
    simpa [tree, result, run] using
      compileOnlineBinaryTree_finalConfig_toOnline strategy fuel
        (SymbolicBinaryConfig.initial n) input
  have hfinalDone : ∀ job,
      (tree.finalConfig input).toOnline.jobs job = .done := by
    intro job
    rw [hmirror]
    exact hdone job
  have hconsistent := tree.finalConfig_consistent input
    (SymbolicBinaryConfig.initial_consistent n input)
  have hcountFinal := doneTwoCount_eq_trueCount_of_done
    (tree.finalConfig input) input hconsistent hfinalDone
  have hcountPath :=
    _root_.SchedulingPaper.ObligatoryInstance.OnlineBinaryTree.doneTwoCount_add_twoProcessCount
      tree input
  have hinitial : doneTwoCount (SymbolicBinaryConfig.initial n) = 0 := by
    simp [doneTwoCount, SymbolicBinaryConfig.initial]
  rw [hinitial, Nat.zero_add, hcountFinal] at hcountPath
  exact hcountPath

/-- End-to-end deterministic obligatory-testing counterexample.  Every
terminating transcript-only strategy has a fixed balanced `0/2` input on
which its literal completion cost is at least `9n²/8` for `n=2m`. -/
theorem deterministic_balanced_cost_lower
    (m : ℕ) (strategy : Strategy (2 * m)) (fuel : ℕ)
    (hcomplete : ∀ processing : Label (2 * m) → ℝ,
      (∀ job, 0 ≤ processing job) →
      ∀ job, (run .infinite (fixedOracle processing) strategy fuel).config.jobs job =
        .done) :
    ∃ processing : Label (2 * m) → ℝ,
      (∀ job, processing job = 0 ∨ processing job = 2) ∧
      (Finset.univ.filter fun job => processing job = 2).card = m ∧
      9 * ((2 * m : ℕ) : ℝ) ^ 2 / 8 ≤
        runCompletionCost .infinite processing
          (run .infinite (fixedOracle processing) strategy fuel) := by
  let processing := frozenBalanced m strategy fuel
  let input := frozenBalancedInput m strategy fuel
  have hm : m ≤ 2 * m := by omega
  have hfrozen := frozenBalanced_exact_count hm strategy fuel hcomplete
  have hbinary : ∀ job, processing job = 0 ∨ processing job = 2 := by
    exact hfrozen.1
  have hcard :
      (Finset.univ.filter fun job => processing job = 2).card = m := hfrozen.2
  have hprocessing : iidBinaryProcessingTime input = processing := by
    exact iidBinaryProcessingTime_frozenBalancedInput m strategy fuel hbinary
  have hiidNonneg : ∀ job, 0 ≤ iidBinaryProcessingTime input job := by
    intro job
    simp [iidBinaryProcessingTime, positiveIndicator]
    split <;> norm_num
  have hdone : ∀ job,
      (run .infinite (fixedOracle (iidBinaryProcessingTime input))
        strategy fuel).config.jobs job = .done :=
    hcomplete (iidBinaryProcessingTime input) hiidNonneg
  have hreplay :
      run .infinite (fixedOracle (iidBinaryProcessingTime input)) strategy fuel =
        (adaptiveRun .infinite (frontLoadedOracle m) strategy fuel).result := by
    rw [hprocessing]
    exact frozenBalanced_replay m strategy fuel
  have hlength :
      (adaptiveRun .infinite (frontLoadedOracle m) strategy fuel).result.config.transcript.testResults.length =
        2 * m := by
    rw [← hreplay]
    exact testResults_length_eq_n_of_all_done
      (fixedOracle (iidBinaryProcessingTime input)) strategy fuel hdone
  have hstats := adaptiveRun_frontLoadedStats m strategy fuel
  have hadaptiveOrdered :
      testValues
          (adaptiveRun .infinite (frontLoadedOracle m) strategy fuel).result.config.transcript =
        frontLoadedValues m (2 * m) := by
    simpa [hlength] using hstats.ordered
  let tree := compileOnlineBinaryTree strategy fuel
    (SymbolicBinaryConfig.initial (2 * m))
  have hobservations :
      tree.observations input =
        (run .infinite (fixedOracle (iidBinaryProcessingTime input))
          strategy fuel).config.transcript := by
    exact compile_initial_observations_eq_run_transcript strategy fuel input
  have htests : testValues (tree.observations input) = balancedSuffix m 0 := by
    rw [hobservations, hreplay, hadaptiveOrdered, balancedSuffix_zero]
  have hinputCard :
      (Finset.univ.filter fun job => input job = true).card = m := by
    change (Finset.univ.filter fun job =>
      decide (processing job = 2) = true).card = m
    simpa [decide_eq_true_eq] using hcard
  have hprocess : twoProcessCount tree input = m := by
    rw [compile_initial_twoProcessCount_eq_trueCount strategy fuel input hdone,
      sum_bool_eq_filter_card, hinputCard]
  have hinv : CountInvariant m 0 0
      (SymbolicBinaryConfig.initial (2 * m)).unfinished := by
    rw [SymbolicBinaryConfig.initial_unfinished]
    simp [CountInvariant]
  have htree : balancedPotential m 0 0 ≤ tree.cost input := by
    exact
      _root_.SchedulingPaper.ObligatoryInstance.OnlineBinaryTree.balancedSuffix_cost_lower
        tree input (by omega) (by omega) hinv htests (by simpa using hprocess)
  have hbase : 9 * ((2 * m : ℕ) : ℝ) ^ 2 / 8 ≤
      balancedPotential m 0 0 := by
    rw [balancedPotential_initial]
    have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    nlinarith
  refine ⟨processing, hbinary, hcard, ?_⟩
  calc
    9 * ((2 * m : ℕ) : ℝ) ^ 2 / 8 ≤ balancedPotential m 0 0 := hbase
    _ ≤ tree.cost input := htree
    _ = runCompletionCost .infinite (iidBinaryProcessingTime input)
          (run .infinite (fixedOracle (iidBinaryProcessingTime input))
            strategy fuel) := by
      exact compileOnlineBinaryTree_initial_cost_eq_runCompletionCost
        strategy fuel input hdone
    _ = runCompletionCost .infinite processing
          (run .infinite (fixedOracle processing) strategy fuel) := by
      rw [hprocessing]

end

end ObligatoryInstance
end SchedulingPaper
