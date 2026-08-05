import SchedulingPaper.HarmonicOperational
import SchedulingPaper.HiddenStoppingPairAccounting
import Mathlib.Tactic

/-!
# Bounded-cap transfer for the harmonic adversary

Raw execution is simulated, for accounting purposes, by an immediate
harmonic test followed by processing.  At caps at least `zStar`, every such
virtual test/process block is no more expensive than the raw operation.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Online

namespace LowerBound

/-- A convenient strict numerical lower bound on the harmonic endpoint. -/
theorem zStar_gt_four : (4 : ℝ) < zStar := by
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_one_lt_three.trans (by norm_num)
  have hrootFour : zRootFunction 4 < 0 := by
    unfold zRootFunction
    linarith
  by_contra hnot
  have hzle : zStar ≤ 4 := le_of_not_gt hnot
  have hzlt : zStar < 4 := lt_of_le_of_ne hzle (by
    intro heq
    have hequation := zStar_equation
    rw [heq] at hequation
    unfold zRootFunction at hrootFour
    linarith)
  have hmono :=
    zRootFunction_strictMonoOn zStar_gt_one
      (by norm_num : (1 : ℝ) < 4) hzlt
  have hzroot : zRootFunction zStar = 0 := by
    unfold zRootFunction
    linarith [zStar_equation]
  rw [hzroot] at hmono
  linarith

/-- A coarse bound is enough for raw simulation: throughout a block whose
positive-to-zero ratio is below two, every zero-slack harmonic level is
strictly below three. -/
theorem harmonicLevel_lt_three_of_ratio
    {K Z L : ℕ} (hZ : 0 < Z) (hLK : L ≤ K)
    (hratio : (K : ℝ) / (Z : ℝ) < 2) :
    harmonicLevel (Z : ℝ) 0 L < 3 := by
  have hZreal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hterm :
      ∀ r ∈ Finset.range L,
        1 / ((Z : ℝ) + (r + 1 : ℕ)) ≤ 1 / (Z : ℝ) := by
    intro r hr
    apply one_div_le_one_div_of_le hZreal
    push_cast
    linarith
  have hsum :
      (∑ r ∈ Finset.range L,
          1 / ((Z : ℝ) + (r + 1 : ℕ))) ≤
        (K : ℝ) / (Z : ℝ) := by
    calc
      (∑ r ∈ Finset.range L,
          1 / ((Z : ℝ) + (r + 1 : ℕ))) ≤
          ∑ _r ∈ Finset.range L, 1 / (Z : ℝ) := by
            exact Finset.sum_le_sum hterm
      _ = (L : ℝ) / (Z : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ (K : ℝ) / (Z : ℝ) := by
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast hLK) hZreal.le
  have hsumlt :
      (∑ r ∈ Finset.range L,
          1 / ((Z : ℝ) + (r + 1 : ℕ))) < 2 :=
    hsum.trans_lt hratio
  unfold harmonicLevel
  norm_num
  have hadd := add_lt_add_left hsumlt (1 : ℝ)
  norm_num at hadd
  simpa only [Nat.cast_add, Nat.cast_one, one_div, add_comm] using hadd

/-! ## Cap-free expansion of a bounded transcript -/

/-- Expand one bounded observation into the test/process transcript used by
the obligatory harmonic accounting.  A raw completion becomes an immediate
test at the next harmonic rank followed by processing. -/
def capFreeHarmonicStep
    (K Z : ℕ) (γ : ℝ) (virtual : Online.Transcript n) :
    Online.Observation n → Online.Transcript n
  | .testResult job p => virtual ++ [.testResult job p]
  | .processed job => virtual ++ [.processed job]
  | .rawCompleted job =>
      let p :=
        harmonicRankValue K Z γ virtual.testResults.length
      virtual ++ [.testResult job p, .processed job]

/-- The cap-free expansion of a public bounded transcript. -/
def capFreeHarmonicTranscript
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript n) :
    Online.Transcript n :=
  transcript.foldl (capFreeHarmonicStep K Z γ) []

@[simp] theorem capFreeHarmonicTranscript_nil
    (K Z : ℕ) (γ : ℝ) :
    capFreeHarmonicTranscript K Z γ
      ([] : Online.Transcript n) = [] := rfl

@[simp] theorem capFreeHarmonicTranscript_append_testResult
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript n)
    (job : Online.Label n) (p : ℝ) :
    capFreeHarmonicTranscript K Z γ
        (transcript ++ [.testResult job p]) =
      capFreeHarmonicTranscript K Z γ transcript ++
        [.testResult job p] := by
  simp [capFreeHarmonicTranscript, List.foldl_append,
    capFreeHarmonicStep]

@[simp] theorem capFreeHarmonicTranscript_append_processed
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript n)
    (job : Online.Label n) :
    capFreeHarmonicTranscript K Z γ
        (transcript ++ [.processed job]) =
      capFreeHarmonicTranscript K Z γ transcript ++
        [.processed job] := by
  simp [capFreeHarmonicTranscript, List.foldl_append,
    capFreeHarmonicStep]

@[simp] theorem capFreeHarmonicTranscript_append_rawCompleted
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript n)
    (job : Online.Label n) :
    capFreeHarmonicTranscript K Z γ
        (transcript ++ [.rawCompleted job]) =
      let virtual := capFreeHarmonicTranscript K Z γ transcript
      let p := harmonicRankValue K Z γ virtual.testResults.length
      virtual ++ [.testResult job p, .processed job] := by
  simp [capFreeHarmonicTranscript, List.foldl_append,
    capFreeHarmonicStep]

def capFreeHarmonicConfig
    (K Z : ℕ) (γ : ℝ) (config : Online.Config n) :
    Online.Config n where
  jobs := config.jobs
  transcript :=
    capFreeHarmonicTranscript K Z γ config.transcript

/-- The bounded oracle advances its harmonic rank at every first touch,
including a raw completion. -/
def boundedHarmonicOracle
    (K Z : ℕ) (γ : ℝ) : Online.Oracle (K + Z) :=
  fun transcript _job =>
    harmonicRankValue K Z γ
      (capFreeHarmonicTranscript K Z γ transcript).testResults.length

theorem boundedHarmonicOracle_admissible
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u) :
    (boundedHarmonicOracle K Z 0).Admissible (.finite u) := by
  intro transcript job
  let rank :=
    (capFreeHarmonicTranscript K Z 0 transcript).testResults.length
  constructor
  · exact harmonicRankValue_nonneg hZ (le_refl 0)
  · by_cases hrank : rank < K
    · change harmonicRankValue K Z 0 rank ≤ u
      rw [harmonicRankValue_of_lt hrank]
      have hindex : K - 1 - rank ≤ K := by omega
      have hlevel :=
        harmonicLevel_lt_three_of_ratio hZ hindex hratio
      exact hlevel.le.trans
        (by linarith [zStar_gt_four, hu])
    · change harmonicRankValue K Z 0 rank ≤ u
      rw [harmonicRankValue_of_ge (Nat.le_of_not_gt hrank)]
      linarith [zStar_gt_one, hu]

theorem boundedHarmonic_zero_default_admissible
    {u : ℝ} (hu : zStar ≤ u) :
    ∀ job : Online.Label n,
      Online.ValueAdmissible (.finite u) ((fun _ => 0) job) := by
  intro job
  constructor
  · norm_num
  · linarith [zStar_gt_one, hu]

/-! ## Reachability with raw first touches -/

/-- Reachability for the bounded harmonic oracle.  The four test/process
constructors mirror `HarmonicHistory`; the two additional constructors
record a raw first touch. -/
inductive BoundedHarmonicHistory (K Z : ℕ) (γ : ℝ) :
    ℕ → ℕ → HarmonicPending (K + Z) →
      Online.Config (K + Z) → Prop
  | initial :
      BoundedHarmonicHistory K Z γ K Z []
        (Online.Config.initial (K + Z))
  | testPositive
      {L z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : BoundedHarmonicHistory K Z γ L z pending config)
      (hL : 0 < L) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched) :
      BoundedHarmonicHistory K Z γ (L - 1) z
        (pending ++ [(job,
          harmonicLevel (Z : ℝ) γ (L - 1))])
        {
          jobs := Function.update config.jobs job
            (.tested (harmonicLevel (Z : ℝ) γ (L - 1)))
          transcript := config.transcript ++
            [.testResult job
              (harmonicLevel (Z : ℝ) γ (L - 1))]
        }
  | testZero
      {z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : BoundedHarmonicHistory K Z γ 0 z pending config)
      (hz : 0 < z) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched) :
      BoundedHarmonicHistory K Z γ 0 (z - 1) pending
        {
          jobs := Function.update config.jobs job (.tested 0)
          transcript := config.transcript ++ [.testResult job 0]
        }
  | processPositive
      {L z : ℕ}
      {before after : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      {job : Online.Label (K + Z)} {p : ℝ}
      (history :
        BoundedHarmonicHistory K Z γ L z
          (before ++ (job, p) :: after) config)
      (hjob : config.jobs job = .tested p) :
      BoundedHarmonicHistory K Z γ L z (before ++ after)
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | processZero
      {L z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      {job : Online.Label (K + Z)}
      (history : BoundedHarmonicHistory K Z γ L z pending config)
      (hjob : config.jobs job = .tested 0) :
      BoundedHarmonicHistory K Z γ L z pending
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.processed job]
        }
  | rawPositive
      {L z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : BoundedHarmonicHistory K Z γ L z pending config)
      (hL : 0 < L) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched)
      (hvalue :
        harmonicRankValue K Z γ
            (capFreeHarmonicTranscript K Z γ
              config.transcript).testResults.length =
          harmonicLevel (Z : ℝ) γ (L - 1)) :
      BoundedHarmonicHistory K Z γ (L - 1) z pending
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }
  | rawZero
      {z : ℕ} {pending : HarmonicPending (K + Z)}
      {config : Online.Config (K + Z)}
      (history : BoundedHarmonicHistory K Z γ 0 z pending config)
      (hz : 0 < z) (job : Online.Label (K + Z))
      (hjob : config.jobs job = .untouched)
      (hvalue :
        harmonicRankValue K Z γ
            (capFreeHarmonicTranscript K Z γ
              config.transcript).testResults.length = 0) :
      BoundedHarmonicHistory K Z γ 0 (z - 1) pending
        {
          jobs := Function.update config.jobs job .done
          transcript := config.transcript ++ [.rawCompleted job]
        }

/-- Expanding every raw first touch turns a bounded history into the already
verified obligatory harmonic history. -/
theorem BoundedHarmonicHistory.capFree
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : BoundedHarmonicHistory K Z γ L z pending config) :
    HarmonicHistory K Z γ L z pending
      (capFreeHarmonicConfig K Z γ config) := by
  induction history with
  | initial =>
      simpa [capFreeHarmonicConfig, Online.Config.initial] using
        (HarmonicHistory.initial (K := K) (Z := Z) (γ := γ))
  | testPositive history hL job hjob ih =>
      simpa [capFreeHarmonicConfig] using
        (HarmonicHistory.testPositive ih hL job hjob)
  | testZero history hz job hjob ih =>
      simpa [capFreeHarmonicConfig] using
        (HarmonicHistory.testZero ih hz job hjob)
  | processPositive history hjob ih =>
      simpa [capFreeHarmonicConfig] using
        (HarmonicHistory.processPositive ih hjob)
  | processZero history hjob ih =>
      simpa [capFreeHarmonicConfig] using
        (HarmonicHistory.processZero ih hjob)
  | @rawPositive L z pending config history hL job hjob hvalue ih =>
      let p := harmonicLevel (Z : ℝ) γ (L - 1)
      have htested :
          HarmonicHistory K Z γ (L - 1) z
            (pending ++ [(job, p)])
            {
              jobs := Function.update config.jobs job (.tested p)
              transcript :=
                capFreeHarmonicTranscript K Z γ config.transcript ++
                  [.testResult job p]
            } := by
        simpa [capFreeHarmonicConfig, p] using
          (HarmonicHistory.testPositive ih hL job hjob)
      have hprocessed :=
        HarmonicHistory.processPositive
          (before := pending) (after := []) htested
          (by simp [Function.update])
      simpa [capFreeHarmonicConfig, p, hvalue] using hprocessed
  | @rawZero z pending config history hz job hjob hvalue ih =>
      have htested :
          HarmonicHistory K Z γ 0 (z - 1) pending
            {
              jobs := Function.update config.jobs job (.tested 0)
              transcript :=
                capFreeHarmonicTranscript K Z γ config.transcript ++
                  [.testResult job 0]
            } := by
        simpa [capFreeHarmonicConfig] using
          (HarmonicHistory.testZero ih hz job hjob)
      have hprocessed :=
        HarmonicHistory.processZero htested
          (job := job) (by simp [Function.update])
      simpa [capFreeHarmonicConfig, hvalue] using hprocessed

/-- A job that is currently waiting after an actual test has its test result
recorded in the actual bounded transcript.  Raw first touches cannot create
such a state, since they complete the job immediately. -/
theorem BoundedHarmonicHistory.tested_result
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : BoundedHarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)} {p : ℝ}
    (hjob : config.jobs job = .tested p) :
    (job, p) ∈ config.transcript.testResults := by
  induction history with
  | initial =>
      simp [Online.Config.initial] at hjob
  | @testPositive L z pending config history hL tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        subst p
        simp
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton]
        exact Or.inl (ih hold)
  | @testZero z pending config history hz tested htested ih =>
      by_cases heq : job = tested
      · subst job
        simp [Function.update] at hjob
        subst p
        simp
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simp only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_testResult_cons,
          Online.Transcript.testResults_nil, List.mem_append,
          List.mem_singleton]
        exact Or.inl (ih hold)
  | @processPositive L z before after config processed q history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold
  | @processZero L z pending config processed history hprocessed ih =>
      by_cases heq : job = processed
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_processed_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold
  | @rawPositive L z pending config rawHistory hL raw hraw hvalue ih =>
      by_cases heq : job = raw
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_rawCompleted_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold
  | @rawZero z pending config rawHistory hz raw hraw hvalue ih =>
      by_cases heq : job = raw
      · subst job
        simp [Function.update] at hjob
      · have hold : config.jobs job = .tested p := by
          simpa [Function.update, heq] using hjob
        simpa only [Online.Transcript.testResults_append,
          Online.Transcript.testResults_rawCompleted_cons,
          Online.Transcript.testResults_nil,
          List.append_nil] using ih hold

theorem Online.Transcript.mem_startedLabels_of_testResult
    {transcript : Online.Transcript n}
    {job : Online.Label n} {p : ℝ}
    (hmem : (job, p) ∈ transcript.testResults) :
    job ∈ transcript.startedLabels := by
  induction transcript with
  | nil =>
      simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult tested q =>
          simp only [Online.Transcript.testResults_testResult_cons,
            List.mem_cons] at hmem
          simp only [Online.Transcript.startedLabels_testResult_cons,
            List.mem_cons]
          rcases hmem with h | h
          · exact Or.inl (congrArg Prod.fst h)
          · exact Or.inr (ih h)
      | processed processed =>
          exact ih hmem
      | rawCompleted raw =>
          exact List.mem_cons_of_mem raw (ih hmem)

/-- One valid bounded adaptive step preserves bounded harmonic
reachability. -/
theorem BoundedHarmonicHistory.adaptiveStep
    {K Z : ℕ} {γ u : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config next : Online.Config (K + Z)}
    {assignment nextAssignment : Online.PartialAssignment (K + Z)}
    {action : Online.Action (K + Z)}
    (history : BoundedHarmonicHistory K Z γ L z pending config)
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript)
    (hstep :
      Online.adaptiveStep (.finite u)
        (boundedHarmonicOracle K Z γ)
        config assignment action =
          some (next, nextAssignment)) :
    ∃ L' z' pending',
      BoundedHarmonicHistory K Z γ L' z' pending' next := by
  have virtual := history.capFree
  have hunassigned_of_untouched :
      ∀ {job : Online.Label (K + Z)},
        config.jobs job = .untouched → assignment job = none := by
    intro job hjob
    cases hassigned : assignment job with
    | none => rfl
    | some p =>
        have htested := hsupported job p hassigned
        exact (hstarted.untouched_not_mem job hjob
          (Online.Transcript.mem_startedLabels_of_testResult htested)).elim
  have harmonic_value_of_positive
      (hL : 0 < L) :
      harmonicRankValue K Z γ
          (capFreeHarmonicTranscript K Z γ
            config.transcript).testResults.length =
        harmonicLevel (Z : ℝ) γ (L - 1) := by
    have hzEq : z = Z := by
      rcases virtual.positive_phase with hzero | hz
      · exact (hL.ne' hzero).elim
      · exact hz
    have hcount := virtual.test_count
    simp only [capFreeHarmonicConfig] at hcount
    have hrank :
        (capFreeHarmonicTranscript K Z γ
          config.transcript).testResults.length = K - L := by
      omega
    have hrankLt :
        (capFreeHarmonicTranscript K Z γ
          config.transcript).testResults.length < K := by
      have hLK := virtual.remaining_bounds.1
      omega
    have hidx : K - 1 - (K - L) = L - 1 := by
      have hLK := virtual.remaining_bounds.1
      omega
    rw [harmonicRankValue_of_lt hrankLt, hrank, hidx]
  have harmonic_value_of_zero
      (hLzero : L = 0) :
      harmonicRankValue K Z γ
          (capFreeHarmonicTranscript K Z γ
            config.transcript).testResults.length = 0 := by
    subst L
    have hcount := virtual.test_count
    simp only [capFreeHarmonicConfig] at hcount
    have hzZ := virtual.remaining_bounds.2
    have hrankGe :
        K ≤ (capFreeHarmonicTranscript K Z γ
          config.transcript).testResults.length := by
      omega
    exact harmonicRankValue_of_ge hrankGe
  cases action with
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          by_cases hp : p = 0
          · subst p
            exact ⟨L, z, pending,
              BoundedHarmonicHistory.processZero history hjob⟩
          · have hmem :=
              virtual.tested_positive_mem_pending hjob hp
            obtain ⟨before, after, hpending⟩ :=
              List.append_of_mem hmem
            subst pending
            exact ⟨L, z, before ++ after,
              BoundedHarmonicHistory.processPositive history hjob⟩
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          have hunassigned := hunassigned_of_untouched hjob
          by_cases hL : 0 < L
          · have hvalue := harmonic_value_of_positive hL
            simp [Online.adaptiveStep, Online.Config.step, hjob,
              Online.adaptiveOracle, Online.adaptiveValue,
              hunassigned, boundedHarmonicOracle, hvalue] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact ⟨L - 1, z,
              pending ++ [(job,
                harmonicLevel (Z : ℝ) γ (L - 1))],
              BoundedHarmonicHistory.testPositive history hL job hjob⟩
          · have hLzero : L = 0 := Nat.eq_zero_of_not_pos hL
            have hz : 0 < z := by
              by_contra hnot
              have hz0 : z = 0 := Nat.eq_zero_of_not_pos hnot
              have virtualFinished :
                  HarmonicHistory K Z γ 0 0 pending
                    (capFreeHarmonicConfig K Z γ config) := by
                simpa [hLzero, hz0] using virtual
              exact virtualFinished.no_untouched_of_finished_tests
                job hjob
            have hvalue := harmonic_value_of_zero hLzero
            subst L
            simp [Online.adaptiveStep, Online.Config.step, hjob,
              Online.adaptiveOracle, Online.adaptiveValue,
              hunassigned, boundedHarmonicOracle, hvalue] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact ⟨0, z - 1, pending,
              BoundedHarmonicHistory.testZero history hz job hjob⟩
  | raw job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          by_cases hL : 0 < L
          · have hvalue := harmonic_value_of_positive hL
            exact ⟨L - 1, z, pending,
              BoundedHarmonicHistory.rawPositive
                history hL job hjob hvalue⟩
          · have hLzero : L = 0 := Nat.eq_zero_of_not_pos hL
            have hz : 0 < z := by
              by_contra hnot
              have hz0 : z = 0 := Nat.eq_zero_of_not_pos hnot
              have virtualFinished :
                  HarmonicHistory K Z γ 0 0 pending
                    (capFreeHarmonicConfig K Z γ config) := by
                simpa [hLzero, hz0] using virtual
              exact virtualFinished.no_untouched_of_finished_tests
                job hjob
            have hvalue := harmonic_value_of_zero hLzero
            subst L
            exact ⟨0, z - 1, pending,
              BoundedHarmonicHistory.rawZero
                history hz job hjob hvalue⟩

theorem Online.Config.startedHistoryInvariant_adaptiveStep
    {cap : Cap} {adversary : Online.Oracle n}
    {config next : Online.Config n}
    {assignment nextAssignment : Online.PartialAssignment n}
    {action : Online.Action n}
    (hstarted : config.StartedHistoryInvariant)
    (hstep :
      Online.adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    next.StartedHistoryInvariant := by
  unfold Online.adaptiveStep at hstep
  cases hbase :
      config.step cap (Online.adaptiveOracle adversary assignment) action with
  | none =>
      simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      exact Online.Config.startedHistoryInvariant_step hstarted hbase

theorem runAdaptiveFuel_boundedHarmonicHistory
    {K Z : ℕ} {γ u : ℝ}
    (strategy : Online.Strategy (K + Z))
    (fuel : ℕ) {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    {assignment : Online.PartialAssignment (K + Z)}
    (history : BoundedHarmonicHistory K Z γ L z pending config)
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      Online.SupportedByTranscript assignment config.transcript) :
    ∃ L' z' pending',
      BoundedHarmonicHistory K Z γ L' z' pending'
        (Online.runAdaptiveFuel (.finite u)
          (boundedHarmonicOracle K Z γ)
          strategy fuel config assignment).result.config := by
  induction fuel generalizing L z pending config assignment with
  | zero =>
      exact ⟨L, z, pending, history⟩
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [Online.runAdaptiveFuel, haction] using
            (show ∃ L' z' pending',
              BoundedHarmonicHistory K Z γ L' z' pending' config from
                ⟨L, z, pending, history⟩)
      | some action =>
          cases hstep :
              Online.adaptiveStep (.finite u)
                (boundedHarmonicOracle K Z γ)
                config assignment action with
          | none =>
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                (show ∃ L' z' pending',
                  BoundedHarmonicHistory K Z γ L' z' pending' config from
                    ⟨L, z, pending, history⟩)
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              obtain ⟨Lnext, znext, pendingNext, historyNext⟩ :=
                history.adaptiveStep hstarted hsupported hstep
              have hstartedNext :=
                Online.Config.startedHistoryInvariant_adaptiveStep
                  hstarted hstep
              have hsupportedNext :=
                Online.adaptiveStep_supportedByTranscript
                  (.finite u) (boundedHarmonicOracle K Z γ)
                  config next assignment nextAssignment action
                  hsupported hstep
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                ih historyNext hstartedNext hsupportedNext

theorem adaptiveRun_boundedHarmonicHistory
    (K Z : ℕ) (γ u : ℝ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ) :
    ∃ L z pending,
      BoundedHarmonicHistory K Z γ L z pending
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z γ)
          strategy fuel).result.config := by
  unfold Online.adaptiveRun
  apply runAdaptiveFuel_boundedHarmonicHistory
    strategy fuel
    (BoundedHarmonicHistory.initial (K := K) (Z := Z) (γ := γ))
  · exact Online.Config.initial_startedHistoryInvariant (K + Z)
  · simp [Online.SupportedByTranscript,
      Online.Config.initial, Online.emptyAssignment]

theorem Online.remainingWork_update_raw
    (jobs : Online.Label n → Online.JobState)
    (job : Online.Label n)
    (hjob : jobs job = .untouched) :
    (∑ i : Online.Label n,
        Online.jobWork ((Function.update jobs job .done) i)) + 2 =
      ∑ i : Online.Label n, Online.jobWork (jobs i) := by
  have htest :=
    Online.remainingWork_update_test jobs job 0 hjob
  have hprocess :=
    Online.remainingWork_update_process
      (Function.update jobs job (.tested 0)) job 0
      (by simp [Function.update])
  have hupd :
      Function.update (Function.update jobs job (.tested 0)) job .done =
        Function.update jobs job .done := by
    funext i
    by_cases hi : i = job <;> simp [Function.update, hi]
  rw [hupd] at hprocess
  omega

theorem boundedAdaptiveStep_remainingWork_lt
    {n : ℕ} {u : ℝ} {adversary : Online.Oracle n}
    {config next : Online.Config n}
    {assignment nextAssignment : Online.PartialAssignment n}
    {action : Online.Action n}
    (hstep :
      Online.adaptiveStep (.finite u) adversary
        config assignment action = some (next, nextAssignment)) :
    next.remainingWork < config.remainingWork := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          have h :=
            Online.remainingWork_update_test config.jobs job
              (Online.adaptiveValue adversary assignment
                config.transcript job) hjob
          change
            (∑ i : Online.Label n,
                Online.jobWork
                  ((Function.update config.jobs job
                    (.tested (Online.adaptiveValue adversary assignment
                      config.transcript job))) i)) <
              ∑ i : Online.Label n, Online.jobWork (config.jobs i)
          omega
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          have h :=
            Online.remainingWork_update_process config.jobs job p hjob
          change
            (∑ i : Online.Label n,
                Online.jobWork
                  ((Function.update config.jobs job .done) i)) <
              ∑ i : Online.Label n, Online.jobWork (config.jobs i)
          omega
  | raw job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | done =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
      | untouched =>
          simp [Online.adaptiveStep, Online.Config.step, hjob] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          have h := Online.remainingWork_update_raw config.jobs job hjob
          change
            (∑ i : Online.Label n,
                Online.jobWork
                  ((Function.update config.jobs job .done) i)) <
              ∑ i : Online.Label n, Online.jobWork (config.jobs i)
          omega

theorem runAdaptiveFuel_bounded_settled_of_remainingWork_lt
    {n : ℕ} {u : ℝ} (adversary : Online.Oracle n)
    (strategy : Online.Strategy n)
    (fuel : ℕ) (config : Online.Config n)
    (assignment : Online.PartialAssignment n)
    (hwork : config.remainingWork < fuel) :
    (Online.runAdaptiveFuel (.finite u) adversary strategy
      fuel config assignment).result.reason ≠ .outOfFuel := by
  induction fuel generalizing config assignment with
  | zero =>
      omega
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simp [Online.runAdaptiveFuel, haction]
      | some action =>
          cases hstep :
              Online.adaptiveStep (.finite u) adversary
                config assignment action with
          | none =>
              simp [Online.runAdaptiveFuel, haction, hstep]
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hdecrease :=
                boundedAdaptiveStep_remainingWork_lt hstep
              have hnext : next.remainingWork < fuel := by
                omega
              simpa [Online.runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hnext

theorem boundedHarmonic_analysisFuel_settled
    (K Z : ℕ) (γ u : ℝ)
    (strategy : Online.Strategy (K + Z)) :
    (Online.adaptiveRun (.finite u)
      (boundedHarmonicOracle K Z γ)
      strategy (2 * (K + Z) + 1)).result.reason ≠
        .outOfFuel := by
  unfold Online.adaptiveRun
  apply runAdaptiveFuel_bounded_settled_of_remainingWork_lt
  rw [Online.Config.initial_remainingWork]
  omega

/-! ## Bounded online accounting -/

theorem BoundedHarmonicHistory.amortized_lower
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : BoundedHarmonicHistory K Z 0 L z pending config)
    (processingTime : Online.Label (K + Z) → ℝ)
    (hmatch : HarmonicMatches processingTime config.transcript) :
    harmonicDynamicPotential (Z : ℝ) 0 K Z [] ≤
      Online.completionCost (.finite u) processingTime
          config.transcript +
        Online.transcriptElapsed (.finite u) processingTime
            config.transcript *
          harmonicUnfinished L z pending +
        harmonicDynamicPotential (Z : ℝ) 0 L z pending.values := by
  induction history with
  | initial =>
      simp [Online.Config.initial, harmonicUnfinished,
        Online.completionCost, Online.completionCostFrom]
  | @testPositive L z pending config history hL job hjob ih =>
      let p := harmonicLevel (Z : ℝ) 0 (L - 1)
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hmatch job p
        simp [p]
      have hp1 : 1 ≤ p := by
        dsimp [p]
        exact harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) _
      have hp0 : p ≠ 0 := by linarith
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.testResult job p)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.testResult job p)
      have hpot :=
        harmonicDynamicPotential_test_positive
          (Z : ℝ) 0 (z := z) pending.values hL
      simp only [HarmonicPending.values_append,
        HarmonicPending.values_cons, HarmonicPending.values_nil,
        List.append_nil, p] at hpot ⊢
      simp [Online.Observation.completionLabel, hp0,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_singleton]
      push_cast at hpot hold ⊢
      have hLcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hL))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hLcast]
      simp only [HarmonicPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @testZero z pending config history hz job hjob ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.testResult job 0)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.testResult job 0)
      have hpot :=
        harmonicDynamicPotential_test_zero
          (Z : ℝ) 0 pending.values hz
      simp [Online.Observation.completionLabel,
        Online.Observation.duration] at hcost htime
      unfold harmonicUnfinished at *
      push_cast at hpot hold ⊢
      have hzcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hz))]
        norm_num
      rw [hpot] at hold
      rw [hcost, htime, hzcast]
      simp only [HarmonicPending.values_length] at hold ⊢
      ring_nf at hold ⊢
      nlinarith
  | @processPositive L z before after config job p history hjob ih =>
      have virtual := history.capFree
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = p := by
        apply hprefix job p
        exact history.tested_result hjob
      have hpLower :
          harmonicLevel (Z : ℝ) 0 L ≤ p := by
        apply virtual.pending_lower hZ (job, p)
        simp
      have hp1 : 1 ≤ p :=
        (harmonicLevel_one_le
          (by exact_mod_cast hZ) (le_refl 0) L).trans hpLower
      have hp0 : p ≠ 0 := by linarith
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.processed job)
      have hpot :=
        harmonicDynamicPotential_process
          (ξ := (Z : ℝ)) (γ := (0 : ℝ))
          (by exact_mod_cast hZ) (le_refl 0)
          (L := L) (z := z)
          (before := before.values) (after := after.values)
          (p := p)
          (by
            rcases virtual.positive_phase with hzero | hzEq
            · exact Or.inl hzero
            · exact Or.inr (by exact_mod_cast hzEq))
          hpLower
      simp only [HarmonicPending.values_append,
        HarmonicPending.values_cons] at hpot hold ⊢
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap, hp0] at hcost htime
      unfold harmonicUnfinished at *
      simp only [List.length_append, List.length_cons,
        HarmonicPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      rw [hcost, htime]
      ring_nf at hpot hold ⊢
      nlinarith
  | @processZero L z pending config job history hjob ih =>
      have virtual := history.capFree
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hpmap : processingTime job = 0 := by
        apply hprefix job 0
        exact history.tested_result hjob
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.processed job)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.processed job)
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, hpmap] at hcost htime
      rw [hcost, htime]
      simpa [harmonicUnfinished] using hold
  | @rawPositive L z pending config history hL job hjob hvalue ih =>
      let p := harmonicLevel (Z : ℝ) 0 (L - 1)
      have virtual := history.capFree
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have hzEq : z = Z := by
        rcases virtual.positive_phase with hzero | hz
        · exact (hL.ne' hzero).elim
        · exact hz
      have hLK : L ≤ K := virtual.remaining_bounds.1
      have hpCap : 1 + p ≤ u := by
        have hp3 :
            p < 3 := by
          dsimp [p]
          exact harmonicLevel_lt_three_of_ratio
            hZ (by omega) hratio
        linarith [zStar_gt_four, hu]
      have htest :=
        harmonicDynamicPotential_test_positive
          (Z : ℝ) 0 (z := z) pending.values hL
      have hprocess :=
        harmonicDynamicPotential_process
          (ξ := (Z : ℝ)) (γ := (0 : ℝ))
          (by exact_mod_cast hZ) (le_refl 0)
          (L := L - 1) (z := z)
          (before := pending.values) (after := [])
          (p := p)
          (Or.inr (by exact_mod_cast hzEq))
          (le_refl p)
      have hpot :
          harmonicDynamicPotential (Z : ℝ) 0 L z pending.values ≤
            u * (L + z + pending.length) +
              harmonicDynamicPotential (Z : ℝ) 0
                (L - 1) z pending.values := by
        simp only [List.append_nil, List.length_append,
          List.length_cons, List.length_nil, Nat.add_zero,
          HarmonicPending.values_length] at htest hprocess
        push_cast at htest hprocess ⊢
        have hLcast :
            ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt hL))]
          norm_num
        have hN :
            0 ≤ (L : ℝ) + (z : ℝ) + pending.length := by
          positivity
        have hcapMul :=
          mul_le_mul_of_nonneg_right hpCap hN
        dsimp [p] at htest hprocess
        rw [hLcast] at hprocess
        nlinarith
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.rawCompleted job)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.rawCompleted job)
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, Online.rawDuration] at hcost htime
      unfold harmonicUnfinished at *
      simp only [HarmonicPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      have hLcast :
          ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hL))]
        norm_num
      rw [hcost, htime, hLcast]
      ring_nf at hpot hold ⊢
      nlinarith
  | @rawZero z pending config history hz job hjob hvalue ih =>
      have hprefix := hmatch.of_append
      have hold := ih hprefix
      have htest :=
        harmonicDynamicPotential_test_zero
          (Z : ℝ) 0 pending.values hz
      have huOne : 1 ≤ u := by
        linarith [zStar_gt_four, hu]
      have hpot :
          harmonicDynamicPotential (Z : ℝ) 0 0 z pending.values ≤
            u * (z + pending.length) +
              harmonicDynamicPotential (Z : ℝ) 0
                0 (z - 1) pending.values := by
        push_cast at htest ⊢
        have hzcast :
            ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt hz))]
          norm_num
        have hN :
            0 ≤ (z : ℝ) + pending.length := by positivity
        have hmul :=
          mul_le_mul_of_nonneg_right huOne hN
        simp only [HarmonicPending.values_length] at htest
        nlinarith [htest, hmul]
      have hcost :=
        completionCost_append_singleton (.finite u) processingTime
          config.transcript (.rawCompleted job)
      have htime :=
        transcriptElapsed_append_singleton (.finite u) processingTime
          config.transcript (.rawCompleted job)
      simp [Online.Observation.completionLabel,
        Online.Observation.duration, Online.rawDuration] at hcost htime
      unfold harmonicUnfinished at *
      simp only [HarmonicPending.values_length] at hpot hold ⊢
      push_cast at hpot hold ⊢
      have hzcast :
          ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hz))]
        norm_num
      rw [hcost, htime, hzcast]
      ring_nf at hpot hold ⊢
      nlinarith

/-! ## Freezing the virtual raw revelations -/

theorem capFreeHarmonicFold_testLabels
    (K Z : ℕ) (γ : ℝ)
    (virtual transcript : Online.Transcript n) :
    ((transcript.foldl (capFreeHarmonicStep K Z γ) virtual).testResults.map
        Prod.fst) =
      virtual.testResults.map Prod.fst ++ transcript.startedLabels := by
  induction transcript generalizing virtual with
  | nil =>
      simp
  | cons observation rest ih =>
      rw [List.foldl_cons, ih]
      cases observation <;>
        simp [capFreeHarmonicStep, List.append_assoc]

theorem capFreeHarmonicTranscript_testLabels
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript n) :
    (capFreeHarmonicTranscript K Z γ transcript).testResults.map Prod.fst =
      transcript.startedLabels := by
  simpa [capFreeHarmonicTranscript] using
    capFreeHarmonicFold_testLabels K Z γ
      ([] : Online.Transcript n) transcript

theorem BoundedHarmonicHistory.actual_test_mem_capFree
    {K Z : ℕ} {γ : ℝ} {L z : ℕ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : BoundedHarmonicHistory K Z γ L z pending config)
    {job : Online.Label (K + Z)} {p : ℝ}
    (hmem : (job, p) ∈ config.transcript.testResults) :
    (job, p) ∈
      (capFreeHarmonicTranscript K Z γ
        config.transcript).testResults := by
  induction history with
  | initial =>
      simp [Online.Config.initial] at hmem
  | testPositive history hL tested hjob ih =>
      simp only [capFreeHarmonicTranscript_append_testResult,
        Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil, List.append_nil,
        List.mem_append, List.mem_singleton] at hmem ⊢
      exact hmem.imp_left ih
  | testZero history hz tested hjob ih =>
      simp only [capFreeHarmonicTranscript_append_testResult,
        Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_nil, List.append_nil,
        List.mem_append, List.mem_singleton] at hmem ⊢
      exact hmem.imp_left ih
  | processPositive history hjob ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil,
        List.append_nil] at hmem
      simpa only [capFreeHarmonicTranscript_append_processed,
        Online.Transcript.testResults_append,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil,
        List.append_nil] using ih hmem
  | processZero history hjob ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil,
        List.append_nil] at hmem
      simpa only [capFreeHarmonicTranscript_append_processed,
        Online.Transcript.testResults_append,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil,
        List.append_nil] using ih hmem
  | rawPositive history hL raw hjob hvalue ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_rawCompleted_cons,
        Online.Transcript.testResults_nil, List.append_nil] at hmem
      rw [capFreeHarmonicTranscript_append_rawCompleted]
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil, List.append_nil,
        List.mem_append, List.mem_singleton]
      exact Or.inl (ih hmem)
  | rawZero history hz raw hjob hvalue ih =>
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_rawCompleted_cons,
        Online.Transcript.testResults_nil, List.append_nil] at hmem
      rw [capFreeHarmonicTranscript_append_rawCompleted]
      simp only [Online.Transcript.testResults_append,
        Online.Transcript.testResults_testResult_cons,
        Online.Transcript.testResults_processed_cons,
        Online.Transcript.testResults_nil, List.append_nil,
        List.mem_append, List.mem_singleton]
      exact Or.inl (ih hmem)

theorem pair_snd_eq_of_map_fst_nodup
    {xs : List (α × β)} {a : α} {b c : β}
    (hnodup : (xs.map Prod.fst).Nodup)
    (hb : (a, b) ∈ xs) (hc : (a, c) ∈ xs) :
    b = c := by
  induction xs with
  | nil =>
      simp at hb
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      simp only [List.mem_cons] at hb hc
      rcases hb with hb | hb <;> rcases hc with hc | hc
      · exact congrArg Prod.snd (hb.trans hc.symm)
      · subst head
        exact (hhead (List.mem_map.mpr ⟨(a, c), hc, rfl⟩)).elim
      · subst head
        exact (hhead (List.mem_map.mpr ⟨(a, b), hb, rfl⟩)).elim
      · exact ih htail hb hc

/-- Choose the unique virtual harmonic test value of a label, and zero if
the label has not yet been first-touched. -/
noncomputable def boundedHarmonicDefault
    (K Z : ℕ) (γ : ℝ) (transcript : Online.Transcript (K + Z)) :
    Online.Label (K + Z) → ℝ := by
  classical
  exact fun job =>
    if h : ∃ p,
        (job, p) ∈
          (capFreeHarmonicTranscript K Z γ transcript).testResults
    then Classical.choose h
    else 0

theorem boundedHarmonicDefault_eq_of_testResult
    {K Z : ℕ} {γ : ℝ}
    {transcript : Online.Transcript (K + Z)}
    (hnodup :
      ((capFreeHarmonicTranscript K Z γ transcript).testResults.map
        Prod.fst).Nodup)
    {job : Online.Label (K + Z)} {p : ℝ}
    (hmem :
      (job, p) ∈
        (capFreeHarmonicTranscript K Z γ transcript).testResults) :
    boundedHarmonicDefault K Z γ transcript job = p := by
  unfold boundedHarmonicDefault
  rw [dif_pos ⟨p, hmem⟩]
  let witness :
      ∃ q,
        (job, q) ∈
          (capFreeHarmonicTranscript K Z γ transcript).testResults :=
    ⟨p, hmem⟩
  have hchosen :
      (job, Classical.choose witness) ∈
        (capFreeHarmonicTranscript K Z γ transcript).testResults :=
    Classical.choose_spec witness
  exact pair_snd_eq_of_map_fst_nodup hnodup hchosen hmem

theorem harmonicFullValue_rawSafe
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    {p : ℝ}
    (hp :
      p ∈ harmonicDescendingLevels (Z : ℝ) 0 K ++
        List.replicate Z 0) :
    0 ≤ p ∧ 1 + p ≤ u := by
  rcases List.mem_append.mp hp with hp | hp
  · simp only [harmonicDescendingLevels, List.mem_reverse,
      harmonicFutureLevels, List.mem_map] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    have hmK : m < K := by simpa using hm
    have hZreal : (0 : ℝ) < (Z : ℝ) := by
      exact_mod_cast hZ
    have hp1 :=
      harmonicLevel_one_le
        (ξ := (Z : ℝ)) (γ := 0) hZreal (le_refl 0) m
    have hp3 :=
      harmonicLevel_lt_three_of_ratio
        hZ (Nat.le_of_lt hmK) hratio
    constructor
    · linarith
    · linarith [zStar_gt_four, hu]
  · have hpzero : p = 0 := (List.mem_replicate.mp hp).2
    subst p
    constructor
    · norm_num
    · linarith [zStar_gt_four, hu]

theorem BoundedHarmonicHistory.default_rawSafe
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    {L z : ℕ} {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : BoundedHarmonicHistory K Z 0 L z pending config) :
    ∀ job,
      0 ≤ boundedHarmonicDefault K Z 0 config.transcript job ∧
      1 + boundedHarmonicDefault K Z 0 config.transcript job ≤ u := by
  intro job
  let virtual := history.capFree
  unfold boundedHarmonicDefault
  split
  next h =>
    let p := Classical.choose h
    have hp :
        (job, p) ∈
          (capFreeHarmonicTranscript K Z 0
            config.transcript).testResults :=
      Classical.choose_spec h
    have hpValues :
        p ∈
          (capFreeHarmonicTranscript K Z 0
            config.transcript).testResults.map Prod.snd :=
      List.mem_map.mpr ⟨(job, p), hp, rfl⟩
    have hpExtended :
        p ∈
          (capFreeHarmonicTranscript K Z 0
              config.transcript).testResults.map Prod.snd ++
            harmonicDescendingLevels (Z : ℝ) 0 L ++
            List.replicate z 0 := by
      simp [hpValues]
    have hvalues := virtual.testValues_append_remaining
    simp only [capFreeHarmonicConfig] at hvalues
    rw [hvalues] at hpExtended
    exact harmonicFullValue_rawSafe hZ hratio hu hpExtended
  next h =>
    constructor
    · norm_num
    · linarith [zStar_gt_four, hu]

theorem boundedHarmonicFrozen_eq_default
    (K Z : ℕ) (u : ℝ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0) strategy fuel)
    let default :=
      boundedHarmonicDefault K Z 0 result.result.config.transcript
    Online.frozenProcessingTimes (.finite u)
        (boundedHarmonicOracle K Z 0)
        strategy default fuel =
      default := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_boundedHarmonicHistory K Z 0 u strategy fuel
  have virtual := history.capFree
  have hsupported :
      Online.SupportedByTranscript
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z 0) strategy fuel).assigned
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy fuel).result.config.transcript := by
    unfold Online.adaptiveRun
    apply Online.runAdaptiveFuel_supportedByTranscript
    simp [Online.SupportedByTranscript,
      Online.Config.initial, Online.emptyAssignment]
  funext job
  unfold Online.frozenProcessingTimes
  cases hassigned :
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0)
        strategy fuel).assigned job with
  | none =>
      simp [Online.completeAssignment, hassigned]
  | some p =>
      have hactual := hsupported job p hassigned
      have hvirtual := history.actual_test_mem_capFree hactual
      have hdefault :=
        boundedHarmonicDefault_eq_of_testResult
          virtual.testLabels_nodup hvirtual
      simp [Online.completeAssignment, hassigned, hdefault]

theorem boundedHarmonicDefault_admissible
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0) strategy fuel).result
    ∀ job,
      Online.ValueAdmissible (.finite u)
        (boundedHarmonicDefault K Z 0 result.config.transcript job) := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_boundedHarmonicHistory K Z 0 u strategy fuel
  intro job
  have hsafe := history.default_rawSafe hZ hratio hu job
  exact ⟨hsafe.1, by linarith [hsafe.2]⟩

theorem boundedHarmonicAdaptive_offline_eq_of_completed
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ)
    (hdone :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy fuel).result) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0) strategy fuel).result
    let default :=
      boundedHarmonicDefault K Z 0 result.config.transcript
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (boundedHarmonicOracle K Z 0)
        strategy default fuel
    vectorOfflineCost (.finite u) frozen =
      harmonicFiniteOffline K Z 0 := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_boundedHarmonicHistory K Z 0 u strategy fuel
  have virtual := history.capFree
  have hterminal :=
    virtual.terminal_indices hZ (le_refl 0) hdone
  rcases hterminal with ⟨rfl, rfl, rfl⟩
  let default :=
    boundedHarmonicDefault K Z 0
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0)
        strategy fuel).result.config.transcript
  have hfrozen :=
    boundedHarmonicFrozen_eq_default K Z u strategy fuel
  dsimp only at hfrozen
  change
    vectorOfflineCost (.finite u)
        (Online.frozenProcessingTimes (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy default fuel) =
      harmonicFiniteOffline K Z 0
  rw [hfrozen]
  have hmatch :
      HarmonicMatches default
        (capFreeHarmonicConfig K Z 0
          (Online.adaptiveRun (.finite u)
            (boundedHarmonicOracle K Z 0)
            strategy fuel).result.config).transcript := by
    intro job p hp
    exact boundedHarmonicDefault_eq_of_testResult
      virtual.testLabels_nodup hp
  have hinfinite :=
    HarmonicHistory.terminal_vectorOfflineCost_eq
      hZ (le_refl 0) virtual hdone default hmatch
  have hsafe :
      ∀ job, 1 + default job ≤ u := by
    intro job
    exact (history.default_rawSafe hZ hratio hu job).2
  have heffective :
      vectorEffectiveLengths (.finite u) default =
        vectorEffectiveLengths .infinite default := by
    unfold vectorEffectiveLengths
    congr 1
    funext job
    simp [min_eq_right (hsafe job)]
  unfold vectorOfflineCost at hinfinite ⊢
  rw [heffective]
  exact hinfinite

theorem boundedHarmonicAdaptive_online_lower_of_completed
    {K Z : ℕ} (hZ : 0 < Z)
    (hratio : (K : ℝ) / (Z : ℝ) < 2)
    {u : ℝ} (hu : zStar ≤ u)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ)
    (hdone :
      resultCompleted
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy fuel).result) :
    let result :=
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0) strategy fuel).result
    let default :=
      boundedHarmonicDefault K Z 0 result.config.transcript
    let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (boundedHarmonicOracle K Z 0)
        strategy default fuel
    harmonicFiniteOnline K Z 0 ≤
      Online.runCompletionCost (.finite u) frozen result := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_boundedHarmonicHistory K Z 0 u strategy fuel
  have virtual := history.capFree
  have hterminal :=
    virtual.terminal_indices hZ (le_refl 0) hdone
  rcases hterminal with ⟨rfl, rfl, rfl⟩
  have hmatch :
      HarmonicMatches
        (Online.frozenProcessingTimes (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy
            (boundedHarmonicDefault K Z 0
              (Online.adaptiveRun (.finite u)
                (boundedHarmonicOracle K Z 0)
                strategy fuel).result.config.transcript)
          fuel)
        (Online.adaptiveRun (.finite u)
          (boundedHarmonicOracle K Z 0)
          strategy fuel).result.config.transcript := by
    intro job p hp
    exact Online.frozenProcessingTimes_eq_of_testResult
      (.finite u) (boundedHarmonicOracle K Z 0)
      strategy _ fuel hp
  have hlower :=
    history.amortized_lower hZ hratio hu _ hmatch
  simpa [harmonicFiniteOnline, harmonicUnfinished,
    harmonicDynamicPotential_terminal,
    Online.runCompletionCost] using hlower

theorem boundedHarmonicAdaptive_defeats_of_finite_ratio
    {K Z : ℕ} (hZ : 0 < Z)
    (hspan : (K : ℝ) / (Z : ℝ) < 2)
    {u ratio : ℝ} (hu : zStar ≤ u)
    (hratio :
      ratio * harmonicFiniteOffline K Z 0 ≤
        harmonicFiniteOnline K Z 0)
    (strategy : Online.Strategy (K + Z)) :
    let fuel := 2 * (K + Z) + 1
    let result :=
      (Online.adaptiveRun (.finite u)
        (boundedHarmonicOracle K Z 0) strategy fuel).result
    let default :=
      boundedHarmonicDefault K Z 0 result.config.transcript
    adaptiveDefeats (.finite u)
      (boundedHarmonicOracle K Z 0)
      strategy default fuel ratio := by
  dsimp
  let fuel := 2 * (K + Z) + 1
  let result :=
    (Online.adaptiveRun (.finite u)
      (boundedHarmonicOracle K Z 0) strategy fuel).result
  let default :=
    boundedHarmonicDefault K Z 0 result.config.transcript
  let frozen :=
    Online.frozenProcessingTimes (.finite u)
      (boundedHarmonicOracle K Z 0)
      strategy default fuel
  constructor
  · exact boundedHarmonic_analysisFuel_settled K Z 0 u strategy
  · by_cases hdone : resultCompleted result
    · right
      have hoffline :=
        boundedHarmonicAdaptive_offline_eq_of_completed
          hZ hspan hu strategy fuel hdone
      have honline :=
        boundedHarmonicAdaptive_online_lower_of_completed
          hZ hspan hu strategy fuel hdone
      dsimp [result, default, frozen] at hoffline honline ⊢
      rw [hoffline]
      exact hratio.trans honline
    · exact Or.inl hdone

/-- The cap-free harmonic plateau remains valid at every finite cap at least
`zStar`. -/
theorem boundedHarmonic_adaptive_RStar
    {u : ℝ} (hu : zStar ≤ u) :
    AdaptiveSizeLowerBound (.finite u) RStar := by
  intro strategies ε hε N
  obtain ⟨q, hqPos, hqSpan, hqTarget⟩ :=
    exists_rational_harmonic_parameter hε
  obtain ⟨A, B, hA, hB, hqEq⟩ :=
    positive_rational_as_nat_ratio q hqPos
  have htarget :
      RStar - ε <
        harmonicLimitRatio ((A : ℝ) / (B : ℝ)) := by
    rw [← hqEq]
    exact hqTarget
  have hevent :=
    eventually_harmonicFinite_ratio hA hB htarget
  obtain ⟨m₀, hm₀⟩ :=
    Filter.eventually_atTop.1 hevent
  let m : ℕ := max m₀ N
  let K : ℕ := A * (m + 1)
  let Z : ℕ := B * (m + 1)
  let fuel := 2 * (K + Z) + 1
  let result :=
    (Online.adaptiveRun (.finite u)
      (boundedHarmonicOracle K Z 0)
      (strategies (K + Z)) fuel).result
  let default :=
    boundedHarmonicDefault K Z 0 result.config.transcript
  have hm : m₀ ≤ m := le_max_left _ _
  have hratio :
      (RStar - ε) * harmonicFiniteOffline K Z 0 ≤
        harmonicFiniteOnline K Z 0 := by
    exact hm₀ m hm
  have hZ : 0 < Z := by
    dsimp [Z]
    exact Nat.mul_pos hB (by omega)
  have hscaleRatio :
      (K : ℝ) / (Z : ℝ) = (q : ℝ) := by
    dsimp [K, Z]
    rw [hqEq]
    have hs : (m + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  have hspan : (K : ℝ) / (Z : ℝ) < 2 := by
    rw [hscaleRatio]
    linarith [hqSpan, Real.exp_one_lt_three]
  have hsize : N ≤ K + Z := by
    have hNm : N ≤ m := le_max_right _ _
    have hscale : m + 1 ≤ K := by
      dsimp [K]
      exact Nat.le_mul_of_pos_left (m + 1) hA
    omega
  refine ⟨K + Z, hsize,
    boundedHarmonicOracle K Z 0,
    default, fuel, ?_, ?_, ?_⟩
  · exact boundedHarmonicOracle_admissible hZ hspan hu
  · dsimp [default, result]
    exact boundedHarmonicDefault_admissible
      hZ hspan hu (strategies (K + Z)) fuel
  · dsimp [default, result, fuel]
    exact boundedHarmonicAdaptive_defeats_of_finite_ratio
      hZ hspan hu hratio (strategies (K + Z))

end LowerBound

end

end SchedulingPaper
