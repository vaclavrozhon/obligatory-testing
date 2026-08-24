import SchedulingPaper.Replay
import Mathlib.Tactic

/-!
# Generic test-history invariant

This invariant is independent of any particular strategy.  It records that
successful tests use fresh labels, that every non-untouched state has a test
record, and that a completed obligatory run therefore tested every label
exactly once.
-/

namespace SchedulingPaper
namespace Online

noncomputable section

structure Config.TestingInvariant (config : Config n) : Prop where
  testNodup : (config.transcript.testResults.map Prod.fst).Nodup
  untouched_iff : ∀ job,
    config.jobs job = .untouched ↔
      job ∉ config.transcript.testResults.map Prod.fst

theorem Config.initial_testingInvariant (n : ℕ) :
    (Config.initial n).TestingInvariant := by
  constructor <;> simp [Config.initial]

theorem Config.TestingInvariant.step
    {oracle : Oracle n} {config next : Config n}
    {action : Action n} (hinv : config.TestingInvariant)
    (hstep : config.step .infinite oracle action = some next) :
    next.TestingInvariant := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | untouched =>
          have hfresh : job ∉ config.transcript.testResults.map Prod.fst :=
            (hinv.untouched_iff job).mp hstate
          simp [Config.step, hstate] at hstep
          subst next
          constructor
          · simp only [Transcript.testResults_append, List.map_append]
            apply hinv.testNodup.append
            · exact List.nodup_singleton _
            · intro other hother hsingleton
              have heq : other = job := by
                simpa [Transcript.testResults, Observation.testResult?] using hsingleton
              subst other
              exact hfresh hother
          · intro other
            simp only [Transcript.testResults_append, List.map_append]
            by_cases heq : other = job
            · subst other
              simp [Function.update, hfresh]
            · simp [Function.update, heq, hinv.untouched_iff other]
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
  | process job =>
      cases hstate : config.jobs job with
      | untouched => simp [Config.step, hstate] at hstep
      | tested p =>
          simp [Config.step, hstate] at hstep
          subst next
          constructor
          · simpa using hinv.testNodup
          · intro other
            by_cases heq : other = job
            · subst other
              have htested : job ∈ config.transcript.testResults.map Prod.fst := by
                by_contra hnot
                have := (hinv.untouched_iff job).mpr hnot
                rw [hstate] at this
                contradiction
              simp [Function.update, htested]
            · simp [Function.update, heq, hinv.untouched_iff other]
      | done => simp [Config.step, hstate] at hstep
  | raw job => simp [Config.step] at hstep

theorem runFuel_testingInvariant
    (oracle : Oracle n) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n) (hinv : config.TestingInvariant) :
    (runFuel .infinite oracle strategy fuel config).config.TestingInvariant := by
  induction fuel generalizing config with
  | zero => simpa [runFuel] using hinv
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none => simpa [runFuel, haction] using hinv
      | some action =>
          cases hstep : config.step .infinite oracle action with
          | none => simpa [runFuel, haction, hstep] using hinv
          | some next =>
              simpa [runFuel, haction, hstep] using ih next (hinv.step hstep)

theorem run_testingInvariant
    (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ) :
    (run .infinite oracle strategy fuel).config.TestingInvariant := by
  unfold run
  exact runFuel_testingInvariant oracle strategy fuel (Config.initial n)
    (Config.initial_testingInvariant n)

/-- In an obligatory run, completion of every job forces exactly `n` test
records. -/
theorem testResults_length_eq_n_of_all_done
    (oracle : Oracle n) (strategy : Strategy n) (fuel : ℕ)
    (hdone : ∀ job,
      (run .infinite oracle strategy fuel).config.jobs job = .done) :
    (run .infinite oracle strategy fuel).config.transcript.testResults.length = n := by
  let config := (run .infinite oracle strategy fuel).config
  have hinv := run_testingInvariant oracle strategy fuel
  have hall : ∀ job,
      job ∈ config.transcript.testResults.map Prod.fst := by
    intro job
    by_contra hnot
    have huntouched := (hinv.untouched_iff job).mpr hnot
    have hdone' := hdone job
    change (run .infinite oracle strategy fuel).config.jobs job = .untouched
      at huntouched
    rw [hdone'] at huntouched
    contradiction
  have hperm : (config.transcript.testResults.map Prod.fst).Perm
      (List.ofFn fun job : Fin n => job) := by
    apply (List.perm_ext_iff_of_nodup hinv.testNodup
      (List.nodup_ofFn.mpr fun _ _ hij => hij)).2
    intro job
    constructor
    · intro _
      simp
    · intro _
      exact hall job
  have hlength := hperm.length_eq
  simpa [config] using hlength

end

end Online
end SchedulingPaper
