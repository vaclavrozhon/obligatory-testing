import SchedulingPaper.RandomizedOptionalObservedStrategyCompletion
import SchedulingPaper.RandomizedOptionalObservedPairAccounting
import Mathlib.Tactic

/-!
# Policy-sensitive accounting for observed optional-testing runs

This file records the small operational facts needed to connect the literal
four-block strategy to its finite pair kernel.  In particular, every
observation of a run was requested by the strategy on the preceding prefix,
and the pending-job selector really returns a minimum processing time.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedOnline

noncomputable section
attribute [local instance] Classical.propDecidable

def Observation.requestedAction : Observation n → Action n
  | .testResult job _ => .test job
  | .processed job => .process job
  | .blindCompleted job _ => .blind job

def Transcript.FollowsStrategy
    (strategy : Strategy n) (transcript : Transcript n) : Prop :=
  ∀ index : Fin transcript.length,
    strategy (transcript.take index.val) =
      some (transcript.get index).requestedAction

@[simp] theorem Transcript.followsStrategy_nil (strategy : Strategy n) :
    Transcript.FollowsStrategy strategy [] := by
  intro index
  exact Fin.elim0 index

theorem Transcript.FollowsStrategy.append
    {strategy : Strategy n} {transcript : Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    (observation : Observation n)
    (haction : strategy transcript = some observation.requestedAction) :
    (transcript ++ [observation]).FollowsStrategy strategy := by
  intro index
  by_cases hindex : index.val < transcript.length
  · have hold := hfollow ⟨index.val, hindex⟩
    have htake : (transcript ++ [observation]).take index.val =
        transcript.take index.val :=
      List.take_append_of_le_length hindex.le
    have hget : (transcript ++ [observation]).get index =
        transcript.get ⟨index.val, hindex⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left hindex
    rw [htake, hget]
    exact hold
  · have hvalue : index.val = transcript.length := by
      have hbound : index.val < transcript.length + 1 := by simpa using index.isLt
      omega
    have htake : (transcript ++ [observation]).take index.val = transcript := by
      rw [hvalue]
      exact List.take_left
    have hget : (transcript ++ [observation]).get index = observation := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hvalue]
    rw [htake, hget]
    exact haction

theorem Config.step_observation
    {processing : Label n → ℝ} {config next : Config n}
    {action : Action n} (hstep : config.step processing action = some next) :
    ∃ observation,
      next.transcript = config.transcript ++ [observation] ∧
        observation.requestedAction = action := by
  cases action with
  | test job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          exact ⟨.testResult job (processing job), rfl, rfl⟩
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
  | process job =>
      cases hstate : config.jobs job with
      | untouched => simp [Config.step, hstate] at hstep
      | tested p =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          exact ⟨.processed job, rfl, rfl⟩
      | done => simp [Config.step, hstate] at hstep
  | blind job =>
      cases hstate : config.jobs job with
      | untouched =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          exact ⟨.blindCompleted job (processing job), rfl, rfl⟩
      | tested p => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep

theorem runFuel_followsStrategy
    (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hfollow : config.transcript.FollowsStrategy strategy) :
    (runFuel processing strategy fuel config).config.transcript
      |>.FollowsStrategy strategy := by
  induction fuel generalizing config with
  | zero => simpa [runFuel] using hfollow
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simp only
          exact hfollow
      | some action =>
          simp only
          cases hstep : config.step processing action with
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
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    (run processing strategy fuel).config.transcript
      |>.FollowsStrategy strategy := by
  unfold run
  exact runFuel_followsStrategy processing strategy fuel (Config.initial n)
    (Transcript.followsStrategy_nil strategy)

theorem Transcript.FollowsStrategy.action_at
    {strategy : Strategy n} {transcript : Transcript n}
    (hfollow : transcript.FollowsStrategy strategy)
    {before after : Transcript n} {observation : Observation n}
    (hdecomp : transcript = before ++ observation :: after) :
    strategy before = some observation.requestedAction := by
  subst transcript
  let index : Fin (before ++ observation :: after).length :=
    ⟨before.length, by simp⟩
  have h := hfollow index
  simpa [index, List.get_eq_getElem] using h

private theorem shortestFold_minimal
    (best : Label n × ℝ) (rest : List (Label n × ℝ)) :
    let chosen := rest.foldl
      (fun current candidate =>
        if resultBefore candidate current then candidate else current) best
    chosen.2 ≤ best.2 ∧ ∀ candidate ∈ rest, chosen.2 ≤ candidate.2 := by
  induction rest generalizing best with
  | nil => simp
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hlt : resultBefore candidate best
      · simp only [if_pos hlt]
        have htail := ih candidate
        have hvalue : candidate.2 ≤ best.2 := by
          rcases hlt with hlt | ⟨heq, _⟩
          · exact hlt.le
          · exact heq.le
        refine ⟨htail.1.trans hvalue, ?_⟩
        intro other hmem
        rcases List.mem_cons.mp hmem with rfl | htailMem
        · exact htail.1
        · exact htail.2 other htailMem
      · simp only [if_neg hlt]
        have htail := ih best
        refine ⟨htail.1, ?_⟩
        intro other hmem
        rcases List.mem_cons.mp hmem with rfl | htailMem
        · exact htail.1.trans (le_of_not_gt fun hcandidate =>
            hlt (Or.inl hcandidate))
        · exact htail.2 other htailMem

theorem shortestResult?_processing_le
    {results : List (Label n × ℝ)} {chosen candidate : Label n × ℝ}
    (hchosen : shortestResult? results = some chosen)
    (hcandidate : candidate ∈ results) :
    chosen.2 ≤ candidate.2 := by
  cases results with
  | nil => simp [shortestResult?] at hchosen
  | cons best rest =>
      simp only [shortestResult?, Option.some.injEq] at hchosen
      subst chosen
      have hminimal := shortestFold_minimal best rest
      rcases List.mem_cons.mp hcandidate with rfl | htail
      · exact hminimal.1
      · exact hminimal.2 candidate htail

def resultAtMost (left right : Label n × ℝ) : Prop :=
  left.2 < right.2 ∨
    (left.2 = right.2 ∧ left.1.val ≤ right.1.val)

private theorem resultAtMost_refl (result : Label n × ℝ) :
    resultAtMost result result := by
  exact Or.inr ⟨rfl, le_rfl⟩

private theorem resultAtMost_trans
    {first second third : Label n × ℝ}
    (hfirst : resultAtMost first second)
    (hsecond : resultAtMost second third) :
    resultAtMost first third := by
  rcases hfirst with hlt | ⟨heq, hlabel⟩ <;>
    rcases hsecond with hlt' | ⟨heq', hlabel'⟩
  · exact Or.inl (hlt.trans hlt')
  · exact Or.inl (hlt.trans_le heq'.le)
  · exact Or.inl (heq.le.trans_lt hlt')
  · exact Or.inr ⟨heq.trans heq', hlabel.trans hlabel'⟩

private theorem resultAtMost_of_resultBefore
    {candidate best : Label n × ℝ}
    (hbefore : resultBefore candidate best) :
    resultAtMost candidate best := by
  rcases hbefore with hlt | ⟨heq, hlabel⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hlabel.le⟩

private theorem resultAtMost_of_not_resultBefore
    {candidate best : Label n × ℝ}
    (hbefore : ¬resultBefore candidate best) :
    resultAtMost best candidate := by
  by_cases hlt : best.2 < candidate.2
  · exact Or.inl hlt
  · have hle : candidate.2 ≤ best.2 := le_of_not_gt hlt
    have hnotReverse : ¬candidate.2 < best.2 := fun h =>
      hbefore (Or.inl h)
    have heq : best.2 = candidate.2 :=
      le_antisymm (le_of_not_gt hnotReverse) hle
    have hlabel : best.1.val ≤ candidate.1.val := by
      by_contra hnot
      exact hbefore (Or.inr ⟨heq.symm, Nat.lt_of_not_ge hnot⟩)
    exact Or.inr ⟨heq, hlabel⟩

private theorem shortestFold_lex_minimal
    (best : Label n × ℝ) (rest : List (Label n × ℝ)) :
    let chosen := rest.foldl
      (fun current candidate =>
        if resultBefore candidate current then candidate else current) best
    resultAtMost chosen best ∧
      ∀ candidate ∈ rest, resultAtMost chosen candidate := by
  induction rest generalizing best with
  | nil => simp [resultAtMost_refl]
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      by_cases hbefore : resultBefore candidate best
      · simp only [if_pos hbefore]
        have htail := ih candidate
        refine ⟨resultAtMost_trans htail.1
            (resultAtMost_of_resultBefore hbefore), ?_⟩
        intro other hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact htail.1
        · exact htail.2 other hrest
      · simp only [if_neg hbefore]
        have htail := ih best
        refine ⟨htail.1, ?_⟩
        intro other hmem
        rcases List.mem_cons.mp hmem with rfl | hrest
        · exact resultAtMost_trans htail.1
            (resultAtMost_of_not_resultBefore hbefore)
        · exact htail.2 other hrest

/-- The deterministic SPT selector breaks equal processing-time ties by
virtual label. -/
theorem shortestResult?_resultAtMost
    {results : List (Label n × ℝ)} {chosen candidate : Label n × ℝ}
    (hchosen : shortestResult? results = some chosen)
    (hcandidate : candidate ∈ results) :
    resultAtMost chosen candidate := by
  cases results with
  | nil => simp [shortestResult?] at hchosen
  | cons best rest =>
      simp only [shortestResult?, Option.some.injEq] at hchosen
      subst chosen
      have hminimal := shortestFold_lex_minimal best rest
      rcases List.mem_cons.mp hcandidate with rfl | htail
      · exact hminimal.1
      · exact hminimal.2 candidate htail

theorem shortestResult?_label_le_of_processing_eq
    {results : List (Label n × ℝ)} {chosen candidate : Label n × ℝ}
    (hchosen : shortestResult? results = some chosen)
    (hcandidate : candidate ∈ results)
    (heq : chosen.2 = candidate.2) :
    chosen.1.val ≤ candidate.1.val := by
  rcases shortestResult?_resultAtMost hchosen hcandidate with
      hlt | ⟨_, hlabel⟩
  · rw [heq] at hlt
    exact (lt_irrefl _ hlt).elim
  · exact hlabel

/-! ## One-label lifecycle projections -/

/-- Reachability fixes the complete owner-only shape of every job. -/
structure Config.OwnerProjectionInvariant
    (processing : Label n → ℝ) (config : Config n) : Prop where
  untouched : ∀ job, config.jobs job = .untouched →
    config.transcript.ownerProjection job job = []
  tested : ∀ job value, config.jobs job = .tested value →
    config.transcript.ownerProjection job job =
      [.testResult job (processing job)]
  done : ∀ job, config.jobs job = .done →
    config.transcript.ownerProjection job job =
        [.blindCompleted job (processing job)] ∨
      config.transcript.ownerProjection job job =
        [.testResult job (processing job), .processed job]

theorem Config.initial_ownerProjectionInvariant (processing : Label n → ℝ) :
    (Config.initial n).OwnerProjectionInvariant processing := by
  constructor <;> simp [Config.initial, Transcript.ownerProjection]

private theorem ownerProjection_append_self
    (transcript : Transcript n) (job : Label n) (observation : Observation n) :
    (transcript ++ [observation]).ownerProjection job job =
      transcript.ownerProjection job job ++
        if observation.ownerLabel = job then [observation] else [] := by
  by_cases howner : observation.ownerLabel = job <;>
    simp [Transcript.ownerProjection, howner]

theorem Config.OwnerProjectionInvariant.step
    {processing : Label n → ℝ} {config next : Config n}
    (hinv : config.OwnerProjectionInvariant processing)
    {action : Action n} (hstep : config.step processing action = some next) :
    next.OwnerProjectionInvariant processing := by
  cases action with
  | test touched =>
      cases hstate : config.jobs touched with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          constructor
          · intro job hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp [Observation.ownerLabel, hne, Ne.symm hne,
              hinv.untouched job (by simpa [Function.update, hne] using hjob)]
          · intro job value hjob
            by_cases heq : job = touched
            · subst job
              have hvalue : value = processing touched := by
                simpa [Function.update] using hjob.symm
              subst value
              rw [ownerProjection_append_self]
              simp [Observation.ownerLabel, hinv.untouched touched hstate]
            · rw [ownerProjection_append_self]
              simp [Observation.ownerLabel, heq, Ne.symm heq,
                hinv.tested job value
                  (by simpa [Function.update, heq] using hjob)]
          · intro job hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp only [Observation.ownerLabel, Ne.symm hne, ↓reduceIte,
              List.append_nil]
            exact hinv.done job (by simpa [Function.update, hne] using hjob)
  | process touched =>
      cases hstate : config.jobs touched with
      | untouched => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | tested value =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          constructor
          · intro job hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp [Observation.ownerLabel, hne, Ne.symm hne,
              hinv.untouched job (by simpa [Function.update, hne] using hjob)]
          · intro job other hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp [Observation.ownerLabel, hne, Ne.symm hne,
              hinv.tested job other
                (by simpa [Function.update, hne] using hjob)]
          · intro job hjob
            by_cases heq : job = touched
            · subst job
              rw [ownerProjection_append_self,
                hinv.tested touched value hstate]
              simp [Observation.ownerLabel]
            · rw [ownerProjection_append_self]
              simp only [Observation.ownerLabel, Ne.symm heq, ↓reduceIte,
                List.append_nil]
              exact hinv.done job (by simpa [Function.update, heq] using hjob)
  | blind touched =>
      cases hstate : config.jobs touched with
      | tested value => simp [Config.step, hstate] at hstep
      | done => simp [Config.step, hstate] at hstep
      | untouched =>
          simp only [Config.step, hstate, Option.some.injEq] at hstep
          subst next
          constructor
          · intro job hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp [Observation.ownerLabel, hne, Ne.symm hne,
              hinv.untouched job (by simpa [Function.update, hne] using hjob)]
          · intro job value hjob
            have hne : job ≠ touched := by
              intro heq
              subst job
              simp [Function.update] at hjob
            rw [ownerProjection_append_self]
            simp [Observation.ownerLabel, hne, Ne.symm hne,
              hinv.tested job value
                (by simpa [Function.update, hne] using hjob)]
          · intro job hjob
            by_cases heq : job = touched
            · subst job
              left
              rw [ownerProjection_append_self,
                hinv.untouched touched hstate]
              simp [Observation.ownerLabel]
            · rw [ownerProjection_append_self]
              simp only [Observation.ownerLabel, Ne.symm heq, ↓reduceIte,
                List.append_nil]
              exact hinv.done job (by simpa [Function.update, heq] using hjob)

theorem runFuel_ownerProjectionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (hinv : config.OwnerProjectionInvariant processing) :
    (runFuel processing strategy fuel config).config
      |>.OwnerProjectionInvariant processing := by
  induction fuel generalizing config with
  | zero => exact hinv
  | succ fuel ih =>
      simp only [runFuel]
      cases haction : strategy config.transcript with
      | none =>
          simp only
          exact hinv
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none =>
              simp only
              exact hinv
          | some next =>
              simp only
              exact ih next (hinv.step hstep)

theorem run_ownerProjectionInvariant
    (processing : Label n → ℝ) (strategy : Strategy n) (fuel : ℕ) :
    (run processing strategy fuel).config
      |>.OwnerProjectionInvariant processing := by
  unfold run
  exact runFuel_ownerProjectionInvariant processing strategy fuel
    (Config.initial n) (Config.initial_ownerProjectionInvariant processing)

/-! ## Canonical prefixes stay inside the certified invariant -/

theorem Config.CanonicalGood.step_canonical
    {n q : ℕ} (hq : q ≤ n) {processing : Label n → ℝ}
    {low medium : ℝ → Bool} {config next : Config n}
    (hgood : config.CanonicalGood processing q) {action : Action n}
    (hchosen : canonicalStrategy n q low medium config.transcript = some action)
    (hstep : config.step processing action = some next) :
    next.CanonicalGood processing q := by
  by_cases hzero : config.remainingWork = 0
  · have hstop := canonicalStrategy_stop_of_zero hq hgood hzero low medium
    rw [hstop] at hchosen
    contradiction
  · have hpos : 0 < config.remainingWork := Nat.pos_of_ne_zero hzero
    obtain ⟨certified⟩ := canonicalStrategy_progress hq hgood hpos low medium
    have haction : action = certified.action :=
      Option.some.inj (hchosen.symm.trans certified.chosen)
    subst action
    have hnext : next = certified.next :=
      Option.some.inj (hstep.symm.trans certified.legal)
    subst next
    exact certified.good

theorem runFuel_canonicalGood
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (fuel : ℕ) (config : Config n)
    (hgood : config.CanonicalGood processing q) :
    (runFuel processing (canonicalStrategy n q low medium) fuel config).config
      |>.CanonicalGood processing q := by
  induction fuel generalizing config with
  | zero => exact hgood
  | succ fuel ih =>
      simp only [runFuel]
      cases hchosen : canonicalStrategy n q low medium config.transcript with
      | none =>
          simp only
          exact hgood
      | some action =>
          simp only
          cases hstep : config.step processing action with
          | none =>
              simp only
              exact hgood
          | some next =>
              simp only
              exact ih next (hgood.step_canonical hq hchosen hstep)

theorem run_canonicalGood
    {n q : ℕ} (hq : q ≤ n) (processing : Label n → ℝ)
    (low medium : ℝ → Bool) (fuel : ℕ) :
    (run processing (canonicalStrategy n q low medium) fuel).config
      |>.CanonicalGood processing q := by
  unfold run
  exact runFuel_canonicalGood hq processing low medium fuel (Config.initial n)
    (Config.initial_canonicalGood processing q)

end

end ObservedOnline
end RandomizedOptional
end SchedulingPaper
