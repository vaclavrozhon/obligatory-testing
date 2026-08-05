import SchedulingPaper.RawStrategy
import SchedulingPaper.TimedOnline
import SchedulingPaper.Asymptotics
import Mathlib.Data.List.TakeDrop

/-!
# Exact execution and cost of the Raw policy

The executable `rawStrategy` is evaluated here.  After any positive amount
of extra fuel beyond its `n` raw operations, it has completed every job,
stops normally, and has total completion cost `u * triangular n`.
-/

namespace SchedulingPaper.Online

noncomputable section

def rawPrefixLabels (n k : ℕ) : List (Label n) :=
  (List.finRange n).take k

def rawPrefixTranscript (n k : ℕ) : Transcript n :=
  (rawPrefixLabels n k).map Observation.rawCompleted

def rawPrefixConfig (n k : ℕ) : Config n where
  jobs := fun job => if job.val < k then .done else .untouched
  transcript := rawPrefixTranscript n k

@[simp]
theorem rawPrefixLabels_length
    {n k : ℕ} (hk : k ≤ n) :
    (rawPrefixLabels n k).length = k := by
  simp [rawPrefixLabels, hk]

@[simp]
theorem rawPrefixTranscript_length
    {n k : ℕ} (hk : k ≤ n) :
    (rawPrefixTranscript n k).length = k := by
  simp [rawPrefixTranscript, hk]

theorem rawPrefixTranscript_rawCompletedLabels
    {n k : ℕ} :
    (rawPrefixTranscript n k).rawCompletedLabels =
      rawPrefixLabels n k := by
  unfold rawPrefixTranscript Transcript.rawCompletedLabels
  induction rawPrefixLabels n k with
  | nil => rfl
  | cons label labels ih =>
      simp [ih]

@[simp]
theorem rawPrefixConfig_zero (n : ℕ) :
    rawPrefixConfig n 0 = Config.initial n := by
  rw [Config.mk.injEq]
  constructor
  · funext job
    simp [rawPrefixConfig, Config.initial]
  · simp [rawPrefixConfig, Config.initial, rawPrefixTranscript,
      rawPrefixLabels]

theorem rawPrefixConfig_jobs_current
    {n k : ℕ} (hk : k < n) :
    (rawPrefixConfig n k).jobs ⟨k, hk⟩ = .untouched := by
  simp [rawPrefixConfig]

theorem rawPrefixTranscript_succ
    {n k : ℕ} (hk : k < n) :
    rawPrefixTranscript n (k + 1) =
      rawPrefixTranscript n k ++
        [.rawCompleted ⟨k, hk⟩] := by
  unfold rawPrefixTranscript rawPrefixLabels
  have ht :=
    List.take_concat_get' (List.finRange n) k
      (by simpa using hk)
  have hmap :=
    congrArg (List.map Observation.rawCompleted) ht
  simpa using hmap.symm

theorem rawPrefixConfig_step
    {n k : ℕ} (hk : k < n) (u : ℝ) (oracle : Oracle n) :
    (rawPrefixConfig n k).step (.finite u) oracle
        (.raw ⟨k, hk⟩) =
      some (rawPrefixConfig n (k + 1)) := by
  simp only [Config.step, rawPrefixConfig_jobs_current hk]
  congr 1
  rw [Config.mk.injEq]
  constructor
  · funext job
    simp only [rawPrefixConfig]
    by_cases heq : job = ⟨k, hk⟩
    · subst job
      simp
    · have hval : job.val ≠ k := by
        intro h
        apply heq
        exact Fin.ext h
      have hlt :
          job.val < k + 1 ↔ job.val < k := by omega
      simp [Function.update, heq, hlt]
  · simp only [rawPrefixConfig]
    rw [rawPrefixTranscript_succ hk]

theorem rawStrategy_on_prefix
    {n k : ℕ} (hk : k < n) :
    rawStrategy n (rawPrefixTranscript n k) =
      some (.raw ⟨k, hk⟩) := by
  have hlen :
      (rawPrefixTranscript n k).rawCompletedLabels.length = k := by
    rw [rawPrefixTranscript_rawCompletedLabels]
    exact rawPrefixLabels_length hk.le
  unfold rawStrategy
  simp [hlen, hk]

theorem rawStrategy_on_full_prefix (n : ℕ) :
    rawStrategy n (rawPrefixTranscript n n) = none := by
  have hlen :
      (rawPrefixTranscript n n).rawCompletedLabels.length = n := by
    rw [rawPrefixTranscript_rawCompletedLabels]
    exact rawPrefixLabels_length le_rfl
  unfold rawStrategy
  simp [hlen]

/-- Evaluation from an arbitrary canonical prefix.  `extra` expresses that
the result is stable under any additional positive fuel. -/
theorem runFuel_rawPrefix
    (n k extra : ℕ) (hk : k ≤ n)
    (u : ℝ) (oracle : Oracle n) :
    runFuel (.finite u) oracle (rawStrategy n)
        ((n - k) + 1 + extra) (rawPrefixConfig n k) =
      ⟨rawPrefixConfig n n, .strategyStopped⟩ := by
  induction hremaining : n - k generalizing k extra with
  | zero =>
      have hkn : k = n := by omega
      subst k
      rw [show 0 + 1 + extra = extra + 1 by omega]
      simp only [runFuel]
      change
        (match rawStrategy n (rawPrefixTranscript n n) with
          | none => _
          | some action => _) =
        RunResult.mk (rawPrefixConfig n n) (.strategyStopped)
      rw [rawStrategy_on_full_prefix]
  | succ remaining ih =>
      have hkt : k < n := by omega
      have hnext : n - (k + 1) = remaining := by omega
      rw [show (remaining + 1) + 1 + extra =
          (remaining + 1 + extra) + 1 by omega]
      simp only [runFuel]
      change
        (match rawStrategy n (rawPrefixTranscript n k) with
          | none => _
          | some action =>
              match (rawPrefixConfig n k).step (.finite u) oracle action with
              | none => _
              | some next =>
                  runFuel (.finite u) oracle (rawStrategy n)
                    (remaining + 1 + extra) next) =
          ⟨rawPrefixConfig n n, .strategyStopped⟩
      rw [rawStrategy_on_prefix hkt]
      simp only
      change
        (match (rawPrefixConfig n k).step (.finite u) oracle
            (.raw ⟨k, hkt⟩) with
          | none => _
          | some next =>
              runFuel (.finite u) oracle (rawStrategy n)
                (remaining + 1 + extra) next) =
          RunResult.mk (rawPrefixConfig n n) (.strategyStopped)
      rw [rawPrefixConfig_step hkt u oracle]
      exact ih (k + 1) extra (by omega) hnext

theorem run_rawStrategy
    (n extra : ℕ) (u : ℝ) (oracle : Oracle n) :
    run (.finite u) oracle (rawStrategy n) (n + 1 + extra) =
      ⟨rawPrefixConfig n n, .strategyStopped⟩ := by
  unfold run
  rw [← rawPrefixConfig_zero n]
  simpa using runFuel_rawPrefix n 0 extra (Nat.zero_le n) u oracle

theorem rawPrefixConfig_full_completed (n : ℕ) :
    ∀ job, (rawPrefixConfig n n).jobs job = .done := by
  intro job
  simp [rawPrefixConfig]

theorem raw_run_completed
    (n extra : ℕ) (u : ℝ) (oracle : Oracle n) :
    ∀ job,
      (run (.finite u) oracle (rawStrategy n)
        (n + 1 + extra)).config.jobs job = .done := by
  rw [run_rawStrategy]
  exact rawPrefixConfig_full_completed n

theorem completionCostFrom_rawCompleted
    (u time : ℝ) (processingTime : Label n → ℝ)
    (labels : List (Label n)) :
    completionCostFrom (.finite u) processingTime time
        (labels.map Observation.rawCompleted) =
      labels.length * time + u * triangular labels.length := by
  induction labels generalizing time with
  | nil =>
      simp [completionCostFrom, triangular]
  | cons label labels ih =>
      simp only [List.map_cons, completionCostFrom,
        Observation.duration, rawDuration,
        Observation.completionLabel, Option.isSome_some, if_true]
      rw [ih]
      unfold triangular
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem completionCost_rawPrefix_full
    (n : ℕ) (u : ℝ) (processingTime : Label n → ℝ) :
    completionCost (.finite u) processingTime
        (rawPrefixConfig n n).transcript =
      u * triangular n := by
  unfold completionCost rawPrefixConfig rawPrefixTranscript
  rw [completionCostFrom_rawCompleted]
  simp [rawPrefixLabels]

theorem raw_runCompletionCost
    (n extra : ℕ) (u : ℝ) (processingTime : Label n → ℝ) :
    runCompletionCost (.finite u) processingTime
        (run (.finite u) (fixedOracle processingTime)
          (rawStrategy n) (n + 1 + extra)) =
      u * triangular n := by
  rw [run_rawStrategy]
  exact completionCost_rawPrefix_full n u processingTime

end

end SchedulingPaper.Online
