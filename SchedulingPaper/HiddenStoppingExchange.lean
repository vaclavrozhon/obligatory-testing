import SchedulingPaper.HiddenStoppingPairAccounting

/-!
# The global hidden-stopping exchange

This module closes the remaining literal pair-exchange bridge.  It follows
the raw-safe hidden-stopping proof: first establish the uniform analytic
remainder for the canonical four-block schedule, then show that every
completed operational trace dominates that canonical schedule.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-! ## Uniform analytic remainder for the exact canonical objectives -/

set_option maxHeartbeats 800000

/-- The first-crossing `1/S` overshoot costs only `O(n)` after the normalized
leading expression is rescaled by `n²`.  The deliberately generous constant
`3u²+4u` also absorbs every diagonal term. -/
theorem stoppingExact_competitive_of_firstCrossing
    {u ratio n v e d : ℝ}
    (hu : 1 < u)
    (certificate : BinaryStoppingCertificate u ratio)
    (hn : 0 < n) (hv0 : 0 ≤ v) (hvn : v ≤ n)
    (he0 : 0 ≤ e) (hd0 : 0 ≤ d)
    (hremaining : 0 < n - v)
    (hmass : e + d ≤ n - v)
    (hyAlpha :
      certificate.alpha ≤ (e + d) / (n - v))
    (hyOvershoot :
      (e + d) / (n - v) - certificate.alpha ≤
        1 / (n - v)) :
    ratio * stoppingOptExact u n e d ≤
      stoppingAlgExact u n v e d +
        (3 * u ^ 2 + 4 * u) * n := by
  let S := n - v
  let sigma := S / n
  let y := (e + d) / S
  let b := e / S
  have hu0 : 0 ≤ u := by linarith
  have hS : 0 < S := by simpa [S] using hremaining
  have hn0 : 0 ≤ n := hn.le
  have hSle : S ≤ n := by
    dsimp [S]
    linarith
  have hsigma0 : 0 ≤ sigma := div_nonneg hS.le hn.le
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma]
    exact (div_le_one hn).2 hSle
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (add_nonneg he0 hd0) hS.le
  have hy1 : y ≤ 1 := by
    dsimp [y, S]
    exact (div_le_one hremaining).2 hmass
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg he0 hS.le
  have hbY : b ≤ y := by
    dsimp [b, y]
    apply (div_le_div_iff_of_pos_right hS).2
    linarith
  have hf :
      -(2 * u ^ 2 + 4 * u) *
          (y - certificate.alpha) ≤
        stoppingF u ratio y b :=
    certificate.stoppingF_overshoot_lower hu.le
      (by simpa [y, S] using hyAlpha) hy1 hb0 hbY
  have hover :
      y - certificate.alpha ≤ 1 / S := by
    simpa [y, S] using hyOvershoot
  have hgapIdentity :=
    stoppingLeading_decomposition_sigma u ratio sigma y b
  have hraw :
      0 ≤ (u - ratio) * (1 - sigma ^ 2) :=
    stopping_raw_part_nonneg certificate.ratio_le_cap
      hsigma0 hsigma1
  have hsigmaSq : 0 ≤ sigma ^ 2 := sq_nonneg sigma
  have hscaledF :
      -(2 * u ^ 2 + 4 * u) * sigma ^ 2 / S ≤
        sigma ^ 2 * stoppingF u ratio y b := by
    have hmul :=
      mul_le_mul_of_nonneg_left hf hsigmaSq
    have hoverMul :=
      mul_le_mul_of_nonneg_left hover
        (mul_nonneg
          (by positivity : 0 ≤ 2 * u ^ 2 + 4 * u)
          hsigmaSq)
    calc
      -(2 * u ^ 2 + 4 * u) * sigma ^ 2 / S =
          sigma ^ 2 *
            (-(2 * u ^ 2 + 4 * u) / S) := by ring
      _ ≤ sigma ^ 2 *
          (-(2 * u ^ 2 + 4 * u) *
            (y - certificate.alpha)) := by
        have hcoef : 0 ≤ 2 * u ^ 2 + 4 * u := by positivity
        have hneg :
            -(2 * u ^ 2 + 4 * u) / S ≤
              -(2 * u ^ 2 + 4 * u) *
                (y - certificate.alpha) := by
          have := mul_le_mul_of_nonneg_left hover hcoef
          calc
            -(2 * u ^ 2 + 4 * u) / S =
                -((2 * u ^ 2 + 4 * u) * (1 / S)) := by ring
            _ ≤ -((2 * u ^ 2 + 4 * u) *
                (y - certificate.alpha)) :=
              neg_le_neg this
            _ = -(2 * u ^ 2 + 4 * u) *
                (y - certificate.alpha) := by ring
        exact mul_le_mul_of_nonneg_left hneg hsigmaSq
      _ ≤ sigma ^ 2 * stoppingF u ratio y b := hmul
  have hleading :
      -(2 * u ^ 2 + 4 * u) * S ≤
        n ^ 2 *
          (stoppingAlgLeading u (v / n)
              ((v + e + d) / n) (e / n) -
            ratio *
              stoppingOptLeading u (v / n)
                ((v + e + d) / n)) := by
    have hnu : v / n = 1 - sigma := by
      dsimp [sigma, S]
      field_simp [hn.ne']
      ring
    have hdelta :
        (v + e + d) / n = 1 - sigma + sigma * y := by
      dsimp [sigma, y, S]
      field_simp [hn.ne', hremaining.ne']
      ring
    have hell : e / n = sigma * b := by
      dsimp [sigma, b, S]
      field_simp [hn.ne', hremaining.ne']
    rw [hnu, hdelta, hell, hgapIdentity]
    have hgapLower :
        -(2 * u ^ 2 + 4 * u) * sigma ^ 2 / S ≤
          (u - ratio) * (1 - sigma ^ 2) +
            sigma ^ 2 * stoppingF u ratio y b := by
      linarith
    have hnSq : 0 ≤ n ^ 2 := sq_nonneg n
    have hmul := mul_le_mul_of_nonneg_left hgapLower hnSq
    have hscale :
        n ^ 2 *
            (-(2 * u ^ 2 + 4 * u) * sigma ^ 2 / S) =
          -(2 * u ^ 2 + 4 * u) * S := by
      dsimp [sigma]
      field_simp [hn.ne', hS.ne']
    rwa [hscale] at hmul
  have hAlg :=
    stoppingAlgExact_eq_leading
      (u := u) (n := n) (v := v) (e := e) (d := d) hn.ne'
  have hOpt :=
    stoppingOptExact_eq_leading
      (u := u) (n := n) (v := v) (e := e) (d := d) hn.ne'
  have hL : e + d ≤ n := hmass.trans hSle
  have hdiagAlg :
      0 ≤ d * u - d + e * u + n + u * v - v := by
    nlinarith
  have hdiagOpt0 :
      0 ≤ d * u - d + e * u - e + n := by
    nlinarith
  have hdiagOptUpper :
      d * u - d + e * u - e + n ≤ u * n := by
    nlinarith
  have hratioDiag :
      ratio * (d * u - d + e * u - e + n) ≤
        u ^ 2 * n := by
    have hratio0 := certificate.ratio_nonneg
    have hfirst :=
      mul_le_mul_of_nonneg_left hdiagOptUpper hratio0
    have hsecond :=
      mul_le_mul_of_nonneg_right certificate.ratio_le_cap
        (mul_nonneg hu0 hn0)
    nlinarith
  have hcoef0 : 0 ≤ 2 * u ^ 2 + 4 * u := by positivity
  have hleadN :
      -(2 * u ^ 2 + 4 * u) * n ≤
        n ^ 2 *
          (stoppingAlgLeading u (v / n)
              ((v + e + d) / n) (e / n) -
            ratio *
              stoppingOptLeading u (v / n)
                ((v + e + d) / n)) := by
    have hscale :=
      mul_le_mul_of_nonneg_left hSle hcoef0
    nlinarith
  have hOptMul := congrArg (fun z : ℝ => ratio * z) hOpt
  have htwice :
      -((2 * u ^ 2 + 4 * u) + u ^ 2) * n ≤
        2 * stoppingAlgExact u n v e d -
          2 * ratio * stoppingOptExact u n e d := by
    nlinarith [hAlg, hOptMul, hleadN]
  have hrem0 : 0 ≤ (3 * u ^ 2 + 4 * u) * n := by
    positivity
  nlinarith

end LowerBound

namespace HiddenStoppingOracle

open Online

/-! ## The exact public trace law of the adaptive oracle -/

/-- Chronological traces generated by the stopping oracle.  Tests are long
exactly while the preceding public prefix is below the stopping line and
zero once that line has been crossed. -/
inductive LawfulTrace (n : ℕ) (u α : ℝ) : Transcript n → Prop
  | nil : LawfulTrace n u α []
  | testLong (transcript : Transcript n) (job : Label n)
      (hlawful : LawfulTrace n u α transcript)
      (hbelow : ¬ Crossed n u α transcript) :
      LawfulTrace n u α
        (transcript ++ [.testResult job u])
  | testZero (transcript : Transcript n) (job : Label n)
      (hlawful : LawfulTrace n u α transcript)
      (hcrossed : Crossed n u α transcript) :
      LawfulTrace n u α
        (transcript ++ [.testResult job 0])
  | processed (transcript : Transcript n) (job : Label n)
      (hlawful : LawfulTrace n u α transcript) :
      LawfulTrace n u α
        (transcript ++ [.processed job])
  | rawCompleted (transcript : Transcript n) (job : Label n)
      (hlawful : LawfulTrace n u α transcript) :
      LawfulTrace n u α
        (transcript ++ [.rawCompleted job])

theorem Transcript.mem_startedLabels_of_mem_testResults
    {transcript : Transcript n} {job : Label n} {p : ℝ}
    (hmem : (job, p) ∈ transcript.testResults) :
    job ∈ Transcript.startedLabels transcript := by
  induction transcript with
  | nil =>
      simp [Transcript.testResults] at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult testedJob q =>
          rw [Transcript.testResults_testResult_cons] at hmem
          simp only [List.mem_cons] at hmem
          rw [Transcript.startedLabels_testResult_cons]
          simp only [List.mem_cons]
          cases hmem with
          | inl hnew =>
              exact Or.inl (congrArg Prod.fst hnew)
          | inr hold =>
              exact Or.inr (ih hold)
      | processed processedJob =>
          rw [Transcript.testResults_processed_cons] at hmem
          rw [Transcript.startedLabels_processed_cons]
          exact ih hmem
      | rawCompleted rawJob =>
          rw [Transcript.testResults_rawCompleted_cons] at hmem
          rw [Transcript.startedLabels_rawCompleted_cons]
          simp only [List.mem_cons]
          exact Or.inr (ih hmem)

theorem assignment_eq_none_of_untouched
    {config : Config n} {assignment : PartialAssignment n}
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      SupportedByTranscript assignment config.transcript)
    {job : Label n} (hjob : config.jobs job = .untouched) :
    assignment job = none := by
  cases hassigned : assignment job with
  | none => rfl
  | some p =>
      have htest := hsupported job p hassigned
      exact
        (hstarted.untouched_not_mem job hjob
          (Transcript.mem_startedLabels_of_mem_testResults htest)).elim

theorem adaptiveStep_configStep
    {cap : Cap} {adversary : Oracle n}
    {config next : Config n}
    {assignment nextAssignment : PartialAssignment n}
    {action : Action n}
    (hstep :
      adaptiveStep cap adversary config assignment action =
        some (next, nextAssignment)) :
    config.step cap (adaptiveOracle adversary assignment) action =
      some next := by
  unfold adaptiveStep at hstep
  cases hbase :
      config.step cap (adaptiveOracle adversary assignment) action with
  | none =>
      simp [hbase] at hstep
  | some nextConfig =>
      rw [hbase] at hstep
      cases hstep
      rfl

theorem adaptiveStep_lawful
    {n : ℕ} {u α : ℝ}
    {config next : Config n}
    {assignment nextAssignment : PartialAssignment n}
    {action : Action n}
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      SupportedByTranscript assignment config.transcript)
    (hlawful : LawfulTrace n u α config.transcript)
    (hstep :
      adaptiveStep (.finite u) (oracle n u α)
        config assignment action = some (next, nextAssignment)) :
    LawfulTrace n u α next.transcript := by
  cases action with
  | test job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          have hnone :=
            assignment_eq_none_of_untouched
              hstarted hsupported hjob
          by_cases hcross : Crossed n u α config.transcript
          · have horacle :=
              oracle_eq_zero_of_crossed hcross job
            simp [adaptiveStep, Config.step, hjob,
              adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
            rcases hstep with ⟨hnext, hassignment⟩
            subst next
            exact LawfulTrace.testZero _ _ hlawful hcross
          · have horacle :=
              oracle_eq_long_of_not_crossed hcross job
            simp [adaptiveStep, Config.step, hjob,
              adaptiveOracle, adaptiveValue, hnone, horacle] at hstep
            rcases hstep with ⟨hnext, hassignment⟩
            subst next
            exact LawfulTrace.testLong _ _ hlawful hcross
  | process job =>
      cases hjob : config.jobs job with
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          exact LawfulTrace.processed _ _ hlawful
  | raw job =>
      cases hjob : config.jobs job with
      | tested p =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | done =>
          simp [adaptiveStep, Config.step, hjob] at hstep
      | untouched =>
          simp [adaptiveStep, Config.step, hjob] at hstep
          rcases hstep with ⟨hnext, hassignment⟩
          subst next
          exact LawfulTrace.rawCompleted _ _ hlawful

theorem runAdaptiveFuel_lawful
    (n : ℕ) (u α : ℝ) (strategy : Strategy n)
    (fuel : ℕ) (config : Config n)
    (assignment : PartialAssignment n)
    (hstarted : config.StartedHistoryInvariant)
    (hsupported :
      SupportedByTranscript assignment config.transcript)
    (hlawful : LawfulTrace n u α config.transcript) :
    LawfulTrace n u α
      (runAdaptiveFuel (.finite u) (oracle n u α) strategy
        fuel config assignment).result.config.transcript := by
  induction fuel generalizing config assignment with
  | zero =>
      simpa [runAdaptiveFuel] using hlawful
  | succ fuel ih =>
      cases haction : strategy config.transcript with
      | none =>
          simpa [runAdaptiveFuel, haction] using hlawful
      | some action =>
          cases hstep :
              adaptiveStep (.finite u) (oracle n u α)
                config assignment action with
          | none =>
              simpa [runAdaptiveFuel, haction, hstep] using hlawful
          | some pair =>
              rcases pair with ⟨next, nextAssignment⟩
              have hbase := adaptiveStep_configStep hstep
              have hstartedNext :=
                Config.startedHistoryInvariant_step hstarted hbase
              have hsupportedNext :=
                adaptiveStep_supportedByTranscript
                  (.finite u) (oracle n u α)
                  config next assignment nextAssignment action
                  hsupported hstep
              have hlawfulNext :=
                adaptiveStep_lawful hstarted hsupported hlawful hstep
              simpa [runAdaptiveFuel, haction, hstep] using
                ih next nextAssignment hstartedNext
                  hsupportedNext hlawfulNext

theorem adaptiveRun_lawful
    (n : ℕ) (u α : ℝ) (strategy : Strategy n) (fuel : ℕ) :
    LawfulTrace n u α
      (adaptiveRun (.finite u) (oracle n u α)
        strategy fuel).result.config.transcript := by
  apply runAdaptiveFuel_lawful n u α strategy fuel
    (Config.initial n) emptyAssignment
  · exact Config.initial_startedHistoryInvariant n
  · simp [SupportedByTranscript, Config.initial, emptyAssignment]
  · exact LawfulTrace.nil

end HiddenStoppingOracle

end

end SchedulingPaper
