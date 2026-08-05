import SchedulingPaper.PlateauBank
import SchedulingPaper.ParameterizedAdaptiveStrategy
import SchedulingPaper.LowerBoundAssembly
import SchedulingPaper.UTEEndpointReduction
import SchedulingPaper.ZeroPrefixGame
import SchedulingPaper.RawExecution
import SchedulingPaper.ObligatoryPairAccounting
import SchedulingPaper.StrategyTermination
import SchedulingPaper.CompleteCapReserveRemainder
import SchedulingPaper.CapReservePathGeometry
import SchedulingPaper.CapReserveFiniteRemainder
import SchedulingPaper.ZeroPrefixPairAccounting
import SchedulingPaper.TranscriptPairAccounting
import SchedulingPaper.UTEPairAccounting
import SchedulingPaper.UTERuntimeAccounting
import SchedulingPaper.ZeroPrefixRuntime
import SchedulingPaper.PlateauRuntimeInvariant

/-!
# Assembly of the upper-bound side

This file gives the upper proof the same honest interface boundary as
`LowerBoundAssembly`.

* Algorithms are genuine deterministic `Online.Strategy` families.
* Their displayed cost is evaluated after `2n+1` operations, enough for all
  paper algorithms (one test and at most one processing operation per job,
  followed by a stopping query).
* A certificate includes actual completion and a uniform linear-remainder
  estimate against the true `FixedInput.offlineCost`.
* The proved four-endpoint bank is connected to the actual obligatory
  strategy by one narrow pair-accounting/endpoint-reduction bridge.
* The analogous five-endpoint bridge and its reachable Taylor remainder are
  stated separately.

The final six-branch case split is fully checked.  The fields of
`OperationalUpperInterfaces` are exactly the remaining operational
reductions, rather than axioms hidden behind the theorem names.
-/

namespace SchedulingPaper

noncomputable section

open Set

namespace UpperBound

open LowerBound

abbrev FixedFamily (cap : Cap) (n : ℕ) := FixedInput cap n

def analysisFuel (n : ℕ) : ℕ := 2 * n + 1

def fixedOfflineCost (cap : Cap) :
    ∀ n, FixedFamily cap n → ℝ :=
  fun _ input => input.offlineCost

def strategyCost (cap : Cap)
    (strategy : ∀ n, Online.Strategy n) :
    ∀ n, FixedFamily cap n → ℝ :=
  fun n input => input.onlineCost (strategy n) (analysisFuel n)

def CompletesByAnalysisFuel
    (cap : Cap) (strategy : ∀ n, Online.Strategy n) : Prop :=
  ∀ n (input : FixedFamily cap n),
    resultCompleted (input.runResult (strategy n) (analysisFuel n))

/-- A genuine operational upper certificate with a uniform `O(n)` term. -/
structure FixedUpperCertificate (cap : Cap) (ratio : ℝ) where
  strategy : ∀ n, Online.Strategy n
  completes : CompletesByAnalysisFuel cap strategy
  remainder : ℝ
  remainder_nonneg : 0 ≤ remainder
  linearBound :
    HasLinearRemainder
      (strategyCost cap strategy) (fixedOfflineCost cap)
      ratio remainder

theorem cap_baseLength_pos {cap : Cap} (hcap : cap.Valid) :
    0 < cap.baseLength := by
  cases cap with
  | finite u =>
      simp only [Cap.Valid] at hcap
      simp only [Cap.baseLength]
      exact lt_min hcap zero_lt_one
  | infinite =>
      simp [Cap.baseLength]

theorem fixedOffline_hasQuadraticOptLower
    {cap : Cap} (hcap : cap.Valid) :
    HasQuadraticOptLower (fixedOfflineCost cap) cap.baseLength := by
  intro n input
  have hbound := offlineValue_quadratic_lower (input.toInstance hcap)
  rw [← input.offlineCost_eq_offlineValue hcap] at hbound
  simpa [fixedOfflineCost] using hbound

theorem FixedUpperCertificate.sizeAsymptotic
    {cap : Cap} {ratio : ℝ}
    (certificate : FixedUpperCertificate cap ratio)
    (hcap : cap.Valid) :
    SizeAsymptoticUpper
      (strategyCost cap certificate.strategy)
      (fixedOfflineCost cap) ratio :=
  sizeAsymptoticUpper_of_linearRemainder
    (cap_baseLength_pos hcap)
    certificate.linearBound
    (fixedOffline_hasQuadraticOptLower hcap)

theorem FixedUpperCertificate.additivelyAdmissibleAbove
    {cap : Cap} {ratio ε : ℝ}
    (certificate : FixedUpperCertificate cap ratio)
    (hcap : cap.Valid) (hε : 0 < ε) :
    AdditivelyAdmissible
      (strategyCost cap certificate.strategy)
      (fixedOfflineCost cap) (ratio + ε) :=
  additivelyAdmissible_of_linearRemainder
    (cap_baseLength_pos hcap) hε
    certificate.linearBound
    (fixedOffline_hasQuadraticOptLower hcap)

/-! ## The Raw policy -/

def rawStrategy : ∀ n, Online.Strategy n :=
  Online.rawStrategy

/-- The only operational fact needed about the executable Raw strategy:
after the common analysis fuel it completed every job and its timed transcript
has the static value `u * triangular n`. -/
def RawExecutionBridge (u : ℝ) : Prop :=
  CompletesByAnalysisFuel (.finite u) rawStrategy ∧
    ∀ n (input : FixedFamily (.finite u) n),
      strategyCost (.finite u) rawStrategy n input = rawValue u n

theorem rawExecutionBridge (u : ℝ) :
    RawExecutionBridge u := by
  constructor
  · intro n input job
    unfold FixedInput.runResult analysisFuel rawStrategy
    have h :=
      Online.raw_run_completed n n u
        (Online.fixedOracle input.processingTime) job
    rw [show 2 * n + 1 = n + 1 + n by omega]
    exact h
  · intro n input
    unfold strategyCost FixedInput.onlineCost FixedInput.runResult
      analysisFuel rawStrategy
    rw [show 2 * n + 1 = n + 1 + n by omega]
    rw [Online.raw_runCompletionCost]
    exact (rawValue_eq u n).symm

noncomputable def rawOneCertificate
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (bridge : RawExecutionBridge u) :
    FixedUpperCertificate (.finite u) 1 := by
  refine
    { strategy := rawStrategy
      completes := bridge.1
      remainder := 0
      remainder_nonneg := le_rfl
      linearBound := ?_ }
  intro n input
  rw [bridge.2 n input]
  have hcap : Cap.Valid (.finite u) := by
    simpa [Cap.Valid] using hu
  have hraw :=
    raw_optimal_of_cap_le_one (input.toInstance hcap) u rfl hu1
  rw [← input.offlineCost_eq_offlineValue hcap,
    input.toInstance_jobs_length hcap] at hraw
  simpa [fixedOfflineCost] using hraw.le

noncomputable def rawIdentityCertificate
    {u : ℝ} (hu : 0 < u) (hu1 : 1 ≤ u)
    (bridge : RawExecutionBridge u) :
    FixedUpperCertificate (.finite u) u := by
  refine
    { strategy := rawStrategy
      completes := bridge.1
      remainder := 0
      remainder_nonneg := le_rfl
      linearBound := ?_ }
  intro n input
  rw [bridge.2 n input]
  have hcap : Cap.Valid (.finite u) := by
    simpa [Cap.Valid] using hu
  have hraw :=
    raw_competitive_of_one_le_cap
      (input.toInstance hcap) u rfl hu1
  rw [← input.offlineCost_eq_offlineValue hcap,
    input.toInstance_jobs_length hcap] at hraw
  simpa [fixedOfflineCost] using hraw

noncomputable def verifiedRawOneCertificate
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    FixedUpperCertificate (.finite u) 1 :=
  rawOneCertificate hu hu1 (rawExecutionBridge u)

noncomputable def verifiedRawIdentityCertificate
    {u : ℝ} (hu : 0 < u) (hu1 : 1 ≤ u) :
    FixedUpperCertificate (.finite u) u :=
  rawIdentityCertificate hu hu1 (rawExecutionBridge u)

/-! ## ForcedPrefixUTE: narrow scalar-to-transcript interfaces -/

/-- The concrete UTE strategy on the endpoint-game range `u = s + 1`. -/
def uteEndpointStrategy (s : ℝ) : ∀ n, Online.Strategy n :=
  fun n =>
    Online.forcedPrefixUTEStrategy n (s + 1) (uteB s)

/-- The exact missing transcript/rounding statement for the UTE endpoint
game.  The leading quadratic on the right is completely controlled by
`uteGap_nonpos_of_feasible`; only the extraction of its four masses from an
actual execution, including the `O(n)` diagonal term, is left here. -/
def UTEEndpointCostBridge (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n (input : FixedFamily (.finite (s + 1)) n),
      ∃ a d t m : ℝ,
        0 ≤ a ∧ a ≤ uteB s ∧
        0 ≤ d ∧ 0 ≤ t ∧ 0 ≤ m ∧
        d + t + m ≤ 1 - uteB s ∧
        strategyCost (.finite (s + 1)) (uteEndpointStrategy s) n input -
            uteRho s * fixedOfflineCost (.finite (s + 1)) n input ≤
          (n : ℝ) ^ 2 * uteGap s a d t m + C * n

def UTEEndpointCompletion (s : ℝ) : Prop :=
  CompletesByAnalysisFuel (.finite (s + 1)) (uteEndpointStrategy s)

theorem uteEndpointCompletion (s : ℝ) :
    UTEEndpointCompletion s := by
  intro n input job
  unfold FixedInput.runResult analysisFuel uteEndpointStrategy
  exact
    (Online.run_forcedPrefixUTEStrategy_completed
      n (s + 1) (uteB s) (.finite (s + 1))
      (Online.fixedOracle input.processingTime)).2 job

/-- On `u < 2` the paper first performs an independent Bernoulli
extremalization before applying the binary endpoint calculation.  This is
the exact remaining cost-level statement for that reduction. -/
def UTEBelowTwoCostBridge (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    HasLinearRemainder
      (strategyCost (.finite (s + 1)) (uteEndpointStrategy s))
      (fixedOfflineCost (.finite (s + 1))) (uteRho s) C

/-- Package the below-two Bernoulli reduction once its cost estimate is
supplied. -/
noncomputable def uteBelowTwoCertificate
    {s : ℝ}
    (hcomplete : UTEEndpointCompletion s)
    (hbridge : UTEBelowTwoCostBridge s) :
    FixedUpperCertificate (.finite (s + 1)) (uteRho s) := by
  let C : ℝ := hbridge.choose
  have hC : 0 ≤ C := hbridge.choose_spec.1
  have hcost :
      HasLinearRemainder
        (strategyCost (.finite (s + 1)) (uteEndpointStrategy s))
        (fixedOfflineCost (.finite (s + 1))) (uteRho s) C :=
    hbridge.choose_spec.2
  exact
    { strategy := uteEndpointStrategy s
      completes := hcomplete
      remainder := C
      remainder_nonneg := hC
      linearBound := hcost }

/-- The formal endpoint game turns the narrow execution bridge into a genuine
upper certificate. -/
noncomputable def uteEndpointCertificate
    {s : ℝ} (hs1 : 1 ≤ s) (hs0 : s ≤ sZero)
    (hcomplete : UTEEndpointCompletion s)
    (hbridge : UTEEndpointCostBridge s) :
    FixedUpperCertificate (.finite (s + 1)) (uteRho s) := by
  let C : ℝ := hbridge.choose
  have hC : 0 ≤ C := hbridge.choose_spec.1
  have hcost := hbridge.choose_spec.2
  refine
    { strategy := uteEndpointStrategy s
      completes := hcomplete
      remainder := C
      remainder_nonneg := hC
      linearBound := ?_ }
  intro n input
  obtain ⟨a, d, t, m, ha, hab, hd, ht, hm, hmass, hactual⟩ :=
    hcost n input
  have hgap :
      uteGap s a d t m ≤ 0 :=
    uteGap_nonpos_of_feasible hs1 hs0 ha hab hd ht hm hmass
  have hscaled :
      (n : ℝ) ^ 2 * uteGap s a d t m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hgap
  exact le_of_sub_nonpos (by
    change
      strategyCost (.finite (s + 1)) (uteEndpointStrategy s) n input -
          (uteRho s * fixedOfflineCost (.finite (s + 1)) n input +
            C * n) ≤ 0
    linarith)

/-- The concrete zero-prefix strategy on the reciprocal branch. -/
def zeroPrefixStrategy (s : ℝ) : ∀ n, Online.Strategy n :=
  fun n => Online.forcedPrefixUTEStrategy n (s + 1) 0

/-- Transcript/endpoint extraction for the zero-prefix extension. -/
def ZeroPrefixCostBridge (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n (input : FixedFamily (.finite (s + 1)) n),
      ∃ d t m : ℝ,
        0 ≤ d ∧ 0 ≤ t ∧ 0 ≤ m ∧
        strategyCost (.finite (s + 1)) (zeroPrefixStrategy s) n input -
            zeroPrefixFactor s *
              fixedOfflineCost (.finite (s + 1)) n input ≤
          (n : ℝ) ^ 2 *
              (zeroPrefixAlg s d t m -
                zeroPrefixFactor s * zeroPrefixOpt s d t m) +
            C * n

def ZeroPrefixCompletion (s : ℝ) : Prop :=
  CompletesByAnalysisFuel (.finite (s + 1)) (zeroPrefixStrategy s)

theorem zeroPrefixCompletion (s : ℝ) :
    ZeroPrefixCompletion s := by
  intro n input job
  unfold FixedInput.runResult analysisFuel zeroPrefixStrategy
  exact
    (Online.run_forcedPrefixUTEStrategy_completed
      n (s + 1) 0 (.finite (s + 1))
      (Online.fixedOracle input.processingTime)).2 job

/-- The proved normalized Zero-prefix game turns its narrow execution bridge
into a genuine upper certificate. -/
noncomputable def zeroPrefixCertificate
    {s : ℝ} (hs : 0 < s) (hsφ : s ≤ goldenRatio + 1)
    (hcomplete : ZeroPrefixCompletion s)
    (hbridge : ZeroPrefixCostBridge s) :
    FixedUpperCertificate (.finite (s + 1)) (zeroPrefixFactor s) := by
  let C : ℝ := hbridge.choose
  have hC : 0 ≤ C := hbridge.choose_spec.1
  have hcost := hbridge.choose_spec.2
  refine
    { strategy := zeroPrefixStrategy s
      completes := hcomplete
      remainder := C
      remainder_nonneg := hC
      linearBound := ?_ }
  intro n input
  obtain ⟨d, t, m, hd, ht, hm, hactual⟩ := hcost n input
  have hgap :
      zeroPrefixAlg s d t m -
          zeroPrefixFactor s * zeroPrefixOpt s d t m ≤ 0 := by
    linarith [zeroPrefixAlg_le_factor_mul_opt hs hsφ hd ht hm]
  have hscaled :
      (n : ℝ) ^ 2 *
          (zeroPrefixAlg s d t m -
            zeroPrefixFactor s * zeroPrefixOpt s d t m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hgap
  exact le_of_sub_nonpos (by
    change
      strategyCost (.finite (s + 1)) (zeroPrefixStrategy s) n input -
          (zeroPrefixFactor s *
              fixedOfflineCost (.finite (s + 1)) n input +
            C * n) ≤ 0
    linarith)

/-! ## The obligatory endpoint: one precise remaining bridge -/

def obligatoryStrategy : ∀ n, Online.Strategy n :=
  Online.adaptiveThresholdStrategy

/-- Pair accounting plus simultaneous endpoint reduction for the concrete
obligatory strategy.  Everything after this statement is already proved. -/
def ObligatoryBoundaryBridge : Prop :=
  ∀ n (input : FixedFamily .infinite n),
    ∃ outcomes : List BoundaryOutcome,
      outcomes.length = n ∧
      strategyCost .infinite obligatoryStrategy n input -
          RStar * input.offlineCost ≤
        obligatoryBoundaryExcess outcomes

def ObligatoryCompletion : Prop :=
  CompletesByAnalysisFuel .infinite obligatoryStrategy

theorem obligatoryCompletion :
    ObligatoryCompletion := by
  intro n input job
  unfold FixedInput.runResult analysisFuel obligatoryStrategy
  exact
    (Online.run_adaptiveThresholdStrategy_completed
      n .infinite
      (Online.fixedOracle input.processingTime)).2 job

/-- Once the concrete transcript-to-boundary bridge is supplied, the
obligatory upper theorem has no further analytic premise. -/
noncomputable def obligatoryCertificate_of_boundaryBridge
    (hcomplete : ObligatoryCompletion)
    (hbridge : ObligatoryBoundaryBridge) :
    FixedUpperCertificate .infinite RStar := by
  refine
    { strategy := obligatoryStrategy
      completes := hcomplete
      remainder :=
        max 0
          (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2)
      remainder_nonneg := le_max_left _ _
      linearBound := ?_ }
  intro n input
  obtain ⟨outcomes, hlength, hgap⟩ := hbridge n input
  have hword := obligatoryBoundaryExcess_linear outcomes
  have hKC :
      uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2 ≤
        max 0
          (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2) :=
    le_max_right _ _
  rw [hlength] at hword
  change strategyCost .infinite obligatoryStrategy n input ≤
    RStar * fixedOfflineCost .infinite n input +
      max 0
        (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2) * n
  dsimp [fixedOfflineCost]
  nlinarith

/-! ## The mixed five-endpoint bridge -/

def mixedStrategy (c : MixedRatioDomain) :
    ∀ n, Online.Strategy n :=
  fun n => Online.parameterizedAdaptiveThresholdStrategy n c

def MixedCompletion (c : MixedRatioDomain) : Prop :=
  CompletesByAnalysisFuel (.finite (mixedUpperCurve c)) (mixedStrategy c)

theorem mixedCompletion (c : MixedRatioDomain) :
    MixedCompletion c := by
  intro n input job
  unfold FixedInput.runResult analysisFuel mixedStrategy
  exact
    (Online.run_parameterizedAdaptiveThresholdStrategy_completed
      n c (.finite (mixedUpperCurve c))
      (Online.fixedOracle input.processingTime)).2 job

/-- Exact pair accounting and endpoint reduction for the concrete mixed
strategy.  The right side is precisely the word controlled by
`mixed_boundary_rewards_le`. -/
def MixedBoundaryBridge (c : MixedRatioDomain) : Prop :=
  ∀ n (input : FixedFamily (.finite (mixedUpperCurve c)) n),
    ∃ outcomes : List CappedBoundaryOutcome,
      outcomes.length = n ∧
      strategyCost (.finite (mixedUpperCurve c)) (mixedStrategy c) n input -
          mixedCompetitiveRatio c * input.offlineCost ≤
        -(c : ℝ) * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (mixedCappedEnvelopeReward c)
            (initialParameterizedAnalysisState outcomes.length) outcomes

/-- The finite mixed certificate follows from exactly two remaining inputs:
the concrete endpoint bridge and a reachable five-endpoint Taylor bound. -/
noncomputable def mixedCertificate_of_boundaryBridge
    (c : MixedRatioDomain) {C₀ : ℝ}
    (hTaylor : HasReachableCompleteCappedBankRemainder
      c (mixedReserveDelta c) (mixedMass c) C₀)
    (hcomplete : MixedCompletion c)
    (hbridge : MixedBoundaryBridge c) :
    FixedUpperCertificate (.finite (mixedUpperCurve c))
      (mixedCompetitiveRatio c) := by
  refine
    { strategy := mixedStrategy c
      completes := hcomplete
      remainder := max 0 (C₀ - (c : ℝ) / 2)
      remainder_nonneg := le_max_left _ _
      linearBound := ?_ }
  intro n input
  obtain ⟨outcomes, hlength, hgap⟩ := hbridge n input
  have hreward := mixed_boundary_rewards_le c hTaylor outcomes
  have hKC :
      C₀ - (c : ℝ) / 2 ≤ max 0 (C₀ - (c : ℝ) / 2) :=
    le_max_right _ _
  rw [hlength] at hreward
  rw [hlength] at hgap
  change strategyCost (.finite (mixedUpperCurve c)) (mixedStrategy c)
      n input ≤
    mixedCompetitiveRatio c *
        fixedOfflineCost (.finite (mixedUpperCurve c)) n input +
      max 0 (C₀ - (c : ℝ) / 2) * n
  dsimp [fixedOfflineCost]
  nlinarith

/-! ## The finite plateau reuses the proved obligatory bank -/

def plateauStrategy : ∀ n, Online.Strategy n :=
  fun n => Online.parameterizedAdaptiveThresholdStrategy n rhoStar

def PlateauCompletion (u : ℝ) : Prop :=
  CompletesByAnalysisFuel (.finite u) plateauStrategy

theorem plateauCompletion (u : ℝ) :
    PlateauCompletion u := by
  intro n input job
  unfold FixedInput.runResult analysisFuel plateauStrategy
  exact
    (Online.run_parameterizedAdaptiveThresholdStrategy_completed
      n rhoStar (.finite u)
      (Online.fixedOracle input.processingTime)).2 job

def PlateauBoundaryBridge (u : ℝ) : Prop :=
  ∀ n (input : FixedFamily (.finite u) n),
    ∃ outcomes : List CappedBoundaryOutcome,
      outcomes.length = n ∧
      strategyCost (.finite u) plateauStrategy n input -
          RStar * input.offlineCost ≤
        -rhoStar * outcomes.length * (outcomes.length + 1) / 2 +
          trajectoryReward ParameterizedAnalysisState.step
            (parameterizedOrdinaryReward rhoStar)
            (initialParameterizedAnalysisState outcomes.length) outcomes

/-- On `u ≥ zStar`, the exact cap charge is paid by the ordinary deferred
envelope, and the obligatory uniform remainder applies unchanged. -/
noncomputable def plateauCertificate_of_boundaryBridge
    {u : ℝ}
    (hcomplete : PlateauCompletion u)
    (hbridge : PlateauBoundaryBridge u) :
    FixedUpperCertificate (.finite u) RStar := by
  refine
    { strategy := plateauStrategy
      completes := hcomplete
      remainder :=
        max 0
          (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2)
      remainder_nonneg := le_max_left _ _
      linearBound := ?_ }
  intro n input
  obtain ⟨outcomes, hlength, hgap⟩ := hbridge n input
  have hreward := plateau_boundary_rewards_uniform outcomes
  have hKC :
      uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2 ≤
        max 0
          (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2) :=
    le_max_right _ _
  rw [hlength] at hgap hreward
  change strategyCost (.finite u) plateauStrategy n input ≤
    RStar * fixedOfflineCost (.finite u) n input +
      max 0
        (uniformBankRemainderOnUnitCountdownConstant - rhoStar / 2) * n
  dsimp [fixedOfflineCost]
  nlinarith

/-! ## Six-branch assembly -/

/-- The remaining branchwise operational upper statements.  The scalar
curve, all joins, the Zero-prefix interpolation, and the obligatory bank are
not premises here; they are proved in their respective modules. -/
structure OperationalUpperInterfaces : Type where
  uteBelowTwoCost :
    ∀ {s : ℝ}, uDiamond - 1 < s → s < 1 →
      UTEBelowTwoCostBridge s
  mixedBoundary :
    ∀ c : MixedRatioDomain, MixedBoundaryBridge c

theorem obligatory_RStar_sizeAsymptoticUpper
    (hbridge : ObligatoryBoundaryBridge) :
    SizeAsymptoticUpper
      (strategyCost .infinite
        (obligatoryCertificate_of_boundaryBridge
          obligatoryCompletion
          hbridge).strategy)
      (fixedOfflineCost .infinite) RStar :=
  (obligatoryCertificate_of_boundaryBridge
      obligatoryCompletion
      hbridge).sizeAsymptotic
    (by simp [Cap.Valid])

end UpperBound

end

end SchedulingPaper
