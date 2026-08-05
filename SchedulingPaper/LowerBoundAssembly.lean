import SchedulingPaper.ExactCurve
import SchedulingPaper.HarmonicCore
import SchedulingPaper.HarmonicLimit
import SchedulingPaper.HiddenStoppingOracle

/-!
# Assembly of the lower-bound side

This file separates the part of the paper's lower bound that is already
formal from the remaining operational adversaries.

* `FixedInput` and `FixedSizeLowerBound` state the lower bound for genuine
  fixed processing-time vectors.
* `AdaptiveSizeLowerBound` states the corresponding finite revelation game.
* `fixedSizeLowerBound_of_adaptive` is an unconditional replay theorem:
  every adaptive certificate produces a fixed admissible instance with the
  same transcript and completion cost.
* `BinaryStoppingCertificate` packages the scalar premise of the raw-safe
  hidden-stopping lemma.  The certificates for the identity, algebraic, and
  reciprocal branches are proved below from `BinaryCurve` and
  `AlgebraicBranch`.
* `HiddenStoppingOracle` supplies the explicit legal binary adversary,
  crossing/overshoot invariant, binary freezing, and timed replay.  The only
  binary premise left in `OperationalLowerInterfaces` is its transcript
  exchange estimate with a uniform linear remainder.
* The other remaining interfaces are the baseline transcript-to-OPT bridge,
  mixed quota construction, bounded cap-free transfer, and harmonic
  revelation construction.  Assuming these statements,
  `finite_exactCurve_lower` and `obligatory_RStar_lower` assemble the paper's
  principal lower bounds.

There are no axioms in this file: the unformalized operational content is an
explicit theorem parameter.
-/

namespace SchedulingPaper

noncomputable section

open Set

namespace LowerBound

/-! ## Genuine fixed instances and their costs -/

/-- A labelled fixed input for the operational online model. -/
structure FixedInput (cap : Cap) (n : ℕ) where
  processingTime : Online.Label n → ℝ
  admissible : ∀ job, Online.ValueAdmissible cap (processingTime job)

/-- The clairvoyant effective lengths of a labelled processing-time vector. -/
def vectorEffectiveLengths
    (cap : Cap) (processingTime : Online.Label n → ℝ) : List ℝ :=
  List.ofFn fun job => effectiveLength cap (processingTime job)

/-- The true offline optimum of a labelled processing-time vector. -/
def vectorOfflineCost
    (cap : Cap) (processingTime : Online.Label n → ℝ) : ℝ :=
  prefixCost (shortestFirst (vectorEffectiveLengths cap processingTime))

def FixedInput.offlineCost (I : FixedInput cap n) : ℝ :=
  vectorOfflineCost cap I.processingTime

private theorem admissible_processingTime_nonneg
    {cap : Cap} {p : ℝ} (hp : Online.ValueAdmissible cap p) :
    0 ≤ p := by
  cases cap with
  | finite u => exact hp.1
  | infinite => exact hp

/-- Forget labels and view the same processing vector as the paper's static
`Instance` structure. -/
def FixedInput.toInstance
    (I : FixedInput cap n) (hcap : cap.Valid) : Instance where
  cap := cap
  cap_valid := hcap
  jobs :=
    List.ofFn fun job =>
      { processingTime := I.processingTime job
        processingTime_nonneg :=
          admissible_processingTime_nonneg (I.admissible job) }
  processingTime_le_cap := by
    intro job hjob u hcapEq
    rcases List.mem_ofFn.mp hjob with ⟨label, rfl⟩
    cases cap with
    | finite v =>
        cases hcapEq
        exact (I.admissible label).2
    | infinite =>
        cases hcapEq

@[simp] theorem FixedInput.toInstance_jobs_length
    (I : FixedInput cap n) (hcap : cap.Valid) :
    (I.toInstance hcap).jobs.length = n := by
  simp [FixedInput.toInstance]

/-- `vectorOfflineCost` is definitionally the unified clairvoyant optimum of
the corresponding genuine static instance. -/
theorem FixedInput.offlineCost_eq_offlineValue
    (I : FixedInput cap n) (hcap : cap.Valid) :
    I.offlineCost = offlineValue (I.toInstance hcap) := by
  unfold FixedInput.offlineCost vectorOfflineCost offlineValue
  congr 2
  unfold vectorEffectiveLengths Instance.effectiveLengths
  simp only [FixedInput.toInstance, List.map_ofFn]
  apply congrArg (fun f : Fin n → ℝ => List.ofFn f)
  funext job
  rfl

/-- For `u ≥ 1`, every effective job length is at least one, so every
labelled fixed input has the obligatory quadratic offline lower bound. -/
theorem FixedInput.offlineCost_quadratic_lower_one
    {u : ℝ} (I : FixedInput (.finite u) n) (hu : 1 ≤ u) :
    triangular n ≤ I.offlineCost := by
  have hcap : Cap.Valid (.finite u) := by
    simp [Cap.Valid]
    linarith
  have hbound :=
    finite_offlineValue_quadratic_lower (I.toInstance hcap) u rfl
  rw [← I.offlineCost_eq_offlineValue hcap] at hbound
  simpa [min_eq_right hu] using hbound

def FixedInput.runResult
    (I : FixedInput cap n) (strategy : Online.Strategy n) (fuel : ℕ) :
    Online.RunResult n :=
  Online.run cap (Online.fixedOracle I.processingTime) strategy fuel

def FixedInput.onlineCost
    (I : FixedInput cap n) (strategy : Online.Strategy n) (fuel : ℕ) : ℝ :=
  Online.runCompletionCost cap I.processingTime (I.runResult strategy fuel)

/-- All jobs have completed in this finite result. -/
def resultCompleted (result : Online.RunResult n) : Prop :=
  ∀ job, result.config.jobs job = .done

/-- Fuel exhaustion is not a semantic stopping condition.  Strategy stop and
an invalid next action are terminal; either is a loss if jobs remain. -/
def resultSettled (result : Online.RunResult n) : Prop :=
  result.reason ≠ .outOfFuel

/-- A settled incomplete run represents infinite cost, as in the paper.
Otherwise the displayed finite competitive inequality must hold. -/
def FixedInput.defeats
    (I : FixedInput cap n) (strategy : Online.Strategy n)
    (fuel : ℕ) (ratio : ℝ) : Prop :=
  resultSettled (I.runResult strategy fuel) ∧
    (¬ resultCompleted (I.runResult strategy fuel) ∨
      ratio * I.offlineCost ≤ I.onlineCost strategy fuel)

/-- "Arbitrarily large fixed instances" in epsilon form, uniformly against
an arbitrary size-indexed deterministic strategy. -/
def FixedSizeLowerBound (cap : Cap) (ratio : ℝ) : Prop :=
  ∀ strategies : ∀ n, Online.Strategy n,
    ∀ ε, 0 < ε → ∀ N,
      ∃ n, N ≤ n ∧
        ∃ I : FixedInput cap n, ∃ fuel,
          I.defeats (strategies n) fuel (ratio - ε)

/-! ## Adaptive revelation and unconditional replay -/

/-- The fixed vector obtained by freezing a finite adaptive revelation. -/
def frozenInput
    (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) (default : Online.Label n → ℝ)
    (fuel : ℕ)
    (hadversary : adversary.Admissible cap)
    (hdefault : ∀ job, Online.ValueAdmissible cap (default job)) :
    FixedInput cap n where
  processingTime :=
    Online.frozenProcessingTimes cap adversary strategy default fuel
  admissible :=
    Online.frozenProcessingTimes_admissible cap adversary strategy default fuel
      hadversary hdefault

/-- The adaptive analogue of `FixedInput.defeats`.  Its benchmark is already
the offline optimum of the frozen vector, so replay has no hidden benchmark
conversion step. -/
def adaptiveDefeats
    (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) (default : Online.Label n → ℝ)
    (fuel : ℕ) (ratio : ℝ) : Prop :=
  let frozen :=
    Online.frozenProcessingTimes cap adversary strategy default fuel
  let result := (Online.adaptiveRun cap adversary strategy fuel).result
  resultSettled result ∧
    (¬ resultCompleted result ∨
      ratio * vectorOfflineCost cap frozen ≤
        Online.runCompletionCost cap frozen result)

/-- Finite accounting form of an adaptive defeat, allowing one uniform
linear remainder.  This is the natural output of the paper's exact canonical
schedule calculation before taking the size-asymptotic limit. -/
def adaptiveDefeatsWithLinearRemainder
    (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) (default : Online.Label n → ℝ)
    (fuel : ℕ) (ratio remainder : ℝ) : Prop :=
  let frozen :=
    Online.frozenProcessingTimes cap adversary strategy default fuel
  let result := (Online.adaptiveRun cap adversary strategy fuel).result
  resultSettled result ∧
    (¬ resultCompleted result ∨
      ratio * vectorOfflineCost cap frozen ≤
        Online.runCompletionCost cap frozen result + remainder * n)

/-- Operational lower bound before freezing the revelation experiment. -/
def AdaptiveSizeLowerBound (cap : Cap) (ratio : ℝ) : Prop :=
  ∀ strategies : ∀ n, Online.Strategy n,
    ∀ ε, 0 < ε → ∀ N,
      ∃ n, N ≤ n ∧
        ∃ adversary : Online.Oracle n,
          ∃ default : Online.Label n → ℝ, ∃ fuel,
            adversary.Admissible cap ∧
            (∀ job, Online.ValueAdmissible cap (default job)) ∧
            adaptiveDefeats cap adversary (strategies n) default fuel
              (ratio - ε)

/-- Cost-level form of timed replay on the bundled fixed input. -/
theorem frozenInput_onlineCost_eq_adaptive
    (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) (default : Online.Label n → ℝ)
    (fuel : ℕ)
    (hadversary : adversary.Admissible cap)
    (hdefault : ∀ job, Online.ValueAdmissible cap (default job)) :
    (frozenInput cap adversary strategy default fuel
        hadversary hdefault).onlineCost strategy fuel =
      Online.runCompletionCost cap
        (Online.frozenProcessingTimes cap adversary strategy default fuel)
        (Online.adaptiveRun cap adversary strategy fuel).result := by
  simpa [FixedInput.onlineCost, FixedInput.runResult, frozenInput] using
    Online.replay_preserves_completionCost
      cap adversary strategy default fuel

/-- Replay preserves the complete lower-bound disjunction, including
settledness, completion, the offline benchmark, and total completion cost. -/
theorem frozenInput_defeats_of_adaptive
    (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) (default : Online.Label n → ℝ)
    (fuel : ℕ) (ratio : ℝ)
    (hadversary : adversary.Admissible cap)
    (hdefault : ∀ job, Online.ValueAdmissible cap (default job))
    (hdefeat :
      adaptiveDefeats cap adversary strategy default fuel ratio) :
    (frozenInput cap adversary strategy default fuel hadversary hdefault).defeats
      strategy fuel ratio := by
  simpa [adaptiveDefeats, FixedInput.defeats, FixedInput.runResult,
    FixedInput.onlineCost, FixedInput.offlineCost, frozenInput,
    Online.replay cap adversary strategy default fuel] using hdefeat

/-- The formal adaptive-to-fixed-instance bridge used by every adversary in
the paper. -/
theorem fixedSizeLowerBound_of_adaptive
    {cap : Cap} {ratio : ℝ}
    (h : AdaptiveSizeLowerBound cap ratio) :
    FixedSizeLowerBound cap ratio := by
  intro strategies ε hε N
  obtain ⟨n, hn, adversary, default, fuel, hadversary, hdefault, hdefeat⟩ :=
    h strategies ε hε N
  refine ⟨n, hn,
    frozenInput cap adversary (strategies n) default fuel
      hadversary hdefault, fuel, ?_⟩
  exact frozenInput_defeats_of_adaptive
    cap adversary (strategies n) default fuel (ratio - ε)
      hadversary hdefault hdefeat

/-! ## Scalar binary stopping certificates -/

/-- The exact scalar premise needed by raw-safe hidden stopping.  Since
`stoppingMinimizer` minimizes over every `b ≥ 0` and lies below `alpha`,
the final field certifies the paper's minimum over `0 ≤ b ≤ alpha`. -/
structure BinaryStoppingCertificate (u ratio : ℝ) where
  alpha : ℝ
  ratio_nonneg : 0 ≤ ratio
  ratio_le_cap : ratio ≤ u
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  minimized_nonneg :
    0 ≤ stoppingF u ratio alpha (stoppingMinimizer u alpha)

/-- The maximizing point of the positive-completion quadratic. -/
def positiveTangentAlpha (u ratio : ℝ) : ℝ :=
  stoppingA u / stoppingD u ratio

/-- A nonnegative positive-branch tangency expression yields a complete
binary stopping certificate once the tangent point is in that branch. -/
noncomputable def positiveBranchCertificate
    {u ratio : ℝ} (hu : 1 < u) (hratio : 0 < ratio)
    (hratioCap : ratio ≤ u)
    (htangent : 0 ≤ stoppingTangency u ratio)
    (hbranch :
      0 ≤ u * positiveTangentAlpha u ratio - (u - 1)) :
    BinaryStoppingCertificate u ratio := by
  have hA : 0 < stoppingA u := by
    unfold stoppingA
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hD : 0 < stoppingD u ratio :=
    stoppingD_pos hu hratio
  have hprod : 0 < (u - 1) * ratio :=
    mul_pos (sub_pos.mpr hu) hratio
  have halphaPos : 0 < positiveTangentAlpha u ratio :=
    div_pos hA hD
  have halphaLt : positiveTangentAlpha u ratio < 1 := by
    unfold positiveTangentAlpha
    rw [div_lt_one hD]
    unfold stoppingD
    linarith
  have hmin :
      stoppingMinimizer u (positiveTangentAlpha u ratio) =
        u * positiveTangentAlpha u ratio - (u - 1) := by
    exact max_eq_right hbranch
  have hzero :
      stoppingD u ratio * positiveTangentAlpha u ratio -
          stoppingA u = 0 := by
    unfold positiveTangentAlpha
    field_simp [hD.ne']
    ring
  have hidentity :=
    positiveStoppingEnvelope_completeSquare
      u ratio (positiveTangentAlpha u ratio)
  rw [show
      (1 - ratio - (u - 1) ^ 2) * stoppingD u ratio +
          stoppingA u ^ 2 =
        stoppingTangency u ratio by rfl, hzero] at hidentity
  norm_num at hidentity
  have henvelope :
      0 ≤ positiveStoppingEnvelope u ratio
        (positiveTangentAlpha u ratio) := by
    by_contra hneg
    have hstrict :
        positiveStoppingEnvelope u ratio
            (positiveTangentAlpha u ratio) < 0 :=
      lt_of_not_ge hneg
    have hmul :
        stoppingD u ratio *
            positiveStoppingEnvelope u ratio
              (positiveTangentAlpha u ratio) < 0 :=
      mul_neg_of_pos_of_neg hD hstrict
    rw [hidentity] at hmul
    exact (not_lt_of_ge htangent) hmul
  refine
    { alpha := positiveTangentAlpha u ratio
      ratio_nonneg := hratio.le
      ratio_le_cap := hratioCap
      alpha_pos := halphaPos
      alpha_lt_one := halphaLt
      minimized_nonneg := ?_ }
  rw [hmin, stoppingF_positive_branch]
  exact henvelope

/-- On the identity branch the positive quadratic has nonnegative maximum. -/
theorem identity_stoppingTangency_nonneg
    {u : ℝ} (hu : 1 < u) (huD : u ≤ uDiamond) :
    0 ≤ stoppingTangency u u := by
  let x := u * (u - 1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (by linarith) (by linarith)
  have hfactorNonneg :
      0 ≤ (uDiamond - u) * (uDiamond + u - 1) := by
    exact mul_nonneg (sub_nonneg.mpr huD)
      (by linarith [uDiamond_gt_one])
  have hxleRaw :
      x ≤ uDiamond * (uDiamond - 1) := by
    dsimp [x]
    nlinarith [hfactorNonneg]
  have hxle : x ≤ goldenRatio := by
    simpa [uDiamond_mul_sub_one] using hxleRaw
  have hsecond : 0 ≤ x + goldenRatio - 1 := by
    linarith [goldenRatio_gt_one]
  have hfactor :
      x ^ 2 - x - 1 =
        (x - goldenRatio) * (x + goldenRatio - 1) := by
    calc
      x ^ 2 - x - 1 =
          x ^ 2 - x - (goldenRatio ^ 2 - goldenRatio) := by
            rw [goldenRatio_sq]
            ring
      _ = (x - goldenRatio) * (x + goldenRatio - 1) := by ring
  have hpoly : x ^ 2 - x - 1 ≤ 0 := by
    rw [hfactor]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxle) hsecond
  rw [stoppingTangency_at_ratio_u]
  dsimp [x] at hpoly
  linarith

/-- The maximizing point remains in the positive-completion branch throughout
`1 < u ≤ uDiamond`. -/
theorem identity_positive_branch_condition
    {u : ℝ} (hu : 1 < u) (huD : u ≤ uDiamond) :
    0 ≤ u * positiveTangentAlpha u u - (u - 1) := by
  have hu2 : u < 2 := huD.trans_lt uDiamond_lt_two
  have hu0 : 0 < u := by linarith
  have hD : 0 < stoppingD u u := stoppingD_pos hu hu0
  have hproduct : 0 ≤ u * (u - 1) * (2 - u) :=
    mul_nonneg
      (mul_nonneg (by linarith) (by linarith))
      (by linarith)
  have hnum :
      0 ≤ u * stoppingA u - (u - 1) * stoppingD u u := by
    have hid :
        u * stoppingA u - (u - 1) * stoppingD u u =
          1 + u * (u - 1) * (2 - u) := by
      simp only [stoppingD, stoppingA]
      ring
    rw [hid]
    positivity
  calc
    0 ≤
        (u * stoppingA u - (u - 1) * stoppingD u u) /
          stoppingD u u :=
      div_nonneg hnum hD.le
    _ = u * positiveTangentAlpha u u - (u - 1) := by
      unfold positiveTangentAlpha
      field_simp [hD.ne']

/-- Scalar certificate for the `ratio = u` lower branch. -/
noncomputable def identityStoppingCertificate
    {u : ℝ} (hu : 1 < u) (huD : u ≤ uDiamond) :
    BinaryStoppingCertificate u u :=
  positiveBranchCertificate hu (by linarith) le_rfl
    (identity_stoppingTangency_nonneg hu huD)
    (identity_positive_branch_condition hu huD)

/-- Below `sZero`, the transition polynomial has not yet crossed zero. -/
theorem sZeroPolynomial_nonpos_of_pos_le
    {s : ℝ} (hs : 0 < s) (hs0 : s ≤ sZero) :
    sZeroPolynomial s ≤ 0 := by
  have hroot : sZeroPolynomial sZero = 0 := by
    unfold sZeroPolynomial
    linarith [sZero_spec.2.2]
  by_cases hs2 : s ≤ 2
  · have hcubic : s ^ 3 ≤ 2 * s ^ 2 := by
      have hnonneg : 0 ≤ (2 - s) * s ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hs2) (sq_nonneg s)
      nlinarith
    have hgap : 2 * s ^ 2 < (s + 1) ^ 2 := by
      have hnonneg : 0 ≤ s * (2 - s) :=
        mul_nonneg hs.le (sub_nonneg.mpr hs2)
      nlinarith
    unfold sZeroPolynomial
    linarith
  · have htwo : 2 < s := lt_of_not_ge hs2
    rcases eq_or_lt_of_le hs0 with heq | hlt
    · simpa [heq] using hroot.le
    · have hmono :=
        sZeroPolynomial_strictMono_above_two htwo hlt
      rw [hroot] at hmono
      exact hmono.le

/-- The comparison value used in the paper to keep the algebraic tangent in
the positive-completion branch. -/
theorem rhoPolynomial_candidate_nonneg
    {s : ℝ} (hs : 0 < s) (hs0 : s ≤ sZero) :
    0 ≤
      rhoPolynomial s ((s ^ 2 + s + 1) / s ^ 2) := by
  have hpoly := sZeroPolynomial_nonpos_of_pos_le hs hs0
  have hK : 0 ≤ s ^ 2 + s + 1 := by
    nlinarith [sq_nonneg s]
  have hs3 : 0 < s ^ 3 := by positivity
  have hidentity :
      rhoPolynomial s ((s ^ 2 + s + 1) / s ^ 2) =
        ((s ^ 2 + s + 1) / s ^ 3) *
          (-sZeroPolynomial s) := by
    unfold rhoPolynomial sZeroPolynomial
    field_simp [hs.ne']
    ring
  rw [hidentity]
  exact mul_nonneg (div_nonneg hK hs3.le) (neg_nonneg.mpr hpoly)

/-- On the complete algebraic interval, the positive root lies below the
comparison value `(s²+s+1)/s²`. -/
theorem rhoI_le_algebraic_candidate
    {u : ℝ} (hu : 1 < u) (hu0 : u ≤ uZero) :
    rhoI u ≤ stoppingA u / (u - 1) ^ 2 := by
  let s := u - 1
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hs0 : s ≤ sZero := by
    dsimp [s]
    unfold uZero at hu0
    linarith
  have hcandidate :
      stoppingA u / (u - 1) ^ 2 =
        (s ^ 2 + s + 1) / s ^ 2 := by
    dsimp [s]
    unfold stoppingA
    congr 1
    ring
  have hvalue :
      0 ≤ rhoPolynomial s (stoppingA u / (u - 1) ^ 2) := by
    rw [hcandidate]
    exact rhoPolynomial_candidate_nonneg hs hs0
  have hcandidatePos :
      0 < stoppingA u / (u - 1) ^ 2 := by
    have hA : 0 < stoppingA u := by
      unfold stoppingA
      nlinarith [sq_nonneg (u - 1 / 2)]
    positivity
  by_contra hle
  have hlt :
      stoppingA u / (u - 1) ^ 2 < rhoI u :=
    lt_of_not_ge hle
  have hmono :=
    rhoPolynomial_strictMono_nonneg hs hcandidatePos.le hlt
  have hroot := (rhoI_spec hu).2
  change
    rhoPolynomial s (stoppingA u / (u - 1) ^ 2) <
      rhoPolynomial s (rhoI u) at hmono
  rw [hroot] at hmono
  linarith

/-- The tangent point for `rhoI` remains in the positive branch up to the
join with the reciprocal branch. -/
theorem algebraic_positive_branch_condition
    {u : ℝ} (hu : 1 < u) (hu0 : u ≤ uZero) :
    0 ≤
      u * positiveTangentAlpha u (rhoI u) - (u - 1) := by
  have hrho : 0 < rhoI u := (rhoI_spec hu).1
  have hD : 0 < stoppingD u (rhoI u) :=
    stoppingD_pos hu hrho
  have hsquare : 0 < (u - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hu)
  have hcompare := rhoI_le_algebraic_candidate hu hu0
  have hnum :
      0 ≤ stoppingA u - (u - 1) ^ 2 * rhoI u := by
    have hmul :=
      (le_div_iff₀ hsquare).mp hcompare
    nlinarith
  have hrewrite :
      u * stoppingA u -
          (u - 1) * stoppingD u (rhoI u) =
        stoppingA u - (u - 1) ^ 2 * rhoI u := by
    unfold stoppingD
    ring
  calc
    0 ≤
        (u * stoppingA u -
            (u - 1) * stoppingD u (rhoI u)) /
          stoppingD u (rhoI u) := by
      rw [hrewrite]
      exact div_nonneg hnum hD.le
    _ =
        u * positiveTangentAlpha u (rhoI u) - (u - 1) := by
      unfold positiveTangentAlpha
      field_simp [hD.ne']

/-- Scalar certificate for the implicit algebraic branch. -/
noncomputable def algebraicStoppingCertificate
    {u : ℝ} (huD : uDiamond ≤ u) (hu0 : u ≤ uZero) :
    BinaryStoppingCertificate u (rhoI u) := by
  have hu : 1 < u := uDiamond_gt_one.trans_le huD
  have hrho : 0 < rhoI u := (rhoI_spec hu).1
  have hrhoCap : rhoI u ≤ u :=
    (rhoI_le_uDiamond_of_le huD).trans huD
  have htangent : stoppingTangency u (rhoI u) = 0 :=
    (stoppingTangency_iff_rhoPolynomial u (rhoI u)).2
      (rhoI_spec hu).2
  exact positiveBranchCertificate hu hrho hrhoCap (by rw [htangent])
    (algebraic_positive_branch_condition hu hu0)

/-- Past `sZero`, the zero-completion tangent satisfies its branch
inequality. -/
theorem sZeroPolynomial_nonneg_of_le
    {s : ℝ} (hs0 : sZero ≤ s) :
    0 ≤ sZeroPolynomial s := by
  have hroot : sZeroPolynomial sZero = 0 := by
    unfold sZeroPolynomial
    linarith [sZero_spec.2.2]
  rcases eq_or_lt_of_le hs0 with heq | hlt
  · rw [← heq, hroot]
  · have hmono :=
      sZeroPolynomial_strictMono_above_two sZero_spec.1 hlt
    rw [hroot] at hmono
    exact hmono.le

/-- Scalar certificate for the reciprocal branch, valid from `uZero`
onward. -/
noncomputable def reciprocalStoppingCertificate
    {u : ℝ} (hu0 : uZero ≤ u) :
    BinaryStoppingCertificate u (reciprocalBranch u) := by
  let s := u - 1
  have hs0 : sZero ≤ s := by
    dsimp [s]
    unfold uZero at hu0
    linarith
  have hs : 0 < s := sZero_positive.trans_le hs0
  have hpoly : (s + 1) ^ 2 ≤ s ^ 3 := by
    have h := sZeroPolynomial_nonneg_of_le hs0
    unfold sZeroPolynomial at h
    linarith
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have htSq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hsTwo : 2 < s := sZero_spec.1.trans_le hs0
  have htOneStrict : 1 < Real.sqrt s := by
    nlinarith [Real.sqrt_nonneg s]
  have halphaPos : 0 < 1 / Real.sqrt s := one_div_pos.mpr ht
  have halphaOne : 1 / Real.sqrt s < 1 := by
    rw [div_lt_one ht]
    exact htOneStrict
  have hst : 1 ≤ s * Real.sqrt s := by
    have hstep : Real.sqrt s ≤ s * Real.sqrt s := by
      have hnonneg :
          0 ≤ (s - 1) * Real.sqrt s :=
        mul_nonneg (by linarith) (Real.sqrt_nonneg s)
      linarith
    exact htOneStrict.le.trans hstep
  have hratioCap : reciprocalBranch u ≤ u := by
    have huEq : u = s + 1 := by
      dsimp [s]
      ring
    rw [huEq]
    unfold reciprocalBranch
    rw [show s + 1 - 1 = s by ring]
    rw [show s + 1 = 1 + s by ring]
    rw [add_le_add_iff_left]
    exact (div_le_iff₀ ht).2 hst
  have hbranch :
      (s + 1) * (1 / Real.sqrt s) - s ≤ 0 :=
    zero_tangent_in_zero_branch hs hpoly
  have hmin :
      stoppingMinimizer (s + 1) (1 / Real.sqrt s) = 0 := by
    unfold stoppingMinimizer
    rw [show s + 1 - 1 = s by ring]
    rw [max_eq_left hbranch]
  have hf :
      stoppingF (s + 1) (1 + 1 / Real.sqrt s)
          (1 / Real.sqrt s)
          (stoppingMinimizer (s + 1) (1 / Real.sqrt s)) = 0 := by
    rw [hmin, stoppingF_zero]
    exact zeroStoppingEnvelope_tangent hs
  refine
    { alpha := 1 / Real.sqrt s
      ratio_nonneg := by
        unfold reciprocalBranch
        positivity
      ratio_le_cap := hratioCap
      alpha_pos := halphaPos
      alpha_lt_one := halphaOne
      minimized_nonneg := ?_ }
  have hfNonneg :
      0 ≤
        stoppingF (s + 1) (1 + 1 / Real.sqrt s)
          (1 / Real.sqrt s)
          (stoppingMinimizer (s + 1) (1 / Real.sqrt s)) := by
    rw [hf]
  simpa [s, reciprocalBranch] using hfNonneg

/-- A scalar certificate controls every feasible completion choice, not only
the explicit minimizer. -/
theorem BinaryStoppingCertificate.stoppingF_nonneg
    {u ratio : ℝ} (certificate : BinaryStoppingCertificate u ratio)
    {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ stoppingF u ratio certificate.alpha b := by
  exact certificate.minimized_nonneg.trans
    (stoppingF_minimized hb)

theorem BinaryStoppingCertificate.minimizer_le_alpha
    {u ratio : ℝ} (certificate : BinaryStoppingCertificate u ratio)
    (hu : 1 ≤ u) :
    stoppingMinimizer u certificate.alpha ≤ certificate.alpha :=
  stoppingMinimizer_le_y hu certificate.alpha_pos.le
    certificate.alpha_lt_one.le

/-- Quantitative form of the paper's "Lipschitz on the unit square" step.
At a first crossing, `y` exceeds `alpha` by only one remaining-job unit; an
actual completion fraction `b` may exceed `alpha` by no more than the same
amount.  The explicit constant here is uniform in all algorithmic choices. -/
theorem BinaryStoppingCertificate.stoppingF_overshoot_lower
    {u ratio : ℝ} (certificate : BinaryStoppingCertificate u ratio)
    (hu : 1 ≤ u) {y b : ℝ}
    (hyAlpha : certificate.alpha ≤ y) (hyOne : y ≤ 1)
    (hbZero : 0 ≤ b) (hbY : b ≤ y) :
    -(2 * u ^ 2 + 4 * u) * (y - certificate.alpha) ≤
      stoppingF u ratio y b := by
  let a := certificate.alpha
  let clipped := min b a
  let eta := y - a
  have hu0 : 0 ≤ u := by linarith
  have ha0 : 0 ≤ a := certificate.alpha_pos.le
  have ha1 : a ≤ 1 := certificate.alpha_lt_one.le
  have heta : 0 ≤ eta := by
    dsimp [eta, a]
    exact sub_nonneg.mpr hyAlpha
  have hb1 : b ≤ 1 := hbY.trans hyOne
  have hc0 : 0 ≤ clipped := by
    exact le_min hbZero ha0
  have hcb : clipped ≤ b := min_le_left _ _
  have hca : clipped ≤ a := min_le_right _ _
  have hbc0 : 0 ≤ b - clipped := sub_nonneg.mpr hcb
  have hbcEta : b - clipped ≤ eta := by
    by_cases hba : b ≤ a
    · have hc : clipped = b := min_eq_left hba
      rw [hc]
      simpa using heta
    · have hab : a ≤ b := le_of_not_ge hba
      have hc : clipped = a := min_eq_right hab
      rw [hc]
      dsimp [eta]
      linarith
  have hspan0 : 0 ≤ y + a := add_nonneg (ha0.trans hyAlpha) ha0
  have hspan1 : y + a ≤ 2 := by linarith
  have hetaSpan0 : 0 ≤ eta * (y + a) :=
    mul_nonneg heta hspan0
  have hetaSpan1 : eta * (y + a) ≤ 2 * eta := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hspan1 heta)
  have hcoef :
      -u ^ 2 ≤ (u - 1) * (1 - ratio) := by
    have hratioLower : -u ≤ 1 - ratio := by
      linarith [certificate.ratio_le_cap]
    have hmul :=
      mul_le_mul_of_nonneg_left hratioLower
        (sub_nonneg.mpr hu)
    have hubound : u * (u - 1) ≤ u ^ 2 := by
      nlinarith
    nlinarith
  have hcoefMul :
      -u ^ 2 * (eta * (y + a)) ≤
        (u - 1) * (1 - ratio) * (eta * (y + a)) :=
    mul_le_mul_of_nonneg_right hcoef hetaSpan0
  have hquadLower :
      -2 * u ^ 2 * eta ≤
        (u - 1) * (1 - ratio) * eta * (y + a) := by
    have hscale :=
      mul_le_mul_of_nonneg_left hetaSpan1 (sq_nonneg u)
    nlinarith
  have hbyca :
      b * y - clipped * a =
        b * eta + a * (b - clipped) := by
    dsimp [eta]
    ring
  have hbEta : b * eta ≤ eta := by
    have h := mul_nonneg (sub_nonneg.mpr hb1) heta
    nlinarith
  have haBc : a * (b - clipped) ≤ eta := by
    have hleft :=
      mul_le_mul_of_nonneg_left hbcEta ha0
    have hright : a * eta ≤ eta := by
      have h := mul_nonneg (sub_nonneg.mpr ha1) heta
      nlinarith
    exact hleft.trans hright
  have hbycaNonneg : 0 ≤ b * y - clipped * a := by
    rw [hbyca]
    exact add_nonneg (mul_nonneg hbZero heta)
      (mul_nonneg ha0 hbc0)
  have hbycaUpper : b * y - clipped * a ≤ 2 * eta := by
    rw [hbyca]
    linarith
  have hlast :
      -4 * u * eta ≤ -2 * u * (b * y - clipped * a) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hbycaUpper
        (mul_nonneg zero_le_two hu0)
    nlinarith
  have hclipSquare : 0 ≤ (b - clipped) * (b + clipped) := by
    exact mul_nonneg hbc0 (add_nonneg hbZero hc0)
  have hclipLinear : 0 ≤ 2 * (b - clipped) * (u - 1) := by
    positivity
  have hbase : 0 ≤ stoppingF u ratio a clipped :=
    certificate.stoppingF_nonneg hc0
  have hidentity :
      stoppingF u ratio y b =
        stoppingF u ratio a clipped +
          2 * eta +
          (u - 1) * (1 - ratio) * eta * (y + a) +
          (b - clipped) * (b + clipped) +
          2 * (b - clipped) * (u - 1) -
          2 * u * (b * y - clipped * a) := by
    unfold stoppingF
    dsimp [eta]
    ring
  rw [hidentity]
  nlinarith

/-- Combining a binary certificate with the already formalized hidden
stopping decomposition yields the nonnegative leading competitive excess. -/
theorem BinaryStoppingCertificate.leadingExcess_nonneg
    {u ratio : ℝ} (certificate : BinaryStoppingCertificate u ratio)
    {sigma b : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hb : 0 ≤ b) :
    0 ≤
      stoppingAlgLeading u (1 - sigma)
          (1 - sigma + sigma * certificate.alpha) (sigma * b) -
        ratio *
          stoppingOptLeading u (1 - sigma)
            (1 - sigma + sigma * certificate.alpha) := by
  exact stoppingLeading_excess_nonneg certificate.ratio_le_cap
    hsigma0 hsigma1 (certificate.stoppingF_nonneg hb)

/-! ## The remaining finite accounting bridge for hidden stopping -/

/-- What remains of raw-safe hidden stopping after
`HiddenStoppingOracle.lean`.

The oracle, its admissibility, binary frozen range, local first-crossing
overshoot, and replay are all concrete.  The premise here now bundles only
the still-missing trace-global facts: a terminal fuel/no-crossing outcome and
the scheduling exchange plus offline-identification estimate at a crossing.
For the explicit oracle these must supply one strategy- and size-independent
linear remainder. -/
def HiddenStoppingFiniteCostBridge : Prop :=
  ∀ {u ratio : ℝ} (_hu : 1 < u)
      (certificate : BinaryStoppingCertificate u ratio),
    ∃ remainder : ℝ, 0 ≤ remainder ∧
      ∀ n (strategy : Online.Strategy n),
        ∃ fuel,
          adaptiveDefeatsWithLinearRemainder
            (.finite u)
            (HiddenStoppingOracle.oracle n u certificate.alpha)
            strategy (fun _ => 0) fuel ratio remainder

/-- A linear finite hidden-stopping estimate implies the full
arbitrarily-large adaptive lower bound.  The proof uses the true quadratic
offline lower bound of the frozen instance. -/
theorem hiddenStopping_adaptive_lower
    (bridge : HiddenStoppingFiniteCostBridge)
    {u ratio : ℝ} (hu : 1 < u)
    (certificate : BinaryStoppingCertificate u ratio) :
    AdaptiveSizeLowerBound (.finite u) ratio := by
  obtain ⟨remainder, hremNonneg, hfinite⟩ :=
    bridge hu certificate
  have hu0 : 0 ≤ u := by linarith
  intro strategies ε hε N
  obtain ⟨threshold, hthreshold⟩ :=
    exists_nat_ge (2 * remainder / ε)
  let n := max N threshold
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnThreshold : threshold ≤ n := Nat.le_max_right _ _
  obtain ⟨fuel, hrun⟩ := hfinite n (strategies n)
  refine ⟨n, hnN,
    HiddenStoppingOracle.oracle n u certificate.alpha,
    (fun _ => 0), fuel, ?_, ?_, ?_⟩
  · exact HiddenStoppingOracle.oracle_admissible hu0
  · exact HiddenStoppingOracle.zero_default_admissible hu0
  · let frozen :=
      Online.frozenProcessingTimes (.finite u)
        (HiddenStoppingOracle.oracle n u certificate.alpha)
        (strategies n) (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun (.finite u)
        (HiddenStoppingOracle.oracle n u certificate.alpha)
        (strategies n) fuel).result
    change
      resultSettled result ∧
        (¬ resultCompleted result ∨
          (ratio - ε) * vectorOfflineCost (.finite u) frozen ≤
            Online.runCompletionCost (.finite u) frozen result)
    change
      resultSettled result ∧
        (¬ resultCompleted result ∨
          ratio * vectorOfflineCost (.finite u) frozen ≤
            Online.runCompletionCost (.finite u) frozen result +
              remainder * n) at hrun
    rcases hrun with ⟨hsettled, hincomplete | hcost⟩
    · exact ⟨hsettled, Or.inl hincomplete⟩
    · refine ⟨hsettled, Or.inr ?_⟩
      have hnCast : (threshold : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hnThreshold
      have hlarge :
          2 * remainder / ε ≤ (n : ℝ) :=
        hthreshold.trans hnCast
      have htwo :
          2 * remainder ≤ (n : ℝ) * ε :=
        (div_le_iff₀ hε).mp hlarge
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_right htwo hn0
      have hlinear :
          remainder * (n : ℝ) ≤ ε * triangular n := by
        unfold triangular
        nlinarith
      let I : FixedInput (.finite u) n :=
        frozenInput (.finite u)
          (HiddenStoppingOracle.oracle n u certificate.alpha)
          (strategies n) (fun _ => 0) fuel
          (HiddenStoppingOracle.oracle_admissible hu0)
          (HiddenStoppingOracle.zero_default_admissible hu0)
      have hofflineI :
          triangular n ≤ I.offlineCost :=
        I.offlineCost_quadratic_lower_one hu.le
      have hoffline :
          triangular n ≤ vectorOfflineCost (.finite u) frozen := by
        simpa [I, FixedInput.offlineCost, frozenInput, frozen] using
          hofflineI
      have hremainder :
          remainder * (n : ℝ) ≤
            ε * vectorOfflineCost (.finite u) frozen :=
        hlinear.trans
          (mul_le_mul_of_nonneg_left hoffline hε.le)
      calc
        (ratio - ε) * vectorOfflineCost (.finite u) frozen =
            ratio * vectorOfflineCost (.finite u) frozen -
              ε * vectorOfflineCost (.finite u) frozen := by ring
        _ ≤
            (Online.runCompletionCost (.finite u) frozen result +
                remainder * n) -
              ε * vectorOfflineCost (.finite u) frozen :=
          sub_le_sub_right hcost _
        _ ≤ Online.runCompletionCost (.finite u) frozen result := by
          linarith

/-! ## The exact remaining operational interface -/

/-- The statements below are precisely the operational constructions still
missing between the formal scalar/accounting lemmas and full lower bounds.

`hiddenStoppingFiniteCost` is now only the canonical-schedule relaxation,
termination, and uniform linear-error estimate for the explicit legal oracle
and crossing invariant proved in `HiddenStoppingOracle`.

`mixedQuota` is cap deferral plus raw-safe quota for the scaled harmonic
block.  `boundedHarmonic` is the bounded cap-free transfer.  `harmonic`
constructs the multilevel obligatory revelation experiment.  `baseline`
connects completed transcripts to offline optimality in the degenerate
`u ≤ 1` interval.
-/
structure OperationalLowerInterfaces : Prop where
  baseline :
    ∀ {u : ℝ}, 0 < u → u ≤ 1 →
      AdaptiveSizeLowerBound (.finite u) 1
  hiddenStoppingFiniteCost :
    HiddenStoppingFiniteCostBridge
  mixedQuota :
    ∀ u : MixedUpperDomain,
      goldenRatio + 2 < (u : ℝ) →
      (u : ℝ) < zStar →
      AdaptiveSizeLowerBound (.finite (u : ℝ)) (mixedFiniteCurve u)
  boundedHarmonic :
    ∀ {u : ℝ}, zStar ≤ u →
      AdaptiveSizeLowerBound (.finite u) RStar
  harmonic :
    AdaptiveSizeLowerBound .infinite RStar

/-! ## Branchwise and global assembly -/

theorem finite_exactCurve_adaptive
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : 0 < u) :
    AdaptiveSizeLowerBound (.finite u) (exactCurve u) := by
  by_cases h1 : u ≤ 1
  · rw [exactCurve_eq_one h1]
    exact interfaces.baseline hu h1
  by_cases hDiamond : u ≤ uDiamond
  · have hu1 : 1 < u := lt_of_not_ge h1
    rw [exactCurve_eq_self hu1 hDiamond]
    exact hiddenStopping_adaptive_lower
      interfaces.hiddenStoppingFiniteCost hu1
      (identityStoppingCertificate hu1 hDiamond)
  by_cases hZero : u ≤ uZero
  · have hDiamondStrict : uDiamond < u := lt_of_not_ge hDiamond
    have hu1 : 1 < u := uDiamond_gt_one.trans hDiamondStrict
    rw [exactCurve_eq_rhoI hDiamondStrict hZero]
    exact hiddenStopping_adaptive_lower
      interfaces.hiddenStoppingFiniteCost hu1
      (algebraicStoppingCertificate hDiamondStrict.le hZero)
  by_cases hGolden : u ≤ goldenRatio + 2
  · have hZeroStrict : uZero < u := lt_of_not_ge hZero
    have hu1 : 1 < u := by
      linarith [uZero_bounds.1]
    rw [exactCurve_eq_reciprocal hZeroStrict hGolden]
    exact hiddenStopping_adaptive_lower
      interfaces.hiddenStoppingFiniteCost hu1
      (reciprocalStoppingCertificate hZeroStrict.le)
  by_cases hStar : u < zStar
  · have hGoldenStrict : goldenRatio + 2 < u :=
      lt_of_not_ge hGolden
    rw [exactCurve_eq_mixed hGoldenStrict hStar.le]
    exact interfaces.mixedQuota
      ⟨u, hGoldenStrict.le, hStar.le⟩ hGoldenStrict hStar
  · have hStarLe : zStar ≤ u := le_of_not_gt hStar
    rw [exactCurve_plateau hStarLe]
    exact interfaces.boundedHarmonic hStarLe

/-- Main finite-cap lower theorem: for every deterministic strategy family
and every epsilon, arbitrarily large genuine fixed instances attain
`exactCurve u - epsilon`. -/
theorem finite_exactCurve_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : 0 < u) :
    FixedSizeLowerBound (.finite u) (exactCurve u) :=
  fixedSizeLowerBound_of_adaptive
    (finite_exactCurve_adaptive interfaces hu)

/-- Main obligatory lower theorem at the exact harmonic optimum. -/
theorem obligatory_RStar_lower
    (interfaces : OperationalLowerInterfaces) :
    FixedSizeLowerBound .infinite RStar :=
  fixedSizeLowerBound_of_adaptive interfaces.harmonic

theorem finite_one_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : u ∈ Ioc 0 1) :
    FixedSizeLowerBound (.finite u) 1 := by
  simpa [exactCurve_eq_one_of_mem hu] using
    finite_exactCurve_lower interfaces hu.1

theorem finite_identity_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : u ∈ Icc 1 uDiamond) :
    FixedSizeLowerBound (.finite u) u := by
  have huPos : 0 < u := zero_lt_one.trans_le hu.1
  simpa [exactCurve_eq_self_of_mem hu] using
    finite_exactCurve_lower interfaces huPos

theorem finite_algebraic_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : u ∈ Icc uDiamond uZero) :
    FixedSizeLowerBound (.finite u) (rhoI u) := by
  have huPos : 0 < u :=
    (zero_lt_one.trans uDiamond_gt_one).trans_le hu.1
  simpa [exactCurve_eq_rhoI_of_mem hu] using
    finite_exactCurve_lower interfaces huPos

theorem finite_reciprocal_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : u ∈ Icc uZero (goldenRatio + 2)) :
    FixedSizeLowerBound (.finite u) (reciprocalBranch u) := by
  have huPos : 0 < u := by
    linarith [uZero_bounds.1, hu.1]
  simpa [exactCurve_eq_reciprocal_of_mem hu] using
    finite_exactCurve_lower interfaces huPos

theorem finite_mixed_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : u ∈ Icc (goldenRatio + 2) zStar) :
    FixedSizeLowerBound (.finite u)
      (mixedFiniteCurve ⟨u, hu⟩) := by
  have huPos : 0 < u := by
    linarith [goldenRatio_pos, hu.1]
  simpa [exactCurve_eq_mixed_of_mem hu] using
    finite_exactCurve_lower interfaces huPos

theorem finite_plateau_branch_lower
    (interfaces : OperationalLowerInterfaces)
    {u : ℝ} (hu : zStar ≤ u) :
    FixedSizeLowerBound (.finite u) RStar := by
  have huPos : 0 < u := by
    linarith [zStar_gt_one, hu]
  simpa [exactCurve_plateau hu] using
    finite_exactCurve_lower interfaces huPos

/-! The analytic endpoint feeding `OperationalLowerInterfaces.harmonic` is
already completely formal. -/

theorem harmonic_lower_target :
    harmonicLimitRatio alphaStar = RStar :=
  harmonicLimitRatio_alphaStar

theorem rational_harmonic_lower_target
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ,
      0 < (q : ℝ) ∧
      (q : ℝ) < Real.exp 1 - 1 ∧
      RStar - ε < harmonicLimitRatio (q : ℝ) :=
  exists_rational_harmonic_parameter hε

end LowerBound

end

end SchedulingPaper
