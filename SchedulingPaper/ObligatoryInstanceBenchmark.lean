import SchedulingPaper.RevealingOptimizationSurvival
import SchedulingPaper.RandomizedAnnouncedFluid
import SchedulingPaper.RandomizedIdealSchedule
import Mathlib.Tactic

/-!
# Concrete empirical benchmark for obligatory instance optimality

This file instantiates the maximum-density module on a literal nonempty
finite processing-time vector.  It constructs the threshold from the exact
deficit equation, proves its global fractional density certificate, and
identifies the finite stationary cost with the empirical benchmark plus its
exact diagonal correction.
-/

namespace SchedulingPaper
namespace ObligatoryInstance

open RandomizedAnnounced
open RevealingOptimization
open Randomized
open RandomizedObligatory

noncomputable section

/-- Uniform occurrence mass on a labelled finite input. -/
def empiricalOccurrenceMass (n : ℕ) (_job : Fin n) : ℝ := 1 / n

/-- The complete strict threshold prefix, represented as a fractional
selection of the uniform occurrence masses. -/
def empiricalThresholdSelection {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) (job : Fin n) : ℝ :=
  if p job < τ then 1 / n else 0

/-- Boolean presentation of the same strict threshold prefix, used by the
literal stationary operation word. -/
def empiricalThresholdEarly {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) (job : Fin n) : Bool :=
  decide (p job < τ)

/-- The paper's obligatory instance-specific leading value for the
maximum-density threshold `τ`. -/
def empiricalObligatoryValue {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  let e := thresholdEarlyCount p τ
  let m := thresholdEarlyWork p τ
  let K := thresholdLateOrderedMin p τ
  (1 + m / n) * (1 - (e / n) / 2) +
    (K / (n : ℝ) ^ 2) / 2

theorem earlyMassCount_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    earlyMassCount (empiricalThresholdEarly p τ) =
      thresholdEarlyCount p τ := by
  unfold earlyMassCount empiricalThresholdEarly thresholdEarlyCount
  apply Finset.sum_congr rfl
  intro job _hjob
  by_cases h : p job < τ <;> simp [h]

theorem sum_discoveryBlock_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    (∑ job, discoveryBlock p (empiricalThresholdEarly p τ) job) =
      n + thresholdEarlyWork p τ := by
  unfold discoveryBlock empiricalThresholdEarly thresholdEarlyWork
  rw [show (fun job : Fin n ↦
      1 + if decide (p job < τ) then p job else 0) =
      (fun job ↦ 1 + if p job < τ then p job else 0) by
    funext job
    by_cases h : p job < τ <;> simp [h]]
  rw [Finset.sum_add_distrib]
  simp

theorem earlySelfWork_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    earlySelfWork p (empiricalThresholdEarly p τ) =
      thresholdEarlyCount p τ + thresholdEarlyWork p τ := by
  unfold earlySelfWork empiricalThresholdEarly thresholdEarlyCount
  rw [show (fun job : Fin n ↦
      if decide (p job < τ) = true then
        discoveryBlock p (fun job ↦ decide (p job < τ)) job else 0) =
      (fun job ↦ (if p job < τ then (1 : ℝ) else 0) +
        if p job < τ then p job else 0) by
    funext job
    by_cases h : p job < τ <;> simp [h, discoveryBlock]]
  rw [Finset.sum_add_distrib]
  simp [thresholdEarlyWork]

theorem classifiedLateCount_base_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    classifiedLateCount
        (baseClassifiedJobs p (empiricalThresholdEarly p τ)) =
      n - thresholdEarlyCount p τ := by
  have hcount := classifiedEarlyCount_add_lateCount
    (baseClassifiedJobs p (empiricalThresholdEarly p τ))
  rw [classifiedEarlyCount_ofFn_eq_massCount,
    earlyMassCount_empiricalThresholdEarly] at hcount
  rw [show (baseClassifiedJobs p
      (empiricalThresholdEarly p τ)).length = n by
    simp [baseClassifiedJobs]] at hcount
  linarith

theorem classifiedDiscoveryWork_base_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    classifiedDiscoveryWork
        (baseClassifiedJobs p (empiricalThresholdEarly p τ)) =
      n + thresholdEarlyWork p τ := by
  rw [classifiedDiscoveryWork_ofFn,
    sum_discoveryBlock_empiricalThresholdEarly]

theorem classifiedLateWork_base_empiricalThresholdEarly
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    classifiedLateWork
        (baseClassifiedJobs p (empiricalThresholdEarly p τ)) =
      (∑ job, p job) - thresholdEarlyWork p τ := by
  induction n with
  | zero =>
      simp [baseClassifiedJobs, classifiedLateWork, thresholdEarlyWork]
  | succ n ih =>
      rw [show baseClassifiedJobs p (empiricalThresholdEarly p τ) =
          (p 0, empiricalThresholdEarly p τ 0) ::
            baseClassifiedJobs (fun i ↦ p i.succ)
              (empiricalThresholdEarly (fun i ↦ p i.succ) τ) by
        simp [baseClassifiedJobs, List.ofFn_succ,
          empiricalThresholdEarly]]
      rw [classifiedLateWork, Fin.sum_univ_succ]
      rw [show thresholdEarlyWork p τ =
          (if p 0 < τ then p 0 else 0) +
            thresholdEarlyWork (fun i ↦ p i.succ) τ by
        unfold thresholdEarlyWork
        rw [Fin.sum_univ_succ]]
      rw [ih (fun i ↦ p i.succ)]
      by_cases h : p 0 < τ
      · simp [empiricalThresholdEarly, h]
      · simp [empiricalThresholdEarly, h]
        ring

private def empiricalLatePairCharge (left right : ClassifiedJob) : ℝ :=
  if left.2 then 0 else if right.2 then 0 else min left.1 right.1

private theorem classifiedLatePairMin_eq_listPairObjective
    (jobs : List ClassifiedJob) :
    classifiedLatePairMin jobs =
      listPairObjective (fun _job ↦ 0) empiricalLatePairCharge jobs := by
  induction jobs with
  | nil => simp [classifiedLatePairMin, listPairObjective]
  | cons job jobs ih =>
      rcases job with ⟨p, early⟩
      rw [classifiedLatePairMin, listPairObjective, ih]
      cases early
      · simp only [Bool.false_eq_true, if_false, zero_add]
        congr 1
      · simp only [if_true, zero_add]
        have hzero :
            (jobs.map (empiricalLatePairCharge (p, true))).sum = 0 := by
          have hfun : empiricalLatePairCharge (p, true) = fun _ => 0 := by
            funext other
            rfl
          rw [hfun]
          simp
        rw [hzero]
        ring

/-- Ordered tail pairs are exactly the late diagonal plus twice the strict
late pair sum appearing in the literal stationary word. -/
theorem thresholdLateOrderedMin_eq_lateWork_add_two_pair
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    thresholdLateOrderedMin p τ =
      classifiedLateWork
          (baseClassifiedJobs p (empiricalThresholdEarly p τ)) +
        2 * classifiedLatePairMin
          (baseClassifiedJobs p (empiricalThresholdEarly p τ)) := by
  let early := empiricalThresholdEarly p τ
  let f : Fin n → Fin n → ℝ := fun i j ↦
    thresholdLateIndicator p τ i * thresholdLateIndicator p τ j *
      min (p i) (p j)
  have hsymm : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    rw [min_comm]
    ring
  have hdouble := symmetric_double_sum f hsymm
  have hdiag : (∑ i, f i i) =
      classifiedLateWork (baseClassifiedJobs p early) := by
    rw [classifiedLateWork_base_empiricalThresholdEarly]
    unfold thresholdEarlyWork
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hlate : τ ≤ p i
    · have hnot : ¬p i < τ := not_lt.mpr hlate
      simp [f, thresholdLateIndicator, hlate, hnot]
    · have hearly : p i < τ := lt_of_not_ge hlate
      simp [f, thresholdLateIndicator, hlate, hearly]
  have hupper :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j) =
        classifiedLatePairMin (baseClassifiedJobs p early) := by
    have hfinite := finSelfPairSum_eq_listPairObjective
      (self := fun _job : ClassifiedJob ↦ (0 : ℝ))
      (pair := empiricalLatePairCharge)
      (values := fun i : Fin n ↦ (p i, early i))
    rw [← classifiedLatePairMin_eq_listPairObjective] at hfinite
    simp only [Finset.sum_const_zero, zero_add] at hfinite
    change (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j) =
      classifiedLatePairMin (List.ofFn fun i : Fin n ↦ (p i, early i))
    rw [← hfinite]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [f, early, empiricalThresholdEarly,
      empiricalLatePairCharge]
    by_cases hi : τ ≤ p i
    · have hi' : ¬p i < τ := not_lt.mpr hi
      by_cases hj : τ ≤ p j
      · have hj' : ¬p j < τ := not_lt.mpr hj
        simp [thresholdLateIndicator, hi, hj, hi', hj']
      · have hj' : p j < τ := lt_of_not_ge hj
        simp [thresholdLateIndicator, hi, hj, hi', hj']
    · have hi' : p i < τ := lt_of_not_ge hi
      simp [thresholdLateIndicator, hi, hi']
  unfold thresholdLateOrderedMin
  rw [Fintype.sum_prod_type, hdouble, hdiag, hupper]

/-- The exact expected cost of the finite stationary threshold operation
word under a uniform discovery order. -/
def empiricalStationaryTemplateAverage {n : ℕ}
    (p : Fin n → ℝ) (τ : ℝ) : ℝ :=
  uniformAverage fun order : Equiv.Perm (Fin n) ↦
    classifiedPairCost
      (orderedClassifiedJobs p (empiricalThresholdEarly p τ) order)

/-- The aggregate finite formula used below is exactly the uniform expected
cost of the explicit stationary operation word. -/
theorem empiricalStationaryTemplateAverage_eq_finiteCost
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (τ : ℝ) :
    empiricalStationaryTemplateAverage p τ =
      empiricalStationaryFiniteCost p τ := by
  let early := empiricalThresholdEarly p τ
  let base := baseClassifiedJobs p early
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hpoint :
      (fun order : Equiv.Perm (Fin n) ↦
        classifiedPairCost (orderedClassifiedJobs p early order)) =
      (fun order ↦ stationaryEarlyCost p early order +
        classifiedLateCost base) := by
    funext order
    rw [classifiedPairCost_eq_early_add_late,
      classifiedEarlyCost_ordered_eq_stationary]
    rw [classifiedLateCost_perm
      (orderedClassifiedJobs_perm_base p early order)]
  unfold empiricalStationaryTemplateAverage
  change uniformAverage (fun order : Equiv.Perm (Fin n) ↦
    classifiedPairCost (orderedClassifiedJobs p early order)) = _
  rw [hpoint, uniformAverage_add, uniformAverage_const,
    uniformAverage_stationaryEarlyCost]
  have he := earlyMassCount_empiricalThresholdEarly p τ
  have hwork := sum_discoveryBlock_empiricalThresholdEarly p τ
  have hself := earlySelfWork_empiricalThresholdEarly p τ
  have hlateCount := classifiedLateCount_base_empiricalThresholdEarly p τ
  have hlateDiscovery :=
    classifiedDiscoveryWork_base_empiricalThresholdEarly p τ
  have hlateWork := classifiedLateWork_base_empiricalThresholdEarly p τ
  have hK := thresholdLateOrderedMin_eq_lateWork_add_two_pair p τ
  unfold classifiedLateCost
  rw [he, hwork, hself, hlateCount, hlateDiscovery, hlateWork]
  unfold empiricalStationaryFiniteCost
  dsimp only
  rw [hK, hlateWork]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring

theorem discoveryMass_empiricalThresholdSelection
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    discoveryMass 0 (empiricalThresholdSelection p τ) =
      thresholdEarlyCount p τ / n := by
  unfold discoveryMass empiricalThresholdSelection thresholdEarlyCount
  simp only [zero_add]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro job _hjob
  by_cases h : p job < τ <;> simp [h]

theorem discoveryWork_empiricalThresholdSelection
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    discoveryWork p (empiricalThresholdSelection p τ) =
      1 + thresholdEarlyWork p τ / n := by
  unfold discoveryWork empiricalThresholdSelection thresholdEarlyWork
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro job _hjob
  by_cases h : p job < τ <;> simp [h]
  ring

/-- The finite threshold-deficit equation is exactly the normalized module
density identity `τ a = 1+m`. -/
theorem empiricalThreshold_module_density
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (τ : ℝ)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    τ * discoveryMass 0 (empiricalThresholdSelection p τ) =
      discoveryWork p (empiricalThresholdSelection p τ) := by
  rw [discoveryMass_empiricalThresholdSelection,
    discoveryWork_empiricalThresholdSelection]
  have hdeficit : thresholdDeficit p τ = n := by
    simpa [thresholdDeficit] using hthreshold
  rw [thresholdDeficit_eq_threshold_mul_earlyCount_sub_earlyWork]
      at hdeficit
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  linarith

/-- Concrete global maximum-density certificate on a finite empirical
input.  The competitor `x` may select an arbitrary fractional amount of
every occurrence. -/
theorem empiricalThreshold_maximizes_discovery_density
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {τ : ℝ} (hthreshold : ∑ job, max (τ - p job) 0 = n)
    (x : Fin n → ℝ)
    (hx0 : ∀ job, 0 ≤ x job)
    (hxcap : ∀ job, x job ≤ empiricalOccurrenceMass n job) :
    τ * discoveryMass 0 x ≤ discoveryWork p x := by
  apply threshold_maximizes_discovery_density
    (μ := empiricalOccurrenceMass n)
    (xStar := empiricalThresholdSelection p τ)
    hx0 hxcap
  · intro job hlow
    simp [empiricalThresholdSelection, empiricalOccurrenceMass, hlow]
  · intro job hhigh
    have hnlt : ¬p job < τ := not_lt.mpr hhigh.le
    simp [empiricalThresholdSelection, hnlt]
  · exact empiricalThreshold_module_density hn p τ hthreshold

/-- Concrete pointwise completion-line certificate for the empirical
maximum-density module.  At every fractional test time `T`, an arbitrary
feasible partial selection that has used at most work `s` completes no more
mass than the line of slope `1/τ`. -/
theorem empiricalMaximumDensity_completion_le_line
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {τ T s : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    (hthreshold : ∑ job, max (τ - p job) 0 = n)
    (x : Fin n → ℝ)
    (hx0 : ∀ job, 0 ≤ x job)
    (hxcap : ∀ job, x job ≤ empiricalOccurrenceMass n job)
    (hwork : T * discoveryWork p x ≤ s) :
    T * discoveryMass 0 x ≤ s / τ := by
  apply discovery_completion_le_density_line
    (μ0 := 0) (θ := τ) (T := T) (s := s)
    (μ := empiricalOccurrenceMass n)
    (p := p) (x := x)
    (xStar := empiricalThresholdSelection p τ)
    hτ hT hx0 hxcap
  · intro job hlow
    simp [empiricalThresholdSelection, empiricalOccurrenceMass, hlow]
  · intro job hhigh
    have hnlt : ¬p job < τ := not_lt.mpr hhigh.le
    simp [empiricalThresholdSelection, hnlt]
  · exact empiricalThreshold_module_density hn p τ hthreshold
  · exact hwork

/-- Every empirical threshold prefix extending the maximum-density module
has average work per completion at most its marginal threshold. -/
theorem empiricalExtendedPrefix_average_density
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {τ q : ℝ} (hτq : τ ≤ q)
    (hthreshold : ∑ job, max (τ - p job) 0 = n) :
    discoveryWork p (empiricalThresholdSelection p q) ≤
      q * discoveryMass 0 (empiricalThresholdSelection p q) := by
  let xStar := empiricalThresholdSelection p τ
  let y := empiricalThresholdSelection p q
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : ∀ job, 0 ≤ xStar job := by
    intro job
    by_cases h : p job < τ <;>
      simp [xStar, empiricalThresholdSelection, h, hnR.le]
  have hxcap : ∀ job, xStar job ≤ empiricalOccurrenceMass n job := by
    intro job
    by_cases h : p job < τ <;>
      simp [xStar, empiricalThresholdSelection, empiricalOccurrenceMass,
        h, hnR.le]
  have hsupport := threshold_prefix_supporting
    (μ0 := 0) (q := q) (μ := empiricalOccurrenceMass n)
    (p := p) (x := xStar) (y := y) hx0 hxcap
    (by
      intro job hlow
      simp [y, empiricalThresholdSelection, empiricalOccurrenceMass, hlow])
    (by
      intro job hhigh
      have hnlt : ¬p job < q := not_lt.mpr hhigh.le
      simp [y, empiricalThresholdSelection, hnlt])
  have hmass0 : 0 ≤ discoveryMass 0 xStar := by
    unfold discoveryMass
    simp only [zero_add]
    exact Finset.sum_nonneg fun job _hjob ↦ hx0 job
  apply extended_prefix_average_density hτq hmass0
    (empiricalThreshold_module_density hn p τ hthreshold).symm
  dsimp [xStar, y] at hsupport ⊢
  linarith

/-- Finite fractional form of the full pointwise completion envelope.  Once
the maximum-density module is followed by an SPT threshold prefix `q`, no
feasible partial adaptive test state with no more work can have completed
more mass. -/
theorem empiricalPartialCompletion_le_thresholdPrefix
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    {τ q T : ℝ} (hq : 0 < q) (hτq : τ ≤ q)
    (hthreshold : ∑ job, max (τ - p job) 0 = n)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (x : Fin n → ℝ)
    (hx0 : ∀ job, 0 ≤ x job)
    (hxcap : ∀ job, x job ≤ empiricalOccurrenceMass n job)
    (hwork : T * discoveryWork p x ≤
      discoveryWork p (empiricalThresholdSelection p q)) :
    T * discoveryMass 0 x ≤
      discoveryMass 0 (empiricalThresholdSelection p q) := by
  apply partial_completion_le_full_threshold_prefix
    (μ0 := 0) (q := q) (T := T)
    (μ := empiricalOccurrenceMass n) (p := p)
    (y := empiricalThresholdSelection p q) (x := x)
    hq hT0 hT1 hx0 hxcap
  · intro job hlow
    simp [empiricalThresholdSelection, empiricalOccurrenceMass, hlow]
  · intro job hhigh
    have hnlt : ¬p job < q := not_lt.mpr hhigh.le
    simp [empiricalThresholdSelection, hnlt]
  · exact hwork
  · exact empiricalExtendedPrefix_average_density
      hn p hτq hthreshold

/-- Exact finite stationary identity: the empirical obligatory value is not
merely an asymptotic mnemonic; multiplying it by `n²` and adding the
diagonal gives the complete finite stationary formula. -/
theorem empiricalStationaryFiniteCost_eq_obligatoryValue_add_diagonal
    {n : ℕ} (p : Fin n → ℝ) (τ : ℝ) :
    empiricalStationaryFiniteCost p τ =
      (n : ℝ) ^ 2 * empiricalObligatoryValue p τ +
        (thresholdEarlyCount p τ + ∑ job, p job) / 2 := by
  rfl

/-- A bounded empirical input has the advertised linear diagonal remainder. -/
theorem empiricalStationaryFiniteCost_le_value_add_linear
    {n : ℕ} (p : Fin n → ℝ) (τ L : ℝ)
    (hpu : ∀ job, p job ≤ L) :
    empiricalStationaryFiniteCost p τ ≤
      (n : ℝ) ^ 2 * empiricalObligatoryValue p τ +
        (n : ℝ) * (1 + L) / 2 := by
  rw [empiricalStationaryFiniteCost_eq_obligatoryValue_add_diagonal]
  have he : thresholdEarlyCount p τ ≤ n := by
    unfold thresholdEarlyCount
    calc
      (∑ job, if p job < τ then (1 : ℝ) else 0) ≤
          ∑ _job : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro job _hjob
        split <;> norm_num
      _ = n := by simp
  have hpSum : (∑ job, p job) ≤ n * L := by
    calc
      (∑ job, p job) ≤ ∑ _job : Fin n, L :=
        Finset.sum_le_sum fun job _hjob ↦ hpu job
      _ = n * L := by simp
  linarith

/-- Fully concrete announced benchmark constructor for every nonempty
nonnegative finite input. -/
theorem exists_empiricalObligatoryBenchmark
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ p job) :
    ∃ τ, 1 ≤ τ ∧
      (∑ job, max (τ - p job) 0 = n) ∧
      (∀ x : Fin n → ℝ,
        (∀ job, 0 ≤ x job) →
        (∀ job, x job ≤ empiricalOccurrenceMass n job) →
        τ * discoveryMass 0 x ≤ discoveryWork p x) ∧
      empiricalStationaryTemplateAverage p τ =
        empiricalStationaryFiniteCost p τ ∧
      empiricalStationaryFiniteCost p τ =
        (n : ℝ) ^ 2 * empiricalObligatoryValue p τ +
          (thresholdEarlyCount p τ + ∑ job, p job) / 2 := by
  obtain ⟨τ, hτ, hdeficit⟩ :=
    exists_thresholdDeficit_eq_card p hp0
  have hthreshold : ∑ job, max (τ - p job) 0 = n := by
    simpa [thresholdDeficit] using hdeficit
  refine ⟨τ, hτ, hthreshold, ?_,
    empiricalStationaryTemplateAverage_eq_finiteCost hn p τ,
    empiricalStationaryFiniteCost_eq_obligatoryValue_add_diagonal p τ⟩
  intro x hx0 hxcap
  exact empiricalThreshold_maximizes_discovery_density
    hn p hthreshold x hx0 hxcap

end

end ObligatoryInstance
end SchedulingPaper
