import SchedulingPaper.HarmonicOracle
import SchedulingPaper.LowerBoundAssembly
import Mathlib.Tactic

/-!
# Operational completion of the obligatory harmonic lower bound

This file freezes the explicit harmonic revelation, identifies its complete
processing-time multiset, and connects the finite accounting to the analytic
limit.
-/

namespace SchedulingPaper

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Online

namespace LowerBound

theorem List.Perm.of_nodup_mem_iff
    {α : Type*} [BEq α] [LawfulBEq α]
    {left right : List α}
    (hleft : left.Nodup) (hright : right.Nodup)
    (hmem : ∀ a, a ∈ left ↔ a ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro a
  rw [hleft.count, hright.count, if_congr (hmem a) rfl rfl]

theorem HarmonicHistory.terminal_testLabels_perm
    {K Z : ℕ} {γ : ℝ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config)
    (hdone : ∀ job, config.jobs job = .done) :
    (config.transcript.testResults.map Prod.fst).Perm
      (List.ofFn (fun job : Online.Label (K + Z) => job)) := by
  apply List.Perm.of_nodup_mem_iff history.testLabels_nodup
  · rw [List.nodup_ofFn]
    exact Function.injective_id
  · intro job
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨p, hp⟩ :=
        history.done_has_testResult (hdone job)
      exact List.mem_map.mpr ⟨(job, p), hp, rfl⟩

theorem HarmonicHistory.terminal_values_perm_frozen
    {K Z : ℕ} {γ : ℝ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config)
    (hdone : ∀ job, config.jobs job = .done)
    (processingTime : Online.Label (K + Z) → ℝ)
    (hmatch : HarmonicMatches processingTime config.transcript) :
    (harmonicDescendingLevels (Z : ℝ) γ K ++
        List.replicate Z 0).Perm
      (List.ofFn processingTime) := by
  rw [← history.testValues_eq_of_terminal]
  have hvalue :
      config.transcript.testResults.map Prod.snd =
        config.transcript.testResults.map
          (fun result => processingTime result.1) := by
    apply List.map_congr_left
    intro result hresult
    exact (hmatch result.1 result.2 hresult).symm
  rw [hvalue]
  have hlabels :=
    HarmonicHistory.terminal_testLabels_perm history hdone
  have hmapped := hlabels.map processingTime
  simpa only [List.map_map, Function.comp_apply,
    List.map_ofFn, Function.comp_id] using hmapped

theorem harmonicFutureLevels_pairwise
    {ξ γ : ℝ} (hξ : 0 < ξ) (K : ℕ) :
    (harmonicFutureLevels ξ γ K).Pairwise (· ≤ ·) := by
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [show K + 1 = K + 1 by rfl,
        harmonicFutureLevels_succ, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact harmonicFutureLevels_le_level hξ a ha

theorem harmonicEffectiveTail_pairwise
    {ξ γ : ℝ} (hξ : 0 < ξ) (K : ℕ) :
    ((harmonicFutureLevels ξ γ K).map
      (fun p => 1 + p)).Pairwise (· ≤ ·) := by
  exact List.Pairwise.map (fun p : ℝ => 1 + p)
    (fun _ _ (h : (_ : ℝ) ≤ _) => by linarith)
    (harmonicFutureLevels_pairwise hξ K)

theorem harmonicEffectiveCandidate_pairwise
    {ξ γ : ℝ} (hξ : 0 < ξ) (hγ : 0 ≤ γ)
    (K Z : ℕ) :
    (List.replicate Z (1 : ℝ) ++
      (harmonicFutureLevels ξ γ K).map
        (fun p => 1 + p)).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  refine ⟨by simp, harmonicEffectiveTail_pairwise hξ K, ?_⟩
  intro a ha b hb
  have ha : a = 1 := (List.mem_replicate.mp ha).2
  subst a
  rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
  have hp1 : 1 ≤ p := by
    rcases List.mem_map.mp hp with ⟨m, hm, rfl⟩
    exact harmonicLevel_one_le hξ hγ m
  linarith

theorem prefixCost_map_one_add (xs : List ℝ) :
    prefixCost (xs.map (fun p => 1 + p)) =
      triangular xs.length + prefixCost xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, prefixCost_cons,
        List.length_map, List.length_cons, ih, triangular_succ]
      push_cast
      ring

theorem harmonicEffectiveCandidate_cost
    {ξ γ : ℝ} (hξ : 0 < ξ)
    (K Z : ℕ) :
    prefixCost
        (List.replicate Z (1 : ℝ) ++
          (harmonicFutureLevels ξ γ K).map
            (fun p => 1 + p)) =
      triangular (K + Z) +
        pairCost (harmonicFutureLevels ξ γ K) := by
  rw [prefixCost_append, prefixCost_replicate,
    prefixCost_map_one_add,
    prefixCost_eq_pairCost_of_pairwise
      (harmonicFutureLevels_pairwise hξ K)]
  simp only [List.length_map, harmonicFutureLevels_length,
    List.sum_replicate, nsmul_eq_mul, one_mul]
  unfold triangular
  push_cast
  ring

theorem HarmonicHistory.terminal_effective_perm_candidate
    {K Z : ℕ} {γ : ℝ}
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config)
    (hdone : ∀ job, config.jobs job = .done)
    (processingTime : Online.Label (K + Z) → ℝ)
    (hmatch : HarmonicMatches processingTime config.transcript) :
    (List.replicate Z (1 : ℝ) ++
        (harmonicFutureLevels (Z : ℝ) γ K).map
          (fun p => 1 + p)).Perm
      (vectorEffectiveLengths .infinite processingTime) := by
  have hprocessing :=
    HarmonicHistory.terminal_values_perm_frozen
      history hdone processingTime hmatch
  have heffective :=
    hprocessing.map (fun p => effectiveLength .infinite p)
  have hreverse :
      (harmonicDescendingLevels (Z : ℝ) γ K).Perm
        (harmonicFutureLevels (Z : ℝ) γ K) := by
    simpa [harmonicDescendingLevels] using
      (List.reverse_perm
        (harmonicFutureLevels (Z : ℝ) γ K))
  have hpositive :=
    hreverse.map (fun p : ℝ => 1 + p)
  have hcandidateToFull :
      (List.replicate Z (1 : ℝ) ++
          (harmonicFutureLevels (Z : ℝ) γ K).map
            (fun p => 1 + p)).Perm
        ((harmonicDescendingLevels (Z : ℝ) γ K).map
            (fun p => 1 + p) ++
          List.replicate Z (1 : ℝ)) := by
    exact
      (List.perm_append_comm.trans
        (List.Perm.append_right _ hpositive.symm))
  apply hcandidateToFull.trans
  simpa [vectorEffectiveLengths, List.map_append,
    harmonicDescendingLevels] using heffective

theorem HarmonicHistory.terminal_vectorOfflineCost_eq
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    {pending : HarmonicPending (K + Z)}
    {config : Online.Config (K + Z)}
    (history : HarmonicHistory K Z γ 0 0 pending config)
    (hdone : ∀ job, config.jobs job = .done)
    (processingTime : Online.Label (K + Z) → ℝ)
    (hmatch : HarmonicMatches processingTime config.transcript) :
    vectorOfflineCost .infinite processingTime =
      triangular (K + Z) +
        pairCost (harmonicFutureLevels (Z : ℝ) γ K) := by
  unfold vectorOfflineCost
  rw [shortestFirst_pair_formula]
  have hperm :=
    HarmonicHistory.terminal_effective_perm_candidate
      history hdone processingTime hmatch
  rw [← pairCost_perm hperm]
  rw [← prefixCost_eq_pairCost_of_pairwise
    (harmonicEffectiveCandidate_pairwise
      (by exact_mod_cast hZ) hγ K Z)]
  exact harmonicEffectiveCandidate_cost
    (by exact_mod_cast hZ) K Z

def harmonicFiniteOffline (K Z : ℕ) (γ : ℝ) : ℝ :=
  triangular (K + Z) +
    pairCost (harmonicFutureLevels (Z : ℝ) γ K)

def harmonicFiniteOnline (K Z : ℕ) (γ : ℝ) : ℝ :=
  harmonicDynamicPotential (Z : ℝ) γ K Z []

def harmonicFiniteAdvantage (K Z : ℕ) : ℝ :=
  (K : ℝ) * ((K : ℝ) + 2 * (Z : ℝ) - 1) / 2

theorem harmonicFiniteOnline_eq
    (K Z : ℕ) (γ : ℝ) :
    harmonicFiniteOnline K Z γ =
      harmonicFiniteOffline K Z γ +
        harmonicFiniteAdvantage K Z := by
  unfold harmonicFiniteOnline harmonicFiniteOffline
    harmonicFiniteAdvantage harmonicDynamicPotential
  dsimp only
  simp only [List.length_nil, Nat.cast_zero, add_zero, zero_add,
    List.nil_append]
  unfold triangular
  push_cast
  ring

theorem harmonicFrozen_matches
    (K Z : ℕ) (γ : ℝ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ) :
    let frozen :=
      Online.frozenProcessingTimes .infinite
        (harmonicRevelationOracle K Z γ)
        strategy (fun _ => 0) fuel
    let result :=
      (Online.adaptiveRun .infinite
        (harmonicRevelationOracle K Z γ)
        strategy fuel).result
    HarmonicMatches frozen result.config.transcript := by
  dsimp
  intro job p hp
  exact Online.frozenProcessingTimes_eq_of_testResult
    .infinite (harmonicRevelationOracle K Z γ)
    strategy (fun _ => 0) fuel hp

theorem harmonicAdaptive_online_lower_of_completed
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ)
    (hdone :
      resultCompleted
        (Online.adaptiveRun .infinite
          (harmonicRevelationOracle K Z γ)
          strategy fuel).result) :
    let frozen :=
      Online.frozenProcessingTimes .infinite
        (harmonicRevelationOracle K Z γ)
        strategy (fun _ => 0) fuel
    harmonicFiniteOnline K Z γ ≤
      Online.runCompletionCost .infinite frozen
        (Online.adaptiveRun .infinite
          (harmonicRevelationOracle K Z γ)
          strategy fuel).result := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_harmonicHistory K Z γ strategy fuel
  have hterminal :=
    history.terminal_indices hZ hγ hdone
  rcases hterminal with ⟨rfl, rfl, rfl⟩
  have hmatch :=
    harmonicFrozen_matches K Z γ strategy fuel
  have hlower :=
    history.amortized_lower hZ hγ _ hmatch
  simpa [harmonicFiniteOnline, harmonicUnfinished,
    harmonicDynamicPotential_terminal,
    Online.runCompletionCost] using hlower

theorem harmonicAdaptive_offline_eq_of_completed
    {K Z : ℕ} {γ : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    (strategy : Online.Strategy (K + Z)) (fuel : ℕ)
    (hdone :
      resultCompleted
        (Online.adaptiveRun .infinite
          (harmonicRevelationOracle K Z γ)
          strategy fuel).result) :
    let frozen :=
      Online.frozenProcessingTimes .infinite
        (harmonicRevelationOracle K Z γ)
        strategy (fun _ => 0) fuel
    vectorOfflineCost .infinite frozen =
      harmonicFiniteOffline K Z γ := by
  dsimp
  obtain ⟨L, z, pending, history⟩ :=
    adaptiveRun_harmonicHistory K Z γ strategy fuel
  have hterminal :=
    history.terminal_indices hZ hγ hdone
  rcases hterminal with ⟨rfl, rfl, rfl⟩
  have hmatch :=
    harmonicFrozen_matches K Z γ strategy fuel
  exact HarmonicHistory.terminal_vectorOfflineCost_eq
    hZ hγ history hdone _ hmatch

theorem harmonicAdaptive_defeats_of_finite_ratio
    {K Z : ℕ} {γ ratio : ℝ}
    (hZ : 0 < Z) (hγ : 0 ≤ γ)
    (hratio :
      ratio * harmonicFiniteOffline K Z γ ≤
        harmonicFiniteOnline K Z γ)
    (strategy : Online.Strategy (K + Z)) :
    adaptiveDefeats .infinite
      (harmonicRevelationOracle K Z γ)
      strategy (fun _ => 0)
      (2 * (K + Z) + 1) ratio := by
  let fuel := 2 * (K + Z) + 1
  let result :=
    (Online.adaptiveRun .infinite
      (harmonicRevelationOracle K Z γ)
      strategy fuel).result
  let frozen :=
    Online.frozenProcessingTimes .infinite
      (harmonicRevelationOracle K Z γ)
      strategy (fun _ => 0) fuel
  constructor
  · exact harmonic_analysisFuel_settled K Z γ strategy
  · by_cases hdone : resultCompleted result
    · right
      have hoffline :=
        harmonicAdaptive_offline_eq_of_completed
          hZ hγ strategy fuel hdone
      have honline :=
        harmonicAdaptive_online_lower_of_completed
          hZ hγ strategy fuel hdone
      dsimp [result, frozen] at hoffline honline ⊢
      rw [hoffline]
      exact hratio.trans honline
    · exact Or.inl hdone

/-! ## Exact finite benchmark and its scaling limit -/

theorem harmonicFutureLevels_sum_zeroSlack
    (ξ : ℝ) (K : ℕ) :
    (harmonicFutureLevels ξ 0 K).sum =
      K + ∑ r ∈ Finset.range K,
        (K - r - 1 : ℕ) / (ξ + (r + 1 : ℕ)) := by
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [harmonicFutureLevels_succ, List.sum_append,
        ih, harmonicLevel]
      simp only [List.sum_singleton, zero_div, add_zero,
        Finset.sum_range_succ]
      have hsplit :
          ∑ r ∈ Finset.range K,
              ((K + 1 - r - 1 : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ)) =
            ∑ r ∈ Finset.range K,
              (((K - r - 1 : ℕ) : ℝ) /
                  (ξ + (r + 1 : ℕ)) +
                1 / (ξ + (r + 1 : ℕ))) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrK : r < K := Finset.mem_range.mp hr
        have hnat :
            K + 1 - r - 1 = (K - r - 1) + 1 := by
          omega
        rw [hnat]
        push_cast
        ring
      rw [hsplit, Finset.sum_add_distrib]
      have hlast : K + 1 - K - 1 = 0 := by omega
      simp only [hlast, Nat.cast_zero, zero_div, add_zero]
      push_cast
      ring

theorem pairCost_harmonicFutureLevels_zeroSlack
    {ξ : ℝ} (hξ : 0 < ξ) (K : ℕ) :
    pairCost (harmonicFutureLevels ξ 0 K) =
      triangular K +
        (1 / 2 : ℝ) * ∑ r ∈ Finset.range K,
          ((K - r - 1 : ℕ) * (K - r : ℕ) : ℕ) /
            (ξ + (r + 1 : ℕ)) := by
  rw [← prefixCost_eq_pairCost_of_pairwise
    (harmonicFutureLevels_pairwise hξ K)]
  induction K with
  | zero =>
      simp [triangular]
  | succ K ih =>
      rw [harmonicFutureLevels_succ, prefixCost_append,
        ih, harmonicFutureLevels_sum_zeroSlack,
        harmonicLevel, triangular_succ]
      simp only [List.length_singleton, Nat.cast_one,
        one_mul, List.sum_singleton, zero_div, add_zero,
        Finset.sum_range_succ]
      have hsplit :
          ∑ r ∈ Finset.range K,
              (((K + 1 - r - 1 : ℕ) *
                  (K + 1 - r : ℕ) : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ)) =
            ∑ r ∈ Finset.range K,
              ((((K - r - 1 : ℕ) * (K - r : ℕ) : ℕ) : ℝ) /
                  (ξ + (r + 1 : ℕ)) +
                2 * (((K - r : ℕ) : ℝ) /
                  (ξ + (r + 1 : ℕ)))) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrK : r < K := Finset.mem_range.mp hr
        have h₁ : K + 1 - r - 1 = K - r := by omega
        have h₂ : K + 1 - r = (K - r) + 1 := by omega
        have h₃ : K - r = (K - r - 1) + 1 := by omega
        rw [h₁, h₂, h₃]
        push_cast
        ring
      rw [hsplit, Finset.sum_add_distrib]
      have hlast :
          K + 1 - K - 1 = 0 := by omega
      rw [hlast]
      norm_num
      have hmerge :
          (∑ r ∈ Finset.range K,
              (((K - r - 1 : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ)))) +
            ∑ r ∈ Finset.range K,
              1 / (ξ + (r + 1 : ℕ)) =
            ∑ r ∈ Finset.range K,
              (((K - r : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have hrK : r < K := Finset.mem_range.mp hr
        have hnat : K - r = (K - r - 1) + 1 := by
          omega
        rw [hnat]
        push_cast
        ring
      have hdouble :
          (∑ r ∈ Finset.range K,
              2 * (((K - r : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ)))) =
            2 * ∑ r ∈ Finset.range K,
              (((K - r : ℕ) : ℝ) /
                (ξ + (r + 1 : ℕ))) := by
        rw [Finset.mul_sum]
      push_cast at hdouble
      rw [hdouble]
      push_cast at hmerge ⊢
      ring_nf at hmerge ⊢
      linarith

def harmonicPairCorrection (K Z : ℕ) : ℝ :=
  (K : ℝ) / (2 * (Z : ℝ) ^ 2) +
    (1 / (2 * (Z : ℝ) ^ 2)) *
      ∑ r ∈ Finset.range K,
        ((K - r - 1 : ℕ) : ℝ) /
          ((Z : ℝ) + (r + 1 : ℕ))

theorem harmonicRiemannSum_natRatio
    {K Z : ℕ} (hK : 0 < K) (hZ : 0 < Z) :
    (Z : ℝ) ^ 2 *
        harmonicRiemannSum ((K : ℝ) / (Z : ℝ)) (K - 1) =
      ∑ r ∈ Finset.range K,
        (((K - r - 1 : ℕ) : ℝ) ^ 2 /
          ((Z : ℝ) + (r + 1 : ℕ))) := by
  have hKcast : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hZcast : (Z : ℝ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hKsub : K - 1 + 1 = K := by omega
  unfold harmonicRiemannSum
  rw [hKsub, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrK : r < K := Finset.mem_range.mp hr
  unfold harmonicRationalIntegrand
  have hKden : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
    exact_mod_cast hKsub
  rw [hKden]
  have hdiff :
      (K : ℝ) - (r + 1 : ℕ) =
        ((K - r - 1 : ℕ) : ℝ) := by
    have hn : K - (r + 1) = K - r - 1 := by omega
    rw [← hn, Nat.cast_sub (by omega)]
  have hstep :
      (K : ℝ) / (Z : ℝ) * ((r : ℝ) + 1) / (K : ℝ) =
        ((r : ℝ) + 1) / (Z : ℝ) := by
    field_simp [hKcast, hZcast]
  rw [hstep]
  have hnum :
      (K : ℝ) / (Z : ℝ) - ((r : ℝ) + 1) / (Z : ℝ) =
        ((K - r - 1 : ℕ) : ℝ) / (Z : ℝ) := by
    rw [← hdiff]
    push_cast
    ring
  rw [hnum]
  field_simp [hKcast, hZcast]
  push_cast
  ring

theorem pairCost_normalized_eq
    {K Z : ℕ} (hK : 0 < K) (hZ : 0 < Z) :
    pairCost (harmonicFutureLevels (Z : ℝ) 0 K) /
        (Z : ℝ) ^ 2 =
      harmonicNormalizedProcessing
          ((K : ℝ) / (Z : ℝ)) 0 (K - 1) +
        harmonicPairCorrection K Z := by
  have hZreal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hZne : (Z : ℝ) ^ 2 ≠ 0 := by positivity
  rw [pairCost_harmonicFutureLevels_zeroSlack hZreal]
  unfold harmonicNormalizedProcessing harmonicPairCorrection
  simp only [zero_mul, zero_div, add_zero, one_mul]
  have hriemann := harmonicRiemannSum_natRatio hK hZ
  have hsumSplit :
      ∑ r ∈ Finset.range K,
          (((K - r - 1 : ℕ) * (K - r : ℕ) : ℕ) : ℝ) /
            ((Z : ℝ) + (r + 1 : ℕ)) =
        (∑ r ∈ Finset.range K,
          (((K - r - 1 : ℕ) : ℝ) ^ 2 /
            ((Z : ℝ) + (r + 1 : ℕ)))) +
        ∑ r ∈ Finset.range K,
          (((K - r - 1 : ℕ) : ℝ) /
            ((Z : ℝ) + (r + 1 : ℕ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrK : r < K := Finset.mem_range.mp hr
    have hnat : K - r = (K - r - 1) + 1 := by omega
    rw [hnat]
    push_cast
    ring
  rw [hsumSplit]
  unfold triangular
  field_simp [hZne]
  nlinarith [hriemann]

theorem harmonicPairCorrection_nonneg
    {K Z : ℕ} (hZ : 0 < Z) :
    0 ≤ harmonicPairCorrection K Z := by
  have hZreal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  unfold harmonicPairCorrection
  apply add_nonneg
  · positivity
  · apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro r hr
      positivity

theorem harmonicPairCorrection_le
    {K Z : ℕ} (hZ : 0 < Z) :
    harmonicPairCorrection K Z ≤
      (K : ℝ) / (2 * (Z : ℝ) ^ 2) +
        (K : ℝ) ^ 2 / (2 * (Z : ℝ) ^ 3) := by
  have hZreal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hsum :
      (∑ r ∈ Finset.range K,
          ((K - r - 1 : ℕ) : ℝ) /
            ((Z : ℝ) + (r + 1 : ℕ))) ≤
        (K : ℝ) * ((K : ℝ) / (Z : ℝ)) := by
    calc
      (∑ r ∈ Finset.range K,
          ((K - r - 1 : ℕ) : ℝ) /
            ((Z : ℝ) + (r + 1 : ℕ))) ≤
          ∑ _r ∈ Finset.range K,
            ((K : ℝ) / (Z : ℝ)) := by
              apply Finset.sum_le_sum
              intro r hr
              apply div_le_div₀
              · positivity
              · exact_mod_cast Nat.sub_le K (r + 1)
              · exact hZreal
              · push_cast
                linarith
      _ = (K : ℝ) * ((K : ℝ) / (Z : ℝ)) := by
        simp
  unfold harmonicPairCorrection
  have hfactor :
      0 ≤ (1 / (2 * (Z : ℝ) ^ 2)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor
  calc
    (K : ℝ) / (2 * (Z : ℝ) ^ 2) +
          1 / (2 * (Z : ℝ) ^ 2) *
            (∑ r ∈ Finset.range K,
              ((K - r - 1 : ℕ) : ℝ) /
                ((Z : ℝ) + (r + 1 : ℕ))) ≤
        (K : ℝ) / (2 * (Z : ℝ) ^ 2) +
          1 / (2 * (Z : ℝ) ^ 2) *
            ((K : ℝ) * ((K : ℝ) / (Z : ℝ))) :=
      add_le_add_right hmul _
    _ = (K : ℝ) / (2 * (Z : ℝ) ^ 2) +
          (K : ℝ) ^ 2 / (2 * (Z : ℝ) ^ 3) := by
      field_simp

theorem harmonicPairCorrection_scale_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun m : ℕ =>
        harmonicPairCorrection (A * (m + 1)) (B * (m + 1)))
      Filter.atTop (nhds 0) := by
  let C : ℝ :=
    (A : ℝ) / (2 * (B : ℝ) ^ 2) +
      (A : ℝ) ^ 2 / (2 * (B : ℝ) ^ 3)
  apply squeeze_zero
    (g := fun m : ℕ => C / (m + 1 : ℝ))
  · intro m
    apply harmonicPairCorrection_nonneg
    exact Nat.mul_pos hB (by omega)
  · intro m
    have hbound :=
      harmonicPairCorrection_le
        (K := A * (m + 1)) (Z := B * (m + 1))
        (Nat.mul_pos hB (by omega))
    calc
      harmonicPairCorrection (A * (m + 1)) (B * (m + 1)) ≤
          ((A * (m + 1) : ℕ) : ℝ) /
              (2 * ((B * (m + 1) : ℕ) : ℝ) ^ 2) +
            ((A * (m + 1) : ℕ) : ℝ) ^ 2 /
              (2 * ((B * (m + 1) : ℕ) : ℝ) ^ 3) :=
        hbound
      _ = C / (m + 1 : ℝ) := by
        dsimp [C]
        have hs : (m + 1 : ℝ) ≠ 0 := by positivity
        have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
        push_cast
        field_simp [hs, hBreal]
  · have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat C).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun m : ℕ => C / ((m + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht

theorem harmonicPairCost_scale_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun m : ℕ =>
        pairCost
            (harmonicFutureLevels
              ((B * (m + 1) : ℕ) : ℝ) 0
              (A * (m + 1))) /
          ((B * (m + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (harmonicIntegral ((A : ℝ) / (B : ℝ)))) := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hindex :
      Filter.Tendsto
        (fun m : ℕ => A * (m + 1) - 1)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with m hm
    have hscale : m + 1 ≤ A * (m + 1) :=
      Nat.le_mul_of_pos_left (m + 1) hA
    omega
  have hmain :=
    (harmonicNormalizedProcessing_tendsto
      (α := α) (γ := 0) hα).comp hindex
  have hcorrection :=
    harmonicPairCorrection_scale_tendsto hA hB
  have hadd := hmain.add hcorrection
  convert hadd using 1
  · funext m
    have hK : 0 < A * (m + 1) :=
      Nat.mul_pos hA (by omega)
    have hZ : 0 < B * (m + 1) :=
      Nat.mul_pos hB (by omega)
    rw [pairCost_normalized_eq hK hZ]
    congr 2
    dsimp [α]
    have hs : (m + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  · simp [α]

theorem triangular_scale_tendsto
    {A B : ℕ} (hB : 0 < B) :
    Filter.Tendsto
      (fun m : ℕ =>
        triangular ((A + B) * (m + 1)) /
          ((B * (m + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        ((1 + (A : ℝ) / (B : ℝ)) ^ 2 / 2)) := by
  let base : ℝ := (A + B : ℕ) ^ 2 / (2 * (B : ℝ) ^ 2)
  let correction : ℝ := (A + B : ℕ) / (2 * (B : ℝ) ^ 2)
  have hzero :
      Filter.Tendsto
        (fun m : ℕ => correction / (m + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat correction).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun m : ℕ => correction / ((m + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hbase :
      Filter.Tendsto (fun _m : ℕ => base)
        Filter.atTop (nhds base) :=
    tendsto_const_nhds
  have hadd := hbase.add hzero
  convert hadd using 1
  · funext m
    unfold triangular
    dsimp [base, correction]
    have hs : (m + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
  · dsimp [base]
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hBreal]
    ring_nf

theorem harmonicFiniteOffline_scale_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun m : ℕ =>
        harmonicFiniteOffline
            (A * (m + 1)) (B * (m + 1)) 0 /
          ((B * (m + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (harmonicLimitDenominator
          ((A : ℝ) / (B : ℝ)))) := by
  have htri := triangular_scale_tendsto (A := A) hB
  have hpair := harmonicPairCost_scale_tendsto hA hB
  have hadd := htri.add hpair
  convert hadd using 1
  · funext m
    simp only [harmonicFiniteOffline, add_div, Nat.add_mul]
  · rw [harmonicLimitDenominator_eq_integral
      (by positivity :
        0 ≤ (A : ℝ) / (B : ℝ))]
    ring_nf

theorem harmonicFiniteAdvantage_scale_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    Filter.Tendsto
      (fun m : ℕ =>
        harmonicFiniteAdvantage
            (A * (m + 1)) (B * (m + 1)) /
          ((B * (m + 1) : ℕ) : ℝ) ^ 2)
      Filter.atTop
      (nhds
        ((A : ℝ) / (B : ℝ) +
          ((A : ℝ) / (B : ℝ)) ^ 2 / 2)) := by
  let base : ℝ :=
    (A : ℝ) / (B : ℝ) +
      ((A : ℝ) / (B : ℝ)) ^ 2 / 2
  let correction : ℝ :=
    (A : ℝ) / (2 * (B : ℝ) ^ 2)
  have hzero :
      Filter.Tendsto
        (fun m : ℕ => correction / (m + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat correction).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun m : ℕ => correction / ((m + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hbase :
      Filter.Tendsto (fun _m : ℕ => base)
        Filter.atTop (nhds base) :=
    tendsto_const_nhds
  have hsub := hbase.sub hzero
  convert hsub using 1
  · funext m
    unfold harmonicFiniteAdvantage
    dsimp [base, correction]
    have hs : (m + 1 : ℝ) ≠ 0 := by positivity
    have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hs, hBreal]
    ring
  · simp [base]

theorem eventually_harmonicFinite_ratio
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        harmonicLimitRatio ((A : ℝ) / (B : ℝ))) :
    ∀ᶠ m : ℕ in Filter.atTop,
      target *
          harmonicFiniteOffline
            (A * (m + 1)) (B * (m + 1)) 0 ≤
        harmonicFiniteOnline
          (A * (m + 1)) (B * (m + 1)) 0 := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let D : ℝ := harmonicLimitDenominator α
  let G : ℝ := α + α ^ 2 / 2
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hD : 0 < D := by
    exact harmonicLimitDenominator_pos hα
  have hoffline :=
    harmonicFiniteOffline_scale_tendsto hA hB
  have hadvantage :=
    harmonicFiniteAdvantage_scale_tendsto hA hB
  have honline :
      Filter.Tendsto
        (fun m : ℕ =>
          harmonicFiniteOnline
              (A * (m + 1)) (B * (m + 1)) 0 /
            ((B * (m + 1) : ℕ) : ℝ) ^ 2)
        Filter.atTop (nhds (D + G)) := by
    have hadd := hoffline.add hadvantage
    convert hadd using 1
    · funext m
      rw [harmonicFiniteOnline_eq, add_div]
  have htargetScaled :
      Filter.Tendsto
        (fun m : ℕ =>
          target *
            (harmonicFiniteOffline
                (A * (m + 1)) (B * (m + 1)) 0 /
              ((B * (m + 1) : ℕ) : ℝ) ^ 2))
        Filter.atTop (nhds (target * D)) := by
    have h := hoffline.const_mul target
    simpa [α, D] using h
  have hdiff := honline.sub htargetScaled
  have hratioGap : target - 1 < G / D := by
    dsimp [α, D, G]
    unfold harmonicLimitRatio at htarget
    linarith
  have hgapMul :
      (target - 1) * D < G :=
    (lt_div_iff₀ hD).mp hratioGap
  have hlimitPos : 0 < (D + G) - target * D := by
    nlinarith
  have hevent :
      ∀ᶠ m : ℕ in Filter.atTop,
        0 <
          harmonicFiniteOnline
              (A * (m + 1)) (B * (m + 1)) 0 /
              ((B * (m + 1) : ℕ) : ℝ) ^ 2 -
            target *
              (harmonicFiniteOffline
                  (A * (m + 1)) (B * (m + 1)) 0 /
                ((B * (m + 1) : ℕ) : ℝ) ^ 2) := by
    exact hdiff (Ioi_mem_nhds hlimitPos)
  filter_upwards [hevent] with m hm
  have hZ :
      0 < ((B * (m + 1) : ℕ) : ℝ) ^ 2 := by
    positivity
  have hquot :
      0 <
        (harmonicFiniteOnline
            (A * (m + 1)) (B * (m + 1)) 0 -
          target *
            harmonicFiniteOffline
              (A * (m + 1)) (B * (m + 1)) 0) /
          ((B * (m + 1) : ℕ) : ℝ) ^ 2 := by
    convert hm using 1 <;> ring
  have hnum :
      0 <
        harmonicFiniteOnline
            (A * (m + 1)) (B * (m + 1)) 0 -
          target *
            harmonicFiniteOffline
              (A * (m + 1)) (B * (m + 1)) 0 := by
    rcases (div_pos_iff.mp hquot) with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hZ.le hneg.2).elim
  exact (sub_pos.mp hnum).le

theorem positive_rational_as_nat_ratio
    (q : ℚ) (hq : 0 < (q : ℝ)) :
    ∃ A B : ℕ,
      0 < A ∧ 0 < B ∧
        (q : ℝ) = (A : ℝ) / (B : ℝ) := by
  have hqRat : 0 < q := by exact_mod_cast hq
  let A : ℕ := q.num.natAbs
  let B : ℕ := q.den
  have hnum : 0 < q.num := Rat.num_pos.mpr hqRat
  have hA : 0 < A := by
    dsimp [A]
    exact Int.natAbs_pos.mpr hnum.ne'
  have hB : 0 < B := by
    dsimp [B]
    exact q.den_pos
  have hnumCast : (A : ℝ) = (q.num : ℝ) := by
    dsimp [A]
    rw [Nat.cast_natAbs, abs_of_pos]
    exact_mod_cast hnum
  refine ⟨A, B, hA, hB, ?_⟩
  rw [Rat.cast_def, ← hnumCast]

/-- The explicit harmonic oracle discharges the last unconditional
operational interface of the obligatory lower bound. -/
theorem harmonic_adaptive_RStar :
    AdaptiveSizeLowerBound .infinite RStar := by
  intro strategies ε hε N
  obtain ⟨q, hqPos, _hqSpan, hqTarget⟩ :=
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
  have hm : m₀ ≤ m := by
    exact le_max_left _ _
  have hratio :
      (RStar - ε) * harmonicFiniteOffline K Z 0 ≤
        harmonicFiniteOnline K Z 0 := by
    exact hm₀ m hm
  have hZ : 0 < Z := by
    dsimp [Z]
    exact Nat.mul_pos hB (by omega)
  have hsize : N ≤ K + Z := by
    have hNm : N ≤ m := le_max_right _ _
    have hscale : m + 1 ≤ K := by
      dsimp [K]
      exact Nat.le_mul_of_pos_left (m + 1) hA
    omega
  refine ⟨K + Z, hsize,
    harmonicRevelationOracle K Z 0,
    (fun _ => 0), 2 * (K + Z) + 1,
    harmonicRevelationOracle_admissible hZ (le_refl 0),
    harmonic_zero_default_admissible, ?_⟩
  exact harmonicAdaptive_defeats_of_finite_ratio
    hZ (le_refl 0) hratio (strategies (K + Z))

end LowerBound

end

end SchedulingPaper
