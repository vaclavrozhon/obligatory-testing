import SchedulingPaper.BlindOptimizationModel
import SchedulingPaper.BlindOptimizationDistribution
import SchedulingPaper.FinPairObjective
import Mathlib.Tactic

/-!
# Finite deterministic upper policies for blind optimization

This module connects the empirical pair envelope to literal finite
completion-time lists.  It proves the `OptimizeAll` guarantee with the
explicit diagonal remainder `(1+u)n/2`; no asymptotic step is hidden in the
distribution notation.
-/

namespace SchedulingPaper
namespace BlindOptimization

noncomputable section

def pairMaxCost (values : List ℝ) : ℝ :=
  listPairObjective id max values

theorem prefixCost_replicate_eq (n : ℕ) (x : ℝ) :
    prefixCost (List.replicate n x) = x * n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, prefixCost_cons,
        List.length_replicate, ih]
      push_cast
      ring

theorem pairMaxCost_perm {xs ys : List ℝ} (h : xs.Perm ys) :
    pairMaxCost xs = pairMaxCost ys := by
  unfold pairMaxCost
  induction h with
  | nil => rfl
  | cons x h ih =>
      simp only [listPairObjective]
      rw [ih, (h.map (max x)).sum_eq]
  | swap x y l =>
      simp only [listPairObjective, List.map_cons, List.sum_cons]
      rw [max_comm x y]
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem prefixCost_le_pairMaxCost (values : List ℝ) :
    prefixCost values ≤ pairMaxCost values := by
  induction values with
  | nil => simp [pairMaxCost, listPairObjective]
  | cons x xs ih =>
      simp only [prefixCost_cons, pairMaxCost, listPairObjective]
      simp only [id_eq]
      have hrow : (xs.length : ℝ) * x ≤ (xs.map (max x)).sum := by
        calc
          (xs.length : ℝ) * x = (xs.map fun _ ↦ x).sum := by simp
          _ ≤ (xs.map (max x)).sum :=
            List.sum_le_sum fun y hy ↦ le_max_left x y
      dsimp [pairMaxCost] at ih
      linarith

theorem pairCost_unit_lower (values : List ℝ)
    (hunit : ∀ x ∈ values, (1 : ℝ) ≤ x) :
    prefixCost (List.replicate values.length 1) ≤ pairCost values := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      have hx : 1 ≤ x := hunit x (by simp)
      have hxs : ∀ y ∈ xs, (1 : ℝ) ≤ y := by
        intro y hy
        exact hunit y (by simp [hy])
      have hrow : (xs.length : ℝ) ≤ (xs.map (min x)).sum := by
        calc
          (xs.length : ℝ) = (xs.map fun _ ↦ (1 : ℝ)).sum := by simp
          _ ≤ (xs.map (min x)).sum := by
            apply List.sum_le_sum
            intro y hy
            exact le_min hx (hxs y hy)
      have htail := ih hxs
      simp only [List.length_cons, List.replicate_succ, prefixCost_cons,
        List.length_replicate, pairCost, List.sum_cons, pairMinCost_cons]
      unfold pairCost at htail
      push_cast
      linarith

private theorem sum_row_split_lt
    {n : ℕ} (f : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j, f i j) =
      f i i +
        ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j +
        ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), f i j := by
  classical
  let upper := Finset.univ.filter (fun j : Fin n ↦ i < j)
  let lower := Finset.univ.filter (fun j : Fin n ↦ j < i)
  have hdisjoint : Disjoint upper lower := by
    apply Finset.disjoint_left.mpr
    intro j hjUpper hjLower
    simp only [upper, lower, Finset.mem_filter, Finset.mem_univ,
      true_and] at hjUpper hjLower
    exact (not_lt_of_ge hjUpper.le hjLower)
  have hunion : upper ∪ lower = Finset.univ.erase i := by
    ext j
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro (hij | hji)
      · exact ⟨ne_of_gt hij, trivial⟩
      · exact ⟨ne_of_lt hji, trivial⟩
    · rintro ⟨hji, _⟩
      rcases lt_trichotomy i j with hij | heq | hji'
      · exact Or.inl hij
      · exact (hji heq.symm).elim
      · exact Or.inr hji'
  calc
    (∑ j, f i j) = f i i + ∑ j ∈ Finset.univ.erase i, f i j :=
      (Finset.add_sum_erase Finset.univ (fun j ↦ f i j)
        (Finset.mem_univ i)).symm
    _ = f i i + ((∑ j ∈ upper, f i j) +
        ∑ j ∈ lower, f i j) := by
      rw [← Finset.sum_union hdisjoint, hunion]
    _ = _ := by dsimp [upper, lower]; ring

private theorem sum_lower_triangle_transpose
    {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), f i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f j i := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

theorem symmetric_double_sum
    {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + 2 *
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j := by
  simp_rw [sum_row_split_lt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_lower_triangle_transpose]
  have htranspose :
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f j i) =
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hsymm j i
  rw [htranspose]
  ring

theorem two_mul_pairMaxCost_ofFn {n : ℕ} (values : Fin n → ℝ) :
    2 * pairMaxCost (List.ofFn values) =
      (∑ i, ∑ j, max (values i) (values j)) + ∑ i, values i := by
  have hfinite := finSelfPairSum_eq_listPairObjective id max values
  have hdouble := symmetric_double_sum
    (fun i j ↦ max (values i) (values j))
    (fun i j ↦ max_comm _ _)
  dsimp [pairMaxCost]
  rw [← hfinite]
  simp only [id_eq, max_self] at hdouble ⊢
  linarith

theorem two_mul_pairCost_ofFn {n : ℕ} (values : Fin n → ℝ) :
    2 * pairCost (List.ofFn values) =
      (∑ i, ∑ j, min (values i) (values j)) + ∑ i, values i := by
  rw [pairCost_ofFn_eq_finSelfPairSum]
  have hdouble := symmetric_double_sum
    (fun i j ↦ min (values i) (values j))
    (fun i j ↦ min_comm _ _)
  simp only [min_self] at hdouble
  linarith

theorem onlineEffective_eq_distributionEffective
    {u p : ℝ} : Online.effectiveLength u p = effectiveLength u p := by
  unfold Online.effectiveLength effectiveLength
  calc
    min u (1 + p) = min (1 + (u - 1)) (1 + p) := by ring_nf
    _ = 1 + min (u - 1) p := (add_min 1 (u - 1) p).symm

/-- Finite `OptimizeAll` upper bound for every label order.  `durations`
is the literal optimized-block order; the permutation hypothesis is exactly
what the operational strategy supplies. -/
theorem optimizeAll_finite_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 2 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u)
    (durations : List ℝ)
    (hperm : durations.Perm
      (List.ofFn fun job ↦ 1 + processing job)) :
    prefixCost durations ≤
      deterministicOptimizeAllRatio u * Online.offlineCost u processing +
        (1 + u) * n / 2 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let R := deterministicOptimizeAllRatio u
  let onlinePair := deterministicOnlinePair processing
  let offlinePair := empiricalOfflinePair u processing
  have hR : 0 ≤ R := (deterministicOptimizeAllRatio_pos hu).le
  have hratio : onlinePair ≤ R * offlinePair := by
    have hbound := deterministicDistributionRatio_le_curve processing hu hp
    have hoffbase : 0 < 1 + (u - 1) *
        (empiricalMean processing / u) ^ 2 := by
      have : 0 ≤ (u - 1) * (empiricalMean processing / u) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    have hoff : 0 < offlinePair := hoffbase.trans_le
      (empiricalOfflinePair_ge_mean_square processing (by linarith) hp)
    dsimp [deterministicDistributionRatio, onlinePair, offlinePair] at hbound
    exact (div_le_iff₀ hoff).mp hbound
  have hpairMax :
      pairMaxCost (List.ofFn fun job ↦ 1 + processing job) =
        (n : ℝ) ^ 2 / 2 * onlinePair +
          (∑ job, (1 + processing job)) / 2 := by
    have htwo := two_mul_pairMaxCost_ofFn
      (fun job : Fin n ↦ 1 + processing job)
    dsimp [deterministicOnlinePair, onlinePair]
    simp only [Fintype.card_fin]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnreal] at htwo ⊢
    linarith
  have hoffline :
      Online.offlineCost u processing =
        (n : ℝ) ^ 2 / 2 * offlinePair +
          (∑ job, Online.effectiveLength u (processing job)) / 2 := by
    unfold Online.offlineCost
    have htwo := two_mul_pairCost_ofFn
      (fun job : Fin n ↦ Online.effectiveLength u (processing job))
    dsimp [empiricalOfflinePair, offlinePair]
    simp only [Fintype.card_fin]
    simp_rw [onlineEffective_eq_distributionEffective] at htwo ⊢
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hnreal] at htwo ⊢
    linarith
  have hdiagOnline :
      (∑ job, (1 + processing job)) / 2 ≤ (1 + u) * n / 2 := by
    have hsum : (∑ job, (1 + processing job)) ≤
        ∑ _job : Fin n, (1 + u) :=
      Finset.sum_le_sum fun job hjob ↦ by linarith [(hp job).2]
    have hdiv := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
    convert hdiv using 1 <;> simp <;> ring
  have hoffDiag : 0 ≤
      (∑ job, Online.effectiveLength u (processing job)) / 2 := by
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro job hjob
      unfold Online.effectiveLength
      exact le_min (by linarith) (by linarith [(hp job).1])
    · norm_num
  calc
    prefixCost durations ≤ pairMaxCost durations := prefixCost_le_pairMaxCost _
    _ = pairMaxCost (List.ofFn fun job ↦ 1 + processing job) :=
      pairMaxCost_perm hperm
    _ = (n : ℝ) ^ 2 / 2 * onlinePair +
          (∑ job, (1 + processing job)) / 2 := hpairMax
    _ ≤ (n : ℝ) ^ 2 / 2 * (R * offlinePair) +
          (1 + u) * n / 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hratio (by positivity)) hdiagOnline
    _ ≤ R * Online.offlineCost u processing + (1 + u) * n / 2 := by
      rw [hoffline]
      have hdrop := mul_nonneg hR hoffDiag
      nlinarith

/-- Finite Raw upper bound.  For `u≤1` the same argument becomes equality
with the clairvoyant effective lengths; the branch used by the deterministic
curve is `1≤u≤2`. -/
theorem raw_finite_upper
    {n : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job) :
    prefixCost (List.replicate n u) ≤
      u * Online.offlineCost u processing := by
  have heffective : ∀ x ∈
      (List.ofFn fun job : Fin n ↦ Online.effectiveLength u (processing job)),
      (1 : ℝ) ≤ x := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨job, rfl⟩
    unfold Online.effectiveLength
    exact le_min hu (by linarith [hp0 job])
  have hoff := pairCost_unit_lower
    (List.ofFn fun job : Fin n ↦ Online.effectiveLength u (processing job))
    heffective
  simp only [List.length_ofFn] at hoff
  unfold Online.offlineCost
  rw [prefixCost_replicate_eq] at hoff ⊢
  have htri : 0 ≤ (n : ℝ) * (n + 1) / 2 := by positivity
  nlinarith

/-- Operational form of the finite `OptimizeAll` upper bound. -/
theorem optimizeAllStrategy_finite_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 2 ≤ u)
    (processing : Fin n → ℝ)
    (hp : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u) :
    Online.runCost u processing (Online.optimizeAllStrategy n) n ≤
      deterministicOptimizeAllRatio u * Online.offlineCost u processing +
        (1 + u) * n / 2 := by
  unfold Online.runCost Online.completionCost
  apply optimizeAll_finite_upper hn hu processing hp
  exact Online.optimizeAllStrategy_duration_perm u processing

/-- Operational form of the finite `Raw` upper bound. -/
theorem rawStrategy_finite_upper
    {n : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job) :
    Online.runCost u processing (Online.rawStrategy n) n ≤
      u * Online.offlineCost u processing := by
  unfold Online.runCost Online.completionCost
  rw [Online.rawStrategy_duration_list]
  exact raw_finite_upper hu processing hp0

/-- For `0<u≤1`, running raw is exactly clairvoyant-optimal on every
finite input, not merely asymptotically optimal. -/
theorem rawStrategy_exact_of_cap_le_one
    {n : ℕ} {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1)
    (processing : Fin n → ℝ)
    (hp0 : ∀ job, 0 ≤ processing job) :
    Online.runCost u processing (Online.rawStrategy n) n =
      Online.offlineCost u processing := by
  unfold Online.runCost Online.completionCost Online.offlineCost
  rw [Online.rawStrategy_duration_list]
  have heffective :
      (List.ofFn fun job : Fin n ↦ Online.effectiveLength u (processing job)) =
        List.replicate n u := by
    apply List.ext_get
    · simp
    · intro k hkLeft hkRight
      simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_replicate]
      unfold Online.effectiveLength
      rw [min_eq_left]
      linarith [hp0 ⟨k, by simpa using hkLeft⟩]
  rw [heffective]
  exact prefixCost_eq_pairCost_of_pairwise (by simp)

/-- One operational theorem covering all three upper branches of the exact
deterministic curve.  The additive term is linear in the instance size and
is needed only by `OptimizeAll`. -/
theorem deterministicCurve_operational_upper
    {u : ℝ} (hu0 : 0 < u) :
    ∃ strategy : ∀ n, Online.Strategy n,
      (∀ n, Online.CompletesAll u (strategy n)) ∧
      ∀ n (processing : Fin n → ℝ),
        (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) →
        Online.runCost u processing (strategy n) n ≤
          deterministicCurve u * Online.offlineCost u processing +
            (1 + u) * n / 2 := by
  by_cases hu1 : u ≤ 1
  · refine ⟨fun n ↦ Online.rawStrategy n, ?_, ?_⟩
    · intro n
      exact Online.rawStrategy_completesAll u
    · intro n processing hp
      have hexact := rawStrategy_exact_of_cap_le_one hu0 hu1 processing
        (fun job ↦ (hp job).1)
      rw [deterministicCurve_of_le_one hu1, hexact]
      have hrem : 0 ≤ (1 + u) * (n : ℝ) / 2 := by positivity
      linarith
  · have hu1' : 1 < u := lt_of_not_ge hu1
    by_cases hu2 : u ≤ 2
    · refine ⟨fun n ↦ Online.rawStrategy n, ?_, ?_⟩
      · intro n
        exact Online.rawStrategy_completesAll u
      · intro n processing hp
        have hraw := rawStrategy_finite_upper hu1'.le processing
          (fun job ↦ (hp job).1)
        rw [deterministicCurve_of_one_lt_le_two hu1' hu2]
        have hrem : 0 ≤ (1 + u) * (n : ℝ) / 2 := by positivity
        linarith
    · have hu2' : 2 < u := lt_of_not_ge hu2
      refine ⟨fun n ↦ Online.optimizeAllStrategy n, ?_, ?_⟩
      · intro n
        exact Online.optimizeAllStrategy_completesAll u
      · intro n processing hp
        rw [deterministicCurve_of_two_lt hu2']
        by_cases hn : n = 0
        · subst n
          simp [Online.runCost, Online.run, Online.runFuel,
            Online.completionCost, Online.offlineCost, Online.Config.initial]
        · exact optimizeAllStrategy_finite_upper (Nat.pos_of_ne_zero hn)
            hu2'.le processing hp

end

end BlindOptimization
end SchedulingPaper
