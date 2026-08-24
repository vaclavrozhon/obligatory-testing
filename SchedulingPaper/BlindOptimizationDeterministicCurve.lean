import SchedulingPaper.BlindOptimizationHiddenStopping

/-!
# Operational exact deterministic curve for blind optimization

The upper policies and the hidden-stopping adversary are assembled here at
the level of literal finite runs.  For every deterministic strategy and
every positive instance size, the adversary freezes one admissible binary
input on which the claimed curve is attained up to an explicit linear term.
-/

namespace SchedulingPaper
namespace BlindOptimization

open Online
open HiddenStopping

noncomputable section

theorem prefixCost_replicate_le_of_entries
    (a : ℝ) (values : List ℝ) (hvalues : ∀ x ∈ values, a ≤ x) :
    prefixCost (List.replicate values.length a) ≤ prefixCost values := by
  induction values with
  | nil => simp
  | cons x xs ih =>
      have hx : a ≤ x := hvalues x (by simp)
      have hxs : ∀ y ∈ xs, a ≤ y := by
        intro y hy
        exact hvalues y (by simp [hy])
      have htail := ih hxs
      simp only [List.length_cons, List.replicate_succ, prefixCost_cons,
        List.length_replicate] at htail ⊢
      have hcoef : 0 ≤ (xs.length + 1 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hx hcoef]

/-- The low-cap branch needs no adversarial labels: on the all-zero input
every completed block lasts at least `u`, while the clairvoyant benchmark is
the all-`u` triangular schedule. -/
theorem deterministicCurve_operational_lower_of_cap_le_one
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (n : ℕ)
    (strategy : Online.Strategy n) (hcomplete : Online.CompletesAll u strategy) :
    ∃ processing : Fin n → ℝ,
      (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) ∧
      Online.runCost u processing strategy n ≥
        deterministicCurve u * Online.offlineCost u processing -
          (2 * u ^ 2 + u) * n := by
  let processing : Fin n → ℝ := fun _ ↦ 0
  have hadmissible : ∀ job, processing job ∈ Set.Icc (0 : ℝ) u := by
    intro job
    exact ⟨le_rfl, hu0.le⟩
  refine ⟨processing, hadmissible, ?_⟩
  let transcript := (Online.run processing strategy n).config.transcript
  have hfixed : Online.Completes processing strategy :=
    hcomplete processing hadmissible
  have hlength : transcript.length = n :=
    Online.transcript_length_eq_n_of_completes hfixed
  have htruth := Online.run_truthful processing strategy n
  have hentries : ∀ x ∈ transcript.map (Online.Observation.duration u), u ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨observation, hobservation, rfl⟩
    cases observation with
    | rawCompleted job => simp [Online.Observation.duration]
    | optimizedCompleted job p =>
        have hp := htruth job p hobservation
        simp [Online.Observation.duration, processing] at hp ⊢
        linarith
  have hrunLower : u * n * (n + 1) / 2 ≤
      Online.runCost u processing strategy n := by
    have hprefix := prefixCost_replicate_le_of_entries u
      (transcript.map (Online.Observation.duration u)) hentries
    rw [List.length_map, hlength, prefixCost_replicate_eq] at hprefix
    exact hprefix
  have hoffline : Online.offlineCost u processing = u * n * (n + 1) / 2 := by
    have hexact := rawStrategy_exact_of_cap_le_one hu0 hu1 processing
      (fun _ ↦ le_rfl)
    have hraw : Online.runCost u processing (Online.rawStrategy n) n =
        u * n * (n + 1) / 2 := by
      unfold Online.runCost Online.completionCost
      rw [Online.rawStrategy_duration_list, prefixCost_replicate_eq]
    linarith
  rw [deterministicCurve_of_le_one hu1, hoffline]
  have hrem : 0 ≤ (2 * u ^ 2 + u) * (n : ℝ) := by positivity
  nlinarith

/-- The hidden-stopping lower bound for the two nontrivial branches of the
deterministic curve.  This quantifies over arbitrary transcript-dependent
deterministic strategies, including adaptive mixtures of raw and optimized
blocks. -/
theorem deterministicCurve_operational_lower_of_one_lt
    {u : ℝ} (hu : 1 < u) (n : ℕ) (hn : 0 < n)
    (strategy : Online.Strategy n) (hcomplete : Online.CompletesAll u strategy) :
    ∃ processing : Fin n → ℝ,
      (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) ∧
      Online.runCost u processing strategy n ≥
        deterministicCurve u * Online.offlineCost u processing -
          (2 * u ^ 2 + u) * n := by
  by_cases hu2 : u ≤ 2
  · let alpha : ℝ := 1 / u
    let processing := HiddenStopping.frozenProcessing n u alpha strategy
    have ha0 : 0 < alpha := by dsimp [alpha]; positivity
    have ha1 : alpha < 1 := by
      dsimp [alpha]
      rw [div_lt_one (by linarith : 0 < u)]
      linarith
    refine ⟨processing,
      HiddenStopping.frozenProcessing_admissible n (by linarith) strategy, ?_⟩
    let full :=
      (Replay.adaptiveRun (HiddenStopping.oracle n u alpha) strategy n).result.config.transcript
    by_cases hcrossed : HiddenStopping.Crossed n u alpha full
    · obtain ⟨v, ell, hvell, hvlt, hcost, hoffline, hyAlpha, hyOne,
          hyOvershoot⟩ := HiddenStopping.crossed_run_witness hn hu ha0 ha1
          hcomplete hcrossed
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hv0 : (0 : ℝ) ≤ v := by positivity
      have hell0 : (0 : ℝ) ≤ ell := by positivity
      have hvellR : (v : ℝ) + ell ≤ n := by exact_mod_cast hvell
      have hremaining : (0 : ℝ) < n - v := by
        have : (v : ℝ) < n := by exact_mod_cast hvlt
        linarith
      have hlower := raw_branch_crossing_lower hu hu2 hnR hv0 hell0
        hvellR hremaining hyAlpha hyOne hyOvershoot
      dsimp [processing] at hcost hoffline ⊢
      rw [deterministicCurve_of_one_lt_le_two hu hu2]
      calc
        Online.runCost u (HiddenStopping.frozenProcessing n u alpha strategy)
            strategy n ≥ stoppingAlgorithmCost u n v ell := hcost
        _ ≥ u * stoppingOfflineCost u n ell -
            (2 * u ^ 2 + u) * n := hlower
        _ = u * Online.offlineCost u
              (HiddenStopping.frozenProcessing n u alpha strategy) -
            (2 * u ^ 2 + u) * n := by rw [hoffline]
    · have hexact := HiddenStopping.uncrossed_run_exact hu ha0 ha1
          hcomplete hcrossed
      dsimp [processing] at hexact ⊢
      rw [deterministicCurve_of_one_lt_le_two hu hu2, hexact.1, hexact.2]
      have hrem : 0 ≤ (2 * u ^ 2 + u) * (n : ℝ) := by positivity
      linarith
  · have hu2' : 2 < u := lt_of_not_ge hu2
    let R := deterministicOptimizeAllRatio u
    let alpha := u / (u + R * (u - 1))
    let processing := HiddenStopping.frozenProcessing n u alpha strategy
    have hR0 : 0 < R := deterministicOptimizeAllRatio_pos hu2'.le
    have hRu : R ≤ u := deterministicOptimizeAllRatio_le_u hu2'.le
    have hden : 0 < u + R * (u - 1) := by
      exact add_pos_of_pos_of_nonneg (by linarith)
        (mul_nonneg hR0.le (by linarith))
    have ha0 : 0 < alpha := by
      dsimp [alpha]
      exact div_pos (by linarith) hden
    have ha1 : alpha < 1 := by
      dsimp [alpha]
      rw [div_lt_one hden]
      nlinarith [mul_pos hR0 (by linarith : 0 < u - 1)]
    refine ⟨processing,
      HiddenStopping.frozenProcessing_admissible n (by linarith) strategy, ?_⟩
    let full :=
      (Replay.adaptiveRun (HiddenStopping.oracle n u alpha) strategy n).result.config.transcript
    by_cases hcrossed : HiddenStopping.Crossed n u alpha full
    · obtain ⟨v, ell, hvell, hvlt, hcost, hoffline, hyAlpha, hyOne,
          hyOvershoot⟩ := HiddenStopping.crossed_run_witness hn hu ha0 ha1
          hcomplete hcrossed
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hv0 : (0 : ℝ) ≤ v := by positivity
      have hell0 : (0 : ℝ) ≤ ell := by positivity
      have hvellR : (v : ℝ) + ell ≤ n := by exact_mod_cast hvell
      have hremaining : (0 : ℝ) < n - v := by
        have : (v : ℝ) < n := by exact_mod_cast hvlt
        linarith
      have hlower := optimizeAll_branch_crossing_lower hu2'.le hnR hv0
        hell0 hvellR hremaining hyAlpha hyOne hyOvershoot
      dsimp [processing] at hcost hoffline ⊢
      rw [deterministicCurve_of_two_lt hu2']
      dsimp only at hlower
      calc
        Online.runCost u (HiddenStopping.frozenProcessing n u alpha strategy)
            strategy n ≥ stoppingAlgorithmCost u n v ell := hcost
        _ ≥ deterministicOptimizeAllRatio u * stoppingOfflineCost u n ell -
            (2 * u ^ 2 + u) * n := hlower
        _ = deterministicOptimizeAllRatio u * Online.offlineCost u
              (HiddenStopping.frozenProcessing n u alpha strategy) -
            (2 * u ^ 2 + u) * n := by rw [hoffline]
    · have hexact := HiddenStopping.uncrossed_run_exact hu ha0 ha1
          hcomplete hcrossed
      dsimp [processing] at hexact ⊢
      rw [deterministicCurve_of_two_lt hu2', hexact.1, hexact.2]
      have htri : 0 ≤ (n : ℝ) * (n + 1) / 2 := by positivity
      have hrem : 0 ≤ (2 * u ^ 2 + u) * (n : ℝ) := by positivity
      nlinarith

/-- All three branches of the finite deterministic lower bound. -/
theorem deterministicCurve_operational_lower
    {u : ℝ} (hu0 : 0 < u) (n : ℕ) (hn : 0 < n)
    (strategy : Online.Strategy n) (hcomplete : Online.CompletesAll u strategy) :
    ∃ processing : Fin n → ℝ,
      (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) ∧
      Online.runCost u processing strategy n ≥
        deterministicCurve u * Online.offlineCost u processing -
          (2 * u ^ 2 + u) * n := by
  by_cases hu1 : u ≤ 1
  · exact deterministicCurve_operational_lower_of_cap_le_one hu0 hu1 n
      strategy hcomplete
  · exact deterministicCurve_operational_lower_of_one_lt (lt_of_not_ge hu1)
      n hn strategy hcomplete

/-- Finite operational exactness: a canonical strategy attains the displayed
curve with a linear remainder, and every completing deterministic strategy
has an admissible fixed input attaining the same curve up to a linear
remainder. -/
theorem deterministicCurve_operational_exact
    {u : ℝ} (hu0 : 0 < u) :
    (∃ strategy : ∀ n, Online.Strategy n,
      (∀ n, Online.CompletesAll u (strategy n)) ∧
      ∀ n (processing : Fin n → ℝ),
        (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) →
        Online.runCost u processing (strategy n) n ≤
          deterministicCurve u * Online.offlineCost u processing +
            (1 + u) * n / 2) ∧
    (∀ n, 0 < n → ∀ strategy : Online.Strategy n,
      Online.CompletesAll u strategy →
      ∃ processing : Fin n → ℝ,
        (∀ job, processing job ∈ Set.Icc (0 : ℝ) u) ∧
        Online.runCost u processing strategy n ≥
          deterministicCurve u * Online.offlineCost u processing -
            (2 * u ^ 2 + u) * n) := by
  constructor
  · exact deterministicCurve_operational_upper hu0
  · intro n hn strategy hcomplete
    exact deterministicCurve_operational_lower hu0 n hn strategy hcomplete

end

end BlindOptimization
end SchedulingPaper
