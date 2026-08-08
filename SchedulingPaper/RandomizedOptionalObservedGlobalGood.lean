import SchedulingPaper.RandomizedOptionalObservedTrace

/-!
# Global simultaneous urn events for observed optional policies

The checkpoint estimates in `RandomizedOptionalSimultaneousUrn` include a
deterministic extension over the unregulated suffix.  This file reindexes
those global (all-prefix) events through the adaptive reveal bijection.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedTrace

open ObservedOnline
open TraceBijection
open Randomized

noncomputable section

theorem adaptivePolicy_all_categories_global_prefix_probability_le
    {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 1 < n) (p : Fin n → ℝ) (policy : CompletePolicy p)
    (value : κ → Fin n → ℝ) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hvalue0 : ∀ c i, 0 ≤ value c i)
    (hvalue1 : ∀ c i, value c i ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ => ∃ c, ∃ j : Fin n,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card <
        |(∑ k ∈ positionsThrough j,
            compiledTestSelector p policy k
                (revealOrder (touchTrace p policy) σ) *
              value c (revealOrder (touchTrace p policy) σ k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                (revealOrder (touchTrace p policy) σ)|) ≤
      Fintype.card κ *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) := by
  let select := compiledTestSelector p policy
  let bad : Equiv.Perm (Fin n) → Prop := fun reveal =>
    ∃ c, ∃ j : Fin n,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card <
        |(∑ k ∈ positionsThrough j,
            select k reveal * value c (reveal k)) -
          populationMean (value c) *
            ∑ k ∈ positionsThrough j, select k reveal|
  have hcanonical : uniformProbability bad ≤
      Fintype.card κ *
        ((backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
          (backwardCheckpoints suffixStep cutoff).card *
            ((2 / (suffixPositions cutoff).card) / r ^ 2)) := by
    exact predictable_selected_all_categories_global_prefix_regular_probability_le
      hn value select cutoff hMartingaleStep hSuffixStep
      (compiledTestSelector_predictable p policy) hvalue0 hvalue1
      (fun k reveal => compiledTestSelector_nonneg p policy k reveal)
      (fun k reveal => compiledTestSelector_le_one p policy k reveal)
      he hr
  calc
    uniformProbability (fun σ => ∃ c, ∃ j : Fin n,
        e + martingaleStep +
            (r + 2 * suffixStep /
              (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card <
          |(∑ k ∈ positionsThrough j,
              compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                value c (revealOrder (touchTrace p policy) σ k)) -
            populationMean (value c) *
              ∑ k ∈ positionsThrough j,
                compiledTestSelector p policy k
                  (revealOrder (touchTrace p policy) σ)|) =
        uniformProbability bad := by
      simpa [bad, select, Function.comp_def] using
        uniformProbability_adaptive_revealOrder p policy bad
    _ ≤ _ := hcanonical

theorem adaptivePolicy_blind_global_prefix_probability_le
    {n : ℕ} (hn : 1 < n) (p : Fin n → ℝ)
    (policy : CompletePolicy p) (value : Fin n → ℝ) (cutoff : Fin n)
    {martingaleStep suffixStep : ℕ}
    (hMartingaleStep : 0 < martingaleStep)
    (hSuffixStep : 0 < suffixStep)
    (hvalue0 : ∀ i, 0 ≤ value i) (hvalue1 : ∀ i, value i ≤ 1)
    {e r : ℝ} (he : 0 < e) (hr : 0 < r) :
    uniformProbability (fun σ => ∃ j : Fin n,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card <
        |(∑ k ∈ positionsThrough j,
            compiledBlindSelector p policy k
                (revealOrder (touchTrace p policy) σ) *
              value (revealOrder (touchTrace p policy) σ k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                (revealOrder (touchTrace p policy) σ)|) ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
  let select := compiledBlindSelector p policy
  let bad : Equiv.Perm (Fin n) → Prop := fun reveal =>
    ∃ j : Fin n,
      e + martingaleStep +
          (r + 2 * suffixStep /
            (suffixPositions cutoff).card) * n +
          (suffixPositions cutoff).card <
        |(∑ k ∈ positionsThrough j,
            select k reveal * value (reveal k)) -
          populationMean value *
            ∑ k ∈ positionsThrough j, select k reveal|
  have hcanonical : uniformProbability bad ≤
      (backwardCheckpoints martingaleStep cutoff).card * (n / e ^ 2) +
        (backwardCheckpoints suffixStep cutoff).card *
          ((2 / (suffixPositions cutoff).card) / r ^ 2) := by
    exact predictable_selected_global_prefix_regular_probability_le
      hn value select cutoff hMartingaleStep hSuffixStep
      (compiledBlindSelector_predictable p policy) hvalue0 hvalue1
      (compiledBlindSelector_nonneg p policy)
      (compiledBlindSelector_le_one p policy) he hr
  calc
    uniformProbability (fun σ => ∃ j : Fin n,
        e + martingaleStep +
            (r + 2 * suffixStep /
              (suffixPositions cutoff).card) * n +
            (suffixPositions cutoff).card <
          |(∑ k ∈ positionsThrough j,
              compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ) *
                value (revealOrder (touchTrace p policy) σ k)) -
            populationMean value *
              ∑ k ∈ positionsThrough j,
                compiledBlindSelector p policy k
                  (revealOrder (touchTrace p policy) σ)|) =
        uniformProbability bad := by
      simpa [bad, select, Function.comp_def] using
        uniformProbability_adaptive_revealOrder p policy bad
    _ ≤ _ := hcanonical

end

end ObservedTrace
end RandomizedOptional
end SchedulingPaper
