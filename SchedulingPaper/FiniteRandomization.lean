import SchedulingPaper.TimedOnline
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Finite randomization against an oblivious input

For the randomized obligatory-testing result it is enough to use a finite
random seed.  In particular, a uniformly random permutation of the labels
can choose the exploration and testing order.  Keeping expectation as an
explicit finite average avoids measure-theoretic side conditions in the
operational part of the proof.
-/

namespace SchedulingPaper
namespace Randomized

noncomputable section

/-- Expectation under the uniform distribution on a nonempty finite seed
space. -/
def uniformAverage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

@[simp] theorem uniformAverage_const {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (c : ℝ) :
    uniformAverage (fun _ : Ω => c) = c := by
  simp [uniformAverage, Fintype.card_ne_zero]

theorem uniformAverage_add {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f g : Ω → ℝ) :
    uniformAverage (fun ω => f ω + g ω) =
      uniformAverage f + uniformAverage g := by
  simp only [uniformAverage, Finset.sum_add_distrib]
  ring

theorem uniformAverage_smul {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (c : ℝ) (f : Ω → ℝ) :
    uniformAverage (fun ω => c * f ω) = c * uniformAverage f := by
  simp only [uniformAverage, ← Finset.mul_sum]
  ring

/-- A finite sum can be interchanged with a uniform finite average. -/
theorem uniformAverage_fintype_sum
    {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [Fintype β]
    (f : Ω → β → ℝ) :
    uniformAverage (fun ω => ∑ b, f ω b) =
      ∑ b, uniformAverage (fun ω => f ω b) := by
  unfold uniformAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

theorem uniformAverage_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun ω _ => h ω
  · positivity

theorem uniformAverage_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ uniformAverage f := by
  simpa using uniformAverage_mono (f := fun _ : Ω => 0) (g := f) h

/-- Uniform averaging is unchanged by a bijective reparameterization of the
seed. -/
theorem uniformAverage_comp_equiv
    {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) :
    uniformAverage (f ∘ e) = uniformAverage f := by
  unfold uniformAverage
  have hsum : (∑ ω : Ω, f (e ω)) = ∑ ω : Ω', f ω :=
    Fintype.sum_equiv e _ _ fun _ => rfl
  change (∑ ω : Ω, f (e ω)) / Fintype.card Ω =
    (∑ ω : Ω', f ω) / Fintype.card Ω'
  rw [hsum]
  have hcard : Fintype.card Ω = Fintype.card Ω' := Fintype.card_congr e
  rw [hcard]

/-- The canonical finite seed used for random-order algorithms. -/
abbrev PermutationSeed (n : ℕ) := Equiv.Perm (Fin n)

/-- Expected completion cost of a finite-seed randomized online strategy on
a fixed (hence oblivious) processing-time assignment. -/
def expectedCompletionCost {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (cap : Cap) (processingTime : Online.Label n → ℝ)
    (strategy : Ω → Online.Strategy n) (fuel : ℕ) : ℝ :=
  uniformAverage fun seed =>
    Online.runCompletionCost cap processingTime
      (Online.run cap (Online.fixedOracle processingTime)
        (strategy seed) fuel)

theorem expectedCompletionCost_nonneg
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {cap : Cap} {processingTime : Online.Label n → ℝ}
    (hcap : cap.Valid)
    (hp : ∀ job, Online.ValueAdmissible cap (processingTime job))
    (strategy : Ω → Online.Strategy n) (fuel : ℕ) :
    0 ≤ expectedCompletionCost cap processingTime strategy fuel := by
  apply uniformAverage_nonneg
  intro seed
  exact Online.completionCost_nonneg hcap hp _

end

end Randomized
end SchedulingPaper
