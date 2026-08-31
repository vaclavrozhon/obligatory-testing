import SchedulingPaper.FiniteRandomization
import SchedulingPaper.RandomizedObligatoryLower
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# General private randomness

The executable policies in the paper use finite uniform random seeds.  The
comparison algorithms quantified over in the mathematical statements may use
an arbitrary probability space.  This file supplies the measure-theoretic
bridge needed for that stronger quantifier.

Only real-valued run costs are integrated.  Measurability and integrability
are stated for those costs, rather than for the function-valued strategy
itself.  This is the standard semantic condition for an expected-cost
statement and also covers continuous and infinite random tapes.
-/

namespace SchedulingPaper
namespace Randomized

open MeasureTheory

noncomputable section

/-- Expected value with respect to an arbitrary probability law on private
seeds. -/
def generalExpectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω ∂μ

@[simp] theorem generalExpectation_const
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) :
    generalExpectation μ (fun _ : Ω => c) = c := by
  simp [generalExpectation]

theorem generalExpectation_add
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    generalExpectation μ (fun ω => f ω + g ω) =
      generalExpectation μ f + generalExpectation μ g := by
  exact integral_add hf hg

theorem generalExpectation_sub
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    generalExpectation μ (fun ω => f ω - g ω) =
      generalExpectation μ f - generalExpectation μ g := by
  exact integral_sub hf hg

theorem generalExpectation_mono
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    generalExpectation μ f ≤ generalExpectation μ g := by
  exact integral_mono hf hg hfg

/-- A finite uniform average of integrable random variables is integrable. -/
theorem integrable_uniformAverage
    {Ω Inputs : Type*} [MeasurableSpace Ω]
    [Fintype Inputs] [Nonempty Inputs]
    (μ : Measure Ω) (f : Inputs → Ω → ℝ)
    (hf : ∀ input, Integrable (f input) μ) :
    Integrable (fun ω => uniformAverage fun input => f input ω) μ := by
  unfold uniformAverage
  exact (integrable_finsetSum Finset.univ fun input _ => hf input).div_const _

/-- Integration over an arbitrary seed law commutes with a finite uniform
input average. -/
theorem generalExpectation_uniformAverage_comm
    {Ω Inputs : Type*} [MeasurableSpace Ω]
    [Fintype Inputs] [Nonempty Inputs]
    (μ : Measure Ω) (f : Inputs → Ω → ℝ)
    (hf : ∀ input, Integrable (f input) μ) :
    generalExpectation μ (fun ω => uniformAverage fun input => f input ω) =
      uniformAverage fun input => generalExpectation μ (f input) := by
  unfold generalExpectation uniformAverage
  rw [integral_div]
  rw [integral_finsetSum Finset.univ (fun input _ => hf input)]

/-- General-probability Yao selection.  The private seed may live in any
probability space; only the finitely many input-cost random variables must be
integrable. -/
theorem general_yao_select_fixed_input
    {Inputs Ω : Type*} [Fintype Inputs] [Nonempty Inputs]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cost : Inputs → Ω → ℝ) (hcost : ∀ input, Integrable (cost input) μ)
    {L : ℝ}
    (hseed : ∀ seed, L ≤ uniformAverage fun input => cost input seed) :
    ∃ input, L ≤ generalExpectation μ (cost input) := by
  have hconst : Integrable (fun _seed : Ω => L) μ := integrable_const L
  have havg : Integrable
      (fun seed => uniformAverage fun input => cost input seed) μ :=
    integrable_uniformAverage μ cost hcost
  have hjoint : L ≤ generalExpectation μ
      (fun seed => uniformAverage fun input => cost input seed) := by
    rw [← generalExpectation_const μ L]
    exact generalExpectation_mono μ hconst havg hseed
  rw [generalExpectation_uniformAverage_comm μ cost hcost] at hjoint
  obtain ⟨input, hinput⟩ :=
    RandomizedObligatory.exists_uniformAverage_le
      (fun input => generalExpectation μ (cost input))
  exact ⟨input, hjoint.trans hinput⟩

/-- Uniform-input ratio form of general-probability Yao selection. -/
theorem general_yao_select_uniform_ratio
    {Inputs Ω : Type*} [Fintype Inputs] [Nonempty Inputs]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cost : Inputs → Ω → ℝ) (hcost : ∀ input, Integrable (cost input) μ)
    (opt : Inputs → ℝ) {L O c : ℝ}
    (hlower : L ≤ uniformAverage
      (fun input => generalExpectation μ (cost input)))
    (hopt : uniformAverage opt = O) (hcompare : c * O ≤ L) :
    ∃ input, c * opt input ≤ generalExpectation μ (cost input) := by
  let excess : Inputs → Ω → ℝ := fun input seed =>
    cost input seed - c * opt input
  have hexcessInt : ∀ input, Integrable (excess input) μ := by
    intro input
    exact (hcost input).sub (integrable_const (c * opt input))
  have haverage : 0 ≤ uniformAverage
      (fun input => generalExpectation μ (excess input)) := by
    have hsplit : uniformAverage
        (fun input => generalExpectation μ (excess input)) =
        uniformAverage (fun input => generalExpectation μ (cost input)) - c * O := by
      unfold excess
      calc
        uniformAverage
            (fun input => generalExpectation μ
              (fun seed => cost input seed - c * opt input)) =
            uniformAverage
              (fun input => generalExpectation μ (cost input) - c * opt input) := by
                apply congrArg uniformAverage
                funext input
                rw [generalExpectation]
                rw [integral_sub (hcost input)
                  (integrable_const (c * opt input))]
                simp [generalExpectation]
        _ = uniformAverage (fun input => generalExpectation μ (cost input)) -
            c * uniformAverage opt := by
              calc
                _ = uniformAverage
                      (fun input => generalExpectation μ (cost input)) +
                    uniformAverage (fun input => (-c) * opt input) := by
                      rw [show (fun input => generalExpectation μ (cost input) -
                            c * opt input) =
                          (fun input => generalExpectation μ (cost input) +
                            (-c) * opt input) by
                            funext input
                            ring,
                        uniformAverage_add]
                _ = _ := by rw [uniformAverage_smul]; ring
        _ = uniformAverage (fun input => generalExpectation μ (cost input)) -
            c * O := by rw [hopt]
    rw [hsplit]
    linarith
  obtain ⟨input, hinput⟩ := RandomizedObligatory.exists_uniformAverage_le
    (fun input => generalExpectation μ (excess input))
  refine ⟨input, ?_⟩
  have hnonneg : 0 ≤ generalExpectation μ (excess input) :=
    haverage.trans hinput
  unfold excess at hnonneg
  rw [generalExpectation] at hnonneg ⊢
  rw [integral_sub (hcost input) (integrable_const (c * opt input))] at hnonneg
  simp at hnonneg
  linarith

/-- Weighted finite input expectation commutes with an arbitrary integrable
private-seed expectation. -/
theorem finiteExpectation_generalExpectation_comm
    {Inputs Ω : Type*} [Fintype Inputs] [MeasurableSpace Ω]
    (μ : Measure Ω) (weight : Inputs → ℝ) (cost : Inputs → Ω → ℝ)
    (hcost : ∀ input, Integrable (cost input) μ) :
    finiteExpectation weight
        (fun input => generalExpectation μ (cost input)) =
      generalExpectation μ fun seed =>
        finiteExpectation weight fun input => cost input seed := by
  unfold finiteExpectation generalExpectation
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro input _
    rw [integral_const_mul]
  · intro input _
    exact (hcost input).const_mul (weight input)

/-- A finite weighted sum of integrable random variables is integrable. -/
theorem integrable_finiteExpectation
    {Inputs Ω : Type*} [Fintype Inputs] [MeasurableSpace Ω]
    (μ : Measure Ω) (weight : Inputs → ℝ) (cost : Inputs → Ω → ℝ)
    (hcost : ∀ input, Integrable (cost input) μ) :
    Integrable (fun seed =>
      finiteExpectation weight fun input => cost input seed) μ := by
  unfold finiteExpectation
  exact integrable_finsetSum Finset.univ fun input _ =>
    (hcost input).const_mul (weight input)

/-- Weighted general-probability Yao selection in ratio form. -/
theorem general_yao_select_ratio
    {Inputs Ω : Type*} [Fintype Inputs] [Nonempty Inputs]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : Inputs → ℝ) (hweight : ∀ input, 0 ≤ weight input)
    (hmass : ∑ input, weight input = 1)
    (cost : Inputs → Ω → ℝ) (hcost : ∀ input, Integrable (cost input) μ)
    (opt : Inputs → ℝ) {L O c : ℝ}
    (hlower : L ≤ finiteExpectation weight
      (fun input => generalExpectation μ (cost input)))
    (hopt : finiteExpectation weight opt = O)
    (hcompare : c * O ≤ L) :
    ∃ input, c * opt input ≤ generalExpectation μ (cost input) := by
  let excess : Inputs → Ω → ℝ := fun input seed =>
    cost input seed - c * opt input
  have hexcessInt : ∀ input, Integrable (excess input) μ := by
    intro input
    exact (hcost input).sub (integrable_const (c * opt input))
  have hweighted : 0 ≤ finiteExpectation weight
      (fun input => generalExpectation μ (excess input)) := by
    have hsplit : finiteExpectation weight
        (fun input => generalExpectation μ (excess input)) =
        finiteExpectation weight
          (fun input => generalExpectation μ (cost input)) - c * O := by
      unfold excess
      calc
        finiteExpectation weight
            (fun input => generalExpectation μ
              (fun seed => cost input seed - c * opt input)) =
            finiteExpectation weight
              (fun input => generalExpectation μ (cost input) - c * opt input) := by
                apply congrArg (finiteExpectation weight)
                funext input
                rw [generalExpectation]
                rw [integral_sub (hcost input)
                  (integrable_const (c * opt input))]
                simp [generalExpectation]
        _ = finiteExpectation weight
              (fun input => generalExpectation μ (cost input)) +
            finiteExpectation weight (fun input => (-c) * opt input) := by
              rw [show (fun input => generalExpectation μ (cost input) -
                    c * opt input) =
                  (fun input => generalExpectation μ (cost input) +
                    (-c) * opt input) by
                    funext input
                    ring,
                finiteExpectation_add]
        _ = finiteExpectation weight
              (fun input => generalExpectation μ (cost input)) - c * O := by
              rw [finiteExpectation_smul, hopt]
              ring
    rw [hsplit]
    linarith
  have hseedAverage : 0 ≤ generalExpectation μ fun seed =>
      finiteExpectation weight fun input => excess input seed := by
    rw [← finiteExpectation_generalExpectation_comm μ weight excess hexcessInt]
    exact hweighted
  have hexists : ∃ input, 0 ≤ generalExpectation μ (excess input) := by
    obtain ⟨input, hinput⟩ := exists_finiteExpectation_le weight
      (fun input => generalExpectation μ (excess input)) hweight hmass
    refine ⟨input, ?_⟩
    exact hweighted.trans hinput
  obtain ⟨input, hinput⟩ := hexists
  refine ⟨input, ?_⟩
  unfold excess at hinput
  rw [generalExpectation] at hinput ⊢
  rw [integral_sub (hcost input) (integrable_const (c * opt input))] at hinput
  simp at hinput
  linarith

end

end Randomized
end SchedulingPaper
