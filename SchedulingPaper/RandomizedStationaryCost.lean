import SchedulingPaper.RandomPermutation
import SchedulingPaper.RandomizedSampleAlgebra
import Mathlib.Tactic

/-!
# Exact finite stationary random-order cost

This module proves the probability identity behind the stationary policy:
for each early job, every other discovery block precedes it with probability
one half.  The proof uses only the finite uniform average on permutations.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- In the order represented by `σ`, label `i` occurs before label `j`. -/
def Precedes (σ : Equiv.Perm α) (i j : α) : Prop :=
  Fintype.equivFin α (σ.symm i) < Fintype.equivFin α (σ.symm j)

instance (σ : Equiv.Perm α) (i j : α) : Decidable (Precedes σ i j) :=
  by unfold Precedes; infer_instance

theorem precedes_swap_output (σ : Equiv.Perm α) (i j : α) :
    Precedes (Equiv.mulLeft (Equiv.swap i j) σ) i j = Precedes σ j i := by
  unfold Precedes
  change (Fintype.equivFin α (((Equiv.swap i j * σ)⁻¹) i) <
    Fintype.equivFin α (((Equiv.swap i j * σ)⁻¹) j)) = _
  rw [mul_inv_rev]
  simp [Equiv.Perm.mul_apply]

theorem precedes_or_reverse (σ : Equiv.Perm α) {i j : α} (hij : i ≠ j) :
    Precedes σ i j ∨ Precedes σ j i := by
  unfold Precedes
  apply lt_or_gt_of_ne
  intro h
  have hs : σ.symm i = σ.symm j := (Fintype.equivFin α).injective h
  exact hij (σ.symm.injective hs)

theorem not_precedes_and_reverse (σ : Equiv.Perm α) (i j : α) :
    ¬ (Precedes σ i j ∧ Precedes σ j i) := by
  intro h
  exact lt_asymm h.1 h.2

/-- Each of two distinct labels precedes the other with probability one half
under the finite uniform permutation average. -/
theorem uniformAverage_precedes_indicator [Nonempty α]
    {i j : α} (hij : i ≠ j) :
    uniformAverage (fun σ : Equiv.Perm α => if Precedes σ i j then 1 else 0) =
      1 / 2 := by
  let f : Equiv.Perm α → ℝ :=
    fun σ => if Precedes σ i j then 1 else 0
  let e : Equiv.Perm (Equiv.Perm α) := Equiv.mulLeft (Equiv.swap i j)
  have hreparam := uniformAverage_comp_equiv e f
  have hcomp : (f ∘ e) = fun σ => 1 - f σ := by
    funext σ
    dsimp [f, e, Function.comp_def]
    have heq :
        Precedes (Equiv.swap i j * σ) i j = Precedes σ j i := by
      simpa only using precedes_swap_output σ i j
    by_cases h : Precedes σ i j
    · have hn : ¬ Precedes σ j i := fun hr =>
        not_precedes_and_reverse σ i j ⟨h, hr⟩
      have hout : ¬ Precedes (Equiv.swap i j * σ) i j := by
        intro ho
        exact hn (heq.mp ho)
      simp [h, hout]
    · have hr : Precedes σ j i := (precedes_or_reverse σ hij).resolve_left h
      have hout : Precedes (Equiv.swap i j * σ) i j := heq.mpr hr
      simp [h, hout]
  rw [hcomp] at hreparam
  have hcomplement :
      uniformAverage (fun σ => 1 - f σ) = 1 - uniformAverage f := by
    calc
      uniformAverage (fun σ => 1 - f σ) =
          uniformAverage (fun _σ : Equiv.Perm α => (1 : ℝ)) +
            uniformAverage (fun σ => -f σ) := by
        simpa [sub_eq_add_neg] using
          (uniformAverage_add
            (fun _σ : Equiv.Perm α => (1 : ℝ)) (fun σ => -f σ))
      _ = 1 + (-1) * uniformAverage f := by
        rw [uniformAverage_const]
        congr 1
        simpa using uniformAverage_smul (-1) f
      _ = 1 - uniformAverage f := by ring
  rw [hcomplement] at hreparam
  dsimp [f] at hreparam ⊢
  linarith

/-- Duration of one discovery block: every label is tested, and early jobs
are additionally processed immediately. -/
def discoveryBlock (p : α → ℝ) (early : α → Bool) (i : α) : ℝ :=
  1 + if early i then p i else 0

/-- Completion time of label `i` within the discovery order, assuming it is
an early label.  The definition is also useful for late labels algebraically. -/
def discoveryCompletion (p : α → ℝ) (early : α → Bool)
    (σ : Equiv.Perm α) (i : α) : ℝ :=
  discoveryBlock p early i +
    ∑ j, if j = i then 0
      else if Precedes σ j i then discoveryBlock p early j else 0

/-- One early label sees half of every other discovery block in expectation. -/
theorem uniformAverage_discoveryCompletion [Nonempty α]
    (p : α → ℝ) (early : α → Bool) (i : α) :
    uniformAverage (fun σ : Equiv.Perm α =>
      discoveryCompletion p early σ i) =
      ((∑ j, discoveryBlock p early j) + discoveryBlock p early i) / 2 := by
  rw [show (fun σ : Equiv.Perm α => discoveryCompletion p early σ i) =
      (fun σ => (fun _σ : Equiv.Perm α => discoveryBlock p early i) σ +
        (fun σ => ∑ j, if j = i then 0
          else if Precedes σ j i then discoveryBlock p early j else 0) σ) by
      rfl]
  rw [uniformAverage_add, uniformAverage_const, uniformAverage_sum]
  have hterm : ∀ j,
      uniformAverage (fun σ : Equiv.Perm α =>
        if j = i then 0
        else if Precedes σ j i then discoveryBlock p early j else 0) =
      if j = i then 0 else discoveryBlock p early j / 2 := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, if_false]
      rw [show (fun σ : Equiv.Perm α =>
          if Precedes σ j i then discoveryBlock p early j else 0) =
        (fun σ => discoveryBlock p early j *
          (if Precedes σ j i then 1 else 0)) by
            funext σ
            split <;> ring]
      rw [uniformAverage_smul,
        uniformAverage_precedes_indicator hji]
      ring
  simp_rw [hterm]
  have hsumErase :
      (∑ j, if j = i then 0 else discoveryBlock p early j / 2) =
        ((∑ j, discoveryBlock p early j) - discoveryBlock p early i) / 2 := by
    let b : α → ℝ := fun j => discoveryBlock p early j / 2
    let f : α → ℝ := fun j => if j = i then 0 else b j
    have hfzero : f i = 0 := by simp [f]
    have heraseF :
        (∑ j ∈ Finset.univ.erase i, f j) = ∑ j, f j :=
      Finset.sum_erase Finset.univ hfzero
    have heraseEq :
        (∑ j ∈ Finset.univ.erase i, f j) =
          ∑ j ∈ Finset.univ.erase i, b j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [f, hji]
    have hblock := Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
    have hdiv : (∑ j, b j) = (∑ j, discoveryBlock p early j) / 2 := by
      dsimp [b]
      exact (Finset.sum_div Finset.univ
        (fun j => discoveryBlock p early j) 2).symm
    change (∑ j, f j) = _
    rw [← heraseF, heraseEq]
    rw [show (∑ j ∈ Finset.univ.erase i, b j) = (∑ j, b j) - b i by
      linarith]
    rw [hdiv]
    simp [b]
    ring
  rw [hsumErase]
  ring

/-- Total completion cost contributed by early labels during discovery. -/
def stationaryEarlyCost (p : α → ℝ) (early : α → Bool)
    (σ : Equiv.Perm α) : ℝ :=
  ∑ i, if early i then discoveryCompletion p early σ i else 0

/-- Number of early labels, represented as a real. -/
def earlyMassCount (early : α → Bool) : ℝ :=
  ∑ i, if early i then 1 else 0

/-- Sum of self-block lengths of the early labels. -/
def earlySelfWork (p : α → ℝ) (early : α → Bool) : ℝ :=
  ∑ i, if early i then discoveryBlock p early i else 0

/-- Exact finite expectation `eW/2 + L_E/2` from the paper. -/
theorem uniformAverage_stationaryEarlyCost [Nonempty α]
    (p : α → ℝ) (early : α → Bool) :
    uniformAverage (stationaryEarlyCost p early) =
      earlyMassCount early * (∑ j, discoveryBlock p early j) / 2 +
        earlySelfWork p early / 2 := by
  unfold stationaryEarlyCost
  rw [uniformAverage_sum]
  simp_rw [show ∀ i,
      uniformAverage (fun σ : Equiv.Perm α =>
        if early i then discoveryCompletion p early σ i else 0) =
      if early i then
        ((∑ j, discoveryBlock p early j) + discoveryBlock p early i) / 2
      else 0 by
    intro i
    cases h : early i <;> simp [h, uniformAverage_discoveryCompletion]]
  unfold earlyMassCount earlySelfWork
  have hfirst :
      (∑ i, if early i then
          (∑ j, discoveryBlock p early j) / 2 else 0) =
        (∑ i, if early i then 1 else 0) *
          (∑ j, discoveryBlock p early j) / 2 := by
    have hpoint : ∀ i,
        (if early i then (∑ j, discoveryBlock p early j) / 2 else 0) =
          (if early i then (1 : ℝ) else 0) *
            ((∑ j, discoveryBlock p early j) / 2) := by
      intro i
      cases h : early i <;> simp [h]
    simp_rw [hpoint]
    have hsum := (Finset.sum_mul Finset.univ
      (fun i => if early i then (1 : ℝ) else 0)
      ((∑ j, discoveryBlock p early j) / 2)).symm
    rw [hsum]
    ring
  have hsecond :
      (∑ i, if early i then discoveryBlock p early i / 2 else 0) =
        (∑ i, if early i then discoveryBlock p early i else 0) / 2 := by
    have hpoint : ∀ i,
        (if early i then discoveryBlock p early i / 2 else 0) =
          (if early i then discoveryBlock p early i else 0) / 2 := by
      intro i
      cases h : early i <;> simp [h]
    simp_rw [hpoint]
    exact (Finset.sum_div Finset.univ
      (fun i => if early i then discoveryBlock p early i else 0) 2).symm
  simp_rw [show ∀ i,
      (if early i then
          ((∑ j, discoveryBlock p early j) + discoveryBlock p early i) / 2
        else 0) =
      (if early i then (∑ j, discoveryBlock p early j) / 2 else 0) +
        (if early i then discoveryBlock p early i / 2 else 0) by
    intro i
    cases h : early i <;> simp [h] <;> ring]
  rw [Finset.sum_add_distrib, hfirst, hsecond]

/-- Scalar form of the complete stationary schedule: expected early
completion cost followed by the deterministic SPT late tail. -/
def stationaryScalarCost
    (n e sumEarly sumLate pairLate : ℝ) : ℝ :=
  let work := n + sumEarly
  let selfEarly := e + sumEarly
  e * work / 2 + selfEarly / 2 +
    (n - e) * work + sumLate + pairLate

/-- Exact normalized identity from Lemma 2 of the analytic proof.

`pairLate` is the sum over unordered distinct late pairs, so
`sumLate + 2 pairLate` is the full ordered late minimum moment. -/
theorem stationaryScalarCost_eq_normalized
    {n e sumEarly sumLate pairLate : ℝ}
    (hn : n ≠ 0) :
    stationaryScalarCost n e sumEarly sumLate pairLate =
      n ^ 2 *
        ((1 + sumEarly / n) * (1 - (e / n) / 2) +
          ((sumLate + 2 * pairLate) / n ^ 2) / 2) +
        (e + sumEarly + sumLate) / 2 := by
  unfold stationaryScalarCost
  dsimp only
  field_simp [hn]
  ring

/-- Scalar conditional expectation when sample discovery blocks precede the
remaining discovery blocks.  `lateCost` includes the common discovery offset
and the final SPT tail. -/
def sampleFirstScalarCost
    (eSample eRest workSample workRest selfSample selfRest lateCost : ℝ) : ℝ :=
  Randomized.sampleFirstEarlyCost eSample eRest workSample workRest
    selfSample selfRest + lateCost

def uniformStationaryScalarCost
    (eSample eRest workSample workRest selfSample selfRest lateCost : ℝ) : ℝ :=
  Randomized.uniformEarlyCost eSample eRest workSample workRest
    selfSample selfRest + lateCost

/-- The conditional sample-first comparator differs from the fully uniform
stationary schedule by at most `eRest*workSample/2`. -/
theorem sampleFirstScalarCost_le_uniform_add
    {eSample eRest workSample workRest selfSample selfRest lateCost : ℝ}
    (heSample : 0 ≤ eSample) (hworkRest : 0 ≤ workRest) :
    sampleFirstScalarCost eSample eRest workSample workRest
        selfSample selfRest lateCost ≤
      uniformStationaryScalarCost eSample eRest workSample workRest
        selfSample selfRest lateCost + eRest * workSample / 2 := by
  unfold sampleFirstScalarCost uniformStationaryScalarCost
  have h := Randomized.sampleFirstEarlyCost_le_uniform_add
    (eRest := eRest) (workSample := workSample)
    (selfSample := selfSample) (selfRest := selfRest)
    heSample hworkRest
  linarith

/-- With at most `n` early remainder jobs and sample discovery work at most
`17k`, the cross overhead is at most `17nk/2`. -/
theorem sampleFirst_cross_overhead_B32
    {eRest workSample n k : ℝ}
    (heRest0 : 0 ≤ eRest) (heRest : eRest ≤ n)
    (hwork0 : 0 ≤ workSample) (hwork : workSample ≤ 17 * k)
    (hn : 0 ≤ n) :
    eRest * workSample / 2 ≤ 17 * n * k / 2 := by
  have hprod := mul_le_mul heRest hwork hwork0 hn
  nlinarith

/-- Delaying at most `k` sampled early jobs by at most `17k` contributes at
most `17k²`. -/
theorem sampledBatch_delay_B32
    {jobs delay k : ℝ}
    (hjobs0 : 0 ≤ jobs) (hjobs : jobs ≤ k)
    (hdelay0 : 0 ≤ delay) (hdelay : delay ≤ 17 * k)
    (hk : 0 ≤ k) :
    jobs * delay ≤ 17 * k ^ 2 := by
  have hprod := mul_le_mul hjobs hdelay hdelay0 hk
  nlinarith

end

end RandomizedObligatory
end SchedulingPaper
