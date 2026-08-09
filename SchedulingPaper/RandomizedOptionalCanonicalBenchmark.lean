import SchedulingPaper.RandomizedOptionalCanonicalTrace
import SchedulingPaper.RandomizedOptionalBenchmarkKernel
import SchedulingPaper.RandomizedOptionalUniformRoundedGrid
import Mathlib.Tactic

/-!
# Compiling a rounded benchmark into the executable canonical policy

The announced benchmark classifies histogram cells, whereas the executable
policy classifies the processing time revealed by a test.  On an injectively
priced grid these are the same representation.  This file supplies the exact
bridge, including the zero atom.
-/

namespace SchedulingPaper
namespace RandomizedOptional

open Randomized
open ObservedEnvelope
open ObservedOnline
open AnnouncedRoundedLower

noncomputable section
attribute [local instance] Classical.propDecidable

def benchmarkLowSelector
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (x : ℝ) : Bool :=
  decide (x = 0 ∨ ∃ i, G.price i = x ∧ B.selected i = true)

def benchmarkMediumSelector
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (x : ℝ) : Bool :=
  decide (∃ i, G.price i = x ∧ B.selected i = false ∧
    G.price i < B.mean)

theorem benchmarkLowSelector_zero
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : benchmarkLowSelector B 0 = true := by
  simp [benchmarkLowSelector]

theorem benchmarkMediumSelector_zero
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) : benchmarkMediumSelector B 0 = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  have hprop : ∃ i, G.price i = 0 ∧ B.selected i = false ∧
      G.price i < B.mean := by
    simpa [benchmarkMediumSelector] using htrue
  obtain ⟨i, hi, _⟩ := hprop
  exact (ne_of_gt (B.price_pos i)) hi

theorem benchmarkLowSelector_of_category
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    {job : Fin n} {i : ι} (hi : G.category i (p job) = true) :
    benchmarkLowSelector B (G.roundedProcessing job) = B.selected i := by
  have hround := G.roundedProcessing_eq_price_of_category hi
  cases hselected : B.selected i with
  | false =>
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      have hprop : G.roundedProcessing job = 0 ∨
          ∃ j, G.price j = G.roundedProcessing job ∧ B.selected j = true := by
        simpa [benchmarkLowSelector] using htrue
      rcases hprop with hzero | ⟨j, hj, hjselected⟩
      · rw [hround] at hzero
        exact (ne_of_gt (B.price_pos i)) hzero
      · have hji : j = i := hprice (hj.trans hround)
        subst j
        simp_all
  | true =>
      simp only [benchmarkLowSelector, decide_eq_true_eq]
      exact Or.inr ⟨i, hround.symm, hselected⟩

theorem benchmarkMediumSelector_of_category
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    {job : Fin n} {i : ι} (hi : G.category i (p job) = true) :
    benchmarkMediumSelector B (G.roundedProcessing job) =
      (!B.selected i && decide (G.price i < B.mean)) := by
  have hround := G.roundedProcessing_eq_price_of_category hi
  by_cases htarget : B.selected i = false ∧ G.price i < B.mean
  · have hright : (!B.selected i && decide (G.price i < B.mean)) = true := by
      simp [htarget.1, htarget.2]
    rw [hright]
    simp only [benchmarkMediumSelector, decide_eq_true_eq]
    exact ⟨i, hround.symm, htarget⟩
  · have hright : (!B.selected i && decide (G.price i < B.mean)) = false := by
      cases hs : B.selected i <;> simp_all
    rw [hright]
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have hprop : ∃ j, G.price j = G.roundedProcessing job ∧
        B.selected j = false ∧ G.price j < B.mean := by
      simpa [benchmarkMediumSelector] using htrue
    obtain ⟨j, hj, hjselected, hjmean⟩ := hprop
    have hji : j = i := hprice (hj.trans hround)
    exact htarget ⟨by simpa [hji] using hjselected, by simpa [hji] using hjmean⟩

theorem benchmarkSelectors_disjoint_of_injective
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    ∀ x, benchmarkLowSelector B x = true →
      benchmarkMediumSelector B x = false := by
  intro x hlow
  apply Bool.eq_false_of_not_eq_true
  intro hmedium
  have hmediumProp : ∃ i, G.price i = x ∧ B.selected i = false ∧
      G.price i < B.mean := by
    simpa [benchmarkMediumSelector] using hmedium
  obtain ⟨i, hi, hselected, _⟩ := hmediumProp
  have hlowProp : x = 0 ∨
      ∃ j, G.price j = x ∧ B.selected j = true := by
    simpa [benchmarkLowSelector] using hlow
  rcases hlowProp with hx | ⟨j, hj, hjselected⟩
  · exact (ne_of_gt (B.price_pos i)) (hi.trans hx)
  · have hji : j = i := hprice (hj.trans hi.symm)
    subst j
    simp_all

theorem benchmarkLowSelector_zero_of_rounded
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) {job : Fin n}
    (hz : G.roundedProcessing job = 0) :
    benchmarkLowSelector B (G.roundedProcessing job) = true := by
  rw [hz]
  exact benchmarkLowSelector_zero B

theorem uniformGridPrice_injective
    {K : ℕ} {mesh : ℝ} (hmesh : 0 < mesh) :
    Function.Injective (uniformGridPrice (K := K) mesh) := by
  intro i j hij
  apply Fin.ext
  unfold uniformGridPrice at hij
  have hcast : (i.val : ℝ) = j.val := by
    push_cast at hij
    nlinarith
  exact_mod_cast hcast

def benchmarkMediumClass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) : Bool :=
  !B.selected i && decide (G.price i < B.mean)

def benchmarkHighClass
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) : Bool :=
  !B.selected i && !(decide (G.price i < B.mean))

private theorem category_false_of_zero
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    {job : Fin n} (hz : p job = 0) (i : ι) :
    G.category i (p job) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hi
  have hp := G.category_positive i job hi
  linarith

private theorem category_false_of_ne
    {n : ℕ} {ι : Type*} [Fintype ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    {job : Fin n} {i j : ι} (hp : 0 < p job)
    (hi : G.category i (p job) = true) (hji : j ≠ i) :
    G.category j (p job) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hj
  obtain ⟨_witness, _hwitness, hunique⟩ := G.category_unique job hp
  exact hji ((hunique j hj).trans (hunique i hi).symm)

theorem benchmarkLowSelector_weight
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    (job : Fin n) :
    boolWeight (benchmarkLowSelector B (G.roundedProcessing job)) =
      (if p job = 0 then 1 else 0) +
        ∑ i, boolWeight (B.selected i) *
          (if G.category i (p job) then 1 else 0) := by
  by_cases hz : p job = 0
  · have hround := G.roundedProcessing_eq_zero_of_eq_zero hz
    have hsum : (∑ i, boolWeight (B.selected i) *
        (if G.category i (p job) then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [category_false_of_zero hz i]
      simp
    rw [hround, benchmarkLowSelector_zero, if_pos hz, hsum]
    simp [boolWeight]
  · have hp : 0 < p job := lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, hunique⟩ := G.category_unique job hp
    rw [benchmarkLowSelector_of_category B hprice hi]
    rw [if_neg hz, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      rw [category_false_of_ne hp hi hji]
      simp
    · simp

theorem benchmarkMediumSelector_weight
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    (job : Fin n) :
    boolWeight (benchmarkMediumSelector B (G.roundedProcessing job)) =
      ∑ i, boolWeight (benchmarkMediumClass B i) *
        (if G.category i (p job) then 1 else 0) := by
  by_cases hz : p job = 0
  · have hround := G.roundedProcessing_eq_zero_of_eq_zero hz
    rw [hround, benchmarkMediumSelector_zero]
    change 0 = _
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [category_false_of_zero hz i]
    simp
  · have hp : 0 < p job := lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, hunique⟩ := G.category_unique job hp
    rw [benchmarkMediumSelector_of_category B hprice hi]
    rw [Finset.sum_eq_single i]
    · simp [benchmarkMediumClass, hi]
    · intro j _ hji
      rw [category_false_of_ne hp hi hji]
      simp
    · simp

theorem benchmarkHighSelector_weight
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price)
    (job : Fin n) :
    boolWeight (canonicalHigh (benchmarkLowSelector B)
        (benchmarkMediumSelector B) (G.roundedProcessing job)) =
      ∑ i, boolWeight (benchmarkHighClass B i) *
        (if G.category i (p job) then 1 else 0) := by
  by_cases hz : p job = 0
  · have hround := G.roundedProcessing_eq_zero_of_eq_zero hz
    rw [hround]
    unfold canonicalHigh
    rw [benchmarkLowSelector_zero, benchmarkMediumSelector_zero]
    change 0 = _
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [category_false_of_zero hz i]
    simp
  · have hp : 0 < p job := lt_of_le_of_ne (G.processing_nonneg job) (Ne.symm hz)
    obtain ⟨i, hi, hunique⟩ := G.category_unique job hp
    unfold canonicalHigh
    rw [benchmarkLowSelector_of_category B hprice hi,
      benchmarkMediumSelector_of_category B hprice hi]
    rw [Finset.sum_eq_single i]
    · cases hs : B.selected i <;>
        cases hm : decide (G.price i < B.mean) <;>
        simp [canonicalHigh, benchmarkHighClass, hs, hm, hi, boolWeight]
    · intro j _ hji
      rw [category_false_of_ne hp hi hji]
      simp
    · simp

private theorem boolWeight_selected_mul
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) :
    boolWeight (B.selected i) * B.mass i =
      selectedPart B.selected B.mass i := by
  cases h : B.selected i <;>
    simp [boolWeight, selectedPart, h]

private theorem boolWeight_mediumClass_mul
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) :
    boolWeight (benchmarkMediumClass B i) * B.mass i =
      benchmarkMediumMass B i := by
  cases hs : B.selected i <;>
    by_cases hm : G.price i < B.mean <;>
    simp [benchmarkMediumClass, benchmarkMediumMass, residualPart,
      boolWeight, hs, hm]

private theorem boolWeight_highClass_mul
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (i : ι) :
    boolWeight (benchmarkHighClass B i) * B.mass i =
      benchmarkHighMass B i := by
  cases hs : B.selected i <;>
    by_cases hm : G.price i < B.mean <;>
    simp [benchmarkHighClass, benchmarkHighMass, residualPart,
      boolWeight, hs, hm]

private theorem empiricalSingleAverage_category_sum
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (weight : ι → ℝ) :
    empiricalSingleAverage (fun job =>
        ∑ i, weight i * (if G.category i (p job) then 1 else 0)) =
      ∑ i, weight i * B.mass i := by
  unfold empiricalSingleAverage
  simp only [Fintype.card_fin]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [B.mass_def i]
  unfold populationMean
  simp only [Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

private theorem empiricalSingleAverage_rounded_category_sum
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (weight : ι → ℝ) :
    empiricalSingleAverage (fun job => G.roundedProcessing job *
        (∑ i, weight i * (if G.category i (p job) then 1 else 0))) =
      ∑ i, G.price i * weight i * B.mass i := by
  have hpoint : (fun job => G.roundedProcessing job *
      (∑ i, weight i * (if G.category i (p job) then 1 else 0))) =
      (fun job => ∑ i, (G.price i * weight i) *
        (if G.category i (p job) then 1 else 0)) := by
    funext job
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : G.category i (p job) = true
    · rw [G.roundedProcessing_eq_price_of_category hi]
      simp [hi]
    · have hfalse : G.category i (p job) = false := Bool.eq_false_iff.mpr hi
      simp [hfalse]
  rw [hpoint, empiricalSingleAverage_category_sum hn B]

private theorem empiricalSingleAverage_zero_eq
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    empiricalSingleAverage (fun job => if p job = 0 then 1 else 0) =
      B.zeroMass := by
  rw [B.zeroMass_def]
  unfold empiricalSingleAverage populationMean
  simp only [Fintype.card_fin]
  congr 2
  funext job
  simp [zeroCategory]

private theorem empiricalSingleAverage_add_local
    {n : ℕ} (hn : 0 < n) (f g : Fin n → ℝ) :
    empiricalSingleAverage (fun x => f x + g x) =
      empiricalSingleAverage f + empiricalSingleAverage g := by
  unfold empiricalSingleAverage
  rw [Finset.sum_add_distrib]
  ring

theorem canonicalEmpiricalMoments_lowMass
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).lowMass =
      (benchmarkGridFluidData B).moments.lowMass := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  have hpoint : (fun job =>
      boolWeight (benchmarkLowSelector B (G.roundedProcessing job))) =
      (fun job => (if p job = 0 then 1 else 0) +
        ∑ i, boolWeight (B.selected i) *
          (if G.category i (p job) then 1 else 0)) := by
    funext job
    exact benchmarkLowSelector_weight hn B hprice job
  rw [hpoint, empiricalSingleAverage_add_local hn,
    empiricalSingleAverage_zero_eq hn B,
    empiricalSingleAverage_category_sum hn B]
  apply congrArg (fun x => B.zeroMass + x)
  apply Finset.sum_congr rfl
  intro i _
  rw [boolWeight_selected_mul]

theorem canonicalEmpiricalMoments_lowMoment
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).lowMoment =
      (benchmarkGridFluidData B).moments.lowMoment := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  have hpoint : (fun job => G.roundedProcessing job *
      boolWeight (benchmarkLowSelector B (G.roundedProcessing job))) =
      (fun job => G.roundedProcessing job *
        (∑ i, boolWeight (B.selected i) *
          (if G.category i (p job) then 1 else 0))) := by
    funext job
    rw [benchmarkLowSelector_weight hn B hprice job]
    by_cases hz : p job = 0
    · rw [if_pos hz, G.roundedProcessing_eq_zero_of_eq_zero hz]
      ring
    · rw [if_neg hz]
      ring
  rw [hpoint, empiricalSingleAverage_rounded_category_sum hn B]
  apply Finset.sum_congr rfl
  intro i _
  rw [show G.price i * boolWeight (B.selected i) * B.mass i =
      G.price i * (boolWeight (B.selected i) * B.mass i) by ring,
    boolWeight_selected_mul]

theorem canonicalEmpiricalMoments_mediumMoment
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).mediumMoment =
      (benchmarkGridFluidData B).moments.mediumMoment := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  simp_rw [benchmarkMediumSelector_weight hn B hprice]
  rw [empiricalSingleAverage_rounded_category_sum hn B]
  apply Finset.sum_congr rfl
  intro i _
  rw [show G.price i * boolWeight (benchmarkMediumClass B i) * B.mass i =
      G.price i * (boolWeight (benchmarkMediumClass B i) * B.mass i) by ring,
    boolWeight_mediumClass_mul]

theorem canonicalEmpiricalMoments_highMass
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).highMass =
      (benchmarkGridFluidData B).moments.highMass := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  simp_rw [benchmarkHighSelector_weight hn B hprice]
  rw [empiricalSingleAverage_category_sum hn B]
  apply Finset.sum_congr rfl
  intro i _
  rw [boolWeight_highClass_mul]

theorem canonicalEmpiricalMoments_mean
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).mean =
      (benchmarkGridFluidData B).moments.mean := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  have hleft : empiricalSingleAverage G.roundedProcessing = B.mean := by
    rw [B.mean_def]
    rfl
  have hright : (∑ i, G.price i * B.mass i) = B.mean := by
    calc
      (∑ i, G.price i * B.mass i) =
          (∑ i, G.price i * selectedPart B.selected B.mass i) +
            ∑ i, G.price i * residualPart B.selected B.mass i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_add, selectedPart_add_residualPart]
      _ = B.mean := B.mean_partition
  exact hleft.trans hright.symm

private theorem empiricalProductPairAverage_rounded_category_sum
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (weight : ι → ℝ) :
    empiricalProductPairAverage (fun left right =>
        min (G.roundedProcessing left) (G.roundedProcessing right) *
          (∑ i, weight i * (if G.category i (p left) then 1 else 0)) *
          (∑ j, weight j * (if G.category j (p right) then 1 else 0))) =
      ∑ i, ∑ j, min (G.price i) (G.price j) *
        (weight i * B.mass i) * (weight j * B.mass j) := by
  let indicator : ι → Fin n → ℝ := fun i job =>
    if G.category i (p job) then 1 else 0
  have hpoint : ∀ left right,
      min (G.roundedProcessing left) (G.roundedProcessing right) *
          (∑ i, weight i * indicator i left) *
          (∑ j, weight j * indicator j right) =
        ∑ i, ∑ j, min (G.price i) (G.price j) *
          weight i * weight j * indicator i left * indicator j right := by
    intro left right
    have hfirst :
        min (G.roundedProcessing left) (G.roundedProcessing right) *
            (∑ i, weight i * indicator i left) =
          ∑ i, min (G.roundedProcessing left) (G.roundedProcessing right) *
            (weight i * indicator i left) := by
      rw [Finset.mul_sum]
    rw [hfirst, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [indicator]
    by_cases hi : G.category i (p left) = true
    · by_cases hj : G.category j (p right) = true
      · rw [G.roundedProcessing_eq_price_of_category hi,
          G.roundedProcessing_eq_price_of_category hj]
        simp [hi, hj]
      · have hjf : G.category j (p right) = false := Bool.eq_false_iff.mpr hj
        simp [hjf]
    · have hif : G.category i (p left) = false := Bool.eq_false_iff.mpr hi
      simp [hif]
  unfold empiricalProductPairAverage
  simp only [Fintype.card_fin]
  change
    (∑ left, ∑ right,
      min (G.roundedProcessing left) (G.roundedProcessing right) *
        (∑ i, weight i * indicator i left) *
        (∑ j, weight j * indicator j right)) / (n : ℝ) ^ 2 = _
  simp_rw [hpoint]
  have hreorder :
      (∑ left : Fin n, ∑ right : Fin n, ∑ i : ι, ∑ j : ι,
        min (G.price i) (G.price j) * weight i * weight j *
          indicator i left * indicator j right) =
      ∑ i : ι, ∑ j : ι,
        min (G.price i) (G.price j) * weight i * weight j *
          (∑ left : Fin n, indicator i left) *
          (∑ right : Fin n, indicator j right) := by
    calc
      (∑ left : Fin n, ∑ right : Fin n, ∑ i : ι, ∑ j : ι,
          min (G.price i) (G.price j) * weight i * weight j *
            indicator i left * indicator j right) =
          ∑ left : Fin n, ∑ i : ι, ∑ right : Fin n, ∑ j : ι,
            min (G.price i) (G.price j) * weight i * weight j *
              indicator i left * indicator j right := by
        apply Finset.sum_congr rfl
        intro left _
        rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ left : Fin n, ∑ right : Fin n, ∑ j : ι,
            min (G.price i) (G.price j) * weight i * weight j *
              indicator i left * indicator j right := by
        rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ left : Fin n, ∑ j : ι, ∑ right : Fin n,
            min (G.price i) (G.price j) * weight i * weight j *
              indicator i left * indicator j right := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro left _
        rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ j : ι, ∑ left : Fin n, ∑ right : Fin n,
            min (G.price i) (G.price j) * weight i * weight j *
              indicator i left * indicator j right := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        let C := min (G.price i) (G.price j) * weight i * weight j
        change
          (∑ left : Fin n, ∑ right : Fin n,
              C * indicator i left * indicator j right) =
            C * (∑ left : Fin n, indicator i left) *
              ∑ right : Fin n, indicator j right
        calc
          (∑ left : Fin n, ∑ right : Fin n,
              C * indicator i left * indicator j right) =
              ∑ left : Fin n,
                (C * indicator i left) *
                  ∑ right : Fin n, indicator j right := by
            apply Finset.sum_congr rfl
            intro left _
            rw [Finset.mul_sum]
          _ = (∑ left : Fin n, C * indicator i left) *
                ∑ right : Fin n, indicator j right := by
            rw [Finset.sum_mul]
          _ = C * (∑ left : Fin n, indicator i left) *
                ∑ right : Fin n, indicator j right := by
            have hC : (∑ left : Fin n, C * indicator i left) =
                C * ∑ left : Fin n, indicator i left := by
              rw [Finset.mul_sum]
            rw [hC]
  rw [hreorder]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hmassI : (∑ left : Fin n, indicator i left) / n = B.mass i := by
    rw [B.mass_def i]
    unfold populationMean
    simp only [Fintype.card_fin]
    rfl
  have hmassJ : (∑ right : Fin n, indicator j right) / n = B.mass j := by
    rw [B.mass_def j]
    unfold populationMean
    simp only [Fintype.card_fin]
    rfl
  have hsumI : (∑ left : Fin n, indicator i left) = n * B.mass i := by
    simpa [mul_comm] using (div_eq_iff hnR).mp hmassI
  have hsumJ : (∑ right : Fin n, indicator j right) = n * B.mass j := by
    simpa [mul_comm] using (div_eq_iff hnR).mp hmassJ
  rw [hsumI, hsumJ]
  field_simp [hnR]

theorem canonicalEmpiricalMoments_mediumMinPair
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).mediumMinPair =
      (benchmarkGridFluidData B).moments.mediumMinPair := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  simp_rw [benchmarkMediumSelector_weight hn B hprice]
  rw [empiricalProductPairAverage_rounded_category_sum hn B]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [boolWeight_mediumClass_mul, boolWeight_mediumClass_mul]

theorem canonicalEmpiricalMoments_highMinPair
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    (canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))).highMinPair =
      (benchmarkGridFluidData B).moments.highMinPair := by
  unfold canonicalEmpiricalMoments GridFluidData.moments benchmarkGridFluidData
  simp_rw [benchmarkHighSelector_weight hn B hprice]
  rw [empiricalProductPairAverage_rounded_category_sum hn B]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [boolWeight_highClass_mul, boolWeight_highClass_mul]

private theorem fluidMoments_eq_of_components
    (A B : FluidMoments)
    (hLowMass : A.lowMass = B.lowMass)
    (hLowMoment : A.lowMoment = B.lowMoment)
    (hMediumMoment : A.mediumMoment = B.mediumMoment)
    (hHighMass : A.highMass = B.highMass)
    (hMean : A.mean = B.mean)
    (hMediumMinPair : A.mediumMinPair = B.mediumMinPair)
    (hHighMinPair : A.highMinPair = B.highMinPair) : A = B := by
  cases A
  cases B
  simp_all

theorem canonicalEmpiricalMoments_eq_benchmark
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (hprice : Function.Injective G.price) :
    canonicalEmpiricalMoments G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B)) =
        (benchmarkGridFluidData B).moments := by
  apply fluidMoments_eq_of_components
  · exact canonicalEmpiricalMoments_lowMass hn B hprice
  · exact canonicalEmpiricalMoments_lowMoment hn B hprice
  · exact canonicalEmpiricalMoments_mediumMoment hn B hprice
  · exact canonicalEmpiricalMoments_highMass hn B hprice
  · exact canonicalEmpiricalMoments_mean hn B
  · exact canonicalEmpiricalMoments_mediumMinPair hn B hprice
  · exact canonicalEmpiricalMoments_highMinPair hn B hprice

/-! ## From a hidden placement to an executable canonical run -/

/-- Completion cost of the canonical policy after the occurrence multiset is
hidden behind a placement.  The policy sees public labels; `σ` assigns an
occurrence, and hence a processing time, to each label. -/
def canonicalPlacedRunCost
    {n q : ℕ} (processing : Fin n → ℝ)
    (low medium : ℝ → Bool) (σ : Equiv.Perm (Fin n)) : ℝ :=
  completionCost (fun job => processing (σ job))
    (canonicalRun q (fun job => processing (σ job)) low medium).config.transcript

/-- The operational canonical run on a hidden placement is exactly the
placement kernel used by the finite expectation theorem. -/
theorem canonicalPlacedRunCost_eq_kernel
    {n q : ℕ} (hq : q ≤ n) (processing : Fin n → ℝ)
    (low medium : ℝ → Bool)
    (hdisjoint : ∀ x, low x = true → medium x = false)
    (hzeroLow : ∀ i, processing i = 0 → low (processing i) = true)
    (σ : Equiv.Perm (Fin n)) :
    canonicalPlacedRunCost (q := q) processing low medium σ =
      canonicalKernelCost q processing low medium (canonicalHigh low medium) σ := by
  unfold canonicalPlacedRunCost
  rw [canonicalRun_completionCost_eq_kernel hq
    (fun job => processing (σ job)) low medium hdisjoint]
  · unfold canonicalKernelCost positionKernelCost
    simp only [Equiv.refl_apply]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply Finset.sum_congr rfl
      intro job _
      rfl
    · apply Finset.sum_congr rfl
      intro pair _
      rfl
  · intro job hzero
    exact hzeroLow (σ job) hzero

/-! ## Finite announced upper bound -/

/-- The empirical benchmark is implemented by an actual complete canonical
run, averaged only over the policy's private relabelling.  This is the
operational version of `exists_canonicalKernelCost_le_benchmark`. -/
theorem exists_canonicalPlacedRunCost_le_benchmark
    {n : ℕ} (hn : 1 < n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : Fin n → ℝ} {G : RoundedPositiveGrid ι p}
    (B : BenchmarkData p G) (htauMean : B.tau ≤ B.mean)
    (hprice : Function.Injective G.price)
    {L : ℝ} (hroundedL : ∀ job, G.roundedProcessing job ≤ L) :
    ∃ q : ℕ, q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) G.roundedProcessing
        (benchmarkLowSelector B) (benchmarkMediumSelector B)) /
          (n : ℝ) ^ 2 ≤ B.value + (7 + 27 * L) / n := by
  have hmoments := canonicalEmpiricalMoments_eq_benchmark
    (show 0 < n by omega) B hprice
  obtain ⟨q, hq, hkernel⟩ := exists_canonicalKernelCost_le_benchmark
    hn B htauMean G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B))
      G.roundedProcessing_nonneg hroundedL hmoments
  refine ⟨q, hq, ?_⟩
  have hcost :
      canonicalPlacedRunCost (q := q) G.roundedProcessing
          (benchmarkLowSelector B) (benchmarkMediumSelector B) =
        canonicalKernelCost q G.roundedProcessing
          (benchmarkLowSelector B) (benchmarkMediumSelector B)
          (canonicalHigh (benchmarkLowSelector B) (benchmarkMediumSelector B)) := by
    funext σ
    exact canonicalPlacedRunCost_eq_kernel hq G.roundedProcessing
      (benchmarkLowSelector B) (benchmarkMediumSelector B)
      (benchmarkSelectors_disjoint_of_injective B hprice)
      (fun job hzero => benchmarkLowSelector_zero_of_rounded B hzero) σ
  rw [hcost]
  exact hkernel

/-- Concrete bounded-uniform-grid specialization.  The rounded execution is
bounded by `L + L/K`, exactly the scale used by the announced lower bound. -/
theorem exists_boundedUniformBenchmark_canonicalPlacedRunCost_le
    {n K : ℕ} (hn : 1 < n) (hK : 0 < K)
    {L : ℝ} (hL : 0 < L)
    (p : Fin n → ℝ) (hp0 : ∀ job, 0 ≤ p job)
    (hpL : ∀ job, p job ≤ L)
    (B : BenchmarkData p (boundedUniformRoundedGrid hK hL p hp0 hpL))
    (htauMean : B.tau ≤ B.mean) :
    let G := boundedUniformRoundedGrid hK hL p hp0 hpL
    ∃ q : ℕ, q ≤ n ∧
      uniformAverage (canonicalPlacedRunCost (q := q) G.roundedProcessing
        (benchmarkLowSelector B) (benchmarkMediumSelector B)) /
          (n : ℝ) ^ 2 ≤
        B.value + (7 + 27 * (L + L / K)) / n := by
  dsimp
  let G := boundedUniformRoundedGrid hK hL p hp0 hpL
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmesh : 0 < L / (K : ℝ) := div_pos hL hKR
  have hprice : Function.Injective G.price := by
    dsimp [G]
    exact uniformGridPrice_injective hmesh
  exact exists_canonicalPlacedRunCost_le_benchmark hn B htauMean hprice
    (fun job => boundedUniformRoundedGrid_roundedProcessing_le
      hK hL p hp0 hpL job)

end

end RandomizedOptional
end SchedulingPaper
