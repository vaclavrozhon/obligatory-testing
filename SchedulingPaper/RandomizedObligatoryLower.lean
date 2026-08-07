import SchedulingPaper.FiniteRandomization
import Mathlib.Tactic

/-!
# Randomized obligatory testing: binary lower-bound assembly

This module formalizes the deterministic completion envelope for the binary
`0/2` instance, converts it into a lower bound on total completion cost, and
performs the finite Yao averaging step selecting one fixed oblivious input.
The bridge maximal-moment estimate is isolated in a separate module.
-/

namespace SchedulingPaper
namespace RandomizedObligatory

open Randomized

noncomputable section

/-- If the first `k` tests contain at most `k/2 + Δ` zero jobs, and `x`
positive jobs have been processed by physical time `t`, then at most
`t/2 + Δ` jobs are complete. -/
theorem binary_completed_le
    {k zeros processed t Δ : ℝ}
    (hzero : zeros ≤ k / 2 + Δ)
    (hwork : k + 2 * processed ≤ t) :
    zeros + processed ≤ t / 2 + Δ := by
  linarith

/-- Evaluating the completion envelope at the `r`-th completion gives a
pointwise lower bound on its completion time. -/
theorem binary_completion_time_lower
    {rank completion Δ : ℝ}
    (henvelope : rank ≤ completion / 2 + Δ) :
    2 * (rank - Δ) ≤ completion := by
  linarith

/-- A finite decision tree for an algorithm under independent fair binary
processing times.  At a state with `r+1` unfinished jobs, processing a known
two-job leads to a state with `r` jobs; testing branches equally between a
zero completion (`r`) and a revealed two-job (`r+1`).

The type intentionally grants the policy more power than a real scheduler:
it may use a `process` node whenever it wishes.  A lower bound for this larger
class therefore applies to every valid deterministic scheduling policy once
its finite execution tree is unfolded. -/
inductive BinaryPolicy : ℕ → Type
  | done : BinaryPolicy 0
  | process {r : ℕ} : BinaryPolicy r → BinaryPolicy (r + 1)
  | test {r : ℕ} : BinaryPolicy r → BinaryPolicy (r + 1) → BinaryPolicy (r + 1)

/-- Expected remaining area under the unfinished-jobs curve. -/
def BinaryPolicy.expectedArea {r : ℕ} (policy : BinaryPolicy r) : ℝ :=
  match policy with
  | .done => 0
  | .process (r := r) next =>
      2 * ((r + 1 : ℕ) : ℝ) + next.expectedArea
  | .test (r := r) zeroBranch twoBranch =>
      ((r + 1 : ℕ) : ℝ) +
        (zeroBranch.expectedArea + twoBranch.expectedArea) / 2

/-- Every fair binary policy pays expected area at least `r²`. -/
theorem BinaryPolicy.sq_le_expectedArea
    {r : ℕ} (policy : BinaryPolicy r) :
    (r : ℝ) ^ 2 ≤ policy.expectedArea := by
  induction policy with
  | done => simp [BinaryPolicy.expectedArea]
  | @process r next ih =>
      simp only [BinaryPolicy.expectedArea]
      push_cast
      nlinarith
  | @test r zeroBranch twoBranch ihZero ihTwo =>
      simp only [BinaryPolicy.expectedArea]
      push_cast
      norm_num [Nat.cast_add, Nat.cast_one] at ihTwo ⊢
      nlinarith

/-- Sum of the one-based ranks of `Fin n`. -/
theorem sum_fin_rank_add_one (n : ℕ) :
    (∑ r : Fin n, ((r.val + 1 : ℕ) : ℝ)) =
      (n : ℝ) * (n + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => ((r + 1 : ℕ) : ℝ)) n]
  have h : ∀ m : ℕ,
      (∑ r ∈ Finset.range m, ((r + 1 : ℕ) : ℝ)) =
        (m : ℝ) * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  exact h n

/-- Summing the completion envelope over all one-based completion ranks.

This slightly strengthens the area-under-unfinished-jobs bound used in the
paper: it gives `n(n+1)-2nΔ`, which is at least `n²-2nΔ`. -/
theorem totalCompletion_lower_of_rank_envelope
    {n : ℕ} {completion : Fin n → ℝ} {Δ : ℝ}
    (henvelope : ∀ r,
      ((r.val + 1 : ℕ) : ℝ) ≤ completion r / 2 + Δ) :
    (n : ℝ) * (n + 1) - 2 * n * Δ ≤ ∑ r, completion r := by
  have hpoint : ∀ r,
      2 * ((((r.val + 1 : ℕ) : ℝ)) - Δ) ≤ completion r := by
    intro r
    exact binary_completion_time_lower (henvelope r)
  have hsum := Finset.sum_le_sum fun r (_hr : r ∈ (Finset.univ : Finset (Fin n))) =>
    hpoint r
  have hleft :
      (∑ r : Fin n, 2 * ((((r.val + 1 : ℕ) : ℝ)) - Δ)) =
        (n : ℝ) * (n + 1) - 2 * n * Δ := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      sum_fin_rank_add_one]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [hleft] at hsum
  exact hsum

/-- Expected lower bound obtained from a pathwise discrepancy envelope. -/
theorem expectedCost_lower_of_expected_discrepancy
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {n : ℝ} {cost discrepancy : Ω → ℝ}
    (hpoint : ∀ ω,
      n * (n + 1) - 2 * n * discrepancy ω ≤ cost ω) :
    n * (n + 1) - 2 * n * uniformAverage discrepancy ≤
      uniformAverage cost := by
  have havg := uniformAverage_mono hpoint
  have haffine :
      uniformAverage (fun ω => n * (n + 1) - 2 * n * discrepancy ω) =
        n * (n + 1) - 2 * n * uniformAverage discrepancy := by
    calc
      uniformAverage (fun ω => n * (n + 1) - 2 * n * discrepancy ω) =
          uniformAverage (fun _ω : Ω => n * (n + 1)) +
            uniformAverage (fun ω => (-2 * n) * discrepancy ω) := by
        simpa [sub_eq_add_neg, mul_assoc] using
          (uniformAverage_add
            (fun _ω : Ω => n * (n + 1))
            (fun ω => (-2 * n) * discrepancy ω))
      _ = n * (n + 1) + (-2 * n) * uniformAverage discrepancy := by
        rw [uniformAverage_const, uniformAverage_smul]
      _ = n * (n + 1) - 2 * n * uniformAverage discrepancy := by ring
  rw [haffine] at havg
  exact havg

/-- A finite uniform average never exceeds all of its values. -/
theorem exists_uniformAverage_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    ∃ ω, uniformAverage f ≤ f ω := by
  have huniv : (Finset.univ : Finset Ω).Nonempty := Finset.univ_nonempty
  obtain ⟨ω, _hmem, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Ω) f huniv
  refine ⟨ω, ?_⟩
  unfold uniformAverage
  have hcard : 0 < (Fintype.card Ω : ℝ) := by positivity
  rw [div_le_iff₀ hcard]
  calc
    (∑ x, f x) ≤ ∑ _x : Ω, f ω :=
      Finset.sum_le_sum fun x hx => hmax x hx
    _ = (Fintype.card Ω : ℝ) * f ω := by simp
    _ = f ω * (Fintype.card Ω : ℝ) := by ring

/-- Finite Yao selection: if the joint average over inputs and private seeds
is at least `L`, one fixed input has randomized expected cost at least `L`. -/
theorem finite_yao_select_fixed_input
    {Inputs Seeds : Type*}
    [Fintype Inputs] [Nonempty Inputs]
    [Fintype Seeds] [Nonempty Seeds]
    (cost : Inputs → Seeds → ℝ) {L : ℝ}
    (hjoint : L ≤ uniformAverage fun input =>
      uniformAverage fun seed => cost input seed) :
    ∃ input, L ≤ uniformAverage fun seed => cost input seed := by
  obtain ⟨input, hinput⟩ := exists_uniformAverage_le
    (fun input => uniformAverage fun seed => cost input seed)
  exact ⟨input, hjoint.trans hinput⟩

/-- Two finite uniform averages commute. -/
theorem uniformAverage_comm
    {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ]
    (f : Ω → Ξ → ℝ) :
    uniformAverage (fun ω => uniformAverage fun ξ => f ω ξ) =
      uniformAverage (fun ξ => uniformAverage fun ω => f ω ξ) := by
  unfold uniformAverage
  simp only
  rw [show (∑ ω, (∑ ξ, f ω ξ) / (Fintype.card Ξ : ℝ)) =
      (∑ ω, ∑ ξ, f ω ξ) / (Fintype.card Ξ : ℝ) by
        exact (Finset.sum_div Finset.univ (fun ω => ∑ ξ, f ω ξ) _).symm]
  rw [show (∑ ξ, (∑ ω, f ω ξ) / (Fintype.card Ω : ℝ)) =
      (∑ ξ, ∑ ω, f ω ξ) / (Fintype.card Ω : ℝ) by
        exact (Finset.sum_div Finset.univ (fun ξ => ∑ ω, f ω ξ) _).symm]
  rw [Finset.sum_comm]
  ring

/-- Ratio form of finite Yao averaging, allowing the offline optimum to vary
across inputs. -/
theorem finite_yao_select_ratio
    {Inputs Seeds : Type*}
    [Fintype Inputs] [Nonempty Inputs]
    [Fintype Seeds] [Nonempty Seeds]
    (cost : Inputs → Seeds → ℝ) (opt : Inputs → ℝ)
    {L O c : ℝ}
    (hcost : L ≤ uniformAverage fun input =>
      uniformAverage fun seed => cost input seed)
    (hopt : uniformAverage opt = O)
    (hcompare : c * O ≤ L) :
    ∃ input, c * opt input ≤ uniformAverage fun seed => cost input seed := by
  let excess : Inputs → ℝ := fun input =>
    uniformAverage (fun seed => cost input seed) - c * opt input
  have hexcess : 0 ≤ uniformAverage excess := by
    have hcalc : uniformAverage excess =
        uniformAverage (fun input => uniformAverage fun seed => cost input seed) -
          c * uniformAverage opt := by
      unfold excess
      calc
        uniformAverage (fun input =>
            uniformAverage (fun seed => cost input seed) - c * opt input) =
          uniformAverage (fun input => uniformAverage fun seed => cost input seed) +
            uniformAverage (fun input => (-c) * opt input) := by
              simpa [sub_eq_add_neg, mul_assoc] using
                (uniformAverage_add
                  (fun input => uniformAverage fun seed => cost input seed)
                  (fun input => (-c) * opt input))
        _ = uniformAverage (fun input => uniformAverage fun seed => cost input seed) -
            c * uniformAverage opt := by
              rw [uniformAverage_smul]
              ring
    rw [hcalc, hopt]
    linarith
  obtain ⟨input, hinput⟩ := exists_uniformAverage_le excess
  refine ⟨input, ?_⟩
  dsimp [excess] at hinput
  linarith

/-- Clairvoyant cost of `z` zero jobs followed by `l` jobs of processing
time two. -/
def binaryOfflineCost (z l : ℝ) : ℝ :=
  z * (z + 1) / 2 + l * z + 3 * l * (l + 1) / 2

/-- The balanced binary multiset has exact optimum `3m²+2m`. -/
theorem balanced_binaryOfflineCost (m : ℝ) :
    binaryOfflineCost m m = 3 * m ^ 2 + 2 * m := by
  unfold binaryOfflineCost
  ring

/-- Rewriting with `n=2m` gives `3n²/4+n`. -/
theorem balanced_binaryOfflineCost_eq_n
    {n m : ℝ} (hn : n = 2 * m) :
    binaryOfflineCost m m = 3 * n ^ 2 / 4 + n := by
  rw [balanced_binaryOfflineCost, hn]
  ring

/-- Ratio-ready scalar conclusion of the binary Yao lower bound. -/
theorem binary_ratio_lower
    {n error alg opt : ℝ}
    (hn : 0 < n)
    (herror : 0 ≤ error)
    (halg : n ^ 2 - error ≤ alg)
    (hopt : opt = 3 * n ^ 2 / 4 + n)
    (hoptPos : 0 < opt) :
    4 / 3 - (4 * error / (3 * n ^ 2) + 16 / (9 * n)) ≤ alg / opt := by
  rw [le_div_iff₀ hoptPos]
  rw [hopt]
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have herr := halg
  field_simp [hn.ne', hn2.ne']
  nlinarith

end

end RandomizedObligatory
end SchedulingPaper
