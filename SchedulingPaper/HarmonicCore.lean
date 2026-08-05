import SchedulingPaper.Constants
import SchedulingPaper.HiddenStopping

/-!
# Finite harmonic cancellation

This file captures the exact finite algebra that makes the obligatory lower
bound independent of the online algorithm's phase decisions.  Analytic
passage from these finite sums to a Riemann integral is kept separate.
-/

namespace SchedulingPaper

noncomputable section

/-- Processing level at distance `m` above the shortest positive block. -/
def harmonicLevel (ξ γ : ℝ) (m : ℕ) : ℝ :=
  1 + γ / ξ + ∑ r ∈ Finset.range m, 1 / (ξ + (r + 1 : ℕ))

/-- Total multiplicity-weighted gap to the `m` shorter types. -/
def harmonicWeightedGap (ξ : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, (r + 1 : ℕ) / (ξ + (r + 1 : ℕ))

theorem harmonicLevel_zero (ξ γ : ℝ) :
    harmonicLevel ξ γ 0 = 1 + γ / ξ := by
  simp [harmonicLevel]

theorem harmonicLevel_succ (ξ γ : ℝ) (m : ℕ) :
    harmonicLevel ξ γ (m + 1) =
      harmonicLevel ξ γ m + 1 / (ξ + (m + 1 : ℕ)) := by
  simp [harmonicLevel, Finset.sum_range_succ]
  ring

theorem harmonicLevel_strictMono {ξ γ : ℝ} (hξ : 0 < ξ) :
    StrictMono (harmonicLevel ξ γ) := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [harmonicLevel_succ]
  have : 0 < 1 / (ξ + (m + 1 : ℕ)) := by positivity
  linarith

/-- Equation (4.18): the zero-block weight `ξ` and shorter-type
multiplicities telescope each harmonic denominator to one. -/
theorem harmonic_telescope {ξ γ : ℝ} (hξ : 0 < ξ) (m : ℕ) :
    ξ * (harmonicLevel ξ γ m - 1) + harmonicWeightedGap ξ m =
      γ + m := by
  have hbase : ξ * (γ / ξ) = γ := by field_simp [hξ.ne']
  have hterm (r : ℕ) :
      ξ * (1 / (ξ + (r + 1 : ℕ))) +
          (r + 1 : ℕ) / (ξ + (r + 1 : ℕ)) = 1 := by
    have hden : ξ + (r + 1 : ℕ) ≠ 0 := by positivity
    field_simp [hden]
  have hsum :
      ξ * (∑ r ∈ Finset.range m, 1 / (ξ + (r + 1 : ℕ))) +
          (∑ r ∈ Finset.range m,
            (r + 1 : ℕ) / (ξ + (r + 1 : ℕ))) = m := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ r ∈ Finset.range m,
          (ξ * (1 / (ξ + (r + 1 : ℕ))) +
            (r + 1 : ℕ) / (ξ + (r + 1 : ℕ)))) =
          ∑ _r ∈ Finset.range m, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro r _hr
            exact hterm r
      _ = m := by simp
  unfold harmonicLevel harmonicWeightedGap
  rw [show 1 + γ / ξ +
      (∑ r ∈ Finset.range m, 1 / (ξ + (r + 1 : ℕ))) - 1 =
      γ / ξ + ∑ r ∈ Finset.range m, 1 / (ξ + (r + 1 : ℕ)) by ring]
  rw [mul_add, hbase]
  linarith

/-- The phase coefficient `θ_j`, indexed only by the number `m` of shorter
types. -/
def harmonicTheta (ξ γ : ℝ) (m : ℕ) : ℝ :=
  1 - ξ * (harmonicLevel ξ γ m - 1) -
    (harmonicWeightedGap ξ m - m)

/-- Equation (4.19): every type receives the same coefficient. -/
theorem harmonicTheta_eq {ξ γ : ℝ} (hξ : 0 < ξ) (m : ℕ) :
    harmonicTheta ξ γ m = 1 - γ := by
  unfold harmonicTheta
  have ht := harmonic_telescope hξ m (γ := γ)
  linarith

/-- Abstract delayed-completion bracket with `k` intervening types. -/
def delayedBracket {k : ℕ} (γ : ℝ) (gap completed : Fin k → ℝ) : ℝ :=
  (k + 1 : ℕ) - (1 - γ) - ∑ i, gap i * completed i

/-- Replacing every completion fraction by one can only lower the bracket. -/
theorem delayedBracket_lower {k : ℕ} {γ : ℝ}
    {gap completed : Fin k → ℝ}
    (hgap : ∀ i, 0 ≤ gap i) (hcompleted : ∀ i, completed i ≤ 1) :
    γ + ∑ i, (1 - gap i) ≤ delayedBracket γ gap completed := by
  have hsum : ∑ i, gap i * completed i ≤ ∑ i, gap i := by
    exact Finset.sum_le_sum fun i _hi => by
      nlinarith [mul_nonneg (hgap i) (sub_nonneg.mpr (hcompleted i))]
  have hones : (∑ _i : Fin k, (1 : ℝ)) = k := by simp
  unfold delayedBracket
  rw [Finset.sum_sub_distrib, hones]
  push_cast
  linarith

/-- Under the span condition every delayed-completion coefficient is
strictly positive and may be discarded from a lower bound. -/
theorem delayedBracket_pos {k : ℕ} {γ : ℝ}
    {gap completed : Fin k → ℝ}
    (hγ : 0 < γ) (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap1 : ∀ i, gap i < 1) (hcompleted : ∀ i, completed i ≤ 1) :
    0 < delayedBracket γ gap completed := by
  have hlower := delayedBracket_lower (γ := γ) hgap0 hcompleted
  have hsum : 0 ≤ ∑ i, (1 - gap i) :=
    Finset.sum_nonneg fun i _hi => (sub_nonneg.mpr (hgap1 i).le)
  linarith

/-- Own-phase term in the finite accounting identity. -/
def ownPhaseTerm (θ s : ℝ) : ℝ := s ^ 2 / 2 - θ * s

/-- Equation (4.20), completing the independent square for each type. -/
theorem ownPhaseTerm_completeSquare (γ s : ℝ) :
    ownPhaseTerm (1 - γ) s =
      (s - (1 - γ)) ^ 2 / 2 - (1 - γ) ^ 2 / 2 := by
  unfold ownPhaseTerm
  ring

theorem ownPhaseTerm_lower (γ s : ℝ) :
    -(1 - γ) ^ 2 / 2 ≤ ownPhaseTerm (1 - γ) s := by
  rw [ownPhaseTerm_completeSquare]
  nlinarith [sq_nonneg (s - (1 - γ))]

/-! ## Collecting the finite accounting certificate -/

/-- Abstract form of the right-hand side of equation (4.17), after harmonic
cancellation has made every own-phase coefficient equal to `1-γ`. -/
def harmonicAccountingCertificate {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (C γ : ℝ) (own : ι → ℝ) (delayedMass delayedCoeff : κ → ℝ) : ℝ :=
  C + ∑ i, ownPhaseTerm (1 - γ) (own i) +
    ∑ q, delayedMass q * delayedCoeff q

/-- Once delayed masses and their brackets are nonnegative, completing one
independent square per positive type gives the finite lower certificate
`C - K(1-γ)²/2`. -/
theorem harmonicAccountingCertificate_lower
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {C γ : ℝ} {own : ι → ℝ} {delayedMass delayedCoeff : κ → ℝ}
    (hmass : ∀ q, 0 ≤ delayedMass q)
    (hcoeff : ∀ q, 0 ≤ delayedCoeff q) :
    C - Fintype.card ι * (1 - γ) ^ 2 / 2 ≤
      harmonicAccountingCertificate C γ own delayedMass delayedCoeff := by
  have hown :
      ∑ _i : ι, (-(1 - γ) ^ 2 / 2) ≤
        ∑ i : ι, ownPhaseTerm (1 - γ) (own i) :=
    Finset.sum_le_sum fun i _hi => ownPhaseTerm_lower γ (own i)
  have hdelay :
      0 ≤ ∑ q : κ, delayedMass q * delayedCoeff q :=
    Finset.sum_nonneg fun q _hq => mul_nonneg (hmass q) (hcoeff q)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hown
  unfold harmonicAccountingCertificate
  nlinarith

/-- Specialization with exactly `K` positive types. -/
theorem harmonicAccountingCertificate_fin_lower
    {K : ℕ} {κ : Type*} [Fintype κ]
    {C γ : ℝ} {own : Fin K → ℝ}
    {delayedMass delayedCoeff : κ → ℝ}
    (hmass : ∀ q, 0 ≤ delayedMass q)
    (hcoeff : ∀ q, 0 ≤ delayedCoeff q) :
    C - K * (1 - γ) ^ 2 / 2 ≤
      harmonicAccountingCertificate C γ own delayedMass delayedCoeff := by
  simpa using
    harmonicAccountingCertificate_lower
      (C := C) (γ := γ) (own := own)
      (delayedMass := delayedMass) (delayedCoeff := delayedCoeff)
      hmass hcoeff

end

end SchedulingPaper
