import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform testing: the static scheduling model

This file formalizes the common-upper-limit model from Section 3 of
"Exact Deterministic Ratios for Single-Machine Scheduling with Uniform Tests".

The online information structure is deliberately not part of this first
milestone.  Here we capture jobs, the finite/infinite cap, and the clairvoyant
effective length used by the offline optimum.
-/

namespace SchedulingPaper

noncomputable section

/-- A common upper limit.  `finite u` is the optional-testing model, while
`infinite` is obligatory testing. -/
inductive Cap where
  | finite (u : ℝ)
  | infinite
  deriving DecidableEq

/-- The parameter range from the paper: finite caps are strictly positive;
the obligatory endpoint is always valid. -/
def Cap.Valid : Cap → Prop
  | .finite u => 0 < u
  | .infinite => True

/-- Uniform lower bound on every effective length at a given cap. -/
def Cap.baseLength : Cap → ℝ
  | .finite u => min u 1
  | .infinite => 1

/-- A job is represented by its (eventually revealed) processing time. -/
structure Job where
  processingTime : ℝ
  processingTime_nonneg : 0 ≤ processingTime

/-- A fixed input instance.  At a finite cap, processing times lie below the
known common upper limit; obligatory instances have no upper restriction. -/
structure Instance where
  cap : Cap
  cap_valid : cap.Valid
  jobs : List Job
  processingTime_le_cap : ∀ job ∈ jobs, ∀ u, cap = .finite u → job.processingTime ≤ u

/-- The duration chosen by a clairvoyant scheduler for one job:
`min u (1 + p)` at a finite cap and `1 + p` at the obligatory endpoint. -/
def effectiveLength : Cap → ℝ → ℝ
  | .finite u, p => min u (1 + p)
  | .infinite, p => 1 + p

/-- The two modes available at a finite cap. -/
inductive Mode where
  | raw
  | tested
  deriving DecidableEq

/-- Total machine time needed to complete one job in a chosen finite-cap mode. -/
def modeLength (u p : ℝ) : Mode → ℝ
  | .raw => u
  | .tested => 1 + p

@[simp] theorem effectiveLength_finite (u p : ℝ) :
    effectiveLength (.finite u) p = min u (1 + p) := rfl

@[simp] theorem effectiveLength_infinite (p : ℝ) :
    effectiveLength .infinite p = 1 + p := rfl

@[simp] theorem modeLength_raw (u p : ℝ) : modeLength u p .raw = u := rfl

@[simp] theorem modeLength_tested (u p : ℝ) : modeLength u p .tested = 1 + p := rfl

/-- The paper's rule for a clairvoyant mode choice at a finite cap. -/
def offlineMode (u p : ℝ) : Mode := if u ≤ 1 + p then .raw else .tested

theorem modeLength_offlineMode (u p : ℝ) :
    modeLength u p (offlineMode u p) = effectiveLength (.finite u) p := by
  by_cases h : u ≤ 1 + p
  · simp [offlineMode, h, effectiveLength]
  · have h' : 1 + p ≤ u := le_of_not_ge h
    simp [offlineMode, h, effectiveLength, min_eq_right h']

theorem effectiveLength_nonneg (cap : Cap) (hcap : cap.Valid)
    (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ effectiveLength cap p := by
  cases cap with
  | finite u =>
      simp only [effectiveLength_finite]
      exact le_min hcap.le (by linarith)
  | infinite =>
      simp only [effectiveLength_infinite]
      linarith

/-- Every effective length is at least `min u 1` at a finite cap and at
least one at the obligatory endpoint. -/
theorem baseLength_le_effectiveLength (cap : Cap) (p : ℝ) (hp : 0 ≤ p) :
    cap.baseLength ≤ effectiveLength cap p := by
  cases cap with
  | finite u =>
      exact min_le_min le_rfl (by linarith)
  | infinite =>
      simp only [Cap.baseLength, effectiveLength]
      linarith

theorem Cap.baseLength_nonneg {cap : Cap} (hcap : cap.Valid) :
    0 ≤ cap.baseLength := by
  cases cap with
  | finite u => exact le_min hcap.le zero_le_one
  | infinite => simp [Cap.baseLength]

end

end SchedulingPaper
