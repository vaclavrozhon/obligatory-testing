import SchedulingPaper.UpperBoundFinalAssembly
import SchedulingPaper.VerifiedLowerBoundFinalAssembly

/-!
# Main exact-ratio statements

This file is the top-level assembly point.  All operational constructions
have been discharged by the verified lower- and upper-bound assemblies, so
the advertised exact competitive-ratio theorems have no interface
parameters.

All algebraic, analytic, replay, offline-optimality, and branch-assembly
arguments used below are theorems in the imported modules, not axioms.
-/

namespace SchedulingPaper

noncomputable section

open LowerBound UpperBound

/-- Both directions of the exact finite-cap result, including an actual
deterministic online strategy for the upper direction. -/
structure FiniteExactRatioConclusion (u ratio : ℝ) : Prop where
  lower : LowerBound.FixedSizeLowerBound (.finite u) ratio
  upper :
    ∃ strategy : ∀ n, Online.Strategy n,
      UpperBound.CompletesByAnalysisFuel (.finite u) strategy ∧
      SizeAsymptoticUpper
        (UpperBound.strategyCost (.finite u) strategy)
        (UpperBound.fixedOfflineCost (.finite u)) ratio

/-- Both directions at the obligatory-testing endpoint. -/
structure ObligatoryExactRatioConclusion (ratio : ℝ) : Prop where
  lower : LowerBound.FixedSizeLowerBound .infinite ratio
  upper :
    ∃ strategy : ∀ n, Online.Strategy n,
      UpperBound.CompletesByAnalysisFuel .infinite strategy ∧
      SizeAsymptoticUpper
        (UpperBound.strategyCost .infinite strategy)
        (UpperBound.fixedOfflineCost .infinite) ratio

/-- Unconditional top-level finite-cap theorem. -/
theorem finite_exact_ratio
    {u : ℝ} (hu : 0 < u) :
    FiniteExactRatioConclusion u (exactCurve u) := by
  let certificate :=
    UpperBound.verifiedFiniteExactCurveCertificate hu
  refine
    { lower :=
        LowerBound.verified_finite_exactCurve_lower hu
      upper := ?_ }
  exact ⟨certificate.strategy, certificate.completes,
    certificate.sizeAsymptotic
      (by simpa [Cap.Valid] using hu)⟩

/-- Top-level obligatory-testing theorem, at the exact constant `RStar`. -/
theorem obligatory_exact_ratio
    : ObligatoryExactRatioConclusion RStar := by
  let certificate :=
    UpperBound.obligatoryCertificate_of_boundaryBridge
      UpperBound.obligatoryCompletion
      UpperBound.obligatoryBoundaryBridge_verified
  refine
    { lower :=
        LowerBound.verified_obligatory_RStar_lower
      upper := ?_ }
  exact
    ⟨certificate.strategy, certificate.completes,
      certificate.sizeAsymptotic (by simp [Cap.Valid])⟩

/-- One theorem exposing the two advertised conclusions simultaneously. -/
theorem exact_ratio_main
    : (∀ {u : ℝ}, 0 < u →
      FiniteExactRatioConclusion u (exactCurve u)) ∧
      ObligatoryExactRatioConclusion RStar := by
  constructor
  · intro u hu
    exact finite_exact_ratio hu
  · exact obligatory_exact_ratio

end

end SchedulingPaper
