import SchedulingPaper.MixedQuotaVerifiedBridge
import SchedulingPaper.LowBaseline
import SchedulingPaper.HiddenStoppingGlobalExchange
import SchedulingPaper.BoundedHarmonic

/-!
# Final verified lower-bound assembly

This module is the lower-bound counterpart of
`UpperBoundFinalAssembly`.  It bundles the five concrete operational
constructions after the mixed-quota branch has been discharged and exports
the exact-curve lower bounds without an interface parameter.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-- Every operational branch used by the lower-bound assembly, filled by a
verified construction. -/
noncomputable def verifiedOperationalLowerInterfaces :
    OperationalLowerInterfaces where
  baseline := operationalLowerBaseline
  hiddenStoppingFiniteCost := hiddenStoppingFiniteCostBridge
  mixedQuota := mixedQuota_adaptive
  boundedHarmonic := boundedHarmonic_adaptive_RStar
  harmonic := harmonic_adaptive_RStar

/-- Unconditional adaptive exact-curve lower bound for every positive finite
cap. -/
theorem verified_finite_exactCurve_adaptive
    {u : ℝ} (hu : 0 < u) :
    AdaptiveSizeLowerBound (.finite u) (exactCurve u) :=
  finite_exactCurve_adaptive verifiedOperationalLowerInterfaces hu

/-- Unconditional fixed-instance exact-curve lower bound for every positive
finite cap. -/
theorem verified_finite_exactCurve_lower
    {u : ℝ} (hu : 0 < u) :
    FixedSizeLowerBound (.finite u) (exactCurve u) :=
  finite_exactCurve_lower verifiedOperationalLowerInterfaces hu

/-- Unconditional fixed-instance lower bound at the obligatory-testing
endpoint. -/
theorem verified_obligatory_RStar_lower :
    FixedSizeLowerBound .infinite RStar :=
  obligatory_RStar_lower verifiedOperationalLowerInterfaces

end LowerBound

end

end SchedulingPaper
