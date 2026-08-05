import SchedulingPaper.VerifiedZeroPrefixBridge
import SchedulingPaper.UTEEndpointFiniteBridge
import SchedulingPaper.VerifiedBoundaryBridges
import SchedulingPaper.VerifiedUTEBelowTwoBridgeFinal
import SchedulingPaper.VerifiedMixedBoundaryBridge

/-!
# Final upper-bound branch assembly

This module is deliberately downstream of `VerifiedZeroPrefixBridge`.
`UpperBoundAssembly` defines the operational strategies, certificates, and
the still-open branch interface; the present module performs the final
six-branch split after the Zero-prefix operational bridge has been proved.
This dependency direction avoids making the proved Zero-prefix bridge an
extra premise of the public certificate.
-/

namespace SchedulingPaper

noncomputable section

namespace UpperBound

open LowerBound

/-- All formerly open upper operational branches, bundled from their
verified runtime/accounting theorems. -/
noncomputable def verifiedOperationalUpperInterfaces :
    OperationalUpperInterfaces where
  uteBelowTwoCost := uteBelowTwoCostBridge_verified
  mixedBoundary := verifiedMixedBoundaryBridge

/-- A finite-cap certificate for the exact curve.  The Zero-prefix branch is
now discharged by `verifiedZeroPrefixCostBridge`; only the fields of
`OperationalUpperInterfaces` remain as operational inputs. -/
noncomputable def finite_exactCurve_certificate
    (interfaces : OperationalUpperInterfaces)
    {u : ℝ} (hu : 0 < u) :
    FixedUpperCertificate (.finite u) (exactCurve u) := by
  by_cases h1 : u ≤ 1
  · rw [exactCurve_eq_one h1]
    exact verifiedRawOneCertificate hu h1
  by_cases hDiamond : u ≤ uDiamond
  · have hu1 : 1 < u := lt_of_not_ge h1
    rw [exactCurve_eq_self hu1 hDiamond]
    exact verifiedRawIdentityCertificate hu hu1.le
  by_cases hZero : u ≤ uZero
  · have hDiamondStrict : uDiamond < u := lt_of_not_ge hDiamond
    rw [exactCurve_eq_rhoI hDiamondStrict hZero]
    by_cases hTwo : u < 2
    · let s := u - 1
      have hsDiamond : uDiamond - 1 < s := by
        dsimp [s]
        linarith
      have hsOne : s < 1 := by
        dsimp [s]
        linarith
      simpa [s, uteRho] using
        uteBelowTwoCertificate
          (uteEndpointCompletion s)
          (interfaces.uteBelowTwoCost hsDiamond hsOne)
    · let s := u - 1
      have hs1 : 1 ≤ s := by
        dsimp [s]
        linarith
      have hs0 : s ≤ sZero := by
        dsimp [s]
        unfold uZero at hZero
        linarith
      simpa [s, uteRho] using
        uteEndpointCertificate hs1 hs0
          (uteEndpointCompletion s)
          (uteEndpointCostBridge_verified hs1 hs0)
  by_cases hGolden : u ≤ goldenRatio + 2
  · have hZeroStrict : uZero < u := lt_of_not_ge hZero
    rw [exactCurve_eq_reciprocal hZeroStrict hGolden]
    let s := u - 1
    have hs : 0 < s := by
      dsimp [s]
      linarith [uZero_bounds.1]
    have hsφ : s ≤ goldenRatio + 1 := by
      dsimp [s]
      linarith
    simpa [s, zeroPrefixFactor, reciprocalBranch] using
      zeroPrefixCertificate hs hsφ
        (zeroPrefixCompletion s)
        (verifiedZeroPrefixCostBridge hs hsφ)
  by_cases hStar : u ≤ zStar
  · have hGoldenStrict : goldenRatio + 2 < u :=
      lt_of_not_ge hGolden
    rw [exactCurve_eq_mixed hGoldenStrict hStar]
    let us : MixedUpperDomain := ⟨u, hGoldenStrict.le, hStar⟩
    let c : MixedRatioDomain := mixedRatioAtUpper us
    have hfull :=
      exists_reachableCompleteCappedBankRemainder c
    let C₀ : ℝ := hfull.choose
    have hTaylor :
        HasReachableCompleteCappedBankRemainder
          c (mixedReserveDelta c) (mixedMass c) C₀ :=
      hfull.choose_spec.2
    have hcertificate :=
      mixedCertificate_of_boundaryBridge c hTaylor
        (mixedCompletion c)
        (interfaces.mixedBoundary c)
    simpa [us, c, mixedFiniteCurve, mixedCompetitiveRatio,
      mixedRatioAtUpper_equation] using hcertificate
  · have hStarStrict : zStar < u := lt_of_not_ge hStar
    rw [exactCurve_eq_plateau hStarStrict]
    exact plateauCertificate_of_boundaryBridge
      (plateauCompletion u)
      (plateauBoundaryBridge_verified hStarStrict.le)

theorem finite_exactCurve_sizeAsymptoticUpper
    (interfaces : OperationalUpperInterfaces)
    {u : ℝ} (hu : 0 < u) :
    let certificate :=
      finite_exactCurve_certificate interfaces hu
    SizeAsymptoticUpper
      (strategyCost (.finite u) certificate.strategy)
      (fixedOfflineCost (.finite u)) (exactCurve u) := by
  dsimp only
  exact
    (finite_exactCurve_certificate interfaces hu).sizeAsymptotic
      (by simpa [Cap.Valid] using hu)

/-- Unconditional exact-curve upper certificate. -/
noncomputable def verifiedFiniteExactCurveCertificate
    {u : ℝ} (hu : 0 < u) :
    FixedUpperCertificate (.finite u) (exactCurve u) :=
  finite_exactCurve_certificate verifiedOperationalUpperInterfaces hu

/-- Unconditional size-asymptotic upper bound on every positive finite
cap. -/
theorem verified_finite_exactCurve_sizeAsymptoticUpper
    {u : ℝ} (hu : 0 < u) :
    let certificate := verifiedFiniteExactCurveCertificate hu
    SizeAsymptoticUpper
      (strategyCost (.finite u) certificate.strategy)
      (fixedOfflineCost (.finite u)) (exactCurve u) := by
  simpa [verifiedFiniteExactCurveCertificate] using
    finite_exactCurve_sizeAsymptoticUpper
      verifiedOperationalUpperInterfaces hu

end UpperBound

end

end SchedulingPaper
