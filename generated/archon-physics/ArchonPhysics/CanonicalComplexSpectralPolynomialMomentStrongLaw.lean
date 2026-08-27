import ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
import ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Canonical complex spectral-polynomial moment strong law

For every volume in the canonical first-restriction sequence, the iid mass
configuration agrees exactly with the clipped finite-coordinate
configuration used by the periodic polynomial calculation.  Full harmonic
spectral simplicity holds simultaneously at all these countably many
volumes on one probability-one event.  On that event the exact spectral
factorization and periodic reindexing identify the spectral-polynomial
interaction moment with the local polynomial moment.

Combining this identification with the periodic polynomial strong law gives
an almost-sure thermodynamic limit with no simple-spectrum hypothesis left
in the endpoint.
-/

namespace ArchonPhysics.CanonicalComplexSpectralPolynomialMomentStrongLaw

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Reindexing the first `N` iid masses and clipping them does not change the
positive-mass configuration: ensemble coordinates already lie in the frozen
mass support pointwise. -/
theorem clippedPositiveMassConfig_siteVectorOfFin_restrictMassFin
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (omega : Omega) :
    clippedPositiveMassConfig
        (siteVectorOfFin (ensemble.restrictMassFin (N := N) omega)) =
      ensemble.restrictPositiveMass (N := N) omega := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  funext i
  exact RandomEnsemble.clippedMass_eq_self
    (ensemble.mass_mem_support i.val omega)

/-- The physical complex spectral-polynomial interaction moment per site at
volume `N = (2 * windowRadius + 1) + (m + 1)`. -/
def canonicalRestrictedComplexSpectralPolynomialMoment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (m : Nat) (omega : Omega) : Complex :=
  complexWeightedInteractionMoment
      (massWeightedDifferenceMatrix
        (ensemble.restrictPositiveMass
          (N := (2 * windowRadius + 1) + (m + 1)) omega))
      (harmonicHermitian
        (ensemble.restrictPositiveMass
          (N := (2 * windowRadius + 1) + (m + 1)) omega))
      (fun r ↦ complexSpectralPolynomialLegWeight
        (harmonicHermitian
          (ensemble.restrictPositiveMass
            (N := (2 * windowRadius + 1) + (m + 1)) omega))
        (cosineDegree r) (sineDegree r)
        (cosineCoefficient r) (sineCoefficient r)) /
    (((2 * windowRadius + 1) + (m + 1) : Nat) : Real)

/-- One probability-one event carries full ordered spectral simplicity at
every volume in the canonical thermodynamic sequence. -/
theorem canonicalRestrictions_simpleOrderedSpectrum_ae
    (ensemble : IIDMassPhaseEnsemble Omega) (windowRadius : Nat) :
    ∀ᵐ omega ∂ensemble.probability, ∀ m : Nat,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass
            (N := (2 * windowRadius + 1) + (m + 1)) omega)) := by
  apply ae_all_iff.mpr
  intro m
  simpa [harmonicHermitian, harmonicHermitianSample] using
    (simpleOrderedSpectrum_ae ensemble
      (N := (2 * windowRadius + 1) + (m + 1)) (by omega))

/-- At a simple-spectrum realization, the physical spectral-polynomial
moment is exactly the finite periodic polynomial moment of the same first
mass restriction. -/
theorem canonicalRestrictedComplexSpectralPolynomialMoment_eq_periodic_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (m : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass
          (N := (2 * windowRadius + 1) + (m + 1)) omega))) :
    canonicalRestrictedComplexSpectralPolynomialMoment ensemble windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient m omega =
      canonicalRestrictedComplexPeriodicPolynomialMoment ensemble windowRadius
        cosineDegree sineDegree cosineCoefficient sineCoefficient m omega := by
  let x : Fin ((2 * windowRadius + 1) + (m + 1)) → Real :=
    ensemble.restrictMassFin omega
  have hmass :
      clippedPositiveMassConfig (siteVectorOfFin x) =
        ensemble.restrictPositiveMass
          (N := (2 * windowRadius + 1) + (m + 1)) omega := by
    exact clippedPositiveMassConfig_siteVectorOfFin_restrictMassFin
      ensemble omega
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x))) := by
    rw [hmass]
    exact hsimple
  unfold canonicalRestrictedComplexSpectralPolynomialMoment
    canonicalRestrictedComplexPeriodicPolynomialMoment
  rw [← hmass]
  exact complexWeightedInteractionPolynomialMomentPerSite_eq_periodic x hsimple'
    cosineDegree sineDegree cosineCoefficient sineCoefficient

/-- Almost-sure thermodynamic strong law for the complete fixed complex
spectral-polynomial interaction moment per site.  The only hypotheses are
the finite propagation radii needed by the polynomial window calculation;
spectral simplicity has been discharged almost surely and countably for all
volumes. -/
theorem canonicalRestrictedComplexSpectralPolynomialMoment_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun m : Nat ↦
          canonicalRestrictedComplexSpectralPolynomialMoment ensemble
            windowRadius cosineDegree sineDegree
            cosineCoefficient sineCoefficient m omega)
        atTop
        (𝓝 (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  filter_upwards
    [canonicalRestrictedComplexPeriodicPolynomialMoment_strongLaw_ae
      ensemble windowRadius cosineDegree sineDegree
        cosineCoefficient sineCoefficient hcosine hsine,
    canonicalRestrictions_simpleOrderedSpectrum_ae ensemble windowRadius] with
      omega hlimit hsimple
  apply hlimit.congr'
  exact Eventually.of_forall fun m ↦
    (canonicalRestrictedComplexSpectralPolynomialMoment_eq_periodic_of_simple
      ensemble windowRadius cosineDegree sineDegree
      cosineCoefficient sineCoefficient m omega (hsimple m)).symm

end

end ArchonPhysics.CanonicalComplexSpectralPolynomialMomentStrongLaw
