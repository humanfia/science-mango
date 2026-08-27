import ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentAllVolume
import ArchonPhysics.CanonicalComplexSpectralPolynomialMomentStrongLaw

/-!
# Canonical complex spectral-polynomial moments at every positive volume

The periodic polynomial theorem already uses the single sequence of all
positive volumes `N = n + 1`.  On one probability-one event the corresponding
harmonic matrices have simple ordered spectrum simultaneously for every
`n`.  Exact spectral factorization then identifies the physical spectral
moment with its periodic polynomial representative term by term.

Thus the fixed spectral-polynomial moment converges along the common
all-volume sequence, with no realization-wise simplicity assumption in the
endpoint.
-/

namespace ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentAllVolume
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentStrongLaw
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

/-- The physical complex spectral-polynomial interaction moment per site for
the first `n + 1` iid masses. -/
def canonicalPositiveVolumeComplexSpectralPolynomialMoment
    (ensemble : IIDMassPhaseEnsemble Omega)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (n : Nat) (omega : Omega) : Complex :=
  complexWeightedInteractionMoment
      (massWeightedDifferenceMatrix
        (ensemble.restrictPositiveMass (N := n + 1) omega))
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 1) omega))
      (fun r ↦ complexSpectralPolynomialLegWeight
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 1) omega))
        (cosineDegree r) (sineDegree r)
        (cosineCoefficient r) (sineCoefficient r)) /
    (((n + 1 : Nat) : Real))

/-- One probability-one event carries full ordered spectral simplicity at
every volume `N = n + 1` with `N ≥ 2`. -/
theorem canonicalPositiveVolumes_simpleOrderedSpectrum_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability, ∀ n : Nat, 1 ≤ n →
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 1) omega)) := by
  apply ae_all_iff.mpr
  intro n
  by_cases hn : 1 ≤ n
  · filter_upwards
      [simpleOrderedSpectrum_ae ensemble (N := n + 1) (by omega)] with
        omega hsimple
    intro _hn
    simpa [harmonicHermitian, harmonicHermitianSample] using hsimple
  · exact Filter.Eventually.of_forall fun _omega hnprime ↦ (hn hnprime).elim

/-- At a simple-spectrum realization, the physical all-volume spectral
moment is exactly the periodic polynomial moment of the same first mass
restriction. -/
theorem canonicalPositiveVolumeComplexSpectralPolynomialMoment_eq_periodic_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 1) omega))) :
    canonicalPositiveVolumeComplexSpectralPolynomialMoment ensemble
        cosineDegree sineDegree cosineCoefficient sineCoefficient n omega =
      canonicalPositiveVolumeComplexPeriodicPolynomialMoment ensemble
        cosineDegree sineDegree cosineCoefficient sineCoefficient n omega := by
  let x : Fin (n + 1) → Real := ensemble.restrictMassFin omega
  have hmass :
      clippedPositiveMassConfig (siteVectorOfFin x) =
        ensemble.restrictPositiveMass (N := n + 1) omega := by
    exact clippedPositiveMassConfig_siteVectorOfFin_restrictMassFin
      ensemble omega
  have hsimple' : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x))) := by
    rw [hmass]
    exact hsimple
  unfold canonicalPositiveVolumeComplexSpectralPolynomialMoment
    canonicalPositiveVolumeComplexPeriodicPolynomialMoment
  rw [← hmass]
  exact complexWeightedInteractionPolynomialMomentPerSite_eq_periodic x hsimple'
    cosineDegree sineDegree cosineCoefficient sineCoefficient

/-- Almost-sure strong law for the physical fixed spectral-polynomial moment
along the single common sequence of every positive volume.  Spectral
simplicity is discharged on a common probability-one event. -/
theorem canonicalPositiveVolumeComplexSpectralPolynomialMoment_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (windowRadius : Nat)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          canonicalPositiveVolumeComplexSpectralPolynomialMoment ensemble
            cosineDegree sineDegree cosineCoefficient sineCoefficient n omega)
        atTop
        (nhds (complexWindowMean ensemble (2 * windowRadius + 1)
          (complexPolynomialRowWindowObservable windowRadius
            cosineDegree sineDegree cosineCoefficient sineCoefficient))) := by
  filter_upwards
    [canonicalPositiveVolumeComplexPeriodicPolynomialMoment_strongLaw_ae
      ensemble windowRadius cosineDegree sineDegree
        cosineCoefficient sineCoefficient hcosine hsine,
    canonicalPositiveVolumes_simpleOrderedSpectrum_ae ensemble] with
      omega hlimit hsimple
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  exact
    (canonicalPositiveVolumeComplexSpectralPolynomialMoment_eq_periodic_of_simple
      ensemble cosineDegree sineDegree cosineCoefficient sineCoefficient
      n omega (hsimple n hn)).symm

end

end ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
