import ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex

/-!
# Deterministic periodic-kernel/window reindex

The fixed-target row identity is promoted here to the complete finite-volume
double moment.  For an arbitrary finite mass vector, summing first over the
periodic right endpoint and then over the target site is exactly the average
of the corresponding centered translated-window observables.

This is only a finite deterministic reindex.  It assumes neither an iid law
nor a thermodynamic limit, and it does not assert the varying-volume
continuous marked-kernel limit.
-/

namespace ArchonPhysics.DeterministicPeriodicKernelWindowReindex

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex
open ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PeriodicPolynomialWindowGeometricInterior
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section

/-- The complete finite periodic polynomial moment is exactly the average of
its centered translated-window rows.  This is the deterministic
periodic-interior-to-window reindex, before any probability or limiting
argument. -/
theorem complexPeriodicPolynomialDoubleMomentPerSite_eq_centeredWindowAverage
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    let centerBig :=
      Fin.castAdd m (centeredWindowIndex windowRadius)
    complexPeriodicPolynomialDoubleMomentPerSite x
        cosineDegree sineDegree cosineCoefficient sineCoefficient =
      (∑ target : Fin ((2 * windowRadius + 1) + m),
        complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (translatedMassWindow x
            (finCenteringShift centerBig target))) /
        (((2 * windowRadius + 1) + m : Nat) : Real) := by
  dsimp only
  unfold complexPeriodicPolynomialDoubleMomentPerSite
  congr 1
  apply Finset.sum_congr rfl
  intro target _htarget
  simpa [complexPolynomialRowWindowObservable] using
    complexThreeLegPeriodicPolynomialRowSum_eq_centeredWindowSum
      x target cosineDegree sineDegree cosineCoefficient sineCoefficient
        hcosine hsine

/-- Direct physical spectral-polynomial form of the same deterministic
reindex.  The only spectral premise is the existing finite-dimensional
functional-calculus premise; the reindex itself adds no probabilistic or
physical assumption. -/
theorem complexWeightedInteractionPolynomialMomentPerSite_eq_centeredWindowAverage
    {m windowRadius : Nat} [NeZero m]
    (x : Fin ((2 * windowRadius + 1) + m) → Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x))))
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (hcosine : ∀ r, cosineDegree r + 1 ≤ windowRadius)
    (hsine : ∀ r, sineDegree r + 1 ≤ windowRadius) :
    let centerBig :=
      Fin.castAdd m (centeredWindowIndex windowRadius)
    complexWeightedInteractionMoment
        (massWeightedDifferenceMatrix
          (clippedPositiveMassConfig (siteVectorOfFin x)))
        (harmonicHermitian
          (clippedPositiveMassConfig (siteVectorOfFin x)))
        (fun r ↦ complexSpectralPolynomialLegWeight
          (harmonicHermitian
            (clippedPositiveMassConfig (siteVectorOfFin x)))
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r)) /
        (((2 * windowRadius + 1) + m : Nat) : Real) =
      (∑ target : Fin ((2 * windowRadius + 1) + m),
        complexPolynomialRowWindowObservable windowRadius
          cosineDegree sineDegree cosineCoefficient sineCoefficient
          (translatedMassWindow x
            (finCenteringShift centerBig target))) /
        (((2 * windowRadius + 1) + m : Nat) : Real) := by
  dsimp only
  rw [complexWeightedInteractionPolynomialMomentPerSite_eq_periodic
    x hsimple cosineDegree sineDegree cosineCoefficient sineCoefficient]
  exact
    complexPeriodicPolynomialDoubleMomentPerSite_eq_centeredWindowAverage
      x cosineDegree sineDegree cosineCoefficient sineCoefficient
        hcosine hsine

end

end ArchonPhysics.DeterministicPeriodicKernelWindowReindex
