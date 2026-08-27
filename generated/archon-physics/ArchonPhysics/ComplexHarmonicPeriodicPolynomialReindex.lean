import ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
import ArchonPhysics.CanonicalThresholdCountMcDiarmid
import ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
import ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
/-!
# Reindexing complex harmonic polynomial moments to finite periodic coordinates

The physical polynomial legs act on periodic sites `ZMod N`, whereas the
finite-window strong law uses the canonical `Fin N` enumeration.  For a raw
finite mass vector, clipping and inversion commute exactly with this
enumeration.  Consequently both each complex polynomial leg and the complete
three-leg double moment per site agree with their finite periodic versions.
-/

namespace ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex

open ArchonPhysics
open ArchonPhysics.CanonicalComplexPeriodicPolynomialMomentStrongLaw
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexPeriodicPolynomialWindowRowSum
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open ArchonPhysics.PeriodicPolynomialWindowReindex
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw

noncomputable section

/-- The inverse masses of the clipped physical configuration are exactly the
inverse clipped `Fin N` coordinates. -/
theorem inverseMassCoordinates_clipped_siteVectorOfFin
    {N : Nat} [NeZero N] (x : Fin N → Real) :
    RandomMassResultantBridge.inverseMassCoordinates
        (clippedPositiveMassConfig (siteVectorOfFin x)) =
      inverseClippedWindow x := by
  funext i
  simp [RandomMassResultantBridge.inverseMassCoordinates,
    clippedPositiveMassConfig, siteVectorOfFin, inverseClippedWindow,
    val_siteEquivFin_symm]

/-- A complex physical polynomial leg is exactly its canonical finite
periodic reindexing. -/
theorem complexHarmonicPolynomialLeg_reindex
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat → Real)
    (i j : Fin N) :
    complexHarmonicPolynomialLeg
        (clippedPositiveMassConfig (siteVectorOfFin x))
        cosineDegree sineDegree cosineCoefficient sineCoefficient
        ((siteEquivFin N).symm i) ((siteEquivFin N).symm j) =
      complexPeriodicPolynomialLeg x
        cosineDegree sineDegree cosineCoefficient sineCoefficient i j := by
  let m : Lattice.PositiveMassConfig N :=
    clippedPositiveMassConfig (siteVectorOfFin x)
  have hinverse :
      RandomMassResultantBridge.inverseMassCoordinates m =
        inverseClippedWindow x := by
    exact inverseMassCoordinates_clipped_siteVectorOfFin x
  have hmatrix :
      finWeightedCycleLaplacian (inverseClippedWindow x) =
        Matrix.reindex (siteEquivFin N) (siteEquivFin N)
          (weightedCycleLaplacian (fun s ↦ (m.mass s)⁻¹)) := by
    rw [← hinverse]
    unfold finWeightedCycleLaplacian
    rw [RandomMassResultantBridge.weightsOfCoordinates_inverseMassCoordinates]
  unfold complexPeriodicPolynomialLeg
  rw [hmatrix,
    zeroConstantMatrixPolynomialUpTo_reindex_apply,
    zeroConstantMatrixPolynomialUpTo_reindex_apply]
  rfl

/-- The complete physical three-leg polynomial double moment per site is the
finite periodic polynomial double moment per site. -/
theorem complexHarmonicThreeLegPolynomialMomentPerSite_reindex
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
    (∑ j : Lattice.Site N, ∑ l : Lattice.Site N, ∏ r : Fin 3,
        complexHarmonicPolynomialLeg
          (clippedPositiveMassConfig (siteVectorOfFin x))
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) j l) /
        (N : Real) =
      (∑ i : Fin N, ∑ j : Fin N, ∏ r : Fin 3,
        complexPeriodicPolynomialLeg x
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) i j) /
        (N : Real) := by
  congr 1
  apply Fintype.sum_equiv (siteEquivFin N)
  intro j
  apply Fintype.sum_equiv (siteEquivFin N)
  intro l
  apply Finset.prod_congr rfl
  intro r _hr
  simpa using complexHarmonicPolynomialLeg_reindex x
    (cosineDegree r) (sineDegree r)
    (cosineCoefficient r) (sineCoefficient r)
    (siteEquivFin N j) (siteEquivFin N l)

/-- Combining spectral factorization with the coordinate reindexing gives a
direct equality from the complex harmonic interaction moment per site to the
finite periodic polynomial double moment. -/
theorem complexWeightedInteractionPolynomialMomentPerSite_reindex
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x))))
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
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
        (N : Real) =
      (∑ i : Fin N, ∑ j : Fin N, ∏ r : Fin 3,
        complexPeriodicPolynomialLeg x
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) i j) /
        (N : Real) := by
  rw [complexHarmonicThreeLegPolynomialMoment_perSite_factorization
    (clippedPositiveMassConfig (siteVectorOfFin x)) hsimple
    cosineDegree sineDegree cosineCoefficient sineCoefficient]
  exact complexHarmonicThreeLegPolynomialMomentPerSite_reindex x
    cosineDegree sineDegree cosineCoefficient sineCoefficient

/-- Public aggregate form: the spectral polynomial interaction moment per
site is exactly the periodic double-moment observable used by the strong law. -/
theorem complexWeightedInteractionPolynomialMomentPerSite_eq_periodic
    {N : Nat} [NeZero N] (x : Fin N → Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x))))
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real) :
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
        (N : Real) =
      complexPeriodicPolynomialDoubleMomentPerSite x
        cosineDegree sineDegree cosineCoefficient sineCoefficient := by
  simpa [complexPeriodicPolynomialDoubleMomentPerSite] using
    complexWeightedInteractionPolynomialMomentPerSite_reindex x hsimple
      cosineDegree sineDegree cosineCoefficient sineCoefficient

end

end ArchonPhysics.ComplexHarmonicPeriodicPolynomialReindex
