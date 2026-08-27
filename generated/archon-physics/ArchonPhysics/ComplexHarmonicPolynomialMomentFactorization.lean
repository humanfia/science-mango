import ArchonPhysics.ComplexRegularizedMarkedLegBridge
import ArchonPhysics.PolynomialMarkedLegWindowStrongLaw

/-!
# Complex harmonic polynomial interaction moments

Cosine and sine quotient polynomials are combined into one complex spectral
weight.  On simple spectrum, each resulting projected-bond kernel is exactly
the corresponding complex zero-constant polynomial of the physical weighted
cycle.  The three-leg complex interaction moment therefore factors into the
same finite periodic polynomial kernels used by the local-window strong law.
-/

namespace ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization

open ArchonPhysics
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section

/-- Complex quotient-polynomial spectral weight for one marked leg. -/
def complexSpectralPolynomialLegWeight {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota)
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat -> Real)
    (k : Fin (Fintype.card iota)) : Complex :=
  (spectralPolynomialWeight A cosineDegree cosineCoefficient k : Complex) +
    (spectralPolynomialWeight A sineDegree sineCoefficient k : Complex) *
      Complex.I

/-- Complex zero-constant polynomial leg on the physical weighted cycle. -/
def complexHarmonicPolynomialLeg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat -> Real)
    (j l : Lattice.Site N) : Complex :=
  (zeroConstantMatrixPolynomialUpTo cosineDegree cosineCoefficient
      (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)) j l : Complex) +
    (zeroConstantMatrixPolynomialUpTo sineDegree sineCoefficient
      (weightedCycleLaplacian (fun i => (m.mass i)⁻¹)) j l : Complex) *
      Complex.I

/-- Exact one-leg complex polynomial functional-calculus identity. -/
theorem harmonicComplexWeightedProjectedBondKernel_polynomial_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (cosineDegree sineDegree : Nat)
    (cosineCoefficient sineCoefficient : Nat -> Real)
    (j l : Lattice.Site N) :
    complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (complexSpectralPolynomialLegWeight (harmonicHermitian m)
          cosineDegree sineDegree cosineCoefficient sineCoefficient) j l =
      complexHarmonicPolynomialLeg m
        cosineDegree sineDegree cosineCoefficient sineCoefficient j l := by
  apply Complex.ext
  · rw [complexWeightedProjectedBondKernel_re]
    simpa [complexSpectralPolynomialLegWeight, complexHarmonicPolynomialLeg] using
      congrFun (congrFun
        (harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_weightedCycle
          m hsimple cosineDegree cosineCoefficient) j) l
  · rw [complexWeightedProjectedBondKernel_im]
    simpa [complexSpectralPolynomialLegWeight, complexHarmonicPolynomialLeg] using
      congrFun (congrFun
        (harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_weightedCycle
          m hsimple sineDegree sineCoefficient) j) l

/-- Exact three-leg complex polynomial moment factorization. -/
theorem complexHarmonicThreeLegPolynomialMoment_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (cosineDegree sineDegree : Fin 3 -> Nat)
    (cosineCoefficient sineCoefficient : Fin 3 -> Nat -> Real) :
    complexWeightedInteractionMoment (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (fun r => complexSpectralPolynomialLegWeight (harmonicHermitian m)
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r)) =
      ∑ j, ∑ l, ∏ r : Fin 3,
        complexHarmonicPolynomialLeg m
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) j l := by
  rw [complexWeightedInteractionMoment_factorization]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro l _hl
  apply Finset.prod_congr rfl
  intro r _hr
  exact harmonicComplexWeightedProjectedBondKernel_polynomial_eq
    m hsimple (cosineDegree r) (sineDegree r)
      (cosineCoefficient r) (sineCoefficient r) j l

/-- Per-site form used by the thermodynamic strong-law bridge. -/
theorem complexHarmonicThreeLegPolynomialMoment_perSite_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (cosineDegree sineDegree : Fin 3 -> Nat)
    (cosineCoefficient sineCoefficient : Fin 3 -> Nat -> Real) :
    complexWeightedInteractionMoment (massWeightedDifferenceMatrix m)
          (harmonicHermitian m)
          (fun r => complexSpectralPolynomialLegWeight (harmonicHermitian m)
            (cosineDegree r) (sineDegree r)
            (cosineCoefficient r) (sineCoefficient r)) /
        (N : Real) =
      (∑ j, ∑ l, ∏ r : Fin 3,
        complexHarmonicPolynomialLeg m
          (cosineDegree r) (sineDegree r)
          (cosineCoefficient r) (sineCoefficient r) j l) /
        (N : Real) := by
  rw [complexHarmonicThreeLegPolynomialMoment_factorization
    m hsimple cosineDegree sineDegree cosineCoefficient sineCoefficient]

end

end ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
