import ArchonPhysics.ActualProjectorAdjugatePolynomial
import ArchonPhysics.FixedEnergySpectrumAvoidance

/-!
# Polynomial system for actual projector-minor degeneracy

The adjugate numerator still contains three spectral variables.  This module
adds the three characteristic equations that those variables satisfy in the
actual random-mass dual-cycle model.  On the simple-spectrum locus, projector
minor degeneracy is thereby identified with the simultaneous zero set of four
fully explicit multivariate polynomials.

This is the input to chamber-wise or resultant elimination.  It does not claim
that an unsaturated iterated resultant is nonzero; zero-mode and Vandermonde
components must be handled in that later step.
-/

open scoped Matrix

namespace ArchonPhysics.ActualProjectorAdjugateSpectralSystem

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- The symbolic characteristic equation for one of the three spectral
variables. -/
def symbolicSelectedCharacteristicEquation
    {N : Nat} [NeZero N] (r : Fin 3) :
    MvPolynomial (AdjugateSpectralVariable N) Real :=
  (symbolicAdjugateWeightedCycleLaplacian (N := N)).charpoly.eval
    (MvPolynomial.X
      (Sum.inr r : AdjugateSpectralVariable N))

/-- Joint evaluation specializes the symbolic characteristic equation to the
concrete weighted-cycle characteristic polynomial. -/
theorem evaluate_symbolicSelectedCharacteristicEquation
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real) (r : Fin 3) :
    MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
        (symbolicSelectedCharacteristicEquation (N := N) r) =
      (weightedCycleLaplacian (weightsOfCoordinates x)).charpoly.eval
        (lambda r) := by
  unfold symbolicSelectedCharacteristicEquation
  calc
    MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
        (Polynomial.eval
          (MvPolynomial.X
            (Sum.inr r : AdjugateSpectralVariable N))
          (symbolicAdjugateWeightedCycleLaplacian (N := N)).charpoly) =
      Polynomial.eval₂
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda))
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
          (MvPolynomial.X
            (Sum.inr r : AdjugateSpectralVariable N)))
        (symbolicAdjugateWeightedCycleLaplacian (N := N)).charpoly := by
          symm
          exact Polynomial.eval₂_at_apply
            (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)) _
    _ = Polynomial.eval
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
          (MvPolynomial.X
            (Sum.inr r : AdjugateSpectralVariable N)))
        (Polynomial.map
          (MvPolynomial.eval (adjugateSpectralEvaluation x lambda))
          (symbolicAdjugateWeightedCycleLaplacian (N := N)).charpoly) :=
      Polynomial.eval₂_eq_eval_map _
    _ = (weightedCycleLaplacian (weightsOfCoordinates x)).charpoly.eval
        (lambda r) := by
      rw [← Matrix.charpoly_map,
        evaluate_symbolicAdjugateWeightedCycleLaplacian]
      simp [adjugateSpectralEvaluation]

/-- The genuine joint inverse-mass/eigenvalue point for one actual mode
triple. -/
def actualThreeMassAdjugateSpectralPoint
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : AdjugateSpectralVariable N → Real :=
  adjugateSpectralEvaluation
    (inverseMassCoordinates
      (threeMassSiteConfig fixed site₀ site₁ site₂ triple))
    (fun r => orderedEigenvalue
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)
      (modes r))

/-- The inverse-mass polynomial matrix at an actual triple is exactly the
matrix value of the genuine dual Hermitian family. -/
theorem weightedCycleLaplacian_actualThreeMass_eq_matrixVal
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (triple : MassTriple) :
    weightedCycleLaplacian
        (weightsOfCoordinates
          (inverseMassCoordinates
            (threeMassSiteConfig fixed site₀ site₁ site₂ triple))) =
      matrixVal (actualThreeMassDualHermitian
        fixed site₀ site₁ site₂ triple) := by
  let m := threeMassSiteConfig fixed site₀ site₁ site₂ triple
  rw [weightsOfCoordinates_inverseMassCoordinates]
  change weightedCycleLaplacian (fun i => (m.mass i)⁻¹) =
    massWeightedDifferenceMatrix m *
      Matrix.transpose (massWeightedDifferenceMatrix m)
  exact (massWeighted_selfTranspose_eq_weightedCycleLaplacian m).symm

/-- Each actual selected ordered eigenvalue satisfies its displayed symbolic
characteristic equation.  No simplicity assumption is needed. -/
theorem evaluate_symbolicSelectedCharacteristicEquation_actual_eq_zero
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) (r : Fin 3) :
    MvPolynomial.eval
        (actualThreeMassAdjugateSpectralPoint
          fixed site₀ site₁ site₂ modes triple)
        (symbolicSelectedCharacteristicEquation (N := N) r) = 0 := by
  unfold actualThreeMassAdjugateSpectralPoint
  rw [evaluate_symbolicSelectedCharacteristicEquation]
  rw [weightedCycleLaplacian_actualThreeMass_eq_matrixVal]
  exact charpoly_eval_orderedEigenvalue_eq_zero
    (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)
    (modes r)

/-- If two spectral parameters coincide, the adjugate weight matrix has two
equal rows.  Thus its determinant polynomial vanishes after evaluation. -/
theorem evaluate_symbolicAdjugateWeightDetPolynomial_eq_zero_of_lambda_zero_eq_one
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real)
    (directions : Fin 3 → Lattice.Configuration N)
    (hlambda : lambda 0 = lambda 1) :
    MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
        (symbolicAdjugateWeightDetPolynomial directions) = 0 := by
  rw [evaluate_symbolicAdjugateWeightDetPolynomial]
  apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
  funext s
  unfold parameterAdjugateWeightMatrix parameterShiftedMatrix
  rw [hlambda]

/-- Four explicit equations: the adjugate weight determinant followed by the
three selected characteristic equations. -/
def actualThreeMassAdjugateSpectralSystem
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) :
    Fin 4 → MvPolynomial (AdjugateSpectralVariable N) Real :=
  Fin.cases
    (actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂)
    (fun r => symbolicSelectedCharacteristicEquation (N := N) r)

/-- Truth audit for elimination: assigning all three spectral variables to
one actual eigenvalue solves the unsaturated four-polynomial system for every
mass configuration.  Therefore a useful mass-only elimination certificate
must exclude repeated spectral variables, for example by a Vandermonde
saturation or by restricting to an ordered all-distinct chamber. -/
theorem actualThreeMassAdjugateSpectralSystem_has_diagonalSolution
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (triple : MassTriple)
    (mode : Fin (Fintype.card (Lattice.Site N))) :
    ∀ q : Fin 4,
      MvPolynomial.eval
        (actualThreeMassAdjugateSpectralPoint
          fixed site₀ site₁ site₂ (fun _ => mode) triple)
        (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q) = 0 := by
  intro q
  refine Fin.cases ?_ (fun r => ?_) q
  · simpa [actualThreeMassAdjugateSpectralPoint,
      actualThreeMassAdjugateSpectralSystem,
      actualThreeMassAdjugateSpectralPolynomial] using
        (evaluate_symbolicAdjugateWeightDetPolynomial_eq_zero_of_lambda_zero_eq_one
          (inverseMassCoordinates
            (threeMassSiteConfig fixed site₀ site₁ site₂ triple))
          (fun _ : Fin 3 => orderedEigenvalue
            (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) mode)
          (actualThreeMassCycleDirection site₀ site₁ site₂) rfl)
  · simpa [actualThreeMassAdjugateSpectralSystem] using
      (evaluate_symbolicSelectedCharacteristicEquation_actual_eq_zero
        fixed site₀ site₁ site₂ (fun _ => mode) triple r)

/-- On simple spectrum, actual projector-minor degeneracy is exactly the
simultaneous vanishing of the four explicit equations. -/
theorem actualThreeMassProjectorMinor_eq_zero_iff_spectralSystem
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)) :
    (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0 ↔
      ∀ q : Fin 4,
        MvPolynomial.eval
          (actualThreeMassAdjugateSpectralPoint
            fixed site₀ site₁ site₂ modes triple)
          (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q) = 0 := by
  constructor
  · intro hminor q
    refine Fin.cases ?_ (fun r => ?_) q
    · exact
        (actualThreeMassProjectorMinor_eq_zero_iff_adjugateSpectralPolynomial
          fixed site₀ site₁ site₂ modes triple hsimple).mp hminor
    · exact evaluate_symbolicSelectedCharacteristicEquation_actual_eq_zero
        fixed site₀ site₁ site₂ modes triple r
  · intro hsystem
    apply
      (actualThreeMassProjectorMinor_eq_zero_iff_adjugateSpectralPolynomial
        fixed site₀ site₁ site₂ modes triple hsimple).mpr
    simpa [actualThreeMassAdjugateSpectralSystem,
      actualThreeMassAdjugateSpectralPoint] using
      hsystem (0 : Fin 4)

end

end ArchonPhysics.ActualProjectorAdjugateSpectralSystem
