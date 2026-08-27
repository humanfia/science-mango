import ArchonPhysics.OrderedProjectorShiftedAdjugate
import ArchonPhysics.RandomMassResultantBridge

/-!
# Explicit inverse-mass and spectral-parameter polynomial for the actual minor

The shifted-adjugate representation removes every projector denominator.
Here it is lifted to a single multivariate polynomial with one variable for
each inverse mass and three additional variables for the selected ordered
eigenvalues.  Evaluation at the genuine dual-cycle matrix and its selected
ordered eigenvalues recovers the exact actual numerator minor.

This is an algebraic representation theorem, not yet an avoidance theorem:
the spectral parameters depend on the masses.  Eliminating them chamber by
chamber, and proving the resulting mass polynomial nonzero, remain separate
model obligations.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.ActualProjectorAdjugatePolynomial

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison

noncomputable section

/-- Variables are all inverse masses, followed by three spectral parameters. -/
abbrev AdjugateSpectralVariable (N : Nat) := Fin N ⊕ Fin 3

/-- Joint evaluation of inverse-mass and spectral variables. -/
def adjugateSpectralEvaluation {N : Nat}
    (x : Fin N → Real) (lambda : Fin 3 → Real) :
    AdjugateSpectralVariable N → Real
  | Sum.inl k => x k
  | Sum.inr r => lambda r

/-- The weighted cycle matrix over the joint polynomial ring. -/
def symbolicAdjugateWeightedCycleLaplacian
    {N : Nat} [NeZero N] :
    Matrix (Lattice.Site N) (Lattice.Site N)
      (MvPolynomial (AdjugateSpectralVariable N) Real) :=
  differenceMatrix.map MvPolynomial.C *
    Matrix.diagonal (fun i =>
      MvPolynomial.X
        (Sum.inl (siteEquivFin N i) : AdjugateSpectralVariable N)) *
      (Matrix.transpose differenceMatrix).map MvPolynomial.C

/-- Evaluation of the symbolic joint-ring matrix is the concrete weighted
cycle Laplacian. -/
theorem evaluate_symbolicAdjugateWeightedCycleLaplacian
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real) :
    (symbolicAdjugateWeightedCycleLaplacian (N := N)).map
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)) =
      weightedCycleLaplacian (weightsOfCoordinates x) := by
  unfold symbolicAdjugateWeightedCycleLaplacian weightedCycleLaplacian
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.diagonal_map, map_zero]
  congr 2
  · ext i j
    simp
  · ext i j
    simp only [MvPolynomial.eval_X]
    unfold adjugateSpectralEvaluation weightsOfCoordinates
    rfl
  · ext i j
    simp

/-- The characteristic matrix with the `r`-th symbolic spectral parameter. -/
def symbolicAdjugateShiftedMatrix
    {N : Nat} [NeZero N] (r : Fin 3) :
    Matrix (Lattice.Site N) (Lattice.Site N)
      (MvPolynomial (AdjugateSpectralVariable N) Real) :=
  Matrix.diagonal (fun _ =>
      (MvPolynomial.X
        (Sum.inr r : AdjugateSpectralVariable N) :
        MvPolynomial (AdjugateSpectralVariable N) Real)) -
    symbolicAdjugateWeightedCycleLaplacian

/-- Concrete three-parameter shifted matrix before substituting ordered
eigenvalues. -/
def parameterShiftedMatrix
    {N : Nat} [NeZero N]
    (A : Matrix (Lattice.Site N) (Lattice.Site N) Real)
    (lambda : Fin 3 → Real) (r : Fin 3) :
    Matrix (Lattice.Site N) (Lattice.Site N) Real :=
  lambda r • (1 : Matrix (Lattice.Site N) (Lattice.Site N) Real) - A

theorem evaluate_symbolicAdjugateShiftedMatrix
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real) (r : Fin 3) :
    (symbolicAdjugateShiftedMatrix (N := N) r).map
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)) =
      parameterShiftedMatrix
        (weightedCycleLaplacian (weightsOfCoordinates x)) lambda r := by
  unfold symbolicAdjugateShiftedMatrix parameterShiftedMatrix
  ext i j
  have hweighted := congrArg (fun M => M i j)
    (evaluate_symbolicAdjugateWeightedCycleLaplacian x lambda)
  simp only [Matrix.map_apply] at hweighted
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hweighted]
  by_cases hij : i = j
  · subst j
    simp [adjugateSpectralEvaluation]
  · simp [hij]

/-- Three quadratic forms of the symbolic shifted adjugates along fixed
cycle directions.  All entries are explicit polynomials in inverse masses
and the three selected spectral parameters. -/
def symbolicAdjugateWeightMatrix
    {N : Nat} [NeZero N]
    (directions : Fin 3 → Lattice.Configuration N) :
    Matrix (Fin 3) (Fin 3)
      (MvPolynomial (AdjugateSpectralVariable N) Real) :=
  fun r s =>
    (fun i => MvPolynomial.C (directions s i)) ⬝ᵥ
      ((symbolicAdjugateShiftedMatrix (N := N) r).adjugate *ᵥ
        fun i => MvPolynomial.C (directions s i))

/-- Concrete counterpart of the symbolic adjugate weight matrix. -/
def parameterAdjugateWeightMatrix
    {N : Nat} [NeZero N]
    (A : Matrix (Lattice.Site N) (Lattice.Site N) Real)
    (lambda : Fin 3 → Real)
    (directions : Fin 3 → Lattice.Configuration N) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => directions s ⬝ᵥ
    ((parameterShiftedMatrix A lambda r).adjugate *ᵥ directions s)

/-- Evaluation commutes with the three adjugate quadratic forms. -/
theorem evaluate_symbolicAdjugateWeightMatrix
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real)
    (directions : Fin 3 → Lattice.Configuration N) :
    (symbolicAdjugateWeightMatrix directions).map
        (MvPolynomial.eval (adjugateSpectralEvaluation x lambda)) =
      parameterAdjugateWeightMatrix
        (weightedCycleLaplacian (weightsOfCoordinates x)) lambda directions := by
  ext r s
  unfold symbolicAdjugateWeightMatrix parameterAdjugateWeightMatrix
  let f := MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
  change f (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  have hdir : (f ∘ fun i => MvPolynomial.C (directions s i)) =
      directions s := by
    funext i
    simp [f]
  rw [hdir]
  apply congrArg (fun v => directions s ⬝ᵥ v)
  funext i
  simp only [Function.comp_apply]
  rw [RingHom.map_mulVec]
  change (f.mapMatrix
      (symbolicAdjugateShiftedMatrix (N := N) r).adjugate *ᵥ
        (f ∘ fun j => MvPolynomial.C (directions s j))) i = _
  have hshift : f.mapMatrix (symbolicAdjugateShiftedMatrix (N := N) r) =
      parameterShiftedMatrix
        (weightedCycleLaplacian (weightsOfCoordinates x)) lambda r := by
    change (symbolicAdjugateShiftedMatrix (N := N) r).map f = _
    exact evaluate_symbolicAdjugateShiftedMatrix x lambda r
  rw [RingHom.map_adjugate, hshift, hdir]

/-- The determinant of the symbolic three-direction adjugate weight matrix. -/
def symbolicAdjugateWeightDetPolynomial
    {N : Nat} [NeZero N]
    (directions : Fin 3 → Lattice.Configuration N) :
    MvPolynomial (AdjugateSpectralVariable N) Real :=
  (symbolicAdjugateWeightMatrix directions).det

theorem evaluate_symbolicAdjugateWeightDetPolynomial
    {N : Nat} [NeZero N]
    (x : Fin N → Real) (lambda : Fin 3 → Real)
    (directions : Fin 3 → Lattice.Configuration N) :
    MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
        (symbolicAdjugateWeightDetPolynomial directions) =
      (parameterAdjugateWeightMatrix
        (weightedCycleLaplacian (weightsOfCoordinates x))
          lambda directions).det := by
  unfold symbolicAdjugateWeightDetPolynomial
  rw [RingHom.map_det]
  change ((symbolicAdjugateWeightMatrix directions).map
    (MvPolynomial.eval (adjugateSpectralEvaluation x lambda))).det = _
  rw [evaluate_symbolicAdjugateWeightMatrix]

/-- The actual dual-cycle three-site numerator polynomial.  It is independent
of a mode choice; a mode triple enters only through the three spectral
parameters at evaluation time. -/
def actualThreeMassAdjugateSpectralPolynomial
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) :
    MvPolynomial (AdjugateSpectralVariable N) Real :=
  symbolicAdjugateWeightDetPolynomial
    (ActualThreeMassProjectorWeightJacobian.actualThreeMassCycleDirection
      site₀ site₁ site₂)

/-- Exact evaluation of the explicit joint polynomial at the genuine inverse
masses and the three selected ordered eigenvalues. -/
theorem evaluate_actualThreeMassAdjugateSpectralPolynomial
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : ThreeParameterSpectralAveragingDensity.MassTriple) :
    MvPolynomial.eval
        (adjugateSpectralEvaluation
          (inverseMassCoordinates
            (threeMassSiteConfig
              fixed site₀ site₁ site₂ triple))
          (fun r => orderedEigenvalue
            (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
              fixed site₀ site₁ site₂ triple) (modes r)))
        (actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂) =
      (orderedShiftedAdjugateWeightMatrix
        (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
          fixed site₀ site₁ site₂ triple)
        modes
        (ActualThreeMassProjectorWeightJacobian.actualThreeMassCycleDirection
          site₀ site₁ site₂)).det := by
  let m := threeMassSiteConfig
    fixed site₀ site₁ site₂ triple
  let A := ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
    fixed site₀ site₁ site₂ triple
  let lambda : Fin 3 → Real := fun r => orderedEigenvalue A (modes r)
  have hmatrix :
      weightedCycleLaplacian
          (weightsOfCoordinates (inverseMassCoordinates m)) = matrixVal A := by
    rw [weightsOfCoordinates_inverseMassCoordinates]
    change weightedCycleLaplacian (fun i => (m.mass i)⁻¹) =
      massWeightedDifferenceMatrix m *
        Matrix.transpose (massWeightedDifferenceMatrix m)
    exact (massWeighted_selfTranspose_eq_weightedCycleLaplacian m).symm
  change MvPolynomial.eval
      (adjugateSpectralEvaluation (inverseMassCoordinates m) lambda)
        (symbolicAdjugateWeightDetPolynomial
          (ActualThreeMassProjectorWeightJacobian.actualThreeMassCycleDirection
            site₀ site₁ site₂)) = _
  rw [evaluate_symbolicAdjugateWeightDetPolynomial]
  rw [hmatrix]
  rfl

/-- On the simple-spectrum locus, actual projector-minor degeneracy is exactly
the zero set of the displayed inverse-mass-plus-eigenvalue polynomial.  No
Jacobian nondegeneracy hypothesis occurs in this statement. -/
theorem actualThreeMassProjectorMinor_eq_zero_iff_adjugateSpectralPolynomial
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : ThreeParameterSpectralAveragingDensity.MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
        fixed site₀ site₁ site₂ triple)) :
    (ActualThreeMassProjectorWeightJacobian.actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0 ↔
      MvPolynomial.eval
        (adjugateSpectralEvaluation
          (inverseMassCoordinates
            (threeMassSiteConfig
              fixed site₀ site₁ site₂ triple))
          (fun r => orderedEigenvalue
            (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
              fixed site₀ site₁ site₂ triple) (modes r)))
        (actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂) = 0 := by
  rw [actualThreeMassProjectorMinor_eq_zero_iff_shiftedAdjugate
    fixed site₀ site₁ site₂ modes triple hsimple]
  rw [evaluate_actualThreeMassAdjugateSpectralPolynomial]

end


end ArchonPhysics.ActualProjectorAdjugatePolynomial
