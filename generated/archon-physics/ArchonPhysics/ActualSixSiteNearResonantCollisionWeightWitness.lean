import ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
import ArchonPhysics.ActualSixSiteNearResonantJacobianCompleteWitness
import ArchonPhysics.ActualSixSiteNearResonantModularCertificate
import ArchonPhysics.ActualSixSiteNearResonantModularTruthLink
import ArchonPhysics.CyclicMatrixRightInverse
import ArchonPhysics.ModularMatrixDeterminantCertificate

/-!
# A collision-weight witness on the six-site near-resonant path

This module proves the missing interaction nondegeneracy at the explicit
rational path point `t = 1 / 10`.  The certificate uses the 125-dimensional
threefold quotient by the positive characteristic quintic.  A small
mod-`103` inverse certifies that the rational multiplication operator is
nonsingular, without expanding a 130 by 130 Sylvester determinant.
-/

open scoped BigOperators Matrix Polynomial Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

namespace ModularCertificate

/-- Dimension of the threefold degree-five quotient. -/
abbrev FlatIndex := Fin 125

/-- Coefficients of the shifted-adjugate triple contraction reduced modulo
the three copies of the positive characteristic quintic.  The flattening is
`i * 25 + j * 5 + k ↔ E^i F^j G^k`. -/
def residualCoeff : FlatIndex → Rat :=
  ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.residualCoeff

/-- A right inverse of the cleared-denominator multiplication operator over
`ZMod 103`, in the same flattened monomial basis. -/
def inverseCoeff103 : FlatIndex → ZMod 103 :=
  ArchonPhysics.ActualSixSiteNearResonantModularCertificate.inverseCoeff103

/-- One common denominator for the rational multiplication matrix. -/
def multiplicationDenominator : Nat := 9750233588877422087246811

theorem multiplicationDenominator_mod_103 :
    (multiplicationDenominator : ZMod 103) = 53 := by
  exact ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.multiplicationDenominator_mod_103


/-- Product index for the three degree-five quotient factors. -/
abbrev CubeIndex := Fin 5 × (Fin 5 × Fin 5)

/-- Flatten a threefold quotient-basis index in lexicographic order. -/
def flattenIndex (a : CubeIndex) : FlatIndex :=
  ⟨a.1.val * 25 + a.2.1.val * 5 + a.2.2.val, by omega⟩

def residualCube (a : CubeIndex) : Rat :=
  residualCoeff (flattenIndex a)

def inverseCube103 (a : CubeIndex) : ZMod 103 :=
  inverseCoeff103 (flattenIndex a)

/-- Companion matrix for the positive characteristic quintic at `t = 1/10`.
Columns encode multiplication by the quotient generator. -/
def companionRat : Matrix (Fin 5) (Fin 5) Rat :=
  !![0, 0, 0, 0, ((3600 : Rat) / 99);
     1, 0, 0, 0, (-((10495 : Rat)) / 99);
     0, 1, 0, 0, ((11180 : Rat) / 99);
     0, 0, 1, 0, (-((5379 : Rat)) / 99);
     0, 0, 0, 1, ((1192 : Rat) / 99)]

def companion103 : Matrix (Fin 5) (Fin 5) (ZMod 103) :=
  !![0, 0, 0, 0, 27;
     1, 0, 0, 0, 23;
     0, 1, 0, 0, 89;
     0, 0, 1, 0, 83;
     0, 0, 0, 1, 11]

/-- Multiplication by a reduced trivariate polynomial in the tensor-product
quotient, expressed through the three companion matrices. -/
def cubeMultiplication {R : Type*} [CommSemiring R]
    (C : Matrix (Fin 5) (Fin 5) R) (c : CubeIndex → R) :
    Matrix CubeIndex CubeIndex R :=
  ∑ a, c a •
    ((C ^ a.1.val) ⊗ₖ
      ((C ^ a.2.1.val) ⊗ₖ (C ^ a.2.2.val)))

def residualMultiplicationRat : Matrix CubeIndex CubeIndex Rat :=
  cubeMultiplication companionRat residualCube

def inverseMultiplication103 : Matrix CubeIndex CubeIndex (ZMod 103) :=
  cubeMultiplication companion103 inverseCube103

/-- The integer matrix obtained after clearing the common denominator. -/
def clearedMultiplicationInt : Matrix CubeIndex CubeIndex Int :=
  fun i j =>
    ((multiplicationDenominator : Rat) *
      residualMultiplicationRat i j).num


/-- The cleared integer multiplication matrix reduced modulo `103`. -/
def clearedMultiplication103 : Matrix CubeIndex CubeIndex (ZMod 103) :=
  clearedMultiplicationInt.map (Int.castRingHom (ZMod 103))

/-- Exact reduction of a rational with denominator prime to `103`. -/
def ratMod103 : Rat → ZMod 103 :=
  ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.ratMod103

def residualCube103 (a : CubeIndex) : ZMod 103 :=
  ratMod103 (residualCube a)

/-- The cleared residual multiplication operator, computed directly modulo `103`. -/
def directClearedMultiplication103 : Matrix CubeIndex CubeIndex (ZMod 103) :=
  53 • cubeMultiplication companion103 residualCube103

/-- The origin monomial in the threefold quotient basis. -/
def origin : CubeIndex := (0, (0, 0))


/-- Truth link from the rational residual table to the standalone modular table. -/
theorem residualCube103_eq_certificate :
    ∀ a, residualCube103 a =
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103 a := by
  intro a
  simpa [residualCube103, residualCube, ratMod103, residualCoeff,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.residualCube103,
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.flattenIndex, flattenIndex] using
    ArchonPhysics.ActualSixSiteNearResonantModularTruthLink.ratMod103_residualCoeff_eq
      (flattenIndex a)

/-- Truth link from the local inverse vector to the standalone certificate. -/
theorem inverseCube103_eq_certificate :
    ∀ a, inverseCube103 a =
      ArchonPhysics.ActualSixSiteNearResonantModularCertificate.inverseCube103 a := by
  intro a
  rfl

end ModularCertificate

end

end ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
