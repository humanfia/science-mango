import ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
import ArchonPhysics.ActualSixSiteNearResonantScaledCompanionTensor
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A polynomial norm for the three-root collision contraction

The scaled companion matrix removes the non-monic leading coefficient of
the characteristic quintic.  For every monomial of the four-variable
cleared contraction, this file represents the three energy variables by a
threefold Kronecker product.  A compensating power of `1 - t^2` makes every
summand have the same scale.  The determinant of the resulting polynomial
matrix is therefore an honest univariate elimination polynomial.
-/

open scoped BigOperators Matrix Polynomial Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination

open ArchonPhysics.ActualSixSiteNearResonantPathSeparable
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanion
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionTensor
open ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial

noncomputable section

abbrev CollisionExponent := CollisionVariable →₀ Nat
abbrev TripleQuotientIndex := TripleQuinticIndex

def clearedCollisionPolynomial : MvPolynomial CollisionVariable Real :=
  genericSixSiteClearedAdjugateInteractionPolynomial

/-- Total exponent in the three spectral variables (indices `1,2,3`). -/
def collisionEnergyDegree (s : CollisionExponent) : Nat :=
  s 1 + s 2 + s 3

theorem collisionEnergyDegree_le_totalDegree
    {s : CollisionExponent} (hs : s ∈ clearedCollisionPolynomial.support) :
    collisionEnergyDegree s ≤ clearedCollisionPolynomial.totalDegree := by
  have htotal := MvPolynomial.le_totalDegree hs
  rw [Finsupp.sum_fintype, Fin.sum_univ_four] at htotal
  unfold collisionEnergyDegree
  omega
  all_goals simp

/-- Pure tensor representing one monomial in the three quotient roots. -/
def collisionTensorPowerPolynomial (s : CollisionExponent) :
    Matrix TripleQuotientIndex TripleQuotientIndex Real[X] :=
  (nearResonantScaledCompanionPolynomial ^ s 1) ⊗ₖ
    ((nearResonantScaledCompanionPolynomial ^ s 2) ⊗ₖ
      (nearResonantScaledCompanionPolynomial ^ s 3))

def collisionTensorPower (t : Real) (s : CollisionExponent) :
    Matrix TripleQuotientIndex TripleQuotientIndex Real :=
  (nearResonantScaledCompanion t ^ s 1) ⊗ₖ
    ((nearResonantScaledCompanion t ^ s 2) ⊗ₖ
      (nearResonantScaledCompanion t ^ s 3))

/-- One denominator-free regular-representation summand. -/
def scaledCollisionMonomialMatrixPolynomial (s : CollisionExponent) :
    Matrix TripleQuotientIndex TripleQuotientIndex Real[X] :=
  (Polynomial.C (clearedCollisionPolynomial.coeff s) *
      Polynomial.X ^ s 0 *
      nearResonantLeadingPolynomial ^
        (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s)) •
    collisionTensorPowerPolynomial s

def scaledCollisionMonomialMatrix (t : Real) (s : CollisionExponent) :
    Matrix TripleQuotientIndex TripleQuotientIndex Real :=
  (clearedCollisionPolynomial.coeff s * t ^ s 0 *
      (1 - t ^ 2) ^
        (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s)) •
    collisionTensorPower t s

/-- Polynomial multiplication matrix for the cleared collision
contraction in the threefold quintic quotient. -/
def scaledCollisionMultiplicationMatrixPolynomial :
    Matrix TripleQuotientIndex TripleQuotientIndex Real[X] :=
  ∑ s ∈ clearedCollisionPolynomial.support,
    scaledCollisionMonomialMatrixPolynomial s

def scaledCollisionMultiplicationMatrix (t : Real) :
    Matrix TripleQuotientIndex TripleQuotientIndex Real :=
  ∑ s ∈ clearedCollisionPolynomial.support,
    scaledCollisionMonomialMatrix t s

/-- The univariate exceptional polynomial produced by the quotient norm. -/
def scaledCollisionExceptionalPolynomial : Real[X] :=
  scaledCollisionMultiplicationMatrixPolynomial.det

theorem evaluate_nearResonantLeadingPolynomial (t : Real) :
    nearResonantLeadingPolynomial.eval t = 1 - t ^ 2 := by
  simp [nearResonantLeadingPolynomial]

theorem mapMatrix_kronecker
    {R S m n : Type*} [CommRing R] [CommRing S]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : R →+* S) (A : Matrix m m R) (B : Matrix n n R) :
    f.mapMatrix (A ⊗ₖ B) = f.mapMatrix A ⊗ₖ f.mapMatrix B := by
  ext ⟨i₀, i₁⟩ ⟨j₀, j₁⟩
  change f (A i₀ j₀ * B i₁ j₁) = f (A i₀ j₀) * f (B i₁ j₁)
  exact map_mul f (A i₀ j₀) (B i₁ j₁)

theorem evaluate_collisionTensorPowerPolynomial (t : Real)
    (s : CollisionExponent) :
    (Polynomial.evalRingHom t).mapMatrix
        (collisionTensorPowerPolynomial s) =
      collisionTensorPower t s := by
  unfold collisionTensorPowerPolynomial collisionTensorPower
  rw [mapMatrix_kronecker, mapMatrix_kronecker,
    map_pow (Polynomial.evalRingHom t).mapMatrix,
    map_pow (Polynomial.evalRingHom t).mapMatrix,
    map_pow (Polynomial.evalRingHom t).mapMatrix,
    evaluate_nearResonantScaledCompanionPolynomial]

theorem mapMatrix_smul_same
    {R S m : Type*} [CommRing R] [CommRing S] [Fintype m] [DecidableEq m]
    (f : R →+* S) (c : R) (M : Matrix m m R) :
    f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j
  change f (c * M i j) = f c * f (M i j)
  exact map_mul f c (M i j)

theorem evaluate_scaledCollisionMonomialCoefficient (t : Real)
    (s : CollisionExponent) :
    (Polynomial.evalRingHom t)
        (Polynomial.C (clearedCollisionPolynomial.coeff s) *
          Polynomial.X ^ s 0 *
          nearResonantLeadingPolynomial ^
            (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s)) =
      clearedCollisionPolynomial.coeff s * t ^ s 0 *
        (1 - t ^ 2) ^
          (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s) := by
  change Polynomial.eval t
      (Polynomial.C (clearedCollisionPolynomial.coeff s) *
        Polynomial.X ^ s 0 *
        nearResonantLeadingPolynomial ^
          (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s)) = _
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, evaluate_nearResonantLeadingPolynomial]

theorem evaluate_scaledCollisionMonomialMatrixPolynomial (t : Real)
    (s : CollisionExponent) :
    (Polynomial.evalRingHom t).mapMatrix
        (scaledCollisionMonomialMatrixPolynomial s) =
      scaledCollisionMonomialMatrix t s := by
  unfold scaledCollisionMonomialMatrixPolynomial scaledCollisionMonomialMatrix
  rw [mapMatrix_smul_same,
    evaluate_scaledCollisionMonomialCoefficient,
    evaluate_collisionTensorPowerPolynomial]

theorem evaluate_scaledCollisionMultiplicationMatrixPolynomial (t : Real) :
    (Polynomial.evalRingHom t).mapMatrix
        scaledCollisionMultiplicationMatrixPolynomial =
      scaledCollisionMultiplicationMatrix t := by
  unfold scaledCollisionMultiplicationMatrixPolynomial
  unfold scaledCollisionMultiplicationMatrix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact evaluate_scaledCollisionMonomialMatrixPolynomial t s

theorem evaluate_scaledCollisionExceptionalPolynomial (t : Real) :
    scaledCollisionExceptionalPolynomial.eval t =
      (scaledCollisionMultiplicationMatrix t).det := by
  change (Polynomial.evalRingHom t)
      scaledCollisionMultiplicationMatrixPolynomial.det = _
  rw [RingHom.map_det,
    evaluate_scaledCollisionMultiplicationMatrixPolynomial]

end


end ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination
