import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialRightInverse

/-!
# Direct convolution from the structural polynomial Bézout certificate

The symmetric double convolution is first identified with the origin-column
matrix product.  The already kernel-checked polynomial Bézout identity then
proves that column is the origin basis vector.  No staged coefficient table or
native evaluator is used.
-/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularDirectConvolution

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

/-- The sum of two quotient-basis exponents is at most eight. -/
def sumExponent (a b : Fin 5) : Fin 9 :=
  ⟨a.val + b.val, by omega⟩

/-- Direct coefficient of the product of the residual and proposed inverse,
after reducing each of the three monomial exponents. -/
def directReducedProductCoeff103 (o : CubeIndex) : ZMod 103 :=
  ∑ a : CubeIndex, ∑ b : CubeIndex,
    53 * residualCube103 a * inverseCube103 b *
      reducedPower103 (sumExponent a.1 b.1) o.1 *
      reducedPower103 (sumExponent a.2.1 b.2.1) o.2.1 *
      reducedPower103 (sumExponent a.2.2 b.2.2) o.2.2

/-- Expanding the residual multiplication matrix against the proposed inverse
coefficient vector gives the direct symmetric convolution. -/
theorem residualMultiplication103_mulVec_apply_eq_direct (o : CubeIndex) :
    (residualMultiplication103 *ᵥ inverseOrigin103) o =
      directReducedProductCoeff103 o := by
  classical
  rcases o with ⟨ox, oy, oz⟩
  unfold residualMultiplication103 inverseOrigin103 cubeMultiplication
    directReducedProductCoeff103 sumExponent
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  simp_rw [tensorMonomial_companion103_apply_eq_reduced]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The polynomial inverse matrix has the advertised inverse coefficient vector
as its origin column. -/
private theorem polynomialInverse103_apply_origin (i : CubeIndex) :
    cubeMultiplication companion103 inverseCube103 i origin =
      inverseOrigin103 i := by
  classical
  unfold cubeMultiplication
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  unfold tensorMonomial origin
  simp only [Matrix.kroneckerMap_apply]
  simp_rw [companion103_pow_column_origin]
  simp [Matrix.one_apply, Fintype.sum_prod_type, inverseOrigin103]

/-- The direct reduced product is the origin basis vector.  Its proof is the
origin-column projection of the structural polynomial Bézout matrix identity. -/
theorem directReducedProductCoeff103_eq_one :
    ∀ o, directReducedProductCoeff103 o =
      ((Pi.single origin (1 : ZMod 103) : CubeIndex → ZMod 103) o) := by
  classical
  intro o
  calc
    directReducedProductCoeff103 o =
        (residualMultiplication103 *ᵥ inverseOrigin103) o :=
      (residualMultiplication103_mulVec_apply_eq_direct o).symm
    _ = (residualMultiplication103 *
          cubeMultiplication companion103 inverseCube103) o origin := by
      simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [polynomialInverse103_apply_origin]
    _ = (1 : Matrix CubeIndex CubeIndex (ZMod 103)) o origin := by
      rw [residualMultiplication103_mul_polynomialInverse]
    _ = (Pi.single origin (1 : ZMod 103) : CubeIndex → ZMod 103) o := by
      by_cases h : o = origin <;> simp [Matrix.one_apply, h]

end ArchonPhysics.ActualSixSiteNearResonantModularDirectConvolution
