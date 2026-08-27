import ArchonPhysics.ActualSixSiteNearResonantModularMatrixConvolution
import ArchonPhysics.CyclicMatrixRightInverse

/-! Transport the checked inverse origin column to a full right inverse. -/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
open ArchonPhysics.CyclicMatrixRightInverse

theorem tensorMonomial_commute {R : Type*} [CommSemiring R]
    (C : Matrix (Fin 5) (Fin 5) R) (a b : CubeIndex) :
    tensorMonomial C a * tensorMonomial C b =
      tensorMonomial C b * tensorMonomial C a := by
  simp only [tensorMonomial, ← Matrix.mul_kronecker_mul, ← pow_add]
  rw [add_comm a.1.val b.1.val, add_comm a.2.1.val b.2.1.val,
    add_comm a.2.2.val b.2.2.val]

theorem cubeMultiplication_commute_tensorMonomial
    {R : Type*} [CommSemiring R]
    (C : Matrix (Fin 5) (Fin 5) R) (c : CubeIndex → R) (a : CubeIndex) :
    cubeMultiplication C c * tensorMonomial C a =
      tensorMonomial C a * cubeMultiplication C c := by
  unfold cubeMultiplication
  simp_rw [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro b _
  rw [tensorMonomial_commute]

theorem residualMultiplication103_commute_tensorMonomial (a : CubeIndex) :
    residualMultiplication103 * tensorMonomial companion103 a =
      tensorMonomial companion103 a * residualMultiplication103 := by
  unfold residualMultiplication103
  rw [Matrix.smul_mul, Matrix.mul_smul,
    cubeMultiplication_commute_tensorMonomial]

/-- The companion tensor monomials generate every basis column from origin. -/
theorem tensorMonomial_companion103_cyclic :
    ∀ a i, tensorMonomial companion103 a i origin =
      (1 : Matrix CubeIndex CubeIndex (ZMod 103)) i a := by
  rintro ⟨ax, ay, az⟩ ⟨ix, iy, iz⟩
  simp only [tensorMonomial, Matrix.kronecker_apply, origin,
    companion103_pow_column_origin]
  simp only [Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

def certifiedRightInverse103 : Matrix CubeIndex CubeIndex (ZMod 103) :=
  cyclicRightInverse (tensorMonomial companion103) inverseOrigin103

/-- The modular quotient certificate yields a full 125 by 125 right inverse. -/
theorem residualMultiplication103_mul_certifiedRightInverse103 :
    residualMultiplication103 * certifiedRightInverse103 = 1 := by
  exact rightInverse_of_cyclic_column residualMultiplication103
    (tensorMonomial companion103) origin inverseOrigin103
    residualMultiplication103_commute_tensorMonomial
    tensorMonomial_companion103_cyclic
    residualMultiplication103_mulVec_inverseOrigin

end ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
