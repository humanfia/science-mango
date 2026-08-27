import ArchonPhysics.ActualSixSiteNearResonantModularCertificate
import ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Checked companion entries and their threefold tensor realization. -/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate

def tensorMonomial {R : Type*} [CommSemiring R]
    (C : Matrix (Fin 5) (Fin 5) R) (a : CubeIndex) :
    Matrix CubeIndex CubeIndex R :=
  (C ^ a.1.val) ⊗ₖ ((C ^ a.2.1.val) ⊗ₖ (C ^ a.2.2.val))

def cubeMultiplication {R : Type*} [CommSemiring R]
    (C : Matrix (Fin 5) (Fin 5) R) (c : CubeIndex → R) :
    Matrix CubeIndex CubeIndex R :=
  ∑ a, c a • tensorMonomial C a

def residualMultiplication103 : Matrix CubeIndex CubeIndex (ZMod 103) :=
  (53 : ZMod 103) • cubeMultiplication companion103 residualCube103

def inverseOrigin103 : CubeIndex → ZMod 103 := inverseCube103

/-- An arbitrary companion entry follows from the two small origin-column
certificates and `C^(a+b)=C^a C^b`. -/
theorem companion103_pow_entry_eq_reducedPower (a b i : Fin 5) :
    (companion103 ^ a.val) i b =
      reducedPower103 ⟨a.val + b.val, by omega⟩ i := by
  calc
    (companion103 ^ a.val) i b =
        (companion103 ^ a.val * companion103 ^ b.val) i 0 := by
          classical
          rw [Matrix.mul_apply]
          simp_rw [companion103_pow_column_origin]
          simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
          exact (Fintype.sum_ite_eq' b (fun x =>
            (companion103 ^ a.val) i x)).symm
    _ = (companion103 ^ (a.val + b.val)) i 0 := by
      rw [pow_add]
    _ = reducedPower103 ⟨a.val + b.val, by omega⟩ i :=
      companion103_pow_column_eq_reducedPower ⟨a.val + b.val, by omega⟩ i

/-- Tensor-monomial entries are products of the three checked reductions. -/
theorem tensorMonomial_companion103_apply_eq_reduced (a i b : CubeIndex) :
    tensorMonomial companion103 a i b =
      reducedPower103 ⟨a.1.val + b.1.val, by omega⟩ i.1 *
      reducedPower103 ⟨a.2.1.val + b.2.1.val, by omega⟩ i.2.1 *
      reducedPower103 ⟨a.2.2.val + b.2.2.val, by omega⟩ i.2.2 := by
  rcases a with ⟨ax, ay, az⟩
  rcases i with ⟨ix, iy, iz⟩
  rcases b with ⟨bx, by_, bz⟩
  simp only [tensorMonomial, Matrix.kronecker_apply,
    companion103_pow_entry_eq_reducedPower, mul_assoc]

end ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
