import ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse
import ArchonPhysics.ActualSixSiteNearResonantModularMatrixEntry
import ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic
import Mathlib.Algebra.MonoidAlgebra.Lift

/-! Matrix evaluation of the kernel-checked modular polynomial inverse. -/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation

open ArchonPhysics.ActualSixSiteNearResonantModularCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionCertificate
open ArchonPhysics.ActualSixSiteNearResonantModularMatrixLink
open ArchonPhysics.ActualSixSiteNearResonantModularPolynomialInverse
open ArchonPhysics.ActualSixSiteNearResonantModularCompanionQuintic

noncomputable section

def monomialExponent (i j k : Nat) : SpectralVariable →₀ Nat :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

def tensorPower (s : SpectralVariable →₀ Nat) :
    Matrix CubeIndex CubeIndex (ZMod 103) :=
  (companion103 ^ s 0) ⊗ₖ
    ((companion103 ^ s 1) ⊗ₖ (companion103 ^ s 2))

def kroneckerRightOneAlgHom {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
    Matrix n n (ZMod 103) →ₐ[ZMod 103]
      Matrix (n × m) (n × m) (ZMod 103) where
  toFun A := A ⊗ₖ (1 : Matrix m m (ZMod 103))
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]

def kroneckerLeftOneAlgHom {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
    Matrix m m (ZMod 103) →ₐ[ZMod 103]
      Matrix (n × m) (n × m) (ZMod 103) where
  toFun A := (1 : Matrix n n (ZMod 103)) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]

def firstFactorAlgHom :
    Matrix (Fin 5) (Fin 5) (ZMod 103) →ₐ[ZMod 103]
      Matrix CubeIndex CubeIndex (ZMod 103) :=
  kroneckerRightOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)

def secondFactorAlgHom :
    Matrix (Fin 5) (Fin 5) (ZMod 103) →ₐ[ZMod 103]
      Matrix CubeIndex CubeIndex (ZMod 103) :=
  (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)).comp
    (kroneckerRightOneAlgHom (n := Fin 5) (m := Fin 5))

def thirdFactorAlgHom :
    Matrix (Fin 5) (Fin 5) (ZMod 103) →ₐ[ZMod 103]
      Matrix CubeIndex CubeIndex (ZMod 103) :=
  (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)).comp
    (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5))

def tensorPowerMonoidHom :
    Multiplicative (SpectralVariable →₀ Nat) →*
      Matrix CubeIndex CubeIndex (ZMod 103) where
  toFun s := tensorPower s.toAdd
  map_one' := by simp [tensorPower]
  map_mul' a b := by
    change tensorPower (a.toAdd + b.toAdd) =
      tensorPower a.toAdd * tensorPower b.toAdd
    simp [tensorPower, Finsupp.add_apply, pow_add,
      ← Matrix.mul_kronecker_mul]

def companionEvaluation :
    MvPolynomial SpectralVariable (ZMod 103) →+*
      Matrix CubeIndex CubeIndex (ZMod 103) :=
  AddMonoidAlgebra.liftNCRingHom
    (algebraMap (ZMod 103) (Matrix CubeIndex CubeIndex (ZMod 103)))
    tensorPowerMonoidHom
    (by
      intro c s
      exact Matrix.scalar_commute c (fun c' => mul_comm c c')
        (tensorPowerMonoidHom s))

theorem polynomialMonomial_eq_monomial (i j k : Nat) (c : ZMod 103) :
    monomial i j k c = MvPolynomial.monomial (monomialExponent i j k) c := by
  unfold monomial monomialExponent
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [← MvPolynomial.monomial_add_single]
  rw [← MvPolynomial.monomial_add_single]

theorem companionEvaluation_monomial (i j k : Nat) (c : ZMod 103) :
    companionEvaluation (monomial i j k c) =
      c • tensorPower (monomialExponent i j k) := by
  rw [polynomialMonomial_eq_monomial]
  unfold companionEvaluation MvPolynomial.monomial
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap (ZMod 103) (Matrix CubeIndex CubeIndex (ZMod 103)))
      tensorPowerMonoidHom _) (AddMonoidAlgebra.single _ c) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  rw [Matrix.smul_eq_diagonal_mul]
  rfl

theorem companionEvaluation_C (c : ZMod 103) :
    companionEvaluation (MvPolynomial.C c) = c • 1 := by
  simpa [monomial, tensorPower, monomialExponent] using
    companionEvaluation_monomial 0 0 0 c

theorem companionEvaluation_X (r : SpectralVariable) :
    companionEvaluation (MvPolynomial.X r) =
      tensorPower (Finsupp.single r 1) := by
  unfold companionEvaluation MvPolynomial.X
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap (ZMod 103) (Matrix CubeIndex CubeIndex (ZMod 103)))
      tensorPowerMonoidHom _) (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp [tensorPowerMonoidHom]

theorem matrixQuintic103_map
    (f : Matrix (Fin 5) (Fin 5) (ZMod 103) →ₐ[ZMod 103]
      Matrix CubeIndex CubeIndex (ZMod 103))
    (M : Matrix (Fin 5) (Fin 5) (ZMod 103)) :
    matrixQuintic103 (f M) = f (matrixQuintic103 M) := by
  simp [matrixQuintic103]

theorem tensorPower_single_zero :
    tensorPower (Finsupp.single (0 : SpectralVariable) 1) =
      firstFactorAlgHom companion103 := by
  simp [tensorPower, firstFactorAlgHom, kroneckerRightOneAlgHom]

theorem tensorPower_single_one :
    tensorPower (Finsupp.single (1 : SpectralVariable) 1) =
      secondFactorAlgHom companion103 := by
  simp [tensorPower, secondFactorAlgHom, kroneckerLeftOneAlgHom,
    kroneckerRightOneAlgHom]

theorem tensorPower_single_two :
    tensorPower (Finsupp.single (2 : SpectralVariable) 1) =
      thirdFactorAlgHom companion103 := by
  simp [tensorPower, thirdFactorAlgHom, kroneckerLeftOneAlgHom]

end

end ArchonPhysics.ActualSixSiteNearResonantModularPolynomialMatrixEvaluation
