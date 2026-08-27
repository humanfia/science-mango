import ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualBridge
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Specializing the fixed contraction residual certificate

This file transports the rational fixed-point quotient certificate to the
genuine real six-site contraction, the denominator-cleared generic
polynomial, and the ordinary threefold companion representation.
-/

open scoped BigOperators Matrix Polynomial Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualSpecialization

open ArchonPhysics
open ArchonPhysics.ActualSixSiteNearResonantAdjugateBridge
open ArchonPhysics.ActualSixSiteNearResonantClearedContraction
open ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualBridge
open ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.ActualSixSiteNearResonantPathSeparable

noncomputable section

abbrev SpectralVariable := FixedCertificate.SpectralVariable
abbrev CubeIndex := ModularCertificate.CubeIndex

/-! ## Genuine real specialization -/

def realEvaluation (energy : SpectralVariable → Real) :
    MvPolynomial SpectralVariable Rat →+* Real :=
  MvPolynomial.eval₂Hom (Rat.castHom Real) energy

theorem map_fixedShiftedMatrix (energy : SpectralVariable → Real)
    (r : SpectralVariable) :
    (realEvaluation energy).mapMatrix
        (FixedCertificate.shiftedMatrix (MvPolynomial.X r)) =
      sixSiteNearResonantFinShiftedLiteral (1 / 10) (energy r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realEvaluation, FixedCertificate.shiftedMatrix,
      sixSiteNearResonantFinShiftedLiteral, RingHom.mapMatrix_apply]
  all_goals ring

theorem evaluate_fixedRawPolynomial
    (energy : SpectralVariable → Real) :
    realEvaluation energy FixedCertificate.rawPolynomial =
      sixSiteNearResonantFiniteAdjugateInteractionContraction
        (1 / 10) energy := by
  rw [FixedCertificate.rawPolynomial_eq_adjugateContraction,
    map_adjugateEntryProductContraction]
  unfold sixSiteNearResonantFiniteAdjugateInteractionContraction
  congr 1
  funext r
  rw [sixSiteNearResonantFinShiftedMatrix_eq_literal]
  exact map_fixedShiftedMatrix energy r

def residualValue (energy : SpectralVariable → Real) : Real :=
  ∑ a : CubeIndex,
    (ModularCertificate.residualCube a : Real) *
      energy 0 ^ a.1.val * energy 1 ^ a.2.1.val *
        energy 2 ^ a.2.2.val

theorem evaluate_fixedResidualPolynomial
    (energy : SpectralVariable → Real) :
    realEvaluation energy FixedCertificate.residualPolynomial =
      residualValue energy := by
  unfold FixedCertificate.residualPolynomial residualValue
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simp [realEvaluation, FixedCertificate.monomial]

theorem evaluate_fixedSpectralQuintic_eq_pathQuintic
    (energy : SpectralVariable → Real) (r : SpectralVariable) :
    realEvaluation energy (FixedCertificate.spectralQuintic r) =
      (100 / 99 : Real) *
        (nearResonantPathQuintic ((1 / 10 : Real) ^ 2)).eval
          (energy r) := by
  norm_num [realEvaluation, FixedCertificate.spectralQuintic,
    nearResonantPathQuintic, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  ring

theorem finiteContraction_oneTenth_eq_residualValue
    (energy : SpectralVariable → Real)
    (hroot : ∀ r,
      (nearResonantPathQuintic ((1 / 10 : Real) ^ 2)).eval
        (energy r) = 0) :
    sixSiteNearResonantFiniteAdjugateInteractionContraction
        (1 / 10) energy =
      residualValue energy := by
  have hquintic (r : SpectralVariable) :
      realEvaluation energy (FixedCertificate.spectralQuintic r) = 0 := by
    rw [evaluate_fixedSpectralQuintic_eq_pathQuintic, hroot]
    ring
  rw [← evaluate_fixedRawPolynomial,
    FixedCertificate.rawPolynomial_eq_residual_add_quotients]
  simp [hquintic, evaluate_fixedResidualPolynomial]

theorem evaluate_genericClearedPolynomial_oneTenth
    (energy : SpectralVariable → Real)
    (hroot : ∀ r,
      (nearResonantPathQuintic ((1 / 10 : Real) ^ 2)).eval
        (energy r) = 0) :
    MvPolynomial.eval
        (collisionSpectralEvaluation (1 / 10) energy)
        genericSixSiteClearedAdjugateInteractionPolynomial =
      (99 / 100 : Real) ^ 15 * residualValue energy := by
  rw [evaluate_genericSixSiteClearedAdjugateInteractionPolynomial,
    sixSiteNearResonantClearedAdjugateInteractionContraction_eq energy
      (by norm_num),
    finiteContraction_oneTenth_eq_residualValue energy hroot]
  norm_num

/-! ## Polynomial-level fixed specialization -/

def castRatPolynomial :
    MvPolynomial SpectralVariable Rat →+*
      MvPolynomial SpectralVariable Real :=
  MvPolynomial.map (Rat.castHom Real)

def fixedGenericSpecialization :
    MvPolynomial CollisionVariable Real →+*
      MvPolynomial SpectralVariable Real :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : Real →+* MvPolynomial SpectralVariable Real)
    ![MvPolynomial.C (1 / 10), MvPolynomial.X 0,
      MvPolynomial.X 1, MvPolynomial.X 2]

theorem evaluate_fixedGenericSpecialization
    (p : MvPolynomial CollisionVariable Real)
    (energy : SpectralVariable → Real) :
    MvPolynomial.eval energy (fixedGenericSpecialization p) =
      MvPolynomial.eval
        (collisionSpectralEvaluation (1 / 10) energy) p := by
  have hhom :
      (MvPolynomial.eval energy).comp fixedGenericSpecialization =
        MvPolynomial.eval
          (collisionSpectralEvaluation (1 / 10) energy) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fixedGenericSpecialization]
    · intro i
      fin_cases i <;>
        simp [fixedGenericSpecialization, collisionSpectralEvaluation]
  exact DFunLike.congr_fun hhom p

theorem evaluate_castRatPolynomial
    (p : MvPolynomial SpectralVariable Rat)
    (energy : SpectralVariable → Real) :
    MvPolynomial.eval energy (castRatPolynomial p) =
      realEvaluation energy p := by
  simp [castRatPolynomial, realEvaluation, MvPolynomial.eval_map]

theorem fixedGenericSpecialization_polynomial :
    fixedGenericSpecialization
        genericSixSiteClearedAdjugateInteractionPolynomial =
      MvPolynomial.C (99 / 100 : Real) ^ 15 *
        castRatPolynomial FixedCertificate.rawPolynomial := by
  apply MvPolynomial.funext
  intro energy
  rw [evaluate_fixedGenericSpecialization,
    evaluate_genericSixSiteClearedAdjugateInteractionPolynomial,
    sixSiteNearResonantClearedAdjugateInteractionContraction_eq energy
      (by norm_num)]
  simp only [map_mul, map_pow, MvPolynomial.eval_C]
  rw [evaluate_castRatPolynomial, evaluate_fixedRawPolynomial]
  norm_num

/-! ## Ordinary threefold companion representation -/

def monomialExponent (i j k : Nat) : SpectralVariable →₀ Nat :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k

def tensorPower (s : SpectralVariable →₀ Nat) :
    Matrix CubeIndex CubeIndex Rat :=
  (ModularCertificate.companionRat ^ s 0) ⊗ₖ
    ((ModularCertificate.companionRat ^ s 1) ⊗ₖ
      (ModularCertificate.companionRat ^ s 2))

def kroneckerRightOneAlgHom {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
    Matrix n n Rat →ₐ[Rat] Matrix (n × m) (n × m) Rat where
  toFun A := A ⊗ₖ (1 : Matrix m m Rat)
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
    Matrix m m Rat →ₐ[Rat] Matrix (n × m) (n × m) Rat where
  toFun A := (1 : Matrix n n Rat) ⊗ₖ A
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
    Matrix (Fin 5) (Fin 5) Rat →ₐ[Rat]
      Matrix CubeIndex CubeIndex Rat :=
  kroneckerRightOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)

def secondFactorAlgHom :
    Matrix (Fin 5) (Fin 5) Rat →ₐ[Rat]
      Matrix CubeIndex CubeIndex Rat :=
  (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)).comp
    (kroneckerRightOneAlgHom (n := Fin 5) (m := Fin 5))

def thirdFactorAlgHom :
    Matrix (Fin 5) (Fin 5) Rat →ₐ[Rat]
      Matrix CubeIndex CubeIndex Rat :=
  (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5 × Fin 5)).comp
    (kroneckerLeftOneAlgHom (n := Fin 5) (m := Fin 5))

def tensorPowerMonoidHom :
    Multiplicative (SpectralVariable →₀ Nat) →*
      Matrix CubeIndex CubeIndex Rat where
  toFun s := tensorPower s.toAdd
  map_one' := by
    simp [tensorPower]
  map_mul' a b := by
    change tensorPower (a.toAdd + b.toAdd) =
      tensorPower a.toAdd * tensorPower b.toAdd
    simp [tensorPower, Finsupp.add_apply, pow_add,
      ← Matrix.mul_kronecker_mul]

def companionEvaluation :
    MvPolynomial SpectralVariable Rat →+*
      Matrix CubeIndex CubeIndex Rat :=
  AddMonoidAlgebra.liftNCRingHom
    (algebraMap Rat (Matrix CubeIndex CubeIndex Rat))
    tensorPowerMonoidHom
    (by
      intro c s
      exact Matrix.scalar_commute c (fun c' => mul_comm c c')
        (tensorPowerMonoidHom s))

theorem fixedMonomial_eq_monomial (i j k : Nat) (c : Rat) :
    FixedCertificate.monomial i j k c =
      MvPolynomial.monomial (monomialExponent i j k) c := by
  unfold FixedCertificate.monomial monomialExponent
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  rw [← MvPolynomial.monomial_add_single]
  rw [← MvPolynomial.monomial_add_single]

theorem companionEvaluation_fixedMonomial
    (i j k : Nat) (c : Rat) :
    companionEvaluation (FixedCertificate.monomial i j k c) =
      c • tensorPower (monomialExponent i j k) := by
  rw [fixedMonomial_eq_monomial]
  unfold companionEvaluation MvPolynomial.monomial
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Rat (Matrix CubeIndex CubeIndex Rat))
      tensorPowerMonoidHom _) (AddMonoidAlgebra.single _ c) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  rw [Matrix.smul_eq_diagonal_mul]
  rfl

theorem companionEvaluation_C (c : Rat) :
    companionEvaluation (MvPolynomial.C c) = c • 1 := by
  simpa [FixedCertificate.monomial, tensorPower, monomialExponent] using
    companionEvaluation_fixedMonomial 0 0 0 c

theorem companionEvaluation_X (r : SpectralVariable) :
    companionEvaluation (MvPolynomial.X r) =
      tensorPower (Finsupp.single r 1) := by
  unfold companionEvaluation MvPolynomial.X
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Rat (Matrix CubeIndex CubeIndex Rat))
      tensorPowerMonoidHom _) (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp [tensorPowerMonoidHom]

def matrixQuintic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι Rat) : Matrix ι ι Rat :=
  M ^ 5 - (1192 / 99 : Rat) • M ^ 4 +
    (163 / 3 : Rat) • M ^ 3 -
    (11180 / 99 : Rat) • M ^ 2 +
    (10495 / 99 : Rat) • M -
    (400 / 11 : Rat) • 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem matrixQuintic_companionRat :
    matrixQuintic ModularCertificate.companionRat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixQuintic, ModularCertificate.companionRat,
      pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matrixQuintic_map
    (f : Matrix (Fin 5) (Fin 5) Rat →ₐ[Rat]
      Matrix CubeIndex CubeIndex Rat)
    (M : Matrix (Fin 5) (Fin 5) Rat) :
    matrixQuintic (f M) = f (matrixQuintic M) := by
  simp [matrixQuintic]

theorem tensorPower_single_zero :
    tensorPower (Finsupp.single (0 : SpectralVariable) 1) =
      firstFactorAlgHom ModularCertificate.companionRat := by
  simp [tensorPower, firstFactorAlgHom, kroneckerRightOneAlgHom]

theorem tensorPower_single_one :
    tensorPower (Finsupp.single (1 : SpectralVariable) 1) =
      secondFactorAlgHom ModularCertificate.companionRat := by
  simp [tensorPower, secondFactorAlgHom, kroneckerLeftOneAlgHom,
    kroneckerRightOneAlgHom]

theorem tensorPower_single_two :
    tensorPower (Finsupp.single (2 : SpectralVariable) 1) =
      thirdFactorAlgHom ModularCertificate.companionRat := by
  simp [tensorPower, thirdFactorAlgHom, kroneckerLeftOneAlgHom]

theorem companionEvaluation_fixedSpectralQuintic
    (r : SpectralVariable) :
    companionEvaluation (FixedCertificate.spectralQuintic r) = 0 := by
  unfold FixedCertificate.spectralQuintic
  simp only [map_sub, map_add, map_mul, map_pow, companionEvaluation_C,
    companionEvaluation_X, Matrix.smul_mul, one_mul]
  change matrixQuintic (tensorPower (Finsupp.single r 1)) = 0
  have hzero :
      matrixQuintic (tensorPower
        (Finsupp.single (0 : SpectralVariable) 1)) = 0 := by
    rw [tensorPower_single_zero, matrixQuintic_map,
      matrixQuintic_companionRat, map_zero]
  have hone :
      matrixQuintic (tensorPower
        (Finsupp.single (1 : SpectralVariable) 1)) = 0 := by
    rw [tensorPower_single_one, matrixQuintic_map,
      matrixQuintic_companionRat, map_zero]
  have htwo :
      matrixQuintic (tensorPower
        (Finsupp.single (2 : SpectralVariable) 1)) = 0 := by
    rw [tensorPower_single_two, matrixQuintic_map,
      matrixQuintic_companionRat, map_zero]
  fin_cases r
  · simpa using hzero
  · simpa using hone
  · simpa using htwo

theorem companionEvaluation_fixedResidualPolynomial :
    companionEvaluation FixedCertificate.residualPolynomial =
      ModularCertificate.residualMultiplicationRat := by
  unfold FixedCertificate.residualPolynomial
    ModularCertificate.residualMultiplicationRat
    ModularCertificate.cubeMultiplication
  simp_rw [map_sum, companionEvaluation_fixedMonomial]
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  simp [tensorPower, monomialExponent]

theorem companionEvaluation_fixedRawPolynomial :
    companionEvaluation FixedCertificate.rawPolynomial =
      ModularCertificate.residualMultiplicationRat := by
  rw [FixedCertificate.rawPolynomial_eq_residual_add_quotients]
  simp [companionEvaluation_fixedSpectralQuintic,
    companionEvaluation_fixedResidualPolynomial]

end

end ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualSpecialization
