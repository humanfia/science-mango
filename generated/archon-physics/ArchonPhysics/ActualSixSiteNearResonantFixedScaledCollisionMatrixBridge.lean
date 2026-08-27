import ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualSpecialization
import ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination

/-!
# The fixed scaled collision matrix is the residual regular representation

This file combines the fixed rational quotient certificate with the generic
scaled-companion construction at `t = 1 / 10`.  The resulting equality uses
the same `residualMultiplicationRat` matrix as the modular determinant
certificate.
-/

open scoped BigOperators Matrix Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantFixedScaledCollisionMatrixBridge

open ArchonPhysics.ActualSixSiteNearResonantCollisionWeightWitness
open ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualBridge
open ArchonPhysics.ActualSixSiteNearResonantFixedContractionResidualSpecialization
open ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanion
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination

noncomputable section

abbrev CubeIndex := ModularCertificate.CubeIndex

/-! ## Real companion evaluation -/

def companionReal : Matrix (Fin 5) (Fin 5) Real :=
  (Rat.castHom Real).mapMatrix ModularCertificate.companionRat

def realTensorPower (s : Fin 3 →₀ Nat) :
    Matrix CubeIndex CubeIndex Real :=
  (companionReal ^ s 0) ⊗ₖ
    ((companionReal ^ s 1) ⊗ₖ (companionReal ^ s 2))

theorem scaledCompanion_oneTenth :
    nearResonantScaledCompanion (1 / 10) =
      (99 / 100 : Real) • companionReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nearResonantScaledCompanion, companionReal,
      ModularCertificate.companionRat, RingHom.mapMatrix_apply]

def energyExponent (s : CollisionExponent) : Fin 3 →₀ Nat :=
  Finsupp.single 0 (s 1) + Finsupp.single 1 (s 2) +
    Finsupp.single 2 (s 3)

theorem collisionTensorPower_oneTenth (s : CollisionExponent) :
    collisionTensorPower (1 / 10) s =
      (99 / 100 : Real) ^ collisionEnergyDegree s •
        realTensorPower (energyExponent s) := by
  rw [collisionTensorPower, scaledCompanion_oneTenth]
  ext ⟨i₀, i₁, i₂⟩ ⟨j₀, j₁, j₂⟩
  simp [realTensorPower, energyExponent, collisionEnergyDegree,
    smul_pow, Matrix.smul_apply, pow_add]
  ring

def realTensorPowerMonoidHom :
    Multiplicative (Fin 3 →₀ Nat) →*
      Matrix CubeIndex CubeIndex Real where
  toFun s := realTensorPower s.toAdd
  map_one' := by
    simp [realTensorPower]
  map_mul' a b := by
    change realTensorPower (a.toAdd + b.toAdd) =
      realTensorPower a.toAdd * realTensorPower b.toAdd
    simp [realTensorPower, Finsupp.add_apply, pow_add,
      ← Matrix.mul_kronecker_mul]

def realCompanionEvaluation :
    MvPolynomial (Fin 3) Real →+*
      Matrix CubeIndex CubeIndex Real :=
  AddMonoidAlgebra.liftNCRingHom
    (algebraMap Real (Matrix CubeIndex CubeIndex Real))
    realTensorPowerMonoidHom
    (by
      intro c s
      exact Matrix.scalar_commute c (fun c' => mul_comm c c')
        (realTensorPowerMonoidHom s))

theorem realCompanionEvaluation_monomial
    (s : Fin 3 →₀ Nat) (c : Real) :
    realCompanionEvaluation (MvPolynomial.monomial s c) =
      c • realTensorPower s := by
  unfold realCompanionEvaluation MvPolynomial.monomial
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Real (Matrix CubeIndex CubeIndex Real))
      realTensorPowerMonoidHom _) (AddMonoidAlgebra.single _ c) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  rw [Matrix.smul_eq_diagonal_mul]
  rfl

theorem realCompanionEvaluation_C (c : Real) :
    realCompanionEvaluation (MvPolynomial.C c) = c • 1 := by
  change realCompanionEvaluation (MvPolynomial.monomial 0 c) = _
  rw [realCompanionEvaluation_monomial]
  simp [realTensorPower]

theorem realCompanionEvaluation_X (r : Fin 3) :
    realCompanionEvaluation (MvPolynomial.X r) =
      realTensorPower (Finsupp.single r 1) := by
  unfold realCompanionEvaluation MvPolynomial.X
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Real (Matrix CubeIndex CubeIndex Real))
      realTensorPowerMonoidHom _) (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp [realTensorPowerMonoidHom]

/-! ## The generic collision-variable representation -/

def genericTensorPower (s : CollisionExponent) :
    Matrix CubeIndex CubeIndex Real :=
  (1 / 10 : Real) ^ s 0 • realTensorPower (energyExponent s)

def genericTensorPowerMonoidHom :
    Multiplicative CollisionExponent →*
      Matrix CubeIndex CubeIndex Real where
  toFun s := genericTensorPower s.toAdd
  map_one' := by
    simp [genericTensorPower, realTensorPower, energyExponent]
  map_mul' a b := by
    change genericTensorPower (a.toAdd + b.toAdd) =
      genericTensorPower a.toAdd * genericTensorPower b.toAdd
    simp [genericTensorPower, realTensorPower, energyExponent,
      Finsupp.add_apply, pow_add, ← Matrix.mul_kronecker_mul,
      smul_smul]
    congr 1
    ring

def genericCompanionEvaluation :
    MvPolynomial CollisionVariable Real →+*
      Matrix CubeIndex CubeIndex Real :=
  AddMonoidAlgebra.liftNCRingHom
    (algebraMap Real (Matrix CubeIndex CubeIndex Real))
    genericTensorPowerMonoidHom
    (by
      intro c s
      exact Matrix.scalar_commute c (fun c' => mul_comm c c')
        (genericTensorPowerMonoidHom s))

theorem genericCompanionEvaluation_monomial
    (s : CollisionExponent) (c : Real) :
    genericCompanionEvaluation (MvPolynomial.monomial s c) =
      c • genericTensorPower s := by
  unfold genericCompanionEvaluation MvPolynomial.monomial
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Real (Matrix CubeIndex CubeIndex Real))
      genericTensorPowerMonoidHom _) (AddMonoidAlgebra.single _ c) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  rw [Matrix.smul_eq_diagonal_mul]
  rfl

theorem genericCompanionEvaluation_C (c : Real) :
    genericCompanionEvaluation (MvPolynomial.C c) = c • 1 := by
  change genericCompanionEvaluation (MvPolynomial.monomial 0 c) = _
  rw [genericCompanionEvaluation_monomial]
  simp [genericTensorPower, realTensorPower, energyExponent]

theorem genericCompanionEvaluation_X (i : CollisionVariable) :
    genericCompanionEvaluation (MvPolynomial.X i) =
      genericTensorPower (Finsupp.single i 1) := by
  unfold genericCompanionEvaluation MvPolynomial.X
  change
    (AddMonoidAlgebra.liftNCRingHom
      (algebraMap Real (Matrix CubeIndex CubeIndex Real))
      genericTensorPowerMonoidHom _) (AddMonoidAlgebra.single _ 1) = _
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp [genericTensorPowerMonoidHom]

theorem genericCompanionEvaluation_as_sum
    (p : MvPolynomial CollisionVariable Real) :
    genericCompanionEvaluation p =
      ∑ s ∈ p.support,
        p.coeff s • genericTensorPower s := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp_rw [map_sum, genericCompanionEvaluation_monomial]

theorem genericCompanionEvaluation_eq_comp :
    genericCompanionEvaluation =
      realCompanionEvaluation.comp fixedGenericSpecialization := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [genericCompanionEvaluation_C, realCompanionEvaluation_C,
      fixedGenericSpecialization]
  · intro i
    fin_cases i <;>
      simp [genericCompanionEvaluation_X, realCompanionEvaluation_X,
        realCompanionEvaluation_C, fixedGenericSpecialization,
        genericTensorPower, realTensorPower, energyExponent]

/-! ## Extracting the common scaling factor -/

theorem scaledCollisionMonomialMatrix_oneTenth
    {s : CollisionExponent}
    (hs : s ∈ clearedCollisionPolynomial.support) :
    scaledCollisionMonomialMatrix (1 / 10) s =
      (99 / 100 : Real) ^
          clearedCollisionPolynomial.totalDegree •
        (clearedCollisionPolynomial.coeff s •
          genericTensorPower s) := by
  unfold scaledCollisionMonomialMatrix genericTensorPower
  rw [collisionTensorPower_oneTenth]
  simp only [smul_smul]
  congr 1
  have hpow :
      (99 / 100 : Real) ^
          (clearedCollisionPolynomial.totalDegree -
            collisionEnergyDegree s) *
        (99 / 100 : Real) ^ collisionEnergyDegree s =
      (99 / 100 : Real) ^
        clearedCollisionPolynomial.totalDegree := by
    rw [← pow_add,
      Nat.sub_add_cancel (collisionEnergyDegree_le_totalDegree hs)]
  have hleading :
      (1 - (1 / 10 : Real) ^ 2) = 99 / 100 := by
    norm_num
  rw [hleading]
  rw [mul_assoc, hpow]
  ring

theorem scaledCollisionMultiplicationMatrix_oneTenth_eq_generic :
    scaledCollisionMultiplicationMatrix (1 / 10) =
      (99 / 100 : Real) ^
          clearedCollisionPolynomial.totalDegree •
        genericCompanionEvaluation clearedCollisionPolynomial := by
  unfold scaledCollisionMultiplicationMatrix
  rw [genericCompanionEvaluation_as_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact scaledCollisionMonomialMatrix_oneTenth hs

/-! ## Compatibility with the rational regular representation -/

theorem map_tensorPower (s : Fin 3 →₀ Nat) :
    (Rat.castHom Real).mapMatrix (tensorPower s) =
      realTensorPower s := by
  unfold tensorPower realTensorPower companionReal
  rw [mapMatrix_kronecker, mapMatrix_kronecker,
    map_pow (Rat.castHom Real).mapMatrix,
    map_pow (Rat.castHom Real).mapMatrix,
    map_pow (Rat.castHom Real).mapMatrix]

theorem map_smul_one (c : Rat) :
    (Rat.castHom Real).mapMatrix
        (c • (1 : Matrix CubeIndex CubeIndex Rat)) =
      (c : Real) • (1 : Matrix CubeIndex CubeIndex Real) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RingHom.mapMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [RingHom.mapMatrix_apply, Matrix.smul_apply, smul_eq_mul, hij]

theorem realCompanionEvaluation_comp_cast :
    realCompanionEvaluation.comp castRatPolynomial =
      (Rat.castHom Real).mapMatrix.comp companionEvaluation := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change realCompanionEvaluation
        (castRatPolynomial (MvPolynomial.C c)) =
      (Rat.castHom Real).mapMatrix
        (companionEvaluation (MvPolynomial.C c))
    rw [show castRatPolynomial (MvPolynomial.C c) =
        MvPolynomial.C (c : Real) by simp [castRatPolynomial],
      realCompanionEvaluation_C, companionEvaluation_C,
      map_smul_one]
  · intro r
    change realCompanionEvaluation
        (castRatPolynomial (MvPolynomial.X r)) =
      (Rat.castHom Real).mapMatrix
        (companionEvaluation (MvPolynomial.X r))
    rw [show castRatPolynomial (MvPolynomial.X r) =
        MvPolynomial.X r by simp [castRatPolynomial],
      realCompanionEvaluation_X, companionEvaluation_X,
      map_tensorPower]

theorem genericCompanionEvaluation_fixedPolynomial
    (p : MvPolynomial (Fin 3) Rat)
    (P : MvPolynomial CollisionVariable Real)
    (R : Matrix CubeIndex CubeIndex Rat)
    (hpoly :
      fixedGenericSpecialization P =
        MvPolynomial.C (99 / 100 : Real) ^ 15 *
          castRatPolynomial p)
    (hraw : companionEvaluation p = R) :
    genericCompanionEvaluation P =
      (99 / 100 : Real) ^ 15 •
        (Rat.castHom Real).mapMatrix R := by
  rw [genericCompanionEvaluation_eq_comp]
  change realCompanionEvaluation (fixedGenericSpecialization P) = _
  rw [hpoly]
  simp only [map_mul, map_pow, realCompanionEvaluation_C,
    smul_pow, one_pow, Matrix.smul_mul, one_mul]
  have hcompat := DFunLike.congr_fun
    realCompanionEvaluation_comp_cast p
  change realCompanionEvaluation (castRatPolynomial p) =
    (Rat.castHom Real).mapMatrix (companionEvaluation p) at hcompat
  rw [hcompat, hraw]

theorem genericCompanionEvaluation_cleared_eq_residual :
    genericCompanionEvaluation clearedCollisionPolynomial =
      (99 / 100 : Real) ^ 15 •
        (Rat.castHom Real).mapMatrix
          ModularCertificate.residualMultiplicationRat := by
  refine genericCompanionEvaluation_fixedPolynomial
    FixedCertificate.rawPolynomial
    clearedCollisionPolynomial
    ModularCertificate.residualMultiplicationRat ?_ ?_
  · simpa [clearedCollisionPolynomial] using
      fixedGenericSpecialization_polynomial
  · exact companionEvaluation_fixedRawPolynomial

/-! ## Final fixed scaled-matrix identity -/

theorem scaledCollisionMultiplicationMatrix_oneTenth_eq_residualMultiplication :
    scaledCollisionMultiplicationMatrix (1 / 10) =
      (99 / 100 : Real) ^
          (clearedCollisionPolynomial.totalDegree + 15) •
        (Rat.castHom Real).mapMatrix
          ModularCertificate.residualMultiplicationRat := by
  rw [scaledCollisionMultiplicationMatrix_oneTenth_eq_generic,
    genericCompanionEvaluation_cleared_eq_residual,
    smul_smul, pow_add]

end

end ArchonPhysics.ActualSixSiteNearResonantFixedScaledCollisionMatrixBridge
