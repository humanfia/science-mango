import ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination

/-!
# Soundness of the scaled-companion collision norm

This file proves the semantic half of the elimination certificate.  If three
real energies lie on the characteristic quintic and the cleared collision
contraction vanishes at those energies, then the univariate quotient norm
vanishes at the path parameter.
-/

open scoped BigOperators Matrix Polynomial Kronecker

namespace ArchonPhysics.ActualSixSiteNearResonantScaledCompanionEliminationSoundness

open ArchonPhysics.ActualSixSiteNearResonantPathSeparable
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanion
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionTensor
open ArchonPhysics.ActualSixSiteNearResonantClearedContraction
open ArchonPhysics.ActualSixSiteNearResonantFiniteContractionBridge
open ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
open ArchonPhysics.ActualSixSiteNearResonantScaledCompanionElimination

noncomputable section

def collisionMonomialEvaluation (t : Real) (energy : Fin 3 → Real)
    (s : CollisionExponent) : Real :=
  clearedCollisionPolynomial.coeff s *
    ∏ i, collisionSpectralEvaluation t energy i ^ s i

theorem collisionMonomialEvaluation_eq (t : Real) (energy : Fin 3 → Real)
    (s : CollisionExponent) :
    collisionMonomialEvaluation t energy s =
      clearedCollisionPolynomial.coeff s * t ^ s 0 *
        energy 0 ^ s 1 * energy 1 ^ s 2 * energy 2 ^ s 3 := by
  simp [collisionMonomialEvaluation, collisionSpectralEvaluation,
    Fin.prod_univ_four]
  ring

theorem evaluate_clearedCollisionPolynomial_eq_sum
    (t : Real) (energy : Fin 3 → Real) :
    MvPolynomial.eval (collisionSpectralEvaluation t energy)
        clearedCollisionPolynomial =
      ∑ s ∈ clearedCollisionPolynomial.support,
        collisionMonomialEvaluation t energy s := by
  simpa only [collisionMonomialEvaluation] using
    MvPolynomial.eval_eq' (collisionSpectralEvaluation t energy)
      clearedCollisionPolynomial

theorem scaledCollisionMonomialScalar_identity
    (t : Real) (energy : Fin 3 → Real)
    {s : CollisionExponent} (hs : s ∈ clearedCollisionPolynomial.support) :
    (clearedCollisionPolynomial.coeff s * t ^ s 0 *
        (1 - t ^ 2) ^
          (clearedCollisionPolynomial.totalDegree - collisionEnergyDegree s)) *
      (((1 - t ^ 2) * energy 0) ^ s 1 *
        (((1 - t ^ 2) * energy 1) ^ s 2 *
          ((1 - t ^ 2) * energy 2) ^ s 3)) =
      (1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
        collisionMonomialEvaluation t energy s := by
  rw [collisionMonomialEvaluation_eq, mul_pow, mul_pow, mul_pow]
  have hdegree := collisionEnergyDegree_le_totalDegree hs
  unfold collisionEnergyDegree at hdegree
  have hexponent :
      clearedCollisionPolynomial.totalDegree - (s 1 + s 2 + s 3) +
          s 1 + s 2 + s 3 =
        clearedCollisionPolynomial.totalDegree := by
    omega
  have hpower :
      (1 - t ^ 2) ^
            (clearedCollisionPolynomial.totalDegree - (s 1 + s 2 + s 3)) *
          (1 - t ^ 2) ^ s 1 *
          (1 - t ^ 2) ^ s 2 *
          (1 - t ^ 2) ^ s 3 =
        (1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree := by
    rw [← pow_add, ← pow_add, ← pow_add, hexponent]
  calc
    (clearedCollisionPolynomial.coeff s * t ^ s 0 *
          (1 - t ^ 2) ^
            (clearedCollisionPolynomial.totalDegree - (s 1 + s 2 + s 3))) *
        (((1 - t ^ 2) ^ s 1 * energy 0 ^ s 1) *
          (((1 - t ^ 2) ^ s 2 * energy 1 ^ s 2) *
            ((1 - t ^ 2) ^ s 3 * energy 2 ^ s 3))) =
      ((1 - t ^ 2) ^
            (clearedCollisionPolynomial.totalDegree - (s 1 + s 2 + s 3)) *
          (1 - t ^ 2) ^ s 1 *
          (1 - t ^ 2) ^ s 2 *
          (1 - t ^ 2) ^ s 3) *
        (clearedCollisionPolynomial.coeff s * t ^ s 0 *
          energy 0 ^ s 1 * energy 1 ^ s 2 * energy 2 ^ s 3) := by ring
    _ = (1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
        (clearedCollisionPolynomial.coeff s * t ^ s 0 *
          energy 0 ^ s 1 * energy 1 ^ s 2 * energy 2 ^ s 3) := by
      rw [hpower]

theorem tripleQuinticEvaluationRow_vecMul_scaledCollisionMonomialMatrix
    {t : Real} (energy : Fin 3 → Real)
    (hroot : ∀ r : Fin 3,
      (nearResonantPathQuintic (t ^ 2)).eval (energy r) = 0)
    {s : CollisionExponent} (hs : s ∈ clearedCollisionPolynomial.support) :
    tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) ᵥ*
        scaledCollisionMonomialMatrix t s =
      ((1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
          collisionMonomialEvaluation t energy s) •
        tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) := by
  unfold scaledCollisionMonomialMatrix collisionTensorPower
  rw [Matrix.vecMul_smul,
    tripleQuinticEvaluationRow_vecMul_tensorPowers
      (hroot 0) (hroot 1) (hroot 2),
    smul_smul]
  exact congrArg
    (fun c : Real ↦
      c • tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2))
    (by
      simpa only [mul_assoc] using
        (scaledCollisionMonomialScalar_identity t energy hs))

theorem tripleQuinticEvaluationRow_vecMul_scaledCollisionMultiplicationMatrix
    {t : Real} (energy : Fin 3 → Real)
    (hroot : ∀ r : Fin 3,
      (nearResonantPathQuintic (t ^ 2)).eval (energy r) = 0) :
    tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) ᵥ*
        scaledCollisionMultiplicationMatrix t =
      ((1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
          MvPolynomial.eval (collisionSpectralEvaluation t energy)
            clearedCollisionPolynomial) •
        tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) := by
  unfold scaledCollisionMultiplicationMatrix
  rw [Matrix.vecMul_sum]
  calc
    (∑ s ∈ clearedCollisionPolynomial.support,
        tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) ᵥ*
          scaledCollisionMonomialMatrix t s) =
      ∑ s ∈ clearedCollisionPolynomial.support,
        ((1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
          collisionMonomialEvaluation t energy s) •
            tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact tripleQuinticEvaluationRow_vecMul_scaledCollisionMonomialMatrix
        energy hroot hs
    _ = ((1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
          ∑ s ∈ clearedCollisionPolynomial.support,
            collisionMonomialEvaluation t energy s) •
        tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ((1 - t ^ 2) ^ clearedCollisionPolynomial.totalDegree *
          MvPolynomial.eval (collisionSpectralEvaluation t energy)
            clearedCollisionPolynomial) •
        tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2) := by
      rw [evaluate_clearedCollisionPolynomial_eq_sum]

/-- Semantic soundness of the determinant: vanishing of the cleared
contraction at three on-shell roots forces vanishing of the exceptional
polynomial. -/
theorem clearedCollision_zero_implies_exceptional_eval_zero
    {t : Real} (energy : Fin 3 → Real)
    (hroot : ∀ r : Fin 3,
      (nearResonantPathQuintic (t ^ 2)).eval (energy r) = 0)
    (hzero : MvPolynomial.eval (collisionSpectralEvaluation t energy)
      clearedCollisionPolynomial = 0) :
    scaledCollisionExceptionalPolynomial.eval t = 0 := by
  rw [evaluate_scaledCollisionExceptionalPolynomial]
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨tripleQuinticEvaluationRow (energy 0) (energy 1) (energy 2),
    tripleQuinticEvaluationRow_ne_zero _ _ _, ?_⟩
  rw [tripleQuinticEvaluationRow_vecMul_scaledCollisionMultiplicationMatrix
    energy hroot, hzero, mul_zero, zero_smul]

/-- The same implication with the premise stated as the literal finite
adjugate contraction. -/
theorem finiteContraction_zero_implies_exceptional_eval_zero
    {t : Real} (energy : Fin 3 → Real)
    (hroot : ∀ r : Fin 3,
      (nearResonantPathQuintic (t ^ 2)).eval (energy r) = 0)
    (hpole : 1 - t ^ 2 ≠ 0)
    (hzero :
      sixSiteNearResonantFiniteAdjugateInteractionContraction t energy = 0) :
    scaledCollisionExceptionalPolynomial.eval t = 0 := by
  apply clearedCollision_zero_implies_exceptional_eval_zero energy hroot
  rw [clearedCollisionPolynomial,
    evaluate_genericSixSiteClearedAdjugateInteractionPolynomial,
    sixSiteNearResonantClearedAdjugateInteractionContraction_eq energy hpole,
    hzero, mul_zero]

end


end ArchonPhysics.ActualSixSiteNearResonantScaledCompanionEliminationSoundness
