import ArchonPhysics.OrderedInteractionSpectralFactorization

/-!
# Ordered spectral projectors and the exact finite resolvent

For a finite real Hermitian matrix with simple ordered spectrum, this module
identifies the nonsingular inverse of `z I - A` with its finite ordered
projector expansion whenever the real parameter `z` avoids every ordered
eigenvalue.  Sandwiching that identity by an arbitrary bond matrix gives the
corresponding exact weighted projected-bond kernel formula.

These are deterministic finite-dimensional identities.  In particular, no
boundary-value limit, infinite-volume Green function, or kinetic limit is
asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.OrderedProjectedResolventBridge

open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota]

/-- The finite ordered-projector candidate for the resolvent of `A` at `z`. -/
def orderedResolventProjectorSum (A : HermitianMatrix iota) (z : Real) :
    Matrix iota iota Real :=
  ∑ k : Fin (Fintype.card iota),
    (z - orderedEigenvalue A k)⁻¹ • orderedModeProjector A k

/-- The shifted matrix acts diagonally on the ordered Hermitian eigenbasis. -/
theorem shiftedMatrix_mulVec_eigenvectorBasis
    (A : HermitianMatrix iota) (z : Real)
    (r : Fin (Fintype.card iota)) :
    (z • (1 : Matrix iota iota Real) - matrixVal A) *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      (z - orderedEigenvalue A r) •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    matrixVal_mulVec_eigenvectorBasis]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On simple spectrum, the projector sum acts by the reciprocal shifted
eigenvalue on each ordered eigenvector. -/
theorem orderedResolventProjectorSum_mulVec_eigenvectorBasis
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (z : Real) (r : Fin (Fintype.card iota)) :
    orderedResolventProjectorSum A z *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      (z - orderedEigenvalue A r)⁻¹ •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  rw [orderedResolventProjectorSum, Matrix.sum_mulVec]
  simp [Matrix.smul_mulVec,
    orderedModeProjector_mulVec_eigenvectorBasis A hsimple]

/-- Avoiding the ordered spectrum makes the projector sum a right inverse of
`z I - A`.  This basis calculation is the algebraic core of the bridge. -/
theorem shiftedMatrix_mul_orderedResolventProjectorSum_eq_one
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (z : Real) (hz : ∀ k, z ≠ orderedEigenvalue A k) :
    (z • (1 : Matrix iota iota Real) - matrixVal A) *
        orderedResolventProjectorSum A z = 1 := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [← Matrix.mulVec_mulVec,
    orderedResolventProjectorSum_mulVec_eigenvectorBasis A hsimple,
    Matrix.mulVec_smul, shiftedMatrix_mulVec_eigenvectorBasis,
    Matrix.one_mulVec, smul_smul]
  have hne : z - orderedEigenvalue A r ≠ 0 := sub_ne_zero.mpr (hz r)
  rw [inv_mul_cancel₀ hne, one_smul]

/-- Exact ordered spectral-projector expansion of the nonsingular inverse. -/
theorem orderedResolvent_projectorExpansion
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (z : Real) (hz : ∀ k, z ≠ orderedEigenvalue A k) :
    (z • (1 : Matrix iota iota Real) - matrixVal A)⁻¹ =
      ∑ k : Fin (Fintype.card iota),
        (z - orderedEigenvalue A k)⁻¹ • orderedModeProjector A k := by
  change (z • (1 : Matrix iota iota Real) - matrixVal A)⁻¹ =
    orderedResolventProjectorSum A z
  exact Matrix.inv_eq_right_inv
    (shiftedMatrix_mul_orderedResolventProjectorSum_eq_one A hsimple z hz)

/-- An arbitrary one-leg weight sum is the bond sandwich of the corresponding
ordered-projector sum. -/
theorem weightedProjectedBondKernel_eq_projectorSumSandwich
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (weight : Fin (Fintype.card iota) → Real) :
    weightedProjectedBondKernel B A weight =
      B * (∑ k : Fin (Fintype.card iota),
        weight k • orderedModeProjector A k) * B.transpose := by
  calc
    weightedProjectedBondKernel B A weight =
        ∑ k : Fin (Fintype.card iota),
          weight k • projectedBondKernel B A k := by
      ext j l
      unfold weightedProjectedBondKernel
      rw [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro k _hk
      rfl
    _ = ∑ k : Fin (Fintype.card iota),
          B * (weight k • orderedModeProjector A k) * B.transpose := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [projectedBondKernel, Matrix.mul_smul, Matrix.smul_mul]
    _ = B * (∑ k : Fin (Fintype.card iota),
          weight k • orderedModeProjector A k) * B.transpose := by
      symm
      rw [Matrix.mul_sum, Matrix.sum_mul]

/-- Exact resolvent sandwich for the weighted projected-bond kernel. -/
theorem weightedProjectedBondKernel_resolvent
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A) (z : Real)
    (hz : ∀ k, z ≠ orderedEigenvalue A k) :
    weightedProjectedBondKernel B A
        (fun k ↦ (z - orderedEigenvalue A k)⁻¹) =
      B * (z • (1 : Matrix iota iota Real) - matrixVal A)⁻¹ *
        B.transpose := by
  rw [weightedProjectedBondKernel_eq_projectorSumSandwich,
    ← orderedResolvent_projectorExpansion A hsimple z hz]

end

end ArchonPhysics.OrderedProjectedResolventBridge
