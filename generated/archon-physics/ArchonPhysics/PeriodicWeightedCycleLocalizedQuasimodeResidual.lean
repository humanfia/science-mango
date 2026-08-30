import ArchonPhysics.PeriodicWeightedCycleMismatchPerturbation

open scoped Matrix

/-!
# Localized block eigenvectors as global periodic-chain quasimodes

The periodic coupling between a left block and its complement has operator
norm of order one.  A small global residual can nevertheless arise when the
left-block eigenvector has small overlap with the four cut-bond vectors.

This module records that mechanism exactly.  It does not assume a small
boundary operator, localization, or a probabilistic Green-function estimate.
Those model-specific inputs only have to control four scalar boundary
overlaps.
-/

namespace ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual

open ArchonPhysics
open ArchonPhysics.FiniteVolumeSpectralCountGluing
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PeriodicWeightedCycleMismatchPerturbation

noncomputable section

/-- Zero-extension of a vector on the left periodic block. -/
def leftZeroExtension {n m : Nat} (v : Fin n → Real) :
    Fin n ⊕ Fin m → Real :=
  Sum.elim v (fun _ ↦ 0)

/-- The block-diagonal matrix acts on a left zero-extension exactly through
its left block. -/
theorem periodicBlockDiagonal_mulVec_leftZeroExtension
    {n m : Nat} [NeZero n] [NeZero m]
    (w : Fin (n + m) → Real) (v : Fin n → Real) :
    (periodicBlockDiagonalHermitian w).1 *ᵥ leftZeroExtension v =
      leftZeroExtension
        ((finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v) := by
  let A : Matrix (Fin n) (Fin n) Real :=
    (finWeightedCycleHermitian (leftWeights w)).1
  let D : Matrix (Fin m) (Fin m) Real :=
    (finWeightedCycleHermitian (rightWeights w)).1
  change Matrix.fromBlocks A 0 0 D *ᵥ leftZeroExtension v =
    leftZeroExtension (A *ᵥ v)
  rw [Matrix.fromBlocks_mulVec]
  funext x
  cases x with
  | inl i => simp [leftZeroExtension]
  | inr i =>
      simp only [Sum.elim_inr, leftZeroExtension,
        Matrix.zero_mulVec, zero_add]
      change (D *ᵥ (0 : Fin m → Real)) i = 0
      rw [Matrix.mulVec_zero]
      rfl

/-- A left-block eigenvector remains an exact eigenvector after zero-extension
for the uncoupled block-diagonal reference. -/
theorem periodicBlockDiagonal_mulVec_leftEigenvector
    {n m : Nat} [NeZero n] [NeZero m]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v) :
    (periodicBlockDiagonalHermitian w).1 *ᵥ leftZeroExtension v =
      lambda • leftZeroExtension v := by
  rw [periodicBlockDiagonal_mulVec_leftZeroExtension, hv]
  funext x
  cases x <;> simp [leftZeroExtension]

/-- Exact action of an arbitrary finite signed rank-one update on a vector. -/
theorem rankOneUpdateSum_mulVec
    {label index : Type*} [Fintype index]
    (s : Finset label) (c : label → Real)
    (vectors : label → index → Real) (x : index → Real) :
    rankOneUpdateSum s c vectors *ᵥ x =
      ∑ r ∈ s, (c r * (vectors r ⬝ᵥ x)) • vectors r := by
  classical
  unfold rankOneUpdateSum
  rw [Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [smul_eq_mul, mul_assoc]

/-- The physical periodic boundary residual depends only on four scalar
cut-bond overlaps. -/
theorem periodicBoundaryMatrix_mulVec_eq_overlapSum
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (x : Fin n ⊕ Fin m → Real) :
    periodicBoundaryMatrix w *ᵥ x =
      ∑ r : Fin 4,
        (boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ x)) •
          boundaryVectors (n := n) (m := m) r := by
  simpa [periodicBoundaryMatrix] using
    rankOneUpdateSum_mulVec (Finset.univ : Finset (Fin 4))
      (boundaryCoefficients (n := n) (m := m) w)
      (boundaryVectors (n := n) (m := m)) x

/-- Exact quasimode identity.  The residual of a zero-extended left-block
eigenvector in the genuinely coupled periodic chain is precisely the
four-overlap boundary vector. -/
theorem splitFinWeightedCycle_leftEigenvector_residual_eq_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v) :
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v -
        lambda • leftZeroExtension v =
      periodicBoundaryMatrix w *ᵥ leftZeroExtension v := by
  have hblock :=
    periodicBlockDiagonal_mulVec_leftEigenvector w v lambda hv
  have hboundary := congrArg
    (fun A : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real =>
      A *ᵥ leftZeroExtension v)
    (splitFinWeightedCycle_sub_periodicBlockDiagonal_eq_boundary w)
  calc
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v -
        lambda • leftZeroExtension v =
      (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v -
        (periodicBlockDiagonalHermitian w).1 *ᵥ leftZeroExtension v := by
          rw [hblock]
    _ = ((splitFinWeightedCycleHermitian w).1 -
          (periodicBlockDiagonalHermitian w).1) *ᵥ leftZeroExtension v := by
      exact (Matrix.sub_mulVec
        ((splitFinWeightedCycleHermitian w).1 :
          Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real)
        ((periodicBlockDiagonalHermitian w).1 :
          Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real)
        (leftZeroExtension v)).symm
    _ = periodicBoundaryMatrix w *ᵥ leftZeroExtension v := hboundary

/-- Expanded form of the exact physical residual.  A localization theorem can
feed this endpoint by estimating only the four displayed overlaps. -/
theorem splitFinWeightedCycle_leftEigenvector_residual_eq_overlapSum
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v) :
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v -
        lambda • leftZeroExtension v =
      ∑ r : Fin 4,
        (boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ
            leftZeroExtension v)) •
          boundaryVectors (n := n) (m := m) r := by
  rw [splitFinWeightedCycle_leftEigenvector_residual_eq_boundary w v lambda hv,
    periodicBoundaryMatrix_mulVec_eq_overlapSum]

/-- Vanishing cut-bond overlaps recover an exact eigenvector of the coupled
periodic chain.  Quantitative localization replaces zero by a small bound and
therefore produces a genuine quasimode. -/
theorem splitFinWeightedCycle_mulVec_leftEigenvector_of_boundaryOrthogonal
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v)
    (hcut : ∀ r : Fin 4,
      boundaryVectors (n := n) (m := m) r ⬝ᵥ
        leftZeroExtension v = 0) :
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v =
      lambda • leftZeroExtension v := by
  have hres :=
    splitFinWeightedCycle_leftEigenvector_residual_eq_overlapSum
      w v lambda hv
  have hzero :
      (∑ r : Fin 4,
        (boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ
            leftZeroExtension v)) •
            boundaryVectors (n := n) (m := m) r) = 0 := by
    simp [hcut]
  rw [hzero] at hres
  exact sub_eq_zero.mp hres

end

end ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual
