import ArchonPhysics.SelfAdjointQuasimodeSpectrum
import ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual

/-!
# Vector-local periodic block embedding

This file applies the finite-dimensional quasimode theorem to the actual
periodic weighted cycle.  Unlike an operator-norm perturbation argument, the
hypothesis controls only the boundary matrix acting on one candidate mode.
Consequently an order-one physical boundary is allowed whenever the chosen
mode has a small boundary tail.
-/

open scoped Matrix

namespace ArchonPhysics.PeriodicWeightedCycleQuasimodeEmbedding

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual
open ArchonPhysics.PeriodicWeightedCycleMismatchPerturbation
open ArchonPhysics.SelfAdjointQuasimodeSpectrum

noncomputable section

/-- Matrix form of the abstract quasimode theorem, stated using the ordered
Hermitian spectrum used throughout the harmonic-chain development. -/
theorem exists_orderedEigenvalue_abs_sub_le_of_unit_quasimode
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota) (v : EuclideanSpace Real iota)
    {lambda epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hv : ‖v‖ = 1)
    (hresidual :
      ‖Matrix.toEuclideanLin A.1 v - lambda • v‖ ≤ epsilon) :
    ∃ k : Fin (Fintype.card iota),
      |orderedEigenvalue A k - lambda| ≤ epsilon := by
  let T : EuclideanSpace Real iota →ₗ[Real] EuclideanSpace Real iota :=
    Matrix.toEuclideanLin A.1
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2
  have h := exists_eigenvalue_abs_sub_le_of_unit_quasimode
    T hT (Fintype.card iota) finrank_euclideanSpace
    v hepsilon hv hresidual
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀, T, hT] using h

/-- Exact action form of the four-boundary gluing identity. -/
theorem splitFinWeightedCycle_action_eq_block_add_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real)
    (v : EuclideanSpace Real (Fin n ⊕ Fin m)) :
    Matrix.toEuclideanLin (splitFinWeightedCycleHermitian w).1 v =
      Matrix.toEuclideanLin (periodicBlockDiagonalHermitian w).1 v +
        Matrix.toEuclideanLin (periodicBoundaryMatrix w) v := by
  have hmatrix := (sub_eq_iff_eq_add').mp
    (splitFinWeightedCycle_sub_periodicBlockDiagonal_eq_boundary w)
  rw [hmatrix]
  have hmap := map_add
    (Matrix.toEuclideanLin :
      Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real ≃ₗ[Real]
        (EuclideanSpace Real (Fin n ⊕ Fin m) →ₗ[Real]
          EuclideanSpace Real (Fin n ⊕ Fin m)))
    (periodicBlockDiagonalHermitian w).1 (periodicBoundaryMatrix w)
  exact (DFunLike.congr_fun hmap v).trans
    (LinearMap.add_apply _ _ v)

/-- A normalized exact mode of the uncoupled periodic blocks becomes a
global quasimode when only its vector-specific boundary residual is small.
The conclusion is proximity to the actual large-chain ordered spectrum; no
bound on the full boundary operator norm is assumed. -/
theorem exists_splitFinWeightedCycle_eigenvalue_near_of_boundaryTail
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real)
    (v : EuclideanSpace Real (Fin n ⊕ Fin m))
    {lambda epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hv : ‖v‖ = 1)
    (hblockMode :
      Matrix.toEuclideanLin (periodicBlockDiagonalHermitian w).1 v =
        lambda • v)
    (hboundaryTail :
      ‖Matrix.toEuclideanLin (periodicBoundaryMatrix w) v‖ ≤ epsilon) :
    ∃ k : Fin (Fintype.card (Fin n ⊕ Fin m)),
      |orderedEigenvalue (splitFinWeightedCycleHermitian w) k - lambda| ≤
        epsilon := by
  apply exists_orderedEigenvalue_abs_sub_le_of_unit_quasimode
    (splitFinWeightedCycleHermitian w) v hepsilon hv
  rw [splitFinWeightedCycle_action_eq_block_add_boundary w v, hblockMode]
  simpa only [add_sub_cancel_left] using hboundaryTail

/-- Zero-extension from the left block preserves the Euclidean norm. -/
theorem norm_leftZeroExtension
    {n m : Nat} (u : Fin n → Real) :
    ‖WithLp.toLp 2 (leftZeroExtension (m := m) u)‖ =
      ‖WithLp.toLp 2 u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [leftZeroExtension, Fintype.sum_sum_type]

/-- The norm of the physical boundary residual is controlled by the four
scalar cut-bond overlaps.  This is a vector-local estimate and contains no
operator norm of the boundary matrix. -/
theorem norm_periodicBoundary_leftZeroExtension_le_overlapSum
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (u : Fin n → Real) :
    ‖WithLp.toLp 2
        (periodicBoundaryMatrix w *ᵥ leftZeroExtension (m := m) u)‖ ≤
      ∑ r : Fin 4,
        |boundaryCoefficients (n := n) (m := m) w r *
            (boundaryVectors (n := n) (m := m) r ⬝ᵥ
              leftZeroExtension (m := m) u)| *
          ‖WithLp.toLp 2
            (boundaryVectors (n := n) (m := m) r)‖ := by
  rw [periodicBoundaryMatrix_mulVec_eq_overlapSum]
  change
    ‖∑ r : Fin 4,
        (boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ
            leftZeroExtension (m := m) u)) •
          WithLp.toLp 2 (boundaryVectors (n := n) (m := m) r)‖ ≤ _
  calc
    _ ≤ ∑ r : Fin 4,
        ‖(boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ
            leftZeroExtension (m := m) u)) •
          WithLp.toLp 2 (boundaryVectors (n := n) (m := m) r)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [norm_smul, Real.norm_eq_abs]

/-- Honest local-to-global spectral consumer.  A normalized exact eigenvector
of the left periodic block gives an eigenvalue of the actual coupled periodic
chain within `epsilon` whenever its four weighted cut-bond overlaps have the
displayed total size at most `epsilon`. -/
theorem exists_splitFinWeightedCycle_eigenvalue_near_of_leftEigenvectorOverlaps
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (u : Fin n → Real)
    {lambda epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hunit : ‖WithLp.toLp 2 u‖ = 1)
    (hleftEigenvector :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ u = lambda • u)
    (hoverlapTail :
      ∑ r : Fin 4,
        |boundaryCoefficients (n := n) (m := m) w r *
            (boundaryVectors (n := n) (m := m) r ⬝ᵥ
              leftZeroExtension (m := m) u)| *
          ‖WithLp.toLp 2
            (boundaryVectors (n := n) (m := m) r)‖ ≤ epsilon) :
    ∃ k : Fin (Fintype.card (Fin n ⊕ Fin m)),
      |orderedEigenvalue (splitFinWeightedCycleHermitian w) k - lambda| ≤
        epsilon := by
  let v : EuclideanSpace Real (Fin n ⊕ Fin m) :=
    WithLp.toLp 2 (leftZeroExtension (m := m) u)
  apply exists_splitFinWeightedCycle_eigenvalue_near_of_boundaryTail
    w v hepsilon
  · simpa [v] using (norm_leftZeroExtension (m := m) u).trans hunit
  · have hblock := periodicBlockDiagonal_mulVec_leftEigenvector
      w u lambda hleftEigenvector
    change WithLp.toLp 2
        ((periodicBlockDiagonalHermitian w).1 *ᵥ
          leftZeroExtension (m := m) u) =
      lambda • WithLp.toLp 2 (leftZeroExtension (m := m) u)
    exact congrArg (WithLp.toLp 2) hblock
  · simpa [v, Matrix.toLpLin_apply] using
      (norm_periodicBoundary_leftZeroExtension_le_overlapSum w u).trans
        hoverlapTail

/-- The full-cycle wrap overlap of a left-supported eight-site vector is its
negative first coordinate. -/
theorem boundaryOverlap_eight_zero
    {m : Nat} [NeZero m] [NeZero (8 + m)] (u : Fin 8 → Real) :
    boundaryVectors (n := 8) (m := m) 0 ⬝ᵥ
      leftZeroExtension (m := m) u = -u 0 := by
  have hm : 0 < m := NeZero.pos m
  have hone : (1 : ZMod (8 + m)).val = 1 := by
    simpa using ZMod.val_natCast_of_lt (n := 8 + m) (a := 1) (by omega)
  have hfalse (a : Fin 8) :
      (siteEquivFin (8 + m)).symm (Fin.castAdd m (0 : Fin 8)) ≠
        (siteEquivFin (8 + m)).symm (Fin.castAdd m a) + 1 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [val_siteEquivFin_symm, ZMod.val_add, hone] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  simp [boundaryVectors, splitFullEdgeVector, finCycleEdgeVector,
    cycleMassPerturbationVector, differenceMatrix, dotProduct,
    leftZeroExtension, finSumFinEquiv, hfalse]

/-- The other full-cycle cross-block overlap is the last coordinate of the
left eight-site vector. -/
theorem boundaryOverlap_eight_one
    {m : Nat} [NeZero m] [NeZero (8 + m)] (u : Fin 8 → Real) :
    boundaryVectors (n := 8) (m := m) 1 ⬝ᵥ
      leftZeroExtension (m := m) u = u (Fin.last 7) := by
  have hj : Fin.natAdd 8 (0 : Fin m) ≠ (0 : Fin (8 + m)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hcross (a : Fin 8) :
      Fin.natAdd 8 (0 : Fin m) ≠ Fin.castAdd m a := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hlast (a : Fin 8) : a.val = 7 ↔ a = Fin.last 7 := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      subst a
      rfl
  simp [boundaryVectors, splitFullEdgeVector, dotProduct,
    leftZeroExtension, finSumFinEquiv,
    finCycleEdgeVector_apply_of_ne_zero _ _ hj, hcross, hlast]

/-- The removed left-block wrap overlap is the last-minus-first endpoint
difference. -/
theorem boundaryOverlap_eight_two
    {m : Nat} [NeZero m] [NeZero (8 + m)] (u : Fin 8 → Real) :
    boundaryVectors (n := 8) (m := m) 2 ⬝ᵥ
      leftZeroExtension (m := m) u = u (Fin.last 7) - u 0 := by
  have hwrap (a : Fin 8) :
      (siteEquivFin 8).symm (0 : Fin 8) =
        (siteEquivFin 8).symm a + 1 ↔ a = Fin.last 7 := by
    fin_cases a <;> decide
  simp [boundaryVectors, leftBlockEdgeVector, finCycleEdgeVector,
    cycleMassPerturbationVector, differenceMatrix, dotProduct,
    leftZeroExtension, hwrap, sub_mul, Finset.sum_sub_distrib]

/-- The right-block wrap vector is orthogonal to every left-supported
vector. -/
theorem boundaryOverlap_eight_three
    {m : Nat} [NeZero m] [NeZero (8 + m)] (u : Fin 8 → Real) :
    boundaryVectors (n := 8) (m := m) 3 ⬝ᵥ
      leftZeroExtension (m := m) u = 0 := by
  simp [boundaryVectors, rightBlockEdgeVector, dotProduct,
    leftZeroExtension]

/-- Endpoint-amplitude form of the honest eight-site local-to-global bridge.
The localization input now consists only of the first coordinate, the last
coordinate, and their difference; all three coefficients and bond-vector
norms are displayed explicitly. -/
theorem exists_splitFinWeightedCycle_eigenvalue_near_of_eightEndpointTail
    {m : Nat} [NeZero m] [NeZero (8 + m)]
    (w : Fin (8 + m) → Real) (u : Fin 8 → Real)
    {lambda epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hunit : ‖WithLp.toLp 2 u‖ = 1)
    (hleftEigenvector :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ u = lambda • u)
    (hendpointTail :
      |boundaryCoefficients (n := 8) (m := m) w 0| * |u 0| *
          ‖WithLp.toLp 2 (boundaryVectors (n := 8) (m := m) 0)‖ +
        |boundaryCoefficients (n := 8) (m := m) w 1| *
            |u (Fin.last 7)| *
          ‖WithLp.toLp 2 (boundaryVectors (n := 8) (m := m) 1)‖ +
        |boundaryCoefficients (n := 8) (m := m) w 2| *
            |u (Fin.last 7) - u 0| *
          ‖WithLp.toLp 2 (boundaryVectors (n := 8) (m := m) 2)‖ ≤ epsilon) :
    ∃ k : Fin (Fintype.card (Fin 8 ⊕ Fin m)),
      |orderedEigenvalue (splitFinWeightedCycleHermitian w) k - lambda| ≤
        epsilon := by
  apply
    exists_splitFinWeightedCycle_eigenvalue_near_of_leftEigenvectorOverlaps
      w u hepsilon hunit hleftEigenvector
  simpa [Fin.sum_univ_four, boundaryOverlap_eight_zero,
    boundaryOverlap_eight_one, boundaryOverlap_eight_two,
    boundaryOverlap_eight_three, abs_mul, add_assoc] using hendpointTail

end

end ArchonPhysics.PeriodicWeightedCycleQuasimodeEmbedding
