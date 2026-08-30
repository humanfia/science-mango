import ArchonPhysics.OrderedPhaseMismatchQuantitativePerturbation
import ArchonPhysics.PeriodicWeightedCycleBlockGluing

/-!
# Ordered mismatch under the four periodic boundary updates

The periodic weighted-cycle gluing identity has four signed rank-one terms:
two full-chain cross-block bonds are added and the two smaller-cycle wrap
bonds are removed.  This file exposes that exact difference as one boundary
matrix and applies the quantitative ordered-mismatch estimate to an arbitrary
ordered triad.

This is deliberately a conditional perturbative statement.  It does not
claim that iid inverse masses make the boundary norm small, nor that the
ordered indices of an eight-site block agree with ordered indices of the
coupled large chain.
-/

namespace ArchonPhysics.PeriodicWeightedCycleMismatchPerturbation

open ArchonPhysics
open ArchonPhysics.FiniteVolumeSpectralCountGluing
open ArchonPhysics.MarkedEmpiricalResonanceTransfer
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedPhaseMismatchQuantitativePerturbation
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

/-- The uncoupled pair of periodic subcycles used as the gluing reference. -/
def periodicBlockDiagonalHermitian
    {n m : Nat} [NeZero n] [NeZero m]
    (w : Fin (n + m) -> Real) : HermitianMatrix (Fin n ⊕ Fin m) :=
  blockDiagonalHermitian
    (finWeightedCycleHermitian (leftWeights w))
    (finWeightedCycleHermitian (rightWeights w))

/-- The exact four-term boundary matrix: add the two cross-block bonds and
remove the two subcycle wrap bonds. -/
def periodicBoundaryMatrix
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) -> Real) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) Real :=
  rankOneUpdateSum (Finset.univ : Finset (Fin 4))
    (boundaryCoefficients w) boundaryVectors

/-- Subtracting the uncoupled reference from the actual split periodic chain
gives exactly the four signed boundary updates. -/
theorem splitFinWeightedCycle_sub_periodicBlockDiagonal_eq_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) -> Real) :
    (splitFinWeightedCycleHermitian w).1 -
        (periodicBlockDiagonalHermitian w).1 =
      periodicBoundaryMatrix w := by
  have h := congrArg Subtype.val
    (splitFinWeightedCycleHermitian_eq_rankOneUpdated_blockDiagonal w)
  change (splitFinWeightedCycleHermitian w).1 =
    (rankOneUpdatedHermitian (periodicBlockDiagonalHermitian w)
      (Finset.univ : Finset (Fin 4))
      (boundaryCoefficients w) boundaryVectors).1 at h
  rw [h]
  ext i j
  simp [periodicBoundaryMatrix, rankOneUpdatedHermitian]

/-- Explicit stability bound for every fixed ordered triad across the actual
four-boundary periodic gluing perturbation. -/
theorem abs_orderedTriadMismatch_split_sub_block_le_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) -> Real)
    (sign : Fin 3 -> InteractionSign)
    (modes : Fin 3 -> Fin (Fintype.card (Fin n ⊕ Fin m))) :
    |orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes -
        orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| <=
      3 * Real.sqrt
        ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin n ⊕ Fin m))
          (periodicBoundaryMatrix w)‖ := by
  have h :=
    abs_orderedPhaseMismatch_sub_le_card_mul_sqrt_clmNorm
      (splitFinWeightedCycleHermitian w)
      (periodicBlockDiagonalHermitian w) sign modes
  rw [splitFinWeightedCycle_sub_periodicBlockDiagonal_eq_boundary] at h
  norm_num at h ⊢
  exact h

/-- If the exact boundary operator has norm below `(margin/3)^2`, then the
ordered triad mismatch moves by less than `margin`. -/
theorem abs_orderedTriadMismatch_split_sub_block_lt_of_boundaryNorm
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) -> Real)
    (sign : Fin 3 -> InteractionSign)
    (modes : Fin 3 -> Fin (Fintype.card (Fin n ⊕ Fin m)))
    {margin : Real} (hmargin : 0 < margin)
    (hboundary :
      ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin n ⊕ Fin m))
          (periodicBoundaryMatrix w)‖ < (margin / 3) ^ 2) :
    |orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes -
        orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| <
      margin := by
  have h := abs_orderedPhaseMismatch_sub_lt_of_clmNorm_lt_sq
    (n := 3) (by norm_num)
    (splitFinWeightedCycleHermitian w)
    (periodicBlockDiagonalHermitian w) sign modes hmargin
  apply h
  rw [splitFinWeightedCycle_sub_periodicBlockDiagonal_eq_boundary]
  norm_num
  exact hboundary

/-- Consumer form: a block-diagonal near resonance with tolerance `epsilon`
remains a near resonance with tolerance `epsilon + margin` after the actual
periodic boundary update. -/
theorem abs_orderedTriadMismatch_split_lt_of_block_and_boundary
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) -> Real)
    (sign : Fin 3 -> InteractionSign)
    (modes : Fin 3 -> Fin (Fintype.card (Fin n ⊕ Fin m)))
    {epsilon margin : Real}
    (hblock :
      |orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| <
        epsilon)
    (hmargin : 0 < margin)
    (hboundary :
      ‖(Matrix.toEuclideanCLM (𝕜 := Real) (n := Fin n ⊕ Fin m))
          (periodicBoundaryMatrix w)‖ < (margin / 3) ^ 2) :
    |orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes| <
      epsilon + margin := by
  have hmove :=
    abs_orderedTriadMismatch_split_sub_block_lt_of_boundaryNorm
      w sign modes hmargin hboundary
  calc
    |orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes| =
        |(orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes -
            orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes) +
          orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| := by
      congr 1
      ring
    _ <=
        |orderedPhaseMismatch (splitFinWeightedCycleHermitian w) sign modes -
            orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| +
          |orderedPhaseMismatch (periodicBlockDiagonalHermitian w) sign modes| :=
      abs_add_le _ _
    _ < margin + epsilon := add_lt_add hmove hblock
    _ = epsilon + margin := by ring

end

end ArchonPhysics.PeriodicWeightedCycleMismatchPerturbation
