import ArchonPhysics.ActualFourSitePositiveProjectorWitness
import ArchonPhysics.PeriodicWeightedCycleBlockGluing

/-!
# Zero-cut truth audit for periodic weighted-cycle specialization

Inverse-mass coordinates are algebraic edge weights, so setting selected
coordinates to zero is a legal polynomial specialization.  This module
records exactly what that operation does to a periodic weighted cycle.

Zeroing the two cross-block edge weights makes the large matrix block
diagonal.  However, those same coordinates are the wrap weights of the two
smaller cycle presentations, so both resulting blocks have a zero wrap
weight: they are broken cycles (paths), not smaller all-positive periodic
cycles.  In particular, this operation does not embed the existing positive
four-site periodic witness into a larger volume.
-/

namespace ArchonPhysics.PeriodicWeightedCycleZeroCutAudit

open ArchonPhysics
open ArchonPhysics.ActualFourSitePositiveProjectorWitness
open ArchonPhysics.ActualThreeMassLiftedJacobianPolynomial
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

/-- The exact zero-cut specialization is block diagonal. -/
theorem splitFinWeightedCycleLaplacian_eq_fromBlocks_of_cutWeights_eq_zero
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real)
    (hleft : w (Fin.castAdd m (0 : Fin n)) = 0)
    (hright : w (Fin.natAdd n (0 : Fin m)) = 0) :
    splitFinWeightedCycleLaplacian w =
      Matrix.fromBlocks (finWeightedCycleLaplacian (leftWeights w)) 0 0
        (finWeightedCycleLaplacian (rightWeights w)) := by
  rw [splitFinWeightedCycleLaplacian_eq_fromBlocks_add_four_boundary]
  simp [leftWeights, rightWeights, hleft, hright]

/-- The two zero cut coordinates are simultaneously the two smaller blocks'
wrap weights. -/
theorem zeroCut_blocks_have_zero_wrapWeights
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real)
    (hleft : w (Fin.castAdd m (0 : Fin n)) = 0)
    (hright : w (Fin.natAdd n (0 : Fin m)) = 0) :
    leftWeights w (0 : Fin n) = 0 ∧
      rightWeights w (0 : Fin m) = 0 := by
  exact ⟨hleft, hright⟩

/-- Consequently a zero-cut left four-site block cannot equal the existing
all-positive periodic N=4 witness weights.  This rules out the tempting
direct N=4-to-general-N embedding, but says nothing against a separate path
witness or a nonzero small-boundary perturbation. -/
theorem leftBlock_zeroCut_ne_actualFourSiteWitnessInverseWeights
    {m : Nat} [NeZero m] [NeZero (4 + m)]
    (w : Fin (4 + m) → Real)
    (hleft : w (Fin.castAdd m (0 : Fin 4)) = 0) :
    leftWeights w ≠ fourSiteInverseWeights actualFourSiteWitnessTriple := by
  intro heq
  have hcoordinate := congrFun heq (0 : Fin 4)
  have hone : fourSiteInverseWeights actualFourSiteWitnessTriple (0 : Fin 4) =
      1 := by
    norm_num [fourSiteInverseWeights, actualFourSiteWitnessTriple]
  rw [leftWeights, hleft, hone] at hcoordinate
  norm_num at hcoordinate

end

end ArchonPhysics.PeriodicWeightedCycleZeroCutAudit
