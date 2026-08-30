import ArchonPhysics.RandomBranchingSmallDenominatorUnion

/-! Consumer audit for the fixed-capacity random branching union bound. -/

open MeasureTheory
open ArchonPhysics.RandomBranchingSmallDenominatorUnion
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

example {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (tree : BinaryInteractionTree)
    (assignment : Omega → BinaryInteractionTreePhaseAssignment tree)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (budget : ENNReal)
    (hone : ∀ i : Fin (branchingDenominatorCapacity tree),
      mu {omega |
        |randomBranchingDenominatorCoordinate
          tree assignment defaultValue i omega| < gamma} ≤ budget) :
    mu {omega |
      ¬ FullyNonresonantBranchingHistory gamma tree (assignment omega)} ≤
      (branchingDenominatorCapacity tree : ENNReal) * budget :=
  measure_not_fullyNonresonantBranchingHistory_le_capacity_mul
    mu tree assignment defaultValue gamma hdefault budget hone

#print axioms exists_mem_small_iff_exists_paddedRandomListCoordinate_small
#print axioms measure_exists_mem_small_le_capacity_mul
#print axioms length_branchingHistoryDenominators_le_capacity
#print axioms measure_not_fullyNonresonantBranchingHistory_le_capacity_mul
