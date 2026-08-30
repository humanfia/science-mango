import ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall

/-!
# Consumer: arbitrary-garden compact-atlas small denominators

This consumer checks the fixed arbitrary-order bridge at its honest boundary.
An order-two ordered history already contains the cumulative denominator
`deltaOne + deltaTwo`, so only coordinates separately identified with an A1
mismatch may use the A1 certificate constructor.  Every other ordinary garden
coordinate requires its own scalar one-site compact-atlas certificate.

The ordinary finite union uses no independence.  Identically-zero,
resonant-connected, and recollision coordinates remain in the retained event.
To turn the displayed full-event estimate into high-order decoherence one
still needs both a certificate family for all ordinary cumulative denominators
and a vanishing retained-sector bound.  Nothing here supplies initial-phase
independence, re-Haar, high-order RPA, Markov closure, or annealed multi-site
uniformity.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set

noncomputable section

/-- Consumer audit: complete order-two IBP bookkeeping is already more than
two independent copies of a local A1 mismatch. -/
theorem problem_orderTwoGarden_has_cumulative_denominator
    (deltaOne deltaTwo : Real) :
    orderedHistoryDenominators [deltaOne, deltaTwo] =
      [deltaOne, deltaTwo, deltaOne + deltaTwo] := by
  exact orderedHistoryDenominators_two_eq_local_and_cumulative
    deltaOne deltaTwo

/-- Consumer form of the finite ordinary-sector estimate with individually
displayed compact-atlas data and one union of compact bad fibers. -/
theorem problem_fixedOrderOrdinaryGarden_compactAtlas_unionBound
    (capacity : Nat) (coordinate : Fin capacity → Real → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (certificate : ∀ i : GardenSectorIndex capacity sector
        .ordinaryNonresonant,
      OrdinaryGardenCoordinateCompactAtlas (coordinate i.1))
    (gamma : Real) :
    massCoordinateLaw
        (gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma) ≤
      ordinaryGardenCompactAtlasRegularCoefficient
          capacity coordinate sector certificate *
            ENNReal.ofReal (2 * gamma) +
        massCoordinateLaw
          (ordinaryGardenCompactAtlasBadEvent
            capacity coordinate sector certificate) := by
  exact measure_ordinaryGardenSmallEvent_le_compactAtlas
    capacity coordinate sector certificate gamma

/-- Consumer form of the exact arbitrary-garden ordinary/retained event
partition.  No retained sector is silently included in the small-ball sum. -/
theorem problem_randomBranchingGarden_exact_ordinary_retained_partition
    (trees : List BinaryInteractionTree)
    (assignment : Real → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real) (hdefault : gamma ≤ |defaultValue|)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector) :
    {second | ∃ delta ∈
        branchingGardenDenominators trees (assignment second),
          |delta| < gamma} =
      gardenSectorSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector .ordinaryNonresonant gamma ∪
        gardenRetainedSmallDenominatorEvent
          (branchingGardenDenominatorCapacity trees)
          (randomBranchingGardenDenominatorCoordinate
            trees assignment defaultValue)
          sector gamma := by
  exact randomBranchingGardenSmallEvent_eq_ordinary_union_retained
    trees assignment defaultValue gamma hdefault sector

#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.orderedHistoryDenominators_two_eq_local_and_cumulative
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.measure_coordinateCompactAtlasGoodNear_le
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.measure_ordinaryGardenSmallEvent_le_compactAtlas
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.measure_randomBranchingGardenOrdinarySmallEvent_le_compactAtlas
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.randomBranchingGardenSmallEvent_eq_ordinary_union_retained
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.measure_randomBranchingGardenSmallEvent_le_compactAtlas_add_retained
#print axioms
  ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall.measure_randomBranchingGardenSmallEvent_le_of_compactAtlas_of_retained
#print axioms problem_orderTwoGarden_has_cumulative_denominator
#print axioms problem_fixedOrderOrdinaryGarden_compactAtlas_unionBound
#print axioms
  problem_randomBranchingGarden_exact_ordinary_retained_partition

end

end ArchonPhysicsConsumers.Thermalization
