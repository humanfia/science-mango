import ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics

/-!
# Consumer: arbitrary fixed-order FPUT garden denominator bookkeeping

This consumer checks the complete finite-garden handoff: all cumulative
branching denominators are flattened root by root, their counts and capacity
are additive, actual `FixedRootRawHistoryIndex` entries use the same count,
and only coordinates explicitly classified as ordinary nonresonant enter the
small-ball union bound.  Identically-zero, resonant-connected, and
recollision sectors remain present and receive no false decay claim.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped ENNReal

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
open ArchonPhysics.FreeFPUTArbitraryGardenDenominatorCombinatorics
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-- Every cumulative denominator occurrence in an arbitrary finite tree
garden contributes to the exact rootwise sum. -/
theorem arbitrary_garden_exact_denominator_count_consumer
    (trees : List BinaryInteractionTree)
    (assignment : BranchingGardenPhaseAssignment trees) :
    (branchingGardenDenominators trees assignment).length =
      branchingGardenDenominatorOccurrenceCount trees assignment :=
  length_branchingGardenDenominators trees assignment

/-- The flattened garden fits in the sum of the existing per-root
factorial/exponential capacities. -/
theorem arbitrary_garden_rootwise_capacity_consumer
    (trees : List BinaryInteractionTree)
    (assignment : BranchingGardenPhaseAssignment trees) :
    (branchingGardenDenominators trees assignment).length ≤
      branchingGardenDenominatorCapacity trees :=
  length_branchingGardenDenominators_le_capacity trees assignment

/-- The actual arbitrary-order fixed-root raw-history adapter preserves the
same rootwise denominator count. -/
theorem actual_fixed_root_raw_history_garden_count_consumer
    {N : Nat} [NeZero N]
    (garden : List (FixedRootRawBranchingGardenEntry N)) :
    (fixedRootRawBranchingGardenDenominators garden).length =
      fixedRootRawBranchingGardenDenominatorCount garden :=
  length_fixedRootRawBranchingGardenDenominators garden

/-- Complete padded small events split into four retained, mutually selected
sectors; this theorem does not erase resonances or recollisions. -/
theorem complete_garden_event_retains_all_sectors_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (capacity : Nat) (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector) (gamma : Real) :
    finiteSmallDenominatorEvent coordinate gamma =
      gardenSectorSmallDenominatorEvent capacity coordinate sector
          .ordinaryNonresonant gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .identicallyZero gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .resonantConnected gamma ∪
        gardenSectorSmallDenominatorEvent capacity coordinate sector
          .recollision gamma :=
  finiteSmallDenominatorEvent_eq_sector_union
    capacity coordinate sector gamma

/-- Only ordinary coordinates require the scalar small-ball premise. -/
theorem ordinary_garden_union_bound_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (capacity : Nat)
    (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (gamma : Real) (budget : ENNReal)
    (hone : ∀ i : GardenSectorIndex capacity sector .ordinaryNonresonant,
      mu {omega | |coordinate i.1 omega| < gamma} ≤ budget) :
    mu (gardenSectorSmallDenominatorEvent capacity coordinate sector
        .ordinaryNonresonant gamma) ≤
      (capacity : ENNReal) * budget :=
  measure_ordinaryGardenSmallDenominatorEvent_le_capacity_mul
    mu capacity coordinate sector gamma budget hone

/-- A certified identically-zero retained coordinate has the whole-space
positive-gap event, illustrating why it cannot be counted as ordinary. -/
theorem retained_zero_garden_sector_is_not_small_ball_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (capacity : Nat) (coordinate : Fin capacity → Omega → Real)
    (sector : Fin capacity → GardenDenominatorSector)
    (i : Fin capacity) (hi : sector i = .identicallyZero)
    (hzero : ∀ omega, coordinate i omega = 0)
    {gamma : Real} (hgamma : 0 < gamma) :
    gardenSectorSmallDenominatorEvent capacity coordinate sector
      .identicallyZero gamma = Set.univ :=
  gardenIdenticallyZeroSectorSmallEvent_eq_univ
    capacity coordinate sector i hi hzero hgamma

/-- Fixed-shape random branching gardens inherit the ordinary-sector union
bound without any independence between roots or denominators. -/
theorem random_branching_garden_ordinary_union_bound_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (trees : List BinaryInteractionTree)
    (assignment : Omega → BranchingGardenPhaseAssignment trees)
    (defaultValue gamma : Real)
    (sector : Fin (branchingGardenDenominatorCapacity trees) →
      GardenDenominatorSector)
    (budget : ENNReal)
    (hone : ∀ i : GardenSectorIndex
        (branchingGardenDenominatorCapacity trees) sector
        .ordinaryNonresonant,
      mu {omega |
        |randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue i.1 omega| < gamma} ≤ budget) :
    mu (gardenSectorSmallDenominatorEvent
        (branchingGardenDenominatorCapacity trees)
        (randomBranchingGardenDenominatorCoordinate
          trees assignment defaultValue)
        sector .ordinaryNonresonant gamma) ≤
      (branchingGardenDenominatorCapacity trees : ENNReal) * budget :=
  measure_randomBranchingGardenOrdinarySmallEvent_le_capacity_mul
    mu trees assignment defaultValue gamma sector budget hone

#print axioms arbitrary_garden_exact_denominator_count_consumer
#print axioms arbitrary_garden_rootwise_capacity_consumer
#print axioms actual_fixed_root_raw_history_garden_count_consumer
#print axioms complete_garden_event_retains_all_sectors_consumer
#print axioms ordinary_garden_union_bound_consumer
#print axioms retained_zero_garden_sector_is_not_small_ball_consumer
#print axioms random_branching_garden_ordinary_union_bound_consumer

end

end ArchonPhysicsConsumers.Thermalization
