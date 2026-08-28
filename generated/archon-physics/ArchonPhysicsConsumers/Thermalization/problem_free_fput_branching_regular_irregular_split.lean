import ArchonPhysics.FreeFPUTBranchingRegularIrregularSplit

/-!
Named consumers for the exact regular/irregular branching-history split.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTBranchingRegularIrregularSplit
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-- Every fixed-root perturbative order is exactly its regular contribution
plus the still-uncontrolled near-resonant/recollision contribution. -/
theorem free_FPUT_branching_regular_irregular_exact_split_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r : Nat) :
    fixedRootRawHistoryOrderSum N rootMomentum coefficient r =
      fixedRootRegularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r +
        fixedRootIrregularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r :=
  fixedRootRawHistoryOrderSum_eq_regular_add_irregular
    N rootMomentum phaseAssignment gamma coefficient r

/-- Once the regular orders have a geometric bound, a finite perturbative
tail is reduced to the explicit irregular sum plus the regular envelope. -/
theorem free_FPUT_branching_irregular_blocker_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    {A q : Real} (hA : 0 <= A) (hq0 : 0 <= q) (hq1 : q < 1)
    (hregular : forall r,
      ‖fixedRootRegularBranchingOrderSum
          N rootMomentum phaseAssignment gamma coefficient r‖ <=
        A * q ^ r)
    (R S : Nat) :
    ‖fixedRootBranchingFiniteTail N rootMomentum coefficient R S‖ <=
      ‖fixedRootIrregularBranchingFiniteTail
          N rootMomentum phaseAssignment gamma coefficient R S‖ +
        A * q ^ R / (1 - q) :=
  norm_fixedRootBranchingFiniteTail_le_irregular_add_geometric
    N rootMomentum phaseAssignment gamma coefficient
      hA hq0 hq1 hregular R S

/-- A future deterministic count or probability estimate enters only through
the explicit bad-history cardinality premise. -/
theorem free_FPUT_branching_bad_count_interface_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    (gamma : Real)
    (coefficient :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (r badCount : Nat) {B : Real} (hB : 0 <= B)
    (hbadCount :
      (fixedRootIrregularBranchingHistories
        N rootMomentum phaseAssignment gamma r).card <= badCount)
    (hcoefficient : forall history,
      history ∈ fixedRootIrregularBranchingHistories
          N rootMomentum phaseAssignment gamma r ->
        ‖coefficient r history‖ <= B) :
    ‖fixedRootIrregularBranchingOrderSum
        N rootMomentum phaseAssignment gamma coefficient r‖ <=
      (badCount : Real) * B :=
  norm_fixedRootIrregularBranchingOrderSum_le_count_budget
    N rootMomentum phaseAssignment gamma coefficient r badCount
      hB hbadCount hcoefficient

#print axioms free_FPUT_branching_regular_irregular_exact_split_consumer
#print axioms free_FPUT_branching_irregular_blocker_consumer
#print axioms free_FPUT_branching_bad_count_interface_consumer
#print axioms norm_fixedRootRegularBranchingOrderSum_le_factorial
#print axioms fixedRootRegularBranching_tail_certificate

end

end ArchonPhysicsConsumers.Thermalization
