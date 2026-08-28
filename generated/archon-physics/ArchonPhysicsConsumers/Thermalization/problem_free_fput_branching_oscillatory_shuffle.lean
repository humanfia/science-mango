import ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle

/-!
Named consumer for arbitrary Chen shuffles, exact branching binary-tree
linearization, and the full-branching fixed-root Catalan tail certificate.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology

noncomputable section

theorem free_FPUT_arbitrary_order_shuffle_consumer
    (left right : List Real) (time : Real) :
    linearOrderedOscillatoryIntegral left time *
        linearOrderedOscillatoryIntegral right time =
      orderedOscillatoryIntegralFamilySum
        (orderedPhaseShuffles left right) time :=
  linearOrderedOscillatoryIntegral_mul_eq_shuffleSum left right time

theorem free_FPUT_full_branching_linearization_and_bound_consumer
    {gamma : Real} (hgamma : 0 < gamma)
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    (hregular : FullyNonresonantBranchingHistory gamma tree assignment)
    (time : Real) :
    branchingOscillatoryDuhamelIntegral tree assignment time =
        orderedOscillatoryIntegralFamilySum
          (branchingPhaseLinearExtensions tree assignment) time ∧
      ‖branchingOscillatoryDuhamelIntegral tree assignment time‖ <=
        ((branchingPhaseLinearExtensions tree assignment).length : Real) *
          (2 / gamma) ^ tree.order := by
  exact ⟨branchingOscillatoryDuhamelIntegral_eq_linearExtensionSum
      tree assignment time,
    norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
      hgamma tree assignment hregular time⟩

theorem free_FPUT_full_branching_fixed_root_tail_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseAssignment :
      (r : Nat) ->
        (history : FixedRootRawHistoryIndex N r rootMomentum) ->
          BinaryInteractionTreePhaseAssignment history.1.1)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : 2 * rho / gamma <= q / (16 * (N : Real)))
    (hamplitudeWeighted : forall r history,
      ‖amplitude r history‖ *
          ((branchingPhaseLinearExtensions history.1.1
            (phaseAssignment r history)).length : Real) <=
        A * rho ^ r)
    (hregular : forall r history,
      FullyNonresonantBranchingHistory gamma history.1.1
        (phaseAssignment r history))
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖ <=
        A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootBranchingOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseAssignment time) R‖)
      atTop (nhds 0) :=
  fixedRootBranchingOscillatoryHistory_tail_certificate
    N rootMomentum amplitude phaseAssignment hA hrho hgamma hq0 hq1
      hratio hamplitudeWeighted hregular time

#print axioms free_FPUT_arbitrary_order_shuffle_consumer
#print axioms free_FPUT_full_branching_linearization_and_bound_consumer
#print axioms free_FPUT_full_branching_fixed_root_tail_consumer

end

end ArchonPhysicsConsumers.Thermalization
