import ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory

/-!
Named consumer for the fully nonresonant arbitrary-order oscillatory-history
majorant and its fixed-root FPUT Catalan-tail handoff.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology

noncomputable section

theorem free_FPUT_regular_ordered_resolvent_consumer
    {gamma : Real} (hgamma : 0 < gamma)
    {phases : List Real}
    (hregular : FullyNonresonantOrderedHistory gamma phases)
    (time : Real) :
    ‖linearOrderedOscillatoryIntegral phases time‖ <=
      (2 / gamma) ^ phases.length :=
  norm_linearOrderedOscillatoryIntegral_le_resolvent
    hgamma hregular time

theorem free_FPUT_regular_ordered_history_tail_consumer
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : regularOrderedHistoryAnalyticRatio rho gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) R‖ <=
        A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) R‖)
      atTop (nhds 0) :=
  fixedRootOrderedOscillatoryHistory_tail_certificate
    N rootMomentum amplitude phaseHistory hA hrho hgamma hq0 hq1
      hratio hlength hregular hamplitude time

theorem free_FPUT_regular_realized_Physlib_tail_consumer
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A gamma q : Real} (hA : 0 <= A)
    (hleafA : bound.leafBound <= A)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : regularOrderedHistoryAnalyticRatio
        (bound.leafBound * bound.branchBound) gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) r‖ <= A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) R‖ <= A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) R‖) atTop (nhds 0) :=
  fixedRootRealizedKernelOrderedOscillatoryHistory_tail_certificate
    bound N rootMomentum realize horder phaseHistory hA hleafA
      hgamma hq0 hq1 hratio hlength hregular time

#print axioms free_FPUT_regular_ordered_resolvent_consumer
#print axioms free_FPUT_regular_ordered_history_tail_consumer
#print axioms free_FPUT_regular_realized_Physlib_tail_consumer

end

end ArchonPhysicsConsumers.Thermalization
