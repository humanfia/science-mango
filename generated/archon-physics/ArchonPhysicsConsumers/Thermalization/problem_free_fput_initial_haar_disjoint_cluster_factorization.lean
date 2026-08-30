import ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization

/-!
# Consumer: arbitrary-order initial disjoint-cluster factorization

This consumer checks the balanced independent-cluster endpoint which is not
implied by the older total-charge-nonzero cancellation theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-- Every pair of subblocks of two disjoint base-mode clusters factorizes in
the actual iid initial ensemble, at arbitrary finite joint and tree order. -/
theorem fiveSite_actualIID_initial_disjointCluster_factorization_consumer
    {Omega I : Type*} [MeasurableSpace Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (entry : I → SignedInteractionTree (Lattice.Site 5))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcluster : Disjoint
      (indexedSignedTreeClusterModeSupport entry left)
      (indexedSignedTreeClusterModeSupport entry right))
    {leftSub rightSub : Finset I}
    (hleftSub : leftSub ⊆ left) (hrightSub : rightSub ⊆ right) :
    actualIIDInitialSignedTreeBlockMoment ensemble entry
        (leftSub ∪ rightSub) =
      actualIIDInitialSignedTreeBlockMoment ensemble entry leftSub *
        actualIIDInitialSignedTreeBlockMoment ensemble entry rightSub :=
  actualIIDInitialSignedTreeSubblockMoment_factorizes_of_disjoint_clusters
    ensemble entry hindex hcluster hleftSub hrightSub

#print axioms fiveSite_actualIID_initial_disjointCluster_factorization_consumer

end

end ArchonPhysicsConsumers.Thermalization
