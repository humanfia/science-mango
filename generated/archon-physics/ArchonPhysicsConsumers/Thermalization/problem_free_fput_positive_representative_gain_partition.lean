import ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition

/-!
# Consumer gate: positive representative gain partition
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

noncomputable section

theorem problem_positiveRepresentativeA1GainSum_eq_allDistinct_add_nonAllDistinct
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed,
      ((quadraticSwapOrbit q).card : Real) ^ 2 *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (q.1 r)) =
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed :=
  positiveRepresentativeA1GainSum_eq_allDistinct_add_nonAllDistinct
    m kappa time energy observed

#print axioms
  problem_positiveRepresentativeA1GainSum_eq_allDistinct_add_nonAllDistinct

end

end ArchonPhysicsConsumers.Thermalization
