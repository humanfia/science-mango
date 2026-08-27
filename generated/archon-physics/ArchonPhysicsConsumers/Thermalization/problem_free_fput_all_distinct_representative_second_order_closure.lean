import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSecondOrderClosure

/-!
# Consumer gate: representative-level second-order closure
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSecondOrderClosure
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

theorem problem_fullA1_add_allDistinctRepresentativeFeedback_eq_signedFlux_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticFullSameChargePairSum
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time +
        (allDistinctRepresentativeConnectedFeedbackSum
          m kappa time energy observed : Complex) =
      (allDistinctRepresentativeSignedFluxSum
          m kappa time energy observed : Complex) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time :=
  fullA1_add_allDistinctRepresentativeFeedback_eq_signedFlux_add_remainders
    m kappa time energy observed hEnergy

#print axioms
  problem_fullA1_add_allDistinctRepresentativeFeedback_eq_signedFlux_add_remainders

end

end ArchonPhysicsConsumers.Thermalization
