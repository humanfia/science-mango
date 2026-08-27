import ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge

/-!
# Consumer gate: exact all-distinct representative A1 split
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeA1Bridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

theorem problem_freeQuadraticFullSameChargePairSum_eq_admissible_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    freeQuadraticFullSameChargePairSum
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m) time =
      (allDistinctRepresentativeA1GainSum
          m kappa time energy observed : Complex) +
        nonAdmissibleQuadraticRepresentativeGainRemainder
          m kappa time energy observed +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time :=
  freeQuadraticFullSameChargePairSum_eq_admissible_add_remainders
    m kappa time energy observed hEnergy

#print axioms
  problem_freeQuadraticFullSameChargePairSum_eq_admissible_add_remainders

end

end ArchonPhysicsConsumers.Thermalization
