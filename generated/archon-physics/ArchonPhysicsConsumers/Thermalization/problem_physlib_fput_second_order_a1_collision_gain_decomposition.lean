import ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition

/-!
# Consumer: exact second-order A1 collision gain

This endpoint exposes the coherent A1 broadening sum as the positive
cardinality-correct finite-time collision-kernel sum plus the exact
cross-orbit coherent remainder.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

theorem problem_physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_cross
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    (∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (physlibQuadraticFirstPicardStaticFiberCoefficient m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed charge) :
              Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch
              (modeFrequency m observed) charge (modeFrequency m)) time :
                Complex)) =
      (∑ representative ∈
          positiveQuadraticSwapOrbitRepresentatives N m observed,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          ((finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign representative) time
              (quadraticCollisionModes observed representative) *
            ∏ r : Fin 2,
              modeAction energy (modeFrequency m)
                (representative.1 r) : Real) : Complex)) +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time :=
  physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_cross
    m kappa time observed energy henergy

#print axioms
  problem_physlibQuadraticFirstPicardBroadeningSum_eq_kernelSum_add_cross

end

end ArchonPhysicsConsumers.Thermalization
