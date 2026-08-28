import ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic

/-!
# Consumer: canonical q-level quadratic representation

This consumer checks the constructed quadratic representation of the main
q-level flux and of the exact q-level closure with cross-orbit coherence kept
separate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQLevelQuadratic

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      qLevelResolvedSecondOrderSignedFluxMain m kappa time
        (extendPositiveEnergyProfile m energy) observed) :=
  isPositiveEnergyQuadratic_qLevelResolvedSecondOrderSignedFluxMain
    m kappa time observed

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      qLevelResolvedSecondOrderSignedFluxMain m kappa time
          (extendPositiveEnergyProfile m energy) observed +
        allEqualOrbitGainSum m kappa time
          (extendPositiveEnergyProfile m energy) observed +
        repeatedAwayFixedPointCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
        observedChildPlacementCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
        allEqualChannelFiveCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
        secondOrderCounterrotatingRemainder m kappa time
          (extendPositiveEnergyProfile m energy) observed) :=
  isPositiveEnergyQuadratic_qLevelClosureWithoutCross m kappa time observed

#print axioms isPositiveEnergyQuadratic_qLevelResolvedSecondOrderSignedFluxMain
#print axioms isPositiveEnergyQuadratic_qLevelClosureWithoutCross

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQLevelQuadratic
