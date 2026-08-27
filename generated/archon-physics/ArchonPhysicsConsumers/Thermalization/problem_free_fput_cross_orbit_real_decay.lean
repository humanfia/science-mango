import ArchonPhysics.FreeFPUTCrossOrbitRealDecay

/-!
# Consumer gate: real cross-orbit inverse-time decay
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitRealDecay
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

theorem problem_abs_re_crossOrbitCoherentRemainder_le_inverseTime
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (hfrequency : 0 < frequency observed) (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        coupling m observed radius‖ *
        (4 / (frequency observed ^ 2 * time)) :=
  abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
    coupling m observed radius frequency hfrequency htime

#print axioms
  problem_abs_re_crossOrbitCoherentRemainder_le_inverseTime

end

end ArchonPhysicsConsumers.Thermalization
