import ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
import Mathlib.Analysis.Complex.Norm

/-!
# Real-part decay of the cross-orbit coherent remainder

The exact second-order energy formula uses the real part of the complex
cross-swap-orbit remainder.  The existing zero-charge bridge controls the
complex norm by an explicit inverse-time bound.  This module transfers that
estimate directly to the real summand appearing in the physical formula.
-/

namespace ArchonPhysics.FreeFPUTCrossOrbitRealDecay

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

/-- At fixed positive output frequency, the real coherent remainder in the
second-order physical formula obeys the same explicit `O(T⁻¹)` bound as its
complex norm. -/
theorem abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (hfrequency : 0 < frequency observed) (htime : 0 < time) :
    |(freeQuadraticCrossSwapOrbitCoherentRemainder
        coupling m observed radius frequency time).re| ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        coupling m observed radius‖ *
        (4 / (frequency observed ^ 2 * time)) := by
  exact (Complex.abs_re_le_norm _).trans
    (norm_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
      coupling m observed radius frequency hfrequency htime)

end

end ArchonPhysics.FreeFPUTCrossOrbitRealDecay
