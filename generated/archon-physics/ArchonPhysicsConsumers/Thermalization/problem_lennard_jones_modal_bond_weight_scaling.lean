import ArchonPhysics.LennardJonesModalBondWeightScaling

/-!
# Consumer: finite-volume scaling of the LJ modal bond weight
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesModalBondWeightScaling

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.LennardJonesModalRemainderKineticBound
open ArchonPhysics.LennardJonesModalBondWeightScaling

noncomputable section

theorem fiveSite_modalBondL1Weight_le
    (m : Lattice.PositiveMassConfig 5) (k : Lattice.Site 5) :
    modalBondL1Weight m k <= Real.sqrt 5 * modeFrequency m k := by
  simpa using modalBondL1Weight_le_sqrt_card_mul_frequency m k

theorem fiveSite_modalBondL1Weight_sq_le
    (m : Lattice.PositiveMassConfig 5) (k : Lattice.Site 5) :
    modalBondL1Weight m k ^ 2 <= 5 * modeFrequencySq m k := by
  simpa using modalBondL1Weight_sq_le_card_mul_frequencySq m k

#print axioms fiveSite_modalBondL1Weight_le
#print axioms fiveSite_modalBondL1Weight_sq_le

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesModalBondWeightScaling
