import ArchonPhysics.PhyslibFPUTIteratedA2HaarEnergyCouplingScaling

namespace ArchonPhysicsConsumers

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.PhyslibFPUTIteratedA2HaarEnergyCouplingScaling

noncomputable section

example
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real) :
    completeA2IteratedIteratedRemainder
        m kappa radius observed time =
      kappa ^ 4 *
        completeA2IteratedIteratedRemainder
          m 1 radius observed time := by
  exact completeA2IteratedIteratedRemainder_eq_coupling_four_mul_unit
    m kappa radius observed time

end

end ArchonPhysicsConsumers
