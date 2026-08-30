import ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling

namespace ArchonPhysicsConsumers

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time term =
      ((kappa : Complex) ^ 2) *
        phaseRenormalizedPhysicalIteratedA2Coefficient
          m 1 radius observed time term := by
  exact
    phaseRenormalizedPhysicalIteratedA2Coefficient_eq_coupling_sq_mul_unit
      m kappa radius observed time term

end

end ArchonPhysicsConsumers
