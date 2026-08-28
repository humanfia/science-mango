import ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure

/-!
# Consumer: canonical quadratic closure calculus

This consumer checks that modal-action products have explicit quadratic
representatives and that the representable class is closed under addition.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQuadraticClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

noncomputable section

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (first second : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
        modeAction (extendPositiveEnergyProfile m energy)
          (modeFrequency m) second) :=
  isPositiveEnergyQuadratic_modeActionProduct m first second

example {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N}
    {left right : PositiveEnergyProfile m → Real}
    (hleft : IsPositiveEnergyQuadratic m left)
    (hright : IsPositiveEnergyQuadratic m right) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      left energy + right energy) :=
  hleft.add hright

#check isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
#print axioms isPositiveEnergyQuadratic_modeActionProduct
#print axioms isPositiveEnergyQuadratic_quadraticSignedCollisionFlux

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTCanonicalQuadraticClosure
