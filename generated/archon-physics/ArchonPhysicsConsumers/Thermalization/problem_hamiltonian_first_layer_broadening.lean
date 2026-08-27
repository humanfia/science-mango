import ArchonPhysics.HamiltonianFirstLayerBroadening

/-!
# Consumer: Hamiltonian first-layer Duhamel broadening

This consumer exposes the exact finite-mode bridge from the quadratic FPUT
Hamiltonian source to the signed-mismatch squared-sinc kernel.  It does not
assume a kinetic equation and makes no kinetic-limit or random-phase
propagation claim.
-/

namespace ArchonPhysicsConsumers.Thermalization.HamiltonianFirstLayerBroadening

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HamiltonianFirstLayerBroadening
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- Consumer endpoint: one physical finite FPUT Hamiltonian Duhamel term has
exactly the finite-time broadened resonance weight at its true modal
mismatch. -/
theorem problem_physicalQuadraticFirstLayer_exact_broadening
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real)
    {time : Real} (htime : 0 < time)
    (phase : UnitAddTorus (Lattice.Site N))
    (term : QuadraticPhaseTerm N) :
    Complex.normSq
          (physicalQuadraticFirstLayerTerm
            kappa g m observed radius time phase term) /
        time =
      Complex.normSq
          (freeQuadraticDuhamelCoefficient
            (physicalQuadraticCoupling kappa g m observed)
            m observed radius term) *
        finiteTimeResonanceWeight
          (quadraticPhaseMismatch (modeFrequency m) observed term) time := by
  exact normSq_physicalQuadraticFirstLayerTerm_div_time_eq
    kappa g m observed radius htime phase term

#print axioms problem_physicalQuadraticFirstLayer_exact_broadening

end

end ArchonPhysicsConsumers.Thermalization.HamiltonianFirstLayerBroadening
