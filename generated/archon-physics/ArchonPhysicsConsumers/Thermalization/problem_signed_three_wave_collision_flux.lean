import ArchonPhysics.SignedThreeWaveCollisionFlux

/-!
# Consumer: signed three-wave collision flux

The endpoints expose the algebra that the all-distinct gain/return-tree
reindex will use.  The standard decay sector is retained as a specialization,
while the other input-sign sectors remain explicit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

theorem problem_signedThreeWaveCollisionFlux_decaySector
    (nObserved nZero nOne : Real) :
    signedThreeWaveCollisionFlux (fun _ ↦ .minus)
        nObserved nZero nOne =
      collisionFlux nObserved nZero nOne :=
  signedThreeWaveCollisionFlux_minus_minus nObserved nZero nOne

theorem problem_quadraticSignedCollisionFlux_phasePhase
    {N : Nat} [NeZero N] (term : QuadraticPhaseTerm N)
    (action : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hzero : binaryPhaseSign term.2.1 = .phase)
    (hone : binaryPhaseSign term.2.2 = .phase) :
    quadraticSignedCollisionFlux term action observed =
      collisionFlux (action observed)
        (action (term.1 0)) (action (term.1 1)) :=
  quadraticSignedCollisionFlux_eq_collisionFlux_of_phase_phase
    term action observed hzero hone

#print axioms problem_signedThreeWaveCollisionFlux_decaySector
#print axioms problem_quadraticSignedCollisionFlux_phasePhase

end

end ArchonPhysicsConsumers.Thermalization
