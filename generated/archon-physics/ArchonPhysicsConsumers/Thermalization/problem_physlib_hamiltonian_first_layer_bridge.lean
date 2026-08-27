import ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

/-!
# Consumer: true Physlib trajectory to the physical Hamiltonian first layer

The exact microscopic trajectory is decomposed into its initial amplitude,
the physical free Hamiltonian first layer, the quadratic history defect, and
the actual cubic-force integral.  The last two terms remain explicit.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonianFirstLayerBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HamiltonianFirstLayerBroadening
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

noncomputable section

/-- Consumer endpoint joining the true Hamiltonian trajectory to the exact
first layer used by the collision decomposition. -/
theorem problem_truePhyslibTrajectory_eq_hamiltonianFirstLayer_add_remainders
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (observed : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m observed)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    phaseRenormalize (modeFrequency m observed * time)
        (physlibModeAmplitude m observed p q time) =
      physlibModeAmplitude m observed p q 0 +
        physicalFreeQuadraticHamiltonianFirstLayer
          kappa g m observed radius time phase +
        (∫ s in (0 : Real)..time,
          physlibQuadraticHistoryDifference
            m kappa g observed q radius phase s) +
        (∫ s in (0 : Real)..time,
          physlibCubicRotatedSource m beta g observed q s) := by
  exact
    interactionPicture_physlibMode_eq_initial_add_hamiltonianFirstLayer_add_remainders
      m kappa beta g observed p q hp hq hHamilton homega radius phase time

/-- Consumer endpoint for the exact norm of the nonlinear quadratic-history
source that remains after isolating the physical first Picard layer. -/
theorem problem_quadraticHistorySource_exact_norm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    ‖physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time‖ =
      |kappa * g * physlibQuadraticTensorHistoryDifference
        m observed q radius phase time| /
        Real.sqrt (2 * modeFrequency m observed) := by
  exact norm_physlibQuadraticHistoryDifference
    m kappa g observed q radius phase time

#print axioms problem_truePhyslibTrajectory_eq_hamiltonianFirstLayer_add_remainders
#print axioms problem_quadraticHistorySource_exact_norm

end

end ArchonPhysicsConsumers.Thermalization.PhyslibHamiltonianFirstLayerBridge
