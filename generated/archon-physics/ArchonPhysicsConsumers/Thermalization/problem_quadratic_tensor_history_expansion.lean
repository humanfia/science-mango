import ArchonPhysics.QuadraticTensorHistoryExpansion

/-!
# Consumer: exact quadratic modal-history expansion

This consumer exposes the deterministic finite-volume polarization identity
for the actual-minus-free Physlib modal history.  It assumes neither defect
smallness nor a kinetic closure.
-/

namespace ArchonPhysicsConsumers.Thermalization.QuadraticTensorHistoryExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Consumer endpoint at the real tensor level: the exact history difference
is its base--defect cross contraction plus its defect-square contraction. -/
theorem problem_physlibQuadraticTensorHistoryDifference_exact_split
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticTensorHistoryDifference
        m observed q radius phase time =
      quadraticTensorCrossContraction m observed
          (freeWeightedConfiguration radius (modeFrequency m) time phase)
          (physlibModalHistoryDefect m q radius phase time) +
        distinguishedTensorContraction m
          (physlibModalHistoryDefect m q radius phase time) observed 2 := by
  exact physlibQuadraticTensorHistoryDifference_eq_cross_add_defect
    m observed q radius phase time

/-- Consumer endpoint after the physical force normalization and interaction-
picture output rotation. -/
theorem problem_physlibQuadraticHistoryDifference_exact_split
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibQuadraticHistoryDifference
        m kappa g observed q radius phase time =
      phaseFactor (modeFrequency m observed * time) *
          forcedModeSource (modeFrequency m observed)
            (-(kappa * g * quadraticTensorCrossContraction m observed
              (freeWeightedConfiguration radius (modeFrequency m) time phase)
              (physlibModalHistoryDefect m q radius phase time))) +
        phaseFactor (modeFrequency m observed * time) *
          forcedModeSource (modeFrequency m observed)
            (-(kappa * g * distinguishedTensorContraction m
              (physlibModalHistoryDefect m q radius phase time) observed 2)) := by
  exact physlibQuadraticHistoryDifference_eq_cross_add_defect
    m kappa g observed q radius phase time

#print axioms problem_physlibQuadraticTensorHistoryDifference_exact_split
#print axioms problem_physlibQuadraticHistoryDifference_exact_split

end

end ArchonPhysicsConsumers.Thermalization.QuadraticTensorHistoryExpansion
