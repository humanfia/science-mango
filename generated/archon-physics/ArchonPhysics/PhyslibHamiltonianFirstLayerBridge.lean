import ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
import ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition

/-!
# Bridge from the true Physlib trajectory to the physical first layer

`PhyslibFPUTFirstPicardDecomposition` derives an exact decomposition of a
true nonlinear Hamiltonian trajectory using the coupling obtained directly
from `forcedModeSource`.  The collision modules use the equivalent
energy-normalized `physicalQuadraticCoupling`.  This module proves those two
couplings equal and rewrites the true trajectory decomposition with the
first layer defined literally as the integrated free Hamiltonian force.

Consequently, the first term isolated from the true microscopic Duhamel
formula is exactly the term whose Haar second moment is decomposed into the
coherent charge fibers and finite-time collision weights.  The quadratic
history defect and cubic force integral remain explicit; no claim that they
are small is made here.
-/

namespace ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.HamiltonianFirstLayerBroadening
open ArchonPhysics.HamiltonianFirstLayerCollisionDecomposition
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- The coupling read directly from the forced Physlib modal equation is
the same complex number as the normalized coupling used in the collision
weight calculation. -/
theorem physlibQuadraticCoupling_eq_physicalQuadraticCoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N) :
    physlibQuadraticCoupling m kappa g observed =
      physicalQuadraticCoupling kappa g m observed := by
  unfold physlibQuadraticCoupling forcedModeSource
    physicalQuadraticCoupling modeAmplitudeNormalization
  push_cast
  ring

/-- The freely evaluated source used in the true-trajectory split is
pointwise identical to the source defined directly from the Hamiltonian
force. -/
theorem physlibFreeQuadraticRotatedSource_eq_hamiltonianSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibFreeQuadraticRotatedSource
        m kappa g observed radius phase time =
      freeQuadraticHamiltonianRotatedSource
        kappa g m observed radius time phase := by
  rw [freeQuadraticHamiltonianRotatedSource_eq_picardIntegrand]
  unfold physlibFreeQuadraticRotatedSource
  rw [physlibQuadraticCoupling_eq_physicalQuadraticCoupling]

/-- The free first-Picard correction appearing in the exact true-trajectory
split is the physical first layer defined as the integrated Hamiltonian
force. -/
theorem physlibFreeQuadraticCorrection_eq_hamiltonianFirstLayer
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    freeQuadraticInteractionPictureCorrection
        (physlibQuadraticCoupling m kappa g observed)
        m observed radius (modeFrequency m) time phase =
      physicalFreeQuadraticHamiltonianFirstLayer
        kappa g m observed radius time phase := by
  rw [physlibQuadraticCoupling_eq_physicalQuadraticCoupling]
  exact (physicalFreeQuadraticHamiltonianFirstLayer_eq_correction
    kappa g m observed radius time phase).symm

/-- Exact true-trajectory Duhamel formula with its first term written as the
physical Hamiltonian first layer used by the collision decomposition.  Both
nonlinear history terms remain exact and explicit. -/
theorem interactionPicture_physlibMode_eq_initial_add_hamiltonianFirstLayer_add_remainders
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
  rw [interactionPicture_physlibMode_eq_initial_add_firstPicard_add_remainders
    m kappa beta g observed p q hp hq hHamilton homega radius phase time,
    physlibFreeQuadraticCorrection_eq_hamiltonianFirstLayer]

end

end ArchonPhysics.PhyslibHamiltonianFirstLayerBridge
