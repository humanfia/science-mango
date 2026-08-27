import ArchonPhysics.PhyslibFPUTFirstPicardDecomposition

/-!
# Exact quadratic expansion of the Physlib modal-history defect

At a fixed observed mode, the order-two distinguished tensor contraction is
expanded exactly around the freely rotating reference history.  The defect is
the actual modal history minus that reference.  The resulting history
difference is the sum of the two base--defect cross terms and the purely
quadratic defect term.

This is finite-volume deterministic algebra.  It uses no smallness, random
phase, kinetic, or limiting assumption.
-/

namespace ArchonPhysics.QuadraticTensorHistoryExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModeCoupling
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- The two terms of the quadratic tensor contraction containing exactly one
factor from `base` and one factor from `defect`. -/
def quadraticTensorCrossContraction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : WeightedConfiguration N) : Real :=
  ∑ modes : Fin 2 → Lattice.Site N,
    interactionTensor m 3 (Fin.cons observed modes) *
      (base (modes 0) * defect (modes 1) +
        defect (modes 0) * base (modes 1))

/-- Polarization identity for the order-two distinguished tensor contraction.
The cross term retains both ordered placements of the defect. -/
theorem distinguishedTensorContraction_add_sub_eq_cross_add_defect
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (base defect : WeightedConfiguration N) :
    distinguishedTensorContraction m (base + defect) observed 2 -
        distinguishedTensorContraction m base observed 2 =
      quadraticTensorCrossContraction m observed base defect +
        distinguishedTensorContraction m defect observed 2 := by
  classical
  unfold distinguishedTensorContraction quadraticTensorCrossContraction
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro modes hmodes
  simp only [Fin.prod_univ_two, WithLp.ofLp_add, Pi.add_apply]
  ring

/-- The actual modal history used by the Physlib quadratic force. -/
def physlibActualModalHistory {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N) (time : Real) :
    WeightedConfiguration N :=
  modalCoordinates m
    (massWeightedPosition m (realReparametrize q) time)

/-- Difference between the actual modal history and the freely rotating
reference configuration at the same time. -/
def physlibModalHistoryDefect {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    WeightedConfiguration N :=
  physlibActualModalHistory m q time -
    freeWeightedConfiguration radius (modeFrequency m) time phase

/-- The actual modal history is exactly the free history plus its defect. -/
theorem physlibActualModalHistory_eq_free_add_defect
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Time → HilbertConfiguration N)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real) :
    physlibActualModalHistory m q time =
      freeWeightedConfiguration radius (modeFrequency m) time phase +
        physlibModalHistoryDefect m q radius phase time := by
  unfold physlibModalHistoryDefect
  abel

/-- Exact linear-plus-quadratic split of the tensor-history difference.  The
first term is linear in the modal-history defect and the second is quadratic
in that defect. -/
theorem physlibQuadraticTensorHistoryDifference_eq_cross_add_defect
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
  unfold physlibQuadraticTensorHistoryDifference
  change distinguishedTensorContraction m
        (physlibActualModalHistory m q time) observed 2 -
      distinguishedTensorContraction m
        (freeWeightedConfiguration radius (modeFrequency m) time phase)
        observed 2 = _
  rw [physlibActualModalHistory_eq_free_add_defect]
  exact distinguishedTensorContraction_add_sub_eq_cross_add_defect
    m observed
      (freeWeightedConfiguration radius (modeFrequency m) time phase)
      (physlibModalHistoryDefect m q radius phase time)

/-- The rotated physical history source inherits the same exact split after
applying its output phase and force coupling. -/
theorem physlibQuadraticHistoryDifference_eq_cross_add_defect
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
  rw [physlibQuadraticHistoryDifference_eq_tensorDifference,
    physlibQuadraticTensorHistoryDifference_eq_cross_add_defect]
  unfold forcedModeSource
  push_cast
  ring

end

end ArchonPhysics.QuadraticTensorHistoryExpansion
