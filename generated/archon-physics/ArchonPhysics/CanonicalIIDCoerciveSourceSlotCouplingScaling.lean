import ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation

/-!
# Coupling scaling of canonical iid source-slot defects

The continuous canonical iid source expectations retain the same exact
physical powers as the finite-ensemble hierarchy.  This file separates the
coefficients selecting the actual alpha--beta flow from the coefficient in
one displayed source insertion and pulls the latter through the Bochner
expectation and factorization defect.

No decay, independence at positive time, RPA, or kinetic limit is used.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScaling

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

theorem nonlinearPotentialDerivative_quadratic_eq_coupling_mul_unit
    (kappa g x : Real) :
    nonlinearPotentialDerivative kappa 0 g x =
      (kappa * g) * nonlinearPotentialDerivative 1 0 1 x := by
  unfold nonlinearPotentialDerivative
  ring

theorem nonlinearPotentialDerivative_quartic_eq_coupling_mul_unit
    (beta g x : Real) :
    nonlinearPotentialDerivative 0 beta g x =
      (beta * g ^ 2) * nonlinearPotentialDerivative 0 1 1 x := by
  unfold nonlinearPotentialDerivative
  ring

theorem nonlinearPotentialGradient_quadratic_eq_coupling_smul_unit
    (kappa g : Real) (q : HilbertConfiguration N) :
    nonlinearPotentialGradient kappa 0 g q =
      (kappa * g) • nonlinearPotentialGradient 1 0 1 q := by
  classical
  unfold nonlinearPotentialGradient
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [nonlinearPotentialDerivative_quadratic_eq_coupling_mul_unit,
    smul_smul]

theorem nonlinearPotentialGradient_quartic_eq_coupling_smul_unit
    (beta g : Real) (q : HilbertConfiguration N) :
    nonlinearPotentialGradient 0 beta g q =
      (beta * g ^ 2) • nonlinearPotentialGradient 0 1 1 q := by
  classical
  unfold nonlinearPotentialGradient
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [nonlinearPotentialDerivative_quartic_eq_coupling_mul_unit,
    smul_smul]

theorem transformedNonlinearForce_quadratic_eq_coupling_smul_unit
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (q : HilbertConfiguration N) :
    transformedNonlinearForce m kappa 0 g q =
      (kappa * g) • transformedNonlinearForce m 1 0 1 q := by
  unfold transformedNonlinearForce
  rw [nonlinearPotentialGradient_quadratic_eq_coupling_smul_unit,
    map_smul]
  simp

theorem transformedNonlinearForce_quartic_eq_coupling_smul_unit
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (q : HilbertConfiguration N) :
    transformedNonlinearForce m 0 beta g q =
      (beta * g ^ 2) • transformedNonlinearForce m 0 1 1 q := by
  unfold transformedNonlinearForce
  rw [nonlinearPotentialGradient_quartic_eq_coupling_smul_unit,
    map_smul]
  simp

theorem orderedSignedNonlinearForce_quadratic_eq_coupling_mul_unit
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : OrderedModeIndex N) (q : HilbertConfiguration N) :
    orderedSignedNonlinearForce m kappa 0 g mode q =
      (kappa * g) * orderedSignedNonlinearForce m 1 0 1 mode q := by
  unfold orderedSignedNonlinearForce
  rw [transformedNonlinearForce_quadratic_eq_coupling_smul_unit]
  calc
    orderedSignedCoordinate m mode
          ((kappa * g) • transformedNonlinearForce m 1 0 1 q) =
        orderedSignedCoordinateCLM m mode
          ((kappa * g) • transformedNonlinearForce m 1 0 1 q) := by
      rw [orderedSignedCoordinateCLM_apply]
    _ = (kappa * g) • orderedSignedCoordinateCLM m mode
          (transformedNonlinearForce m 1 0 1 q) := by rw [map_smul]
    _ = (kappa * g) * orderedSignedCoordinate m mode
          (transformedNonlinearForce m 1 0 1 q) := by
      rw [orderedSignedCoordinateCLM_apply]
      rfl

theorem orderedSignedNonlinearForce_quartic_eq_coupling_mul_unit
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (mode : OrderedModeIndex N) (q : HilbertConfiguration N) :
    orderedSignedNonlinearForce m 0 beta g mode q =
      (beta * g ^ 2) * orderedSignedNonlinearForce m 0 1 1 mode q := by
  unfold orderedSignedNonlinearForce
  rw [transformedNonlinearForce_quartic_eq_coupling_smul_unit]
  calc
    orderedSignedCoordinate m mode
          ((beta * g ^ 2) • transformedNonlinearForce m 0 1 1 q) =
        orderedSignedCoordinateCLM m mode
          ((beta * g ^ 2) • transformedNonlinearForce m 0 1 1 q) := by
      rw [orderedSignedCoordinateCLM_apply]
    _ = (beta * g ^ 2) • orderedSignedCoordinateCLM m mode
          (transformedNonlinearForce m 0 1 1 q) := by rw [map_smul]
    _ = (beta * g ^ 2) * orderedSignedCoordinate m mode
          (transformedNonlinearForce m 0 1 1 q) := by
      rw [orderedSignedCoordinateCLM_apply]
      rfl

theorem orderedSignedRotatedSource_quadratic_eq_coupling_mul_unit
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : OrderedModeIndex N) (q : Real -> HilbertConfiguration N)
    (time : Real) :
    orderedSignedRotatedSource m kappa 0 g mode q time =
      ((kappa * g : Real) : Complex) *
        orderedSignedRotatedSource m 1 0 1 mode q time := by
  unfold orderedSignedRotatedSource forcedModeSource
  rw [orderedSignedNonlinearForce_quadratic_eq_coupling_mul_unit]
  push_cast
  ring

theorem orderedSignedRotatedSource_quartic_eq_coupling_mul_unit
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (mode : OrderedModeIndex N) (q : Real -> HilbertConfiguration N)
    (time : Real) :
    orderedSignedRotatedSource m 0 beta g mode q time =
      ((beta * g ^ 2 : Real) : Complex) *
        orderedSignedRotatedSource m 0 1 1 mode q time := by
  unfold orderedSignedRotatedSource forcedModeSource
  rw [orderedSignedNonlinearForce_quartic_eq_coupling_mul_unit]
  push_cast
  ring

theorem canonicalSignedPotentialChannelRotatedSource_quadratic_eq_coupling_mul_unit
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a kappa g : Real) (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) :
    canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a kappa 0 g entry st =
      ((kappa * g : Real) : Complex) *
        canonicalSignedPotentialChannelRotatedSource (N := N)
          flowKappa flowBeta flowG hflowBeta a 1 0 1 entry st := by
  unfold canonicalSignedPotentialChannelRotatedSource
    canonicalOrderedPotentialChannelRotatedSource
  rw [orderedSignedRotatedSource_quadratic_eq_coupling_mul_unit]
  cases entry.1 <;> simp [phaseSignActComplex]

theorem canonicalSignedPotentialChannelRotatedSource_quartic_eq_coupling_mul_unit
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a beta g : Real) (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) :
    canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 beta g entry st =
      ((beta * g ^ 2 : Real) : Complex) *
        canonicalSignedPotentialChannelRotatedSource (N := N)
          flowKappa flowBeta flowG hflowBeta a 0 1 1 entry st := by
  unfold canonicalSignedPotentialChannelRotatedSource
    canonicalOrderedPotentialChannelRotatedSource
  rw [orderedSignedRotatedSource_quartic_eq_coupling_mul_unit]
  cases entry.1 <;> simp [phaseSignActComplex]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem canonicalPotentialSourceSlotObservable_quadratic_eq_coupling_mul_unit
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a kappa g : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a kappa 0 g
          entry block slot st =
      ((kappa * g : Real) : Complex) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 1 0 1
            entry block slot st := by
  unfold canonicalPotentialSourceSlotObservable
  rw [canonicalSignedPotentialChannelRotatedSource_quadratic_eq_coupling_mul_unit]
  ring

theorem canonicalPotentialSourceSlotObservable_quartic_eq_coupling_mul_unit
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a beta g : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a 0 beta g
          entry block slot st =
      ((beta * g ^ 2 : Real) : Complex) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a 0 1 1
            entry block slot st := by
  unfold canonicalPotentialSourceSlotObservable
  rw [canonicalSignedPotentialChannelRotatedSource_quartic_eq_coupling_mul_unit]
  ring

end


end ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScaling
