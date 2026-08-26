import ArchonPhysics.ReducedModeTransform
import ArchonPhysics.ModalPhaseMismatch

/-!
# Forced dynamics in deterministic normal-mode coordinates

This module projects an abstract forced mass-weighted harmonic evolution onto
one selected normal mode.  The projected real coordinate and velocity obey a
scalar forced oscillator equation.  The existing
`ArchonPhysics.ForcedComplexModeDuhamel` module is the intended next
positive-frequency complex-amplitude and interaction-picture adapter, but no
theorem in this module invokes that adapter.

The configuration-space residual `G` remains supplied data.  No theorem here
identifies it with the nonlinear force of the target lattice Hamiltonian or
with a `ModeCoupling.interactionTensor` expansion.
-/

namespace ArchonPhysics.ModalForcedDynamics

open ArchonPhysics
open HarmonicModes
open ModalPhaseMismatch
open ReducedModeTransform

noncomputable section

/-- The selected normal-mode coordinate as a continuous linear functional. -/
def modalCoordinateCLM {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) :
    WeightedConfiguration N →L[Real] Real :=
  (PiLp.proj 2 (fun _ : Lattice.Site N => Real) k).comp
    (modalCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem modalCoordinateCLM_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (X : WeightedConfiguration N) :
    modalCoordinateCLM m k X = modalCoordinates m X k := by
  change modalCoordinates m X k = modalCoordinates m X k
  simp

/-- The harmonic operator is diagonal after applying the selected modal
coordinate functional. -/
theorem modalCoordinates_harmonicOperator {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (X : WeightedConfiguration N)
    (k : Lattice.Site N) :
    modalCoordinates m (harmonicOperator m X) k =
      modeFrequencySq m k * modalCoordinates m X k := by
  classical
  rw [← (normalModeBasis m).sum_repr X]
  simp only [map_sum, map_smul, harmonicOperator_eigenmode, smul_smul]
  simp [modalCoordinates, Pi.single_apply, mul_comm]

/-- A differentiable configuration path remains differentiable after taking
one normal-mode coordinate. -/
theorem hasDerivAt_modalCoordinate {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    {X V : Real → WeightedConfiguration N} {t : Real}
    (hX : HasDerivAt X (V t) t) :
    HasDerivAt (fun s ↦ modalCoordinates m (X s) k)
      (modalCoordinates m (V t) k) t := by
  simpa [Function.comp_def] using
    (modalCoordinateCLM m k).hasFDerivAt.comp_hasDerivAt t hX

/-- Projection of the abstract forced harmonic evolution gives the exact
scalar position and velocity equations for mode `k`. -/
theorem modalEquations_of_forcedDynamics {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    {X Y G : Real → WeightedConfiguration N} {t : Real}
    (hX : HasDerivAt X (Y t) t)
    (hY : HasDerivAt Y (-harmonicOperator m (X t) + G t) t) :
    HasDerivAt (fun s ↦ modalCoordinates m (X s) k)
        (modalCoordinates m (Y t) k) t ∧
      HasDerivAt (fun s ↦ modalCoordinates m (Y s) k)
        (-(modeFrequency m k) ^ 2 * modalCoordinates m (X t) k +
          modalCoordinates m (G t) k) t := by
  constructor
  · exact hasDerivAt_modalCoordinate m k hX
  · have hYmodal := hasDerivAt_modalCoordinate m k
      (X := Y) (V := fun s => -harmonicOperator m (X s) + G s) hY
    convert hYmodal using 1
    simp [modalCoordinates_harmonicOperator, modeFrequency_sq]


end

end ArchonPhysics.ModalForcedDynamics
