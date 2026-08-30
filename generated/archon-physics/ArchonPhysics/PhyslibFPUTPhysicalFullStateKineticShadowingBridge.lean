import ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily

/-!
# Physical full-state FPUT data imply kinetic-time moment shadowing

This module is the direct adapter from the physical blockwise family to the
existing full-state kinetic shadowing theorem.  Every block in the source
family carries an actual Physlib Hamiltonian trajectory, and its
Hamiltonian-to-second-Picard endpoint error is derived rather than assumed.

The remaining nonlinear-RPA input is displayed literally in the final theorem
as `hstateDelta_cubic`: the initial full state of every restarted block must
be coupled to a fresh canonical reference state at cubic order.  This bridge
does not assert that estimate or derive it from the Hamiltonian flow; it proves
that no further residual or recurrence hypothesis is needed once it is given.
-/

namespace ArchonPhysics.PhyslibFPUTPhysicalFullStateKineticShadowingBridge

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily

noncomputable section

/-- A blockwise family of genuine Physlib Hamiltonian trajectories, equipped
with the displayed cubic initial-state RPA coupling, shadows the kinetic
Euler trajectory on every bounded kinetic-time window.

No block residual, final-endpoint coupling, or multiblock recurrence is an
extra hypothesis of this theorem: all three are derived by the imported
physical/full-state chain. -/
theorem physicalHamiltonian_fullState_kineticEuler_shadowing_tendsto_zero
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : PositiveMassConfig N} {mUpper kappa beta H T : Real}
    {observed : Site N}
    {g : Nat -> Real} {E V : Nat -> Nat -> Real} {Q : Real -> Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTPhysicalFullStateBlockwiseMomentFamily
      (Omega := Omega) (X := X) mu M m mUpper kappa beta H T observed
        g E Q Cref Cstate Cpicard Ainitial Aflow)
    (hstateDelta_cubic : forall n j,
      (family.physicalBlock n j).stateDelta <= Cstate * |g n| ^ 3)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 <= L)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (K : Nat -> Nat) (tau : Real)
    (hQ : forall x y, |Q x - Q y| <= L * |x - y|)
    (hkinetic : forall n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hkineticBudget : forall n,
      (g n ^ 2 * T) * (K n : Real) <= tau)
    (hinitial : Tendsto (fun n => |E n 0 - V n 0|)
      atTop (nhds 0)) :
    Tendsto (fun n => |E n (K n) - V n (K n)|)
      atTop (nhds 0) := by
  let fullStateFamily :=
    { family.toFullStateBlockwiseMomentFamily with
      stateDelta_cubic := hstateDelta_cubic }
  exact fullStateFamily
    |>.actual_fullState_kineticEuler_shadowing_tendsto_zero
      hT homega L hL hg hg0 V K tau hQ hkinetic hkineticBudget hinitial

end

end ArchonPhysics.PhyslibFPUTPhysicalFullStateKineticShadowingBridge
