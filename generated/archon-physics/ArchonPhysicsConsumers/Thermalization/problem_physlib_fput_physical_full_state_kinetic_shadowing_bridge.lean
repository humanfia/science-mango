import ArchonPhysics.PhyslibFPUTPhysicalFullStateKineticShadowingBridge

/-!
# Consumer: physical full-state FPUT kinetic shadowing bridge

This gate checks the direct theorem from physical Hamiltonian block families
to kinetic-time moment shadowing.  The nonlinear-RPA restart estimate remains
the explicit `stateDelta_cubic` field of the supplied physical family.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateKineticShadowingBridge

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTPhysicalFullStateBlockwiseFamily
open ArchonPhysics.PhyslibFPUTPhysicalFullStateKineticShadowingBridge

noncomputable section

#check physicalHamiltonian_fullState_kineticEuler_shadowing_tendsto_zero

/-- Consumer-level restatement of the physical Hamiltonian-to-kinetic
shadowing bridge. -/
theorem physical_family_shadows_kinetic_time
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
      atTop (nhds 0) :=
  physicalHamiltonian_fullState_kineticEuler_shadowing_tendsto_zero
    family hstateDelta_cubic hT homega L hL hg hg0 K tau hQ hkinetic
      hkineticBudget hinitial

#print axioms physicalHamiltonian_fullState_kineticEuler_shadowing_tendsto_zero
#print axioms physical_family_shadows_kinetic_time

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPhysicalFullStateKineticShadowingBridge
