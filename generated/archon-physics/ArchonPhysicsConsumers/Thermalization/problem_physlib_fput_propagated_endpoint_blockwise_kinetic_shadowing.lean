import ArchonPhysics.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing

/-!
# Consumer: propagated re-Haarization closes the final endpoint interface

This gate verifies the full composition from independently re-Haarized
initial data, through deterministic one-block propagation, to canonical-Haar
kinetic-time moment shadowing.  A final endpoint coupling and a kinetic
residual are both conclusions, not consumer assumptions.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

#check FPUTPropagatedEndpointBlockwiseMomentFamily
#check FPUTPropagatedEndpointBlockwiseMomentFamily.blockData
#check FPUTPropagatedEndpointBlockwiseMomentFamily.initialDelta_cubic
#check FPUTPropagatedEndpointBlockwiseMomentFamily.picardDelta_cubic
#check FPUTPropagatedEndpointBlockwiseMomentFamily.flowAmplification_le
#check FPUTPropagatedEndpointBlockwiseMomentFamily.actualInitialMoment
#check FPUTPropagatedEndpointBlockwiseMomentFamily.actualFinalMoment
#check FPUTPropagatedEndpointBlockwiseMomentFamily.referenceInitialMoment
#check FPUTPropagatedEndpointBlockwiseMomentFamily.referenceFinalMoment
#check FPUTPropagatedEndpointBlockwiseMomentFamily.couplingConstant
#check FPUTPropagatedEndpointBlockwiseMomentFamily.initial_endpoint_control
#check FPUTPropagatedEndpointBlockwiseMomentFamily.final_endpoint_control
#check FPUTPropagatedEndpointBlockwiseMomentFamily.toCanonicalHaarBlockwiseMomentCertificate
#check FPUTPropagatedEndpointBlockwiseMomentFamily.actual_propagatedEndpoint_kineticEuler_shadowing_uniform_bound
#check FPUTPropagatedEndpointBlockwiseMomentFamily.actual_propagatedEndpoint_kineticEuler_shadowing_tendsto_zero

/-- Consumer-facing closure.  The final scalar endpoint estimate is produced
by the propagated common-source coupling; the canonical Haar calculation
then produces the reference residual and kinetic-time conclusion. -/
theorem propagated_rehaarization_derives_kinetic_time_shadowing_contract
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cinitial Cpicard A : Real}
    (family : FPUTPropagatedEndpointBlockwiseMomentFamily
      mu M m kappa beta T observed g E Q Cref Cinitial Cpicard A)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ᶠ n in atTop, g n ≠ 0)
    (V : Nat → Nat → Real) (K : Nat → Nat) (tau : Real)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (hkinetic : ∀ n,
      IsKineticEulerTrajectory (V n) (g n ^ 2 * T) Q)
    (hkineticBudget : ∀ n,
      (g n ^ 2 * T) * (K n : Real) ≤ tau)
    (hinitial : Tendsto (fun n ↦ |E n 0 - V n 0|)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ |E n (K n) - V n (K n)|)
      atTop (nhds 0) :=
  family.actual_propagatedEndpoint_kineticEuler_shadowing_tendsto_zero
    hT homega L hL hg hg0 V K tau hQ hkinetic hkineticBudget hinitial

#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.couplingConstant_nonneg
#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.initial_endpoint_control
#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.final_endpoint_control
#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.toCanonicalHaarBlockwiseMomentCertificate
#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.actual_propagatedEndpoint_kineticEuler_shadowing_uniform_bound
#print axioms FPUTPropagatedEndpointBlockwiseMomentFamily.actual_propagatedEndpoint_kineticEuler_shadowing_tendsto_zero
#print axioms propagated_rehaarization_derives_kinetic_time_shadowing_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTPropagatedEndpointBlockwiseKineticShadowing
