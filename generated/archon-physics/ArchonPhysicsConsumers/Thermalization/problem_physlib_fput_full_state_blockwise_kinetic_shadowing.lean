import ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing

/-!
# Consumer: full-state RPA restart closes kinetic-time shadowing

This gate checks the type-correct composition from coupled multimode states,
through Lipschitz endpoint propagation and second-Picard consistency, to the
canonical-Haar kinetic-time theorem.  A final coupling and both kinetic
residuals are derived rather than supplied by the consumer.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateBlockwiseKineticShadowing

open Filter
open Topology
open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFullStateBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter

noncomputable section

#check FPUTFullStateBlockwiseMomentFamily
#check FPUTFullStateBlockwiseMomentFamily.blockData
#check FPUTFullStateBlockwiseMomentFamily.stateDelta_cubic
#check FPUTFullStateBlockwiseMomentFamily.picardDelta_cubic
#check FPUTFullStateBlockwiseMomentFamily.initialObservableAmplification_le
#check FPUTFullStateBlockwiseMomentFamily.flowAmplification_le
#check FPUTFullStateBlockwiseMomentFamily.couplingConstant
#check FPUTFullStateBlockwiseMomentFamily.initial_endpoint_control
#check FPUTFullStateBlockwiseMomentFamily.final_endpoint_control
#check FPUTFullStateBlockwiseMomentFamily.toCanonicalHaarBlockwiseMomentCertificate
#check FPUTFullStateBlockwiseMomentFamily.explicitActualResidualDefect
#check FPUTFullStateBlockwiseMomentFamily.actualResidualDefect_eq_explicit
#check FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticEuler_shadowing_uniform_bound
#check FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticEuler_shadowing_tendsto_zero
#check physlibSecondPicard_fullState_reference_consistent
#check physlibSecondPicard_fullState_final_near_abs_cube

/-- Consumer-facing finite-block estimate with the fully expanded cubic
endpoint-transfer residual. -/
theorem full_state_rehaarization_finite_block_shadowing_contract
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (L : Real) (hL : 0 ≤ L)
    (hQ : ∀ x y, |Q x - Q y| ≤ L * |x - y|)
    (n : Nat) (V : Nat → Real)
    (hkinetic : IsKineticEulerTrajectory V (g n ^ 2 * T) Q)
    (K : Nat) :
    |E n K - V K| ≤
      (|E n 0 - V 0| +
          (K : Real) * family.explicitActualResidualDefect L n) *
        Real.exp (L * (g n ^ 2 * T) * (K : Real)) :=
  family.actual_fullState_kineticEuler_shadowing_uniform_bound
    hT homega L hL hQ n V hkinetic K

/-- Consumer-facing closure with a full-state restart certificate.  The
remaining physical input is the initial quantitative RPA coupling, standard
Lipschitz bounds, and the Hamiltonian/second-Picard realization bridge used
to discharge the consistency field of each block datum. -/
theorem full_state_rehaarization_derives_kinetic_time_shadowing_contract
    {Omega X : Type*} [MeasurableSpace Omega] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M : Real}
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Cstate Cpicard : Real} {Ainitial Aflow : NNReal}
    (family : FPUTFullStateBlockwiseMomentFamily (Omega := Omega) (X := X)
      mu M m kappa beta T observed g E Q Cref Cstate Cpicard
        Ainitial Aflow)
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
  family.actual_fullState_kineticEuler_shadowing_tendsto_zero
    hT homega L hL hg hg0 V K tau hQ hkinetic hkineticBudget hinitial

#print axioms FPUTFullStateBlockwiseMomentFamily.couplingConstant_nonneg
#print axioms FPUTFullStateBlockwiseMomentFamily.initial_endpoint_control
#print axioms FPUTFullStateBlockwiseMomentFamily.final_endpoint_control
#print axioms FPUTFullStateBlockwiseMomentFamily.toCanonicalHaarBlockwiseMomentCertificate
#print axioms FPUTFullStateBlockwiseMomentFamily.actualResidualDefect_eq_explicit
#print axioms FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticEuler_shadowing_uniform_bound
#print axioms FPUTFullStateBlockwiseMomentFamily.actual_fullState_kineticEuler_shadowing_tendsto_zero
#print axioms full_state_rehaarization_finite_block_shadowing_contract
#print axioms full_state_rehaarization_derives_kinetic_time_shadowing_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTFullStateBlockwiseKineticShadowing
