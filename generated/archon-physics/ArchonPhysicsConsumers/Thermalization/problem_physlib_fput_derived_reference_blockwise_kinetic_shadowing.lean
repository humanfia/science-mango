import ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

/-!
# Consumer: canonical Haar blocks close the reference-residual interface

This gate verifies that the physical blockwise certificate contains no
kinetic-residual field.  Canonical Haar endpoints and their exact
finite-character expansion construct the abstract re-Haarized certificate,
which in turn yields kinetic-time shadowing of the actual moment chain.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

open Filter
open Topology
open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing

noncomputable section

#check canonicalHaarBlockInitial
#check canonicalHaarBlockFinal
#check FPUTCanonicalHaarBlockwiseMomentCertificate
#check FPUTCanonicalHaarBlockwiseMomentCertificate.energy
#check FPUTCanonicalHaarBlockwiseMomentCertificate.initial_endpoint_control
#check FPUTCanonicalHaarBlockwiseMomentCertificate.final_endpoint_control
#check FPUTCanonicalHaarBlockwiseMomentCertificate.collision_compatibility
#check FPUTCanonicalHaarBlockwiseMomentCertificate.finiteCharacterEnvelope
#check FPUTCanonicalHaarBlockwiseMomentCertificate.Cref_nonneg
#check FPUTCanonicalHaarBlockwiseMomentCertificate.canonical_reference_is_momentKineticEulerResidual
#check FPUTCanonicalHaarBlockwiseMomentCertificate.toBlockwiseReHaarizedMomentCertificate
#check FPUTCanonicalHaarBlockwiseMomentCertificate.actual_canonicalHaarBlockwise_kineticEuler_shadowing_tendsto_zero

/-- Consumer-facing closure: once canonical Haar blocks are cubically coupled
to actual endpoints, their derived reference residual gives bounded
kinetic-time shadowing.  No actual or reference residual is supplied. -/
theorem canonical_Haar_blocks_derive_kinetic_time_shadowing_contract
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {observed : Lattice.Site N}
    {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
    {Cref Ccoupling : Real}
    (certificate : FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref Ccoupling)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (hCcoupling : 0 ≤ Ccoupling)
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
  certificate.actual_canonicalHaarBlockwise_kineticEuler_shadowing_tendsto_zero
    hT homega hCcoupling L hL hg hg0 V K tau hQ hkinetic
      hkineticBudget hinitial

#print axioms FPUTCanonicalHaarBlockwiseMomentCertificate.Cref_nonneg
#print axioms FPUTCanonicalHaarBlockwiseMomentCertificate.canonical_reference_is_momentKineticEulerResidual
#print axioms FPUTCanonicalHaarBlockwiseMomentCertificate.toBlockwiseReHaarizedMomentCertificate
#print axioms FPUTCanonicalHaarBlockwiseMomentCertificate.actual_canonicalHaarBlockwise_kineticEuler_shadowing_tendsto_zero
#print axioms canonical_Haar_blocks_derive_kinetic_time_shadowing_contract

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
