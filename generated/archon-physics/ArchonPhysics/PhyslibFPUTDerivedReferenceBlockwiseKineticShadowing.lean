import ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
import ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

/-!
# Canonical Haar blocks derive blockwise FPUT kinetic shadowing

This module closes the interface between the canonical finite-character Haar
reference block and blockwise re-Haarized kinetic shadowing.  The new
certificate contains no reference-residual field and no actual-residual
field.  For every block it records only

* an energy profile defining a fresh canonical Haar reference law,
* cubic endpoint coupling of the actual moment to that reference block,
* compatibility of the chosen collision field with the finite-time Haar
  broadening, and
* one uniform finite-character coefficient bound.

The reference residual is derived from the exact two-step Haar expansion.  It
is then transferred to the actual endpoints by the existing coupling theorem,
and the resulting cubic defect is accumulated over kinetic time by the
existing shadowing theorem.

Thus the remaining transparent input is endpoint re-Haarization coupling (and
collision-field compatibility) with a uniform finite-character bound; a
kinetic residual is no longer among the assumptions.
-/

namespace ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing

open Filter
open Topology
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTBlockwiseReHaarizedKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
open FPUTBlockwiseReHaarizedMomentCertificate

noncomputable section

/-! ## Canonical reference endpoints -/

/-- Initial endpoint of the fresh canonical Haar block with energy profile
`energy`. -/
def canonicalHaarBlockInitial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real)
    (observed : Lattice.Site N) : Real :=
  physlibReferenceInitialHaarMoment m
    (phaseEnergyRadius energy (modeFrequency m)) observed

/-- Final endpoint of the canonical two-step Picard Haar reference block. -/
def canonicalHaarBlockFinal
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (energy : Lattice.Site N → Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  physlibReferenceTwoStepHaarMoment m kappa beta g
    (phaseEnergyRadius energy (modeFrequency m)) T observed

/-! ## Residual-free physical certificate -/

/-- A coherent actual moment chain together with independently re-Haarized
canonical reference blocks.

Neither the actual nor the reference kinetic residual is a field.  The
unit-coupling window and the last field turn the exact reference defect into
the single uniform envelope `Cref * |g n|^3`. -/
structure FPUTCanonicalHaarBlockwiseMomentCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real)
    (observed : Lattice.Site N)
    (g : Nat → Real) (E : Nat → Nat → Real) (Q : Real → Real)
    (Cref Ccoupling : Real) where
  energy : Nat → Nat → Lattice.Site N → Real
  couplingWindow : ∀ n, |g n| ≤ 1
  initial_endpoint_control : ∀ n j,
    |E n j - canonicalHaarBlockInitial m (energy n j) observed| ≤
      Ccoupling * |g n| ^ 3
  final_endpoint_control : ∀ n j,
    |E n (j + 1) -
        canonicalHaarBlockFinal m kappa beta (g n) (energy n j) T observed| ≤
      Ccoupling * |g n| ^ 3
  collision_compatibility : ∀ n j,
    Q (canonicalHaarBlockInitial m (energy n j) observed) =
      normalizedSecondOrderHaarBroadening
        m kappa beta (energy n j) observed T
  finiteCharacterEnvelope : ∀ n j,
    physlibHaarEnergyDriftC3 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed +
        physlibHaarEnergyDriftC4 m kappa beta
          (phaseEnergyRadius (energy n j) (modeFrequency m)) T observed ≤
      Cref

namespace FPUTCanonicalHaarBlockwiseMomentCertificate

variable {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {observed : Lattice.Site N}
  {g : Nat → Real} {E : Nat → Nat → Real} {Q : Real → Real}
  {Cref Ccoupling : Real}

/-- The uniform reference constant is automatically nonnegative because it
majorizes nonnegative finite-character coefficient masses. -/
theorem Cref_nonneg
    (certificate : FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref Ccoupling) :
    0 ≤ Cref := by
  have h3 := physlibHaarEnergyDriftC3_nonneg m kappa beta
    (phaseEnergyRadius (certificate.energy 0 0) (modeFrequency m)) T observed
  have h4 := physlibHaarEnergyDriftC4_nonneg m kappa beta
    (phaseEnergyRadius (certificate.energy 0 0) (modeFrequency m)) T observed
  exact (add_nonneg h3 h4).trans (certificate.finiteCharacterEnvelope 0 0)

/-- The exact finite-character calculation supplies the reference residual,
and the certificate's uniform coefficient bound enlarges it to
`Cref * |g n|^3`. -/
theorem canonical_reference_is_momentKineticEulerResidual
    (certificate : FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref Ccoupling)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed)
    (n j : Nat) :
    MomentKineticEulerResidual
      (canonicalHaarBlockInitial m (certificate.energy n j) observed)
      (canonicalHaarBlockFinal m kappa beta (g n)
        (certificate.energy n j) T observed)
      (g n ^ 2 * T)
      (Q (canonicalHaarBlockInitial m (certificate.energy n j) observed))
      (Cref * |g n| ^ 3) := by
  have href := physlibReferenceBlock_is_momentKineticEulerResidual
    m kappa beta (g n) (certificate.energy n j) observed hT homega
  have hfixed :=
    physlibReferenceBlockKineticDefect_le_abs_cube_mul_fixedEnvelope
      m kappa beta
      (phaseEnergyRadius (certificate.energy n j) (modeFrequency m))
      T observed (certificate.couplingWindow n)
  have henvelope :
      |g n| ^ 3 *
          (physlibHaarEnergyDriftC3 m kappa beta
              (phaseEnergyRadius (certificate.energy n j) (modeFrequency m))
              T observed +
            physlibHaarEnergyDriftC4 m kappa beta
              (phaseEnergyRadius (certificate.energy n j) (modeFrequency m))
              T observed) ≤
        |g n| ^ 3 * Cref :=
    mul_le_mul_of_nonneg_left (certificate.finiteCharacterEnvelope n j)
      (pow_nonneg (abs_nonneg _) _)
  unfold MomentKineticEulerResidual at href ⊢
  rw [certificate.collision_compatibility n j]
  exact href.trans (hfixed.trans (by simpa [mul_comm] using henvelope))

/-- Forgetting the physical definitions yields the abstract blockwise
re-Haarized certificate.  Its `reference_residual` component is a theorem,
not data supplied by the caller. -/
def toBlockwiseReHaarizedMomentCertificate
    (certificate : FPUTCanonicalHaarBlockwiseMomentCertificate
      m kappa beta T observed g E Q Cref Ccoupling)
    (hT : 0 < T) (homega : 0 < modeFrequency m observed) :
    FPUTBlockwiseReHaarizedMomentCertificate
      g T E Q Cref Ccoupling where
  referenceInitial n j :=
    canonicalHaarBlockInitial m (certificate.energy n j) observed
  referenceFinal n j :=
    canonicalHaarBlockFinal m kappa beta (g n)
      (certificate.energy n j) T observed
  reference_residual n j :=
    certificate.canonical_reference_is_momentKineticEulerResidual
      hT homega n j
  initial_endpoint_control := certificate.initial_endpoint_control
  final_endpoint_control := certificate.final_endpoint_control

/-! ## Kinetic-time consequence -/

/-- Kinetic-time shadowing derived from canonical Haar reference blocks.

There is no residual hypothesis in this theorem.  What remains is the
quantitative endpoint re-Haarization coupling, compatibility of `Q` with the
finite-time collision field, and a uniform finite-character envelope, all
displayed in `FPUTCanonicalHaarBlockwiseMomentCertificate`. -/
theorem actual_canonicalHaarBlockwise_kineticEuler_shadowing_tendsto_zero
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
      atTop (nhds 0) := by
  exact
    actual_blockwiseReHaarized_kineticEuler_shadowing_tendsto_zero
        (certificate.toBlockwiseReHaarizedMomentCertificate hT homega)
        hT certificate.Cref_nonneg hCcoupling L hL hg hg0 V K tau
        hQ hkinetic hkineticBudget hinitial

end FPUTCanonicalHaarBlockwiseMomentCertificate

end

end ArchonPhysics.PhyslibFPUTDerivedReferenceBlockwiseKineticShadowing
