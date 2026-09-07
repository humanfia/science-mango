import ArchonPhysics.FullThermalization
import ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1

/-!
# Unconditional no-go for the frozen full thermalization certificate

The conditional full thermalization theorem turns every
`FullThermalizationCertificate` into `HighProbabilityG2Bounds` for the
canonical frozen hitting time.  The actual-Hamiltonian supervolume theorem
rules out any such bounds at the current `g^(-2)` clock.  Their direct
composition therefore proves that the certificate type is empty.

This module adds no persistence, kinetic, approximation, or
conclusion-shaped premise.
-/

namespace ArchonPhysics.R32FrozenFullCertificateNoGoV1

open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad] [Nonempty Mode]

/-- No full thermalization certificate can inhabit the frozen current-clock
interface.  The required bounds on `mu` and `delta` are read from the
certificate itself, so this literal emptiness theorem exposes no redundant
hypotheses. -/
theorem not_nonempty_fullThermalizationCertificate
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode → Real}
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real}
    (sizeCutoff : Real → Nat) :
    ¬ Nonempty (FullThermalizationCertificate model actionZero
      kappa beta hbeta mu delta sizeCutoff) := by
  rintro ⟨certificate⟩
  have hbounds := fullNonzeroModeThermalizationLaw certificate
  exact
    (_root_.ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1.not_exists_frozen_root_highProbabilityG2Bounds
        hbeta certificate.kinetic.mu_nonnegative
        certificate.kinetic.mu_less_one
        certificate.threshold_below_frozen_initial)
      ⟨sizeCutoff, certificate.kinetic.lower,
        certificate.kinetic.upper, hbounds⟩

#print axioms not_nonempty_fullThermalizationCertificate

end

end ArchonPhysics.R32FrozenFullCertificateNoGoV1
