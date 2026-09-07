import ArchonPhysics

/-!
# Consumer: frozen full thermalization certificate no-go

This consumer checks that the unconditional certificate obstruction is
available through the public `ArchonPhysics` barrel.
-/

namespace ArchonPhysicsConsumers.Thermalization.R32FrozenFullCertificateNoGo

open ArchonPhysics
open ArchonPhysics.ConditionalFiniteThreeWaveKineticFamily
open ArchonPhysics.R32FrozenFullCertificateNoGoV1

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad] [Nonempty Mode]

theorem problem_r32_frozen_full_certificate_no_go
    {model : FiniteCollisionModel Mode Triad}
    {actionZero : Mode → Real}
    {kappa beta : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {mu delta : Real}
    (sizeCutoff : Real → Nat) :
    ¬ Nonempty (FullThermalizationCertificate model actionZero
      kappa beta hbeta mu delta sizeCutoff) :=
  not_nonempty_fullThermalizationCertificate sizeCutoff

#print axioms problem_r32_frozen_full_certificate_no_go

end

end ArchonPhysicsConsumers.Thermalization.R32FrozenFullCertificateNoGo
