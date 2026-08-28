import ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature

/-!
# Consumer endpoints for the linear-time collision quadrature

The squared-sinc resonance peak has finite total variation.  On a monotone
transverse chart this yields an `O(T/N)` Fourier-grid error and closes the
actual rooted Umklapp diagonal under the optimal deterministic window
`T_N/N → 0`.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter Topology

noncomputable section

theorem sincSquareKernel_boundedVariation_consumer :
    BoundedVariationOn
      ArchonPhysics.NormalizedResonancePeakKernel.sincSquareKernel
      (Set.univ : Set Real) :=
  boundedVariationOn_sincSquareKernel_univ

theorem monotone_collision_peak_linear_variation_consumer
    {phase : Real → Real} {s : Set Real} {T : Real} (hT : 0 < T)
    (hphase : MonotoneOn phase s) :
    eVariationOn
        (fun x ↦ normalizedFiniteTimeResonanceKernel (phase x) T) s ≤
      ENNReal.ofReal (T / (2 * Real.pi) * sincSquareTotalVariation) :=
  eVariationOn_normalizedFiniteTimeResonanceKernel_comp_le hT hphase

theorem actualRooted_collision_linearTime_diagonal_consumer
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (canonicalDiagramUmklappMismatch diagram)
          (actualRootedLocalCollisionMark alpha out diagram)
          (canonicalDiagramLocalLeft diagram)
          (canonicalDiagramLocalRight diagram)
          (canonicalPositiveGeometry_principalZone
              (canonicalDiagramGridK₀_pos diagram)
              (canonicalDiagramGridK₀_lt_two_pi diagram)
              (canonicalDiagramGridK₁_pos diagram)
              (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (time n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  actualRootedLocalFourierGridCollision_tendsto_rate_of_linearTime_unconditional
    alpha out diagram hdisc ha0 hb2pi time htimePos htime hlinear

#print axioms sincSquareKernel_boundedVariation_consumer
#print axioms monotone_collision_peak_linear_variation_consumer
#print axioms actualRooted_collision_linearTime_diagonal_consumer

end

end ArchonPhysicsConsumers.Thermalization
