import ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate

/-!
# Consumer endpoints for the explicit local collision certificate

The certificate concerns one reachable actual diagram and one aligned local
Umklapp chart.  These statements do not expose a global kinetic kernel.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTActualRootedEffectiveCoefficient
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.EqualMassPeriodicFPUTUmklappCollisionChartAdapter
open ArchonPhysics.EqualMassPeriodicFPUTUmklappFiniteAtlas
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open Filter MeasureTheory Topology

noncomputable section

theorem equalMassPeriodicFPUT_actualEffectiveCoefficientNonzero_consumer
    {N : Nat} [NeZero N] {alpha : Real} (halpha : alpha ≠ 0)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out) :
    reachableActualSwappedEffectiveFourWaveCoefficient
      N alpha out diagram ≠ 0 :=
  reachableActualSwappedEffectiveFourWaveCoefficient_ne_zero
    halpha out diagram

theorem equalMassPeriodicFPUT_localRateObstruction_consumer
    {N : Nat} [NeZero N] (alpha : Real)
    (out : ActualInteractionBranchMode N)
    (diagram : ActiveFeedbackEffectiveDiagramImage N out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)) :
    0 < actualRootedLocalCollisionRate alpha out diagram ↔
      reachableActualSwappedEffectiveFourWaveCoefficient
        N alpha out diagram ≠ 0 :=
  actualRootedLocalCollisionRate_pos_iff alpha out diagram hdisc

theorem equalMassPeriodicFPUT_certificateDiscreteShellResonant_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    reducedTwoToTwoMismatch
        (outputMomentum (reachableEffectiveDiagram diagram))
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 1)
        (canonicalTwoToTwoExternalModes (reachableEffectiveDiagram diagram) 2) = 0 :=
  certificate.discreteShell_resonant

theorem equalMassPeriodicFPUT_certificateLocalRatePositive_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    0 < actualRootedLocalCollisionRate alpha out diagram :=
  certificate.rate_pos

theorem equalMassPeriodicFPUT_certificateCollisionLimit_consumer
    {N : Nat} [NeZero N] {alpha : Real}
    {out : ActualInteractionBranchMode N}
    {diagram : ActiveFeedbackEffectiveDiagramImage N out}
    (certificate : ExplicitCollisionKernelCertificate alpha out diagram) :
    Tendsto
      (fun T : Real ↦ ∫ z in
        umklappArcsineLocalLeft
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram)..
          umklappArcsineLocalRight
            (umklappPositiveArcsineBranch
              (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
            (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram),
        normalizedFiniteTimeResonanceKernel
            (umklappReducedFourWaveMismatch
              (canonicalDiagramGridK₀ diagram)
              (canonicalDiagramGridK₁ diagram) z) T *
          actualRootedLocalCollisionMark alpha out diagram z)
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) :=
  certificate.collision_limit

#print axioms equalMassPeriodicFPUT_actualEffectiveCoefficientNonzero_consumer
#print axioms equalMassPeriodicFPUT_localRateObstruction_consumer
#print axioms equalMassPeriodicFPUT_certificateDiscreteShellResonant_consumer
#print axioms equalMassPeriodicFPUT_certificateLocalRatePositive_consumer
#print axioms equalMassPeriodicFPUT_certificateCollisionLimit_consumer

end

end ArchonPhysicsConsumers.Thermalization
