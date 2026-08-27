import ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint

/-!
# Consumer: canonical marked-kernel identification endpoint

The consumer checks the explicit volume-uniform continuous-to-window error
and the complete varying-size marked finite-measure limit.
-/

open scoped Topology

namespace ArchonPhysicsConsumers.Thermalization.CanonicalMarkedKernelIdentificationEndpoint

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
open ArchonPhysics.CanonicalMarkedKernelIdentificationEndpoint
open ArchonPhysics.CanonicalRankFrequencyMarkedConvergenceInProbability
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CanonicalThresholdCountMcDiarmid
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter MeasureTheory Set Topology

noncomputable section

/-- Consumer-facing finite deterministic continuous-to-window estimate. -/
theorem finiteContinuousCollisionKernel_to_centeredWindow
    {m : Nat} [NeZero m]
    (sign : Fin 3 → InteractionSign) (time : Real) (k : Nat)
    (x : Fin
      ((2 * (collisionPolynomialApproximation sign time k).windowRadius + 1) +
        m) → Real)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (clippedPositiveMassConfig (siteVectorOfFin x)))) :
    ‖positiveWeightedMismatchFourierSum
          (clippedPositiveMassConfig (siteVectorOfFin x)) sign time /
          (((((2 *
            (collisionPolynomialApproximation sign time k).windowRadius + 1) +
              m : Nat) : Real)) : Complex) -
        collisionPolynomialCenteredWindowAverage sign time k x‖ ≤
      collisionThreeLegReplacementError k := by
  exact clippedCollisionFourierPerSite_sub_centeredWindowAverage_norm_le
    sign time k x hsimple

/-- Consumer-facing full marked finite-measure convergence in probability. -/
theorem fullMarkedKernel_convergesInProbability :
    let _ : PseudoMetricSpace
        (FiniteMeasure (Fin 3 → RankFrequencyMark)) :=
      canonicalRankFrequencyMarkedFiniteMeasureWeakPseudoMetricSpace
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun n omega ↦ canonicalRankFrequencyTriplePerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble (n + 1) omega)
      atTop
      (fun _omega ↦ canonicalRankFrequencyMarkedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble) :=
  canonicalFullMarkedKernel_tendstoInMeasure_limit

#print axioms positiveWeightedMismatchFourierSum_sub_polynomialMoment_norm_le
#print axioms clippedCollisionFourierPerSite_sub_centeredWindowAverage_norm_le
#print axioms canonicalFullMarkedKernel_tendsto_limit_ae
#print axioms canonicalFullMarkedKernel_tendstoInMeasure_limit
#print axioms canonicalFullMarkedKernelLimit_map_mismatch
#print axioms finiteContinuousCollisionKernel_to_centeredWindow
#print axioms fullMarkedKernel_convergesInProbability

end

end ArchonPhysicsConsumers.Thermalization.CanonicalMarkedKernelIdentificationEndpoint
