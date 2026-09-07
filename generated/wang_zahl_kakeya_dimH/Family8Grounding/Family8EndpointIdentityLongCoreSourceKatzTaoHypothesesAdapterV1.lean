import Family8Grounding.Family8EndpointIdentityLongCoreDirectNumericsComposerV1
import Family8Grounding.Family8CanonicalSourceKatzTaoNNRealV1
import Family8Grounding.Family8FullRefinementActualDatumV1

/-!
# Source Katz--Tao hypotheses at the endpoint identity LongCore

The endpoint direct-numerics composer takes an `IsKatzTao` certificate on
the full-refinement copy of the source family.  The paper-facing input is
instead `KatzTaoHypotheses D etaKT`.  This adapter performs exactly that
definitionally lossless transport and then invokes the verified V521
numerical endpoint.

The conclusion is intentionally the raw long-interval numerical comparison,
not `DividingScaleOutput`: the latter additionally requires a same-object
three-scale multiplicity factorization and its count/aggregate-loss bounds.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityLongCoreSourceKatzTaoHypothesesAdapterV1

open Family8CanonicalSourceKatzTaoNNRealV1
open Family8EndpointIdentityLongCoreDirectNumericsComposerV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8SectionEightOutputEtaV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma sourceEta etaKT : Real}

/-- A literal source `KatzTaoHypotheses` certificate supplies the exact
full-refinement `IsKatzTao` input of the V521 endpoint.  No reverse transport,
high-concentration alternative, or hidden geometry is used. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_sourceKatzTaoHypotheses
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hKTsource : KatzTaoHypotheses D etaKT)
    (hetaKT : etaKT <= P.epsilon +
      10 * P.eta W.stage / (P.epsilon * beta))
    (hsmall : delta <=
      endpointIdentityLongCoreDirectNumericsThreshold P W.stage) :
    longIntervalKatzTaoRHSENNReal
        ((endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m)
        (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        ((endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m)
        (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  apply
    longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_direct
      D hD P W hbeta hgamma hFOutput
  · exact isKatzTao_canonicalSourceKatzTaoNNReal
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        ((fullRefinementDatum_katzTaoHypotheses_iff D etaKT).2 hKTsource)
  · exact hetaKT
  · exact hsmall

#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_sourceKatzTaoHypotheses

end
end Family8EndpointIdentityLongCoreSourceKatzTaoHypothesesAdapterV1
