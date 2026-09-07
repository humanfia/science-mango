import Family8Grounding.Family8CoreHighPrefixFiberLogBucketFineShadingV1
import Family8Grounding.Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedPayloadV1
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Mathlib.Tactic

/-!
# Reselect the endpoint exact-high occurrence after a fibre-log fine bucket

The historical exact-high payload selects an occurrence before recording its
fibre size.  That order preserves mass, but gives no product count for that
same occurrence.  This adapter deliberately forgets only the old occurrence
and side-label witnesses.  It keeps the literal endpoint tau datum, greedy
partition, selected prefix, and first-hit cover, then buckets the selected
fine indices by fibre-log size before any new occurrence is selected.

Consequently a later quality selector may choose any `q` in the returned
bucket while retaining both the logarithmic source payment and the literal
`R.card * fiber(q).card <= 2 * active.card` count.  No dividing-scale output
or target-equivalent callback is assumed here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityExactSameCoreHighPayloadFiberLogReselectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8CoreHighPrefixFiberLogBucketFineShadingV1
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Forget the prematurely selected occurrence and side label in the old
endpoint exact-high payload, while preserving its partition, selected prefix,
and cover.  The replacement fine-label-first bucket has only logarithmic mass
loss and makes the product count valid for every occurrence selected later. -/
theorem fiberLogBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hHigh :
      EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
        D hD L W A False r hr KT) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    CoreHighPrefixFiberLogBucketFineShadingPayload Dtau A := by
  classical
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  dsimp only
    [EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion]
      at hHigh
  rcases hHigh with hfalse | hhigh
  · exact False.elim hfalse
  · obtain ⟨P, selected, hsourceFirst, hcover, _q, _hq, _hqcore,
      _oldPayload⟩ := hhigh
    have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
      change (tauActiveCoarseDatum E C S W).shading.shadingMass =
        D.shading.shadingMass
      simpa only [E, C, S] using
        (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
    have hDtau0 : Dtau.shading.shadingMass ≠ 0 := by
      rw [hmassEq]
      exact hsource0
    have hfirst : Dtau.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass := by
      rw [hmassEq]
      exact hsourceFirst
    have hprefix : CoreHighPrefixWithFirstHitMass Dtau A :=
      ⟨P, selected, hfirst, hcover⟩
    exact coreHighPrefixWithFirstHitMass_to_fiberLogBucketFineShadingPayload
      Dtau A hDtau0 hprefix

#print axioms
  fiberLogBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload

end
end Family8EndpointIdentityExactSameCoreHighPayloadFiberLogReselectionV1
