import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
import Mathlib.Tactic

/-!
# Endpoint same-core weighted Cordoba mass payload

This module isolates the large dependent high-branch proposition from the
endpoint scalar-transport proof.  Compiling the proposition into its own
object keeps later endpoint wrappers small while preserving the literal
partition, selected prefix, occurrence, block, and bucket witnesses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The endpoint form of the mass-strengthened raw same-core payload.
Compared with the core conclusion, only the tau-parent source mass and
average are rewritten to the original source datum. -/
def EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (lowResult : Prop)
    (r : NNReal) (hr : 0 < r) (KT : ENNReal) : Prop :=
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  lowResult \/
    exists P : GreedyDensityPartition
        Dtau.family.bodyFamily
        (hullCandidates (Finset.univ : Finset {k // k ∈ T.activeCoarse}))
        (hullContainer Dtau.family.bodyFamily) Finset.univ,
      exists selected : Finset {k // k ∈ T.activeCoarse},
        D.shading.shadingMass <=
            2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass /\
        exists hcover : (forall k, k ∈ selected ->
          exists q : Fin (blocks Dtau.family.bodyFamily P).length,
            k ∈ (blockAt Dtau.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence Dtau P A q),
        exists q : Fin (blocks Dtau.family.bodyFamily P).length,
          q ∈ occupiedCoreHighOccurrences
              Dtau P A selected hcover /\
          CoreHighConcentrationOccurrence Dtau P A q /\
          let B := (blockAt T.activeCoarseFamily P q).fiber
          let e := contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame T hrho P q) r hr
          let parent := {p // p ∈ B}
          let side : parent -> Fin 3 -> NNReal := fun p =>
            selectedParentLongRelabeledSide e T B hrho p
          let Z := sameCoreOccurrenceBlockShading
            Dtau P A selected hcover q
          (restrictActualTubeDatum Dtau selected).shading.shadingMass <=
              ((occupiedCoreHighOccurrences
                Dtau P A selected hcover).card : ENNReal) * Z.shadingMass /\
          D.shading.shadingMass <=
              (2 * ((occupiedCoreHighOccurrences
                Dtau P A selected hcover).card : ENNReal)) * Z.shadingMass /\
          exists label : Fin 3 -> Int,
            label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
              (fun p => sideShapeLabel (side p)) /\
            0 < bucketShortA label /\
            bucketShortA label <= bucketShortB label /\
            bucketShortB label <= 1 /\
            exists hplank : forall p,
                p ∈ sideShapeBucket Finset.univ side label ->
                  IsPlank 576 (bucketShortA label) (bucketShortB label)
                    (selectedParentAffineFamily
                      (bucketNormalizedAffineEquiv e label) T B p),
              let Ybucket := selectedParentArbitraryPlankBucketShading
                e T B hrho label Z
              let hplankPos : forall t,
                  IsPlank 576 (bucketShortA label) (bucketShortB label)
                    (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
                selectedParentPlankBucket_isPlank
                  e T B hrho label hplank t.1
              let cert := chosenPlankCertificate hplankPos
              affineJacobian (bucketNormalizedAffineEquiv e label) *
                    Z.shadingMass <=
                  (selectedParentLogarithmicSideBucketLoss
                    (S.tau W.m) : ENNReal) * Ybucket.shadingMass /\
              Ybucket.shadingMass ≠ 0 /\
              D.shading.averageMultiplicity <=
                (2 * ((occupiedCoreHighOccurrences
                  Dtau P A selected hcover).card : ENNReal)) *
                  ((selectedParentLogarithmicSideBucketLoss
                      (S.tau W.m) : ENNReal) *
                    (2 * certifiedPlankDyadicFactor
                      (certifiedPlankThresholdedLevels cert) KT
                        (certifiedPlankThresholdedAngleScaleCap 576 *
                          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                              ENNReal) ^ 3) /
                            quantitativeCarrierFloor Ybucket))))

#print axioms
  EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion

end
end Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
