import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2

/-!
# Automatic Cordoba output on one actual high greedy occurrence

An `ActualHighConcentrationOccurrence` already fixes the greedy occurrence
index `q`, its literal fibre, the strict high-density inequality, and the
constant-one Frostman certificate.  The arbitrary-block endpoint constructs
the side-shape bucket and its memberwise plank certificate on that same
fibre.  This module only composes those two facts; in particular it does not
take the memberwise plank callback required by the older V18 connector.

The Katz--Tao coefficient, angular/John contraction scale, and all scale
hypotheses remain explicit inputs.  No directional separation or DSO output
is asserted here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyHighOccurrenceSelectedParentAutomaticCordobaConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- On the literal fibre of one actual high greedy occurrence, construct the
automatic selected-parent plank bucket and its quantitative Cordoba bound.
The output retains the occurrence's strict density inequality and its exact
constant-one Frostman conclusion at the same dependent index `q`.

There is deliberately no memberwise `IsPlank` input: `hplank` is existential
output from the weighted geometric bucket endpoint. -/
theorem exists_selectedParentAutomaticCordoba_of_actualHighOccurrence
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (Y : Shading D.family.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks S.activeCoarseFamily P).length)
    (hocc : ActualHighConcentrationOccurrence
      (activeParentActualTubeDatum S Y) P A q)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P q).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    let Z := selectedParentActualShading S Y B
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      exists hplank : forall p,
          p ∈ sideShapeBucket Finset.univ side label ->
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (selectedParentAffineFamily
                (bucketNormalizedAffineEquiv e label) S B p),
        let Ybucket := selectedParentArbitraryPlankBucketShading
          e S B hrho label Z
        let hplankPos : forall t,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
        let cert := chosenPlankCertificate hplankPos
        Z.averageMultiplicity <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (2 * certifiedPlankDyadicFactor
                (certifiedPlankThresholdedLevels cert) KT
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                      quantitativeCarrierFloor Ybucket))) ∧
          A < blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P q) ∧
          IsFrostmanIn 1
            (selectedCoarseFamily S.activeCoarseFamily B)
            (blockAt S.activeCoarseFamily P q).body := by
  dsimp only
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let Z := selectedParentActualShading S Y B
  have hcordoba :=
    exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le
      D hD S hrho hrhoOne P q r hr Z KT hKT
  dsimp only at hcordoba
  obtain ⟨label, hoccupied, ha, hab, hb, hplank, hbound⟩ := hcordoba
  refine ⟨label, hoccupied, ha, hab, hb, hplank, hbound, hocc.1, ?_⟩
  exact actualHighOccurrence_isFrostmanIn_selectedParentBlock
    S Y P A q hocc |>.2

#print axioms exists_selectedParentAutomaticCordoba_of_actualHighOccurrence

end
end Family8GreedyHighOccurrenceSelectedParentAutomaticCordobaConnectorV1
