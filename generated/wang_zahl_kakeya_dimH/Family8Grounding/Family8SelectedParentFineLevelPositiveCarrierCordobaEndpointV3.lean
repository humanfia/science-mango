import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5
import Family8Grounding.Family8SelectedParentPositiveCarrierCordobaV2

/-!
# Selected-parent fine-level retention and actual Córdoba endpoint, V3

This module composes the literal fine-level bucket selection/affine mass
retention with the actual positive-carrier Córdoba estimate.  The selected
bucket, its plank certificate, and its carrier-volume floor are all produced
from the existing finite data; no carrier-floor or multiplicity conclusion is
an input.

The resulting factor still contains the *computed* minimum positive carrier
volume.  Obtaining a paper-scale quantitative lower bound for that minimum
(or replacing it by a popularity decomposition) is a separate geometric
step; it is not hidden here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelPositiveCarrierCordobaEndpointV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8PositiveCarrierShadingRestrictionV5
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentFineLevelBucketRetentionV5
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPositiveCarrierCordobaV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- One selected fine-level V9 plank bucket simultaneously retains the
affinely normalized source mass and satisfies the actual thresholded Córdoba
average-multiplicity estimate after automatic zero-carrier deletion. -/
theorem exists_selectedParentFineLevelPlankBucket_massRetention_and_cordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    ∃ label : Fin 3 -> Int,
      ∃ hplank : ∀ p : parent,
        p ∈ selectedParentPlankBucketIndices e S B hrho label ->
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (selectedParentAffineFamily
              (bucketNormalizedAffineEquiv e label) S B p),
        label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p => sideShapeLabel (side p)) ∧
        affineJacobian (bucketNormalizedAffineEquiv e label) *
            (sourceFineLevelShading A (some k)).shadingMass ≤
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (selectedParentPlankBucketShading
              e S Ylevel B hrho label).shadingMass ∧
        0 < bucketShortA label ∧
        bucketShortA label ≤ bucketShortB label ∧
        bucketShortB label ≤ 1 ∧
        let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
        let hplankPos : ∀ q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (positiveCarrierFamily Ybucket q) := fun q =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
        let cert := chosenPlankCertificate hplankPos
        Ybucket.averageMultiplicity ≤
          certifiedPlankDyadicFactor (certifiedPlankThresholdedLevels cert) KT
            (certifiedPlankThresholdedAngleScaleCap 576 *
              (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                automaticPositiveCarrierVolumeFloor Ybucket)) := by
  dsimp only
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ :=
    exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  refine ⟨label, hplank, hoccupied, hretained, ha, hab, hb, ?_⟩
  exact selectedParentPlankBucket_averageMultiplicity_le_thresholdedJohn_positiveCarrier
    S hrho
      (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
      P k r hr label hplank KT hKT

#print axioms
  exists_selectedParentFineLevelPlankBucket_massRetention_and_cordoba

end

end Family8SelectedParentFineLevelPositiveCarrierCordobaEndpointV3
