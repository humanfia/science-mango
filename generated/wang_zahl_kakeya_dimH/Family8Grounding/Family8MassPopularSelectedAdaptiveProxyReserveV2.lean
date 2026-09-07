import Family8Grounding.Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1
import Family8Grounding.Family8SelectedParentMassPopularProp66AInnerV4
import Mathlib.Tactic

/-!
# A mass-popular selected bucket with its actual adaptive reserve, V2

This successor first invokes the genuine mass-popular logarithmic Cordoba
selector.  It preserves the selected bucket's global source-mass retention
certificate and then constructs a proxy-aspect reserve only for that same
selected `(k,label)`.  There is no all-occupied-bucket hypothesis and no
scalar-target premise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8MassPopularSelectedAdaptiveProxyReserveV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAdaptiveActualCapProxyAspectLowerV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularFineLevelCordobaV3
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact source-to-bucket inequality selected by mass popularity. -/
def SelectedBucketGlobalMassRetention
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) : Prop :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  selectedParentMassPopularSourceFactor D S hrho P k r hr label <=
    ((loss : ENNReal) * (P.length : ENNReal)) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        Ybucket.shadingMass

/-- A genuine member of the same selected bucket supplies a transformed
proxy-aspect reserve in its canonical local Eq. (46) cap. -/
def SelectedBucketActualProxyAspectReserve
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (C : ENNReal) : Prop :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let s := selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label
  let hplank := selectedParentLiteralPlankBucket_isPlank
    S hrho P k r hr label
  ∃ W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
    centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C *
        (((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
      (centeredAdaptiveActualBucketFullFiberNatCap
        S hrho P k r hr label C : ENNReal)

/-- The actual mass-popular selector followed by the actual local-cap reserve
constructor on precisely its selected bucket. -/
theorem exists_massPopularGreedyBlock_selectedBucket_with_actualProxyAspectReserve
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily)
    (C : ENNReal) (hCfinite : C ≠ ∞) :
    ∃ k : Fin (blocks S.activeCoarseFamily P).length,
      ∃ label : Fin 3 -> Int,
        label ∈ occupiedWeightBuckets
          (Finset.univ : Finset
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
          (fun p => sideShapeLabel
            (selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ∧
        SelectedBucketGlobalMassRetention D S hrho P k r hr A label ∧
        0 < bucketShortA label ∧
        bucketShortA label <= bucketShortB label ∧
        bucketShortB label <= 1 ∧
        (sourceFineLevelShading A (some k)).averageMultiplicity <=
          selectedParentFineLevelLogarithmicCordobaRHS
            D S hrho P k r hr A label KT ∧
        SelectedBucketActualProxyAspectReserve S hrho P k r hr label C := by
  obtain ⟨k, _hmass, _hvolume, _hproduct, label, _hplank, hoccupied,
      _hretained, hglobal, ha, hab, hb, hfineLog⟩ :=
    exists_massPopularGreedyBlock_sourceAverage_le_logarithmicCordoba
      D hD S hrho hrhoOne P r hr A hsource KT hKT
  have hreserve :=
    exists_actualProxy_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label hoccupied hD.delta_pos C hCfinite
  refine ⟨k, label, hoccupied, ?_, ha, hab, hb, hfineLog, ?_⟩
  · simpa only [SelectedBucketGlobalMassRetention,
      selectedParentMassPopularSourceFactor] using hglobal
  · simpa only [SelectedBucketActualProxyAspectReserve] using hreserve

#print axioms SelectedBucketGlobalMassRetention
#print axioms SelectedBucketActualProxyAspectReserve
#print axioms
  exists_massPopularGreedyBlock_selectedBucket_with_actualProxyAspectReserve

end
end Family8MassPopularSelectedAdaptiveProxyReserveV2
