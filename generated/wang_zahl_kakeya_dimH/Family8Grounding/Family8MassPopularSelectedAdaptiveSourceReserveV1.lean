import Family8Grounding.Family8MassPopularSelectedAdaptiveProxyReserveV2
import Family8Grounding.Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
import Mathlib.Tactic

/-!
# The mass-popular selected bucket has the source reserve or is not yet small

The genuine selector is run once.  On precisely its chosen `(k,label)`, the
adaptive construction either already lies in the packing-small regime and
retains `C*(b/a)^2` in the actual local cap, or the failure of that explicit
smallness inequality is returned as the complementary branch.  No uniform
all-bucket premise and no target-valued callback is introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8MassPopularSelectedAdaptiveSourceReserveV1

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
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8MassPopularSelectedAdaptiveProxyReserveV2
open Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentMassPopularFineLevelCordobaV3
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The exact source-constant/aspect reserve in the actual local cap. -/
def SelectedBucketActualSourceAspectReserve
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (C : ENNReal) : Prop :=
  C * (((bucketShortB label : ENNReal) /
      (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
    (centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label C : ENNReal)

theorem exists_massPopularGreedyBlock_selectedBucket_with_sourceReserve_or_notSmall
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
        SelectedBucketActualProxyAspectReserve S hrho P k r hr label C ∧
        (¬ selectedParentCenteredHalfPostAdaptiveProxyScale
              delta rho r label / 8 <= (1 / 100 : NNReal) ∨
          SelectedBucketActualSourceAspectReserve
            S hrho P k r hr label C) := by
  obtain ⟨k, label, hoccupied, hglobal, ha, hab, hb, hfineLog,
      hproxyReserve⟩ :=
    exists_massPopularGreedyBlock_selectedBucket_with_actualProxyAspectReserve
      D hD S hrho hrhoOne P r hr A hsource KT hKT C hCfinite
  refine ⟨k, label, hoccupied, hglobal, ha, hab, hb, hfineLog,
    hproxyReserve, ?_⟩
  by_cases hsmall : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 <= (1 / 100 : NNReal)
  · right
    exact exists_sourceKatzTaoConstant_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label hoccupied hD.delta_pos hD.delta_le_half
        hsmall C hCfinite
  · exact Or.inl hsmall

#print axioms SelectedBucketActualSourceAspectReserve
#print axioms
  exists_massPopularGreedyBlock_selectedBucket_with_sourceReserve_or_notSmall

end
end Family8MassPopularSelectedAdaptiveSourceReserveV1
