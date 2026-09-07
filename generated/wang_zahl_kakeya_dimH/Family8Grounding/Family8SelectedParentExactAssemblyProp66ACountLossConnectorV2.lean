import Family8Grounding.Family8SelectedParentExactAssemblyProp66AConnectorV3
import Family8Grounding.Family8Prop66AUniformCountLossAlgebraV3

/-!
# Selected-parent exact assembly with the honest count loss, V2

Canonical successor to V1, with the actual active-parent and greedy-factor
namespaces opened explicitly.  A one-sided count comparison replaces the
artificial exact product identity and contributes precisely
`countLoss^(1-beta/2)`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66AUniformCountLossAlgebraV3
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentExactAssemblyCordobaProductV2
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
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
set_option maxHeartbeats 10000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual selected block reaches the genuine source-volume RHS with the
uniform-count loss forced by the honest cardinality comparison. -/
theorem exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
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
    {plankCount tubesPerPlank : Nat}
    {CF countLoss : ENNReal} {epsilon beta : Real}
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (Fintype.card (ActiveParentIndex S) : ENNReal))
    (houter : forall k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ->
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity <=
        proposition66AOuterFactor rho
          (bucketShortA label) (bucketShortB label)
          plankCount CF epsilon beta)
    (hinnerScalar : forall k label,
      label ∈ occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ->
      selectedParentFineLevelLogarithmicCordobaRHS
          D S hrho P k r hr A label KT <=
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) :
    exists a b : NNReal,
      0 < a /\ a <= b /\ b <= 1 /\
      A.refinement.shading.averageMultiplicity <=
        countLoss ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho
              (activeParentActualTubeDatum S D.shading).actualFamilyVolume
              epsilon beta) := by
  obtain ⟨k, _hvolume, label, hplank, hoccupied, ha, hab, hb,
      _hfine, hproduct⟩ :=
    exists_survivingGreedyBlock_refinementAverage_le_outer_mul_explicitCordoba
      D hD S hrho hrhoOne P r hr A hsource KT hKT
  have hlog := selectedParentFineLevelExplicitCordobaRHS_le_namedLogarithmic
    D hD S hrho hrhoOne P k r hr A label hplank hoccupied KT
  have hinner := hlog.trans (hinnerScalar k label hoccupied)
  have hfactor : A.refinement.shading.averageMultiplicity <=
      countLoss ^ (1 - beta / 2) *
        proposition66AFrostmanFactor rho
          (bucketShortA label) (bucketShortB label)
          (Fintype.card (ActiveParentIndex S)) CF epsilon beta := by
    calc
      A.refinement.shading.averageMultiplicity <=
          ((greedyParentFactorization S P).inducedShading
            A.refinement.shading).averageMultiplicity *
            selectedParentFineLevelExplicitCordobaRHS
              D S hrho P k r hr A label hplank KT := hproduct
      _ <= proposition66AOuterFactor rho
            (bucketShortA label) (bucketShortB label)
            plankCount CF epsilon beta *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta :=
        mul_le_mul' (houter k label hoccupied) hinner
      _ <= countLoss ^ (1 - beta / 2) *
          proposition66AFrostmanFactor rho
            (bucketShortA label) (bucketShortB label)
            (Fintype.card (ActiveParentIndex S)) CF epsilon beta :=
        proposition66AOuterFactor_mul_innerFactor_le_countLoss_mul_frostmanFactor
          hrho ha (ha.trans_le hab) hbeta hbetaOne hcount
  have hactual :=
    proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
      (activeParentActualTubeDatum S D.shading)
      (a := bucketShortA label) (b := bucketShortB label)
      (CF := CF) (epsilon := epsilon) (beta := beta)
      hrhoHalf (hbetaOne.trans (by norm_num))
  refine ⟨bucketShortA label, bucketShortB label, ha, hab, hb, ?_⟩
  exact hfactor.trans (mul_le_mul' le_rfl hactual)

#print axioms
  exists_selectedParentScales_refinementAverage_le_countLoss_mul_actualFrostmanRHS

end

end Family8SelectedParentExactAssemblyProp66ACountLossConnectorV2
