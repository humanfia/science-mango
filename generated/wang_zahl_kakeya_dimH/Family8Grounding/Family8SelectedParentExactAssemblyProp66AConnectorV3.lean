import Family8Grounding.Family8SelectedParentExactAssemblyCordobaLogarithmicRHSV2
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8Prop66AActualFamilyVolumeTransportV1
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1

/-!
# Selected-parent exact assembly to the actual Proposition 6.6(A) RHS, V3

This canonical successor supplies the positive `b` premise of the scalar
identity from the proved inequalities `0 < a <= b`.  The exact assembly
chooses one surviving greedy block, the actual selected-parent Cordoba chain
bounds it by its logarithmic scalar, and the proved Proposition 6.6(A)
identity converts the product to the genuine actual-family-volume RHS.

Only the outer Lemma 6.4 estimate and the pure comparison of the expanded
inner scalar with Equation (46) remain as transparent analytic premises.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyProp66AConnectorV3

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
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaLogarithmicRHSV2
open Family8SelectedParentExactAssemblyCordobaProductV2
open Family8SelectedParentFineLevelLiftV2
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

/-- A named version of the fully expanded logarithmic scalar. -/
noncomputable def selectedParentFineLevelLogarithmicCordobaRHS
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
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
    (2 *
      (((2 * threeSideDyadicRatioLoss
        (11943936 / (rho : Real)) : Nat) : ENNReal) * KT *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            (Ybucket.shadingMass /
              (((selectedParentPlankBucketIndices e S B hrho label).card :
                ENNReal) * 2))))))

/-- The literal logarithmic conclusion in the named scalar form. -/
theorem selectedParentFineLevelExplicitCordobaRHS_le_namedLogarithmic
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int)
    (hplank : forall p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      p ∈ selectedParentPlankBucketIndices
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (KT : ENNReal) :
    selectedParentFineLevelExplicitCordobaRHS
        D S hrho P k r hr A label hplank KT <=
      selectedParentFineLevelLogarithmicCordobaRHS
        D S hrho P k r hr A label KT := by
  simpa only [selectedParentFineLevelLogarithmicCordobaRHS] using
    (selectedParentFineLevelExplicitCordobaRHS_le_logarithmic
      D hD S hrho hrhoOne P k r hr A label hplank hoccupied KT)

/-- The selected block and its actual plank scales feed into the genuine
actual-volume Proposition 6.6(A) right-hand side. -/
theorem exists_selectedParentScales_refinementAverage_le_actualFrostmanRHS
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
    {CF : ENNReal} {epsilon beta : Real}
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcount : Fintype.card (ActiveParentIndex S) =
      plankCount * tubesPerPlank)
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
        (proposition66AFrostmanAspectGain a b CF beta *
            (2 : ENNReal) ^ (1 - beta / 2)) *
          frostmanMultiplicityRHS rho
            (activeParentActualTubeDatum S D.shading).actualFamilyVolume
            epsilon beta := by
  obtain ⟨k, _hvolume, label, hplank, hoccupied, ha, hab, hb,
      _hfine, hproduct⟩ :=
    exists_survivingGreedyBlock_refinementAverage_le_outer_mul_explicitCordoba
      D hD S hrho hrhoOne P r hr A hsource KT hKT
  have hlog := selectedParentFineLevelExplicitCordobaRHS_le_namedLogarithmic
    D hD S hrho hrhoOne P k r hr A label hplank hoccupied KT
  have hinner := hlog.trans (hinnerScalar k label hoccupied)
  have hprop : A.refinement.shading.averageMultiplicity <=
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
      _ = proposition66AFrostmanFactor rho
          (bucketShortA label) (bucketShortB label)
          (Fintype.card (ActiveParentIndex S)) CF epsilon beta :=
        proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
          hrho ha (ha.trans_le hab) hbeta hbetaOne hcount
  have hactual :=
    proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
      (activeParentActualTubeDatum S D.shading)
      (a := bucketShortA label) (b := bucketShortB label)
      (CF := CF) (epsilon := epsilon) (beta := beta)
      hrhoHalf (hbetaOne.trans (by norm_num))
  exact ⟨bucketShortA label, bucketShortB label, ha, hab, hb,
    hprop.trans hactual⟩

#print axioms selectedParentFineLevelExplicitCordobaRHS_le_namedLogarithmic
#print axioms exists_selectedParentScales_refinementAverage_le_actualFrostmanRHS

end

end Family8SelectedParentExactAssemblyProp66AConnectorV3
