import Family8Grounding.Family8SelectedParentCombinedLogLossPowerAbsorptionV3
import Family8Grounding.Family8SelectedParentFrozenComparableExplicitCordobaV1

/-!
# Absorb the actual selected-parent Cordoba logarithms

The explicit frozen-fibre endpoint carries exactly one side-bucket logarithm
and four times the thresholded angle-ratio logarithm.  The canonical combined
absorption theorem turns that product into an arbitrary negative power of
`rho`, leaving the genuine Katz--Tao, John-volume, and popularity-floor
scalar visible.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFrozenComparableCordobaLogAbsorptionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCombinedLogLossPowerAbsorptionV3
open Family8SelectedParentFrozenComparableExplicitCordobaV1
open Family8SelectedParentFrozenComparablePlankBucketV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
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

/-- The explicit side and angle logarithms in the arbitrary-block Cordoba
factor are absorbed into `rho ^ (-lossEta)`. -/
theorem sideLoss_mul_selectedParentExplicitCordobaFactor_le_rpow_mul
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    {rho r : NNReal} {label : Fin 3 -> Int} {KT : ENNReal}
    (Y : Shading F) {lossEta : Real}
    (hlossEta : 0 < lossEta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hsideThreshold :
      rho <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        4 (lossEta / 4)) :
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        selectedParentExplicitCordobaFactor rho r label KT Y <=
      (rho : ENNReal) ^ (-lossEta) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            quantitativeCarrierFloor Y))) := by
  let angleLoss : ENNReal :=
    (threeSideDyadicRatioLoss (11943936 / (rho : Real)) : Nat)
  let scale : ENNReal := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      quantitativeCarrierFloor Y)
  have hlog :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (4 * angleLoss) <= (rho : ENNReal) ^ (-lossEta) := by
    exact fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow
      (rho := rho) (fixedConstant := 4) (lossEta := lossEta)
        (by norm_num) hlossEta hrho hrhoHalf hsideThreshold hangleThreshold
  unfold selectedParentExplicitCordobaFactor
  change (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 * ((((2 * threeSideDyadicRatioLoss
        (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) * scale)) <=
    (rho : ENNReal) ^ (-lossEta) * (KT * scale)
  have hrewrite :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * ((((2 * threeSideDyadicRatioLoss
          (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) * scale)) =
      ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (4 * angleLoss)) * (KT * scale) := by
    dsimp only [angleLoss]
    norm_num [Nat.cast_mul]
    ring
  rw [hrewrite]
  exact mul_le_mul' hlog le_rfl

/-- Frozen paper-facing endpoint after all side/angle logarithms have been
absorbed. -/
theorem exists_frozenComparable_selectedParentCordoba_logAbsorbed
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        4 (lossEta / 4)) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (greedyParentFactorization S P)
        (parentAggregatedShading S D.shading) rFrozen,
      A.loss = frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) ∧
      ∃ k : Fin (blocks S.activeCoarseFamily P).length,
        let B := (blockAt S.activeCoarseFamily P k).fiber
        let Z := frozenFinalGreedyBlockShading D S P A k
        let e := contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
        let parent := {p // p ∈ B}
        let side : parent -> Fin 3 -> NNReal := fun p =>
          selectedParentLongRelabeledSide e S B hrho p
        0 < volume Z.shadedUnion ∧
        ∃ label : Fin 3 -> Int,
          label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
            (fun p => sideShapeLabel (side p)) ∧
          0 < bucketShortA label ∧
          bucketShortA label <= bucketShortB label ∧
          bucketShortB label <= 1 ∧
          (forall p,
            p ∈ sideShapeBucket Finset.univ side label ->
              IsPlank 576 (bucketShortA label) (bucketShortB label)
                (selectedParentAffineFamily
                  (bucketNormalizedAffineEquiv e label) S B p)) ∧
          let Ybucket := selectedParentArbitraryPlankBucketShading
            e S B hrho label Z
          let scale := certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket)
          Z.averageMultiplicity <=
              (rho : ENNReal) ^ (-lossEta) * (KT * scale) ∧
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
              A).averageMultiplicity <=
              4 * (A.frozenCoarse.averageMultiplicity *
                ((rho : ENNReal) ^ (-lossEta) * (KT * scale))) := by
  have hrhoOne : rho <= 1 := hrhoHalf.trans (by norm_num)
  obtain ⟨A, hLoss, k, hZVolume, label, hoccupied, ha, hab, hb,
      hplank, hZexplicit, hActualExplicit⟩ :=
    exists_frozenComparable_selectedParentExplicitCordoba
      D hD S hrho hrhoOne P r hr rFrozen hrFrozen hsource KT hKT
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let Z := frozenFinalGreedyBlockShading D S P A k
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let scale : ENNReal := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      quantitativeCarrierFloor Ybucket)
  have hlogs :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          selectedParentExplicitCordobaFactor rho r label KT Ybucket <=
        (rho : ENNReal) ^ (-lossEta) * (KT * scale) :=
    sideLoss_mul_selectedParentExplicitCordobaFactor_le_rpow_mul
      Ybucket hlossEta hrho hrhoHalf hsideThreshold hangleThreshold
  have hZabsorbed : Z.averageMultiplicity <=
      (rho : ENNReal) ^ (-lossEta) * (KT * scale) :=
    hZexplicit.trans hlogs
  have hActualAbsorbed :
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
        A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          ((rho : ENNReal) ^ (-lossEta) * (KT * scale))) :=
    hActualExplicit.trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hlogs))
  exact ⟨A, hLoss, k, hZVolume, label, hoccupied, ha, hab, hb,
    hplank, hZabsorbed, hActualAbsorbed⟩

#print axioms sideLoss_mul_selectedParentExplicitCordobaFactor_le_rpow_mul
#print axioms exists_frozenComparable_selectedParentCordoba_logAbsorbed

end

end Family8SelectedParentFrozenComparableCordobaLogAbsorptionV2
