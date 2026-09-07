import Family8Grounding.Family8SelectedParentAngleBucketLogarithmicLossV2
import Family8Grounding.Family8SelectedParentFrozenComparableQuantitativeCordobaV5

/-!
# Explicit logarithmic Cordoba factor on the frozen surviving fibre

The certified thresholded-angle factor is bounded by its actual angle-bucket
cardinality.  The selected-parent geometry then bounds that cardinality by
the explicit cubic logarithm at `11943936 / rho`.  This converts the canonical
frozen Cordoba endpoint to the scalar form needed by the existing logarithmic
power-absorption modules.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFrozenComparableExplicitCordobaV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentFrozenComparablePlankBucketV3
open Family8SelectedParentFrozenComparableQuantitativeCordobaV5
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

/-- The fully explicit scalar replacing the dependent certified angle-row
factor.  Its only shading dependence is the genuine popularity floor. -/
def selectedParentExplicitCordobaFactor
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} (rho r : NNReal) (label : Fin 3 -> Int)
    (KT : ENNReal) (Y : Shading F) : ENNReal :=
  2 * ((((2 * threeSideDyadicRatioLoss
      (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) *
    (certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        quantitativeCarrierFloor Y)))

/-- The same frozen surviving block as in V5, now with a completely explicit
side/angle logarithmic Cordoba factor. -/
theorem exists_frozenComparable_selectedParentExplicitCordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
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
          Z.averageMultiplicity <=
              (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                selectedParentExplicitCordobaFactor rho r label KT Ybucket ∧
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
              A).averageMultiplicity <=
              4 * (A.frozenCoarse.averageMultiplicity *
                ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                  selectedParentExplicitCordobaFactor rho r label KT Ybucket)) := by
  obtain ⟨A, hLoss, k, hZVolume, label, hoccupied, ha, hab, hb,
      hplank, hZcert, hActualCert⟩ :=
    exists_frozenComparable_selectedParentQuantitativeCordoba
      D hD S hrho hrhoOne P r hr rFrozen hrFrozen hsource KT hKT
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let Z := frozenFinalGreedyBlockShading D S P A k
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
  let cert := chosenPlankCertificate hplankPos
  let scale : ENNReal := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      quantitativeCarrierFloor Ybucket)
  have hangleNat : certifiedPlankThresholdedAngleBucketLoss
      (bucketShortA label) (bucketShortB label) <=
        2 * threeSideDyadicRatioLoss (11943936 / (rho : Real)) :=
    selectedParent_angleBucketLoss_le_logarithmic
      hD.contained_in_unit_ball S hrho hrhoOne P k r hr label hoccupied
  have hangle :
      (certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) : ENNReal) <=
      ((2 * threeSideDyadicRatioLoss
        (11943936 / (rho : Real)) : Nat) : ENNReal) := by
    exact_mod_cast hangleNat
  have hcert : certifiedPlankDyadicFactor
      (certifiedPlankThresholdedLevels cert) KT scale <=
      ((2 * threeSideDyadicRatioLoss
        (11943936 / (rho : Real)) : Nat) : ENNReal) * KT * scale := by
    calc
      certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT scale <=
        (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : ENNReal) * KT * scale :=
        certifiedPlankDyadicFactor_thresholded_le_explicit cert KT scale
      _ <= ((2 * threeSideDyadicRatioLoss
          (11943936 / (rho : Real)) : Nat) : ENNReal) * KT * scale := by
        exact mul_le_mul' (mul_le_mul' hangle le_rfl) le_rfl
  have hfactor : 2 * certifiedPlankDyadicFactor
      (certifiedPlankThresholdedLevels cert) KT scale <=
      selectedParentExplicitCordobaFactor rho r label KT Ybucket := by
    unfold selectedParentExplicitCordobaFactor
    exact mul_le_mul' le_rfl hcert
  have hZexplicit : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        selectedParentExplicitCordobaFactor rho r label KT Ybucket :=
    hZcert.trans (mul_le_mul' le_rfl hfactor)
  have hActualExplicit :
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
        A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            selectedParentExplicitCordobaFactor rho r label KT Ybucket)) :=
    hActualCert.trans
      (mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hfactor)))
  exact ⟨A, hLoss, k, hZVolume, label, hoccupied, ha, hab, hb,
    hplank, hZexplicit, hActualExplicit⟩

#print axioms selectedParentExplicitCordobaFactor
#print axioms exists_frozenComparable_selectedParentExplicitCordoba

end

end Family8SelectedParentFrozenComparableExplicitCordobaV1
