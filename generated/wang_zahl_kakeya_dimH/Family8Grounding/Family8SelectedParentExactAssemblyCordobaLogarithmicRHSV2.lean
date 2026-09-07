import Family8Grounding.Family8SelectedParentAngleBucketLogarithmicLossV2

/-!
# Fully logarithmic selected-parent Cordoba scalar, V2

Canonical successor to V1, whose only failures were missing namespace opens.
This lean version states the final literal expression directly: both finite
dyadic cardinality losses are explicit functions of `rho`, while the actual
Katz--Tao constant, John scale, and popularity mass/cardinality quotient stay
visible.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyCordobaLogarithmicRHSV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaExpandedV6
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
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The literal actual selected-parent right-hand side is bounded by a scalar
whose side and angle counts are both explicit logarithmic functions of
`rho`. -/
theorem selectedParentFineLevelExplicitCordobaRHS_le_logarithmic
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
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel := fineShadingAtGreedyBlockLevel
      S D.shading P k A.fineLevel
    let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
    selectedParentFineLevelExplicitCordobaRHS
        D S hrho P k r hr A label hplank KT <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 *
          (((2 * threeSideDyadicRatioLoss
            (11943936 / (rho : Real)) : Nat) : ENNReal) * KT *
            (certifiedPlankThresholdedAngleScaleCap 576 *
              (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                (Ybucket.shadingMass /
                  (((selectedParentPlankBucketIndices e S B hrho label).card :
                    ENNReal) * 2)))))) := by
  dsimp only
  apply (selectedParentFineLevelExplicitCordobaRHS_le_expanded
    D S hrho P k r hr A label hplank KT).trans
  have hangleNat := selectedParent_angleBucketLoss_le_logarithmic
    hD.contained_in_unit_ball S hrho hrhoOne P k r hr label hoccupied
  have hangle :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : ENNReal) <=
        ((2 * threeSideDyadicRatioLoss
          (11943936 / (rho : Real)) : Nat) : ENNReal) := by
    exact_mod_cast hangleNat
  dsimp only [selectedParentFineLevelExpandedCordobaRHS]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
    (mul_le_mul' (mul_le_mul' hangle le_rfl) le_rfl))

#print axioms selectedParentFineLevelExplicitCordobaRHS_le_logarithmic

end

end Family8SelectedParentExactAssemblyCordobaLogarithmicRHSV2
