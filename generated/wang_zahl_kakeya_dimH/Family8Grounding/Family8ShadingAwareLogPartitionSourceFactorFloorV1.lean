import Family8Grounding.Family8ExactPartitionBalancedSourceFactorFloorV1
import Family8Grounding.Family8StickyShadingAwareCanonicalLogSelectedDatumV1
import Family8Grounding.Family8CanonicalFullGreedyPartitionChoiceV4

/-!
# Shading-aware logarithmic selection gives the Eq46 source factor

This composes the actual selected shading-mass floor with the balanced
partition source-factor bridge.  Both logarithmic selection loss and actual
branching loss remain explicit; no target inequality is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareLogPartitionSourceFactorFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ExactPartitionBalancedSourceFactorFloorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularProp66AInnerV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCanonicalLogSelectedDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The canonical shading-aware partition supplies an honest source-factor
floor for every actual bucket of its full greedy partition. -/
theorem shadingAwareLogPartition_selectedParentSourceFactor_floor
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (A : ENNReal)
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn D.shading S.activeFine ≠ 0)
    (k : Fin (blocks
      (exactPartitionStickyCover
        (shadingAwareLogPartition S D.shading A hA0 hAtop hrho hscale
          hactive hmass)).activeCoarseFamily
      (canonicalFullGreedyPartition
        (exactPartitionStickyCover
          (shadingAwareLogPartition S D.shading A hA0 hAtop hrho hscale
            hactive hmass)))).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) :
    let P0 := shadingAwareLogPartition
      S D.shading A hA0 hAtop hrho hscale hactive hmass
    let D1 := shadingAwareSelectedActualDatum
      D S A hA0 hAtop hrho hactive hmass
    let S1 := exactPartitionStickyCover P0
    let G := canonicalFullGreedyPartition S1
    let selectionLoss : Nat :=
      2 * (Nat.log 2 (Fintype.card index) + 1)
    let fiberCap : Nat := P0.branchingLoss * P0.branching
    affineJacobian
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S1 hrho G k) r hr)
          label) *
      ((shadingMassOn D.shading S.activeFine /
          (selectionLoss : ENNReal)) / (fiberCap : ENNReal)) ≤
      selectedParentMassPopularSourceFactor D1 S1 hrho G k r hr label := by
  dsimp only
  let P0 := shadingAwareLogPartition
    S D.shading A hA0 hAtop hrho hscale hactive hmass
  let D1 := shadingAwareSelectedActualDatum
    D S A hA0 hAtop hrho hactive hmass
  let S1 := exactPartitionStickyCover P0
  let G := canonicalFullGreedyPartition S1
  let selectionLoss : Nat :=
    2 * (Nat.log 2 (Fintype.card index) + 1)
  let fiberCap : Nat := P0.branchingLoss * P0.branching
  have hselected : shadingMassOn D.shading S.activeFine /
        (selectionLoss : ENNReal) ≤
      shadingMassOn D.shading P0.fineIndices := by
    dsimp only [D1, shadingAwareSelectedActualDatum, S1, P0]
    dsimp only [selectionLoss, P0]
    exact shadingAwareLogPartition_sourceFloor
      S D.shading A hA0 hAtop hrho hscale hactive hmass
  have hactiveMass :
      (activeFineShading S1 D1.shading).shadingMass =
        shadingMassOn D.shading P0.fineIndices := by
    dsimp only [D1, shadingAwareSelectedActualDatum, S1, P0]
    unfold Shading.shadingMass activeFineShading shadingMassOn
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach
      (shadingAwareLogPartition
        S D.shading A hA0 hAtop hrho hscale hactive hmass).fineIndices
      (fun i => volume (D.shading.carrier i))
  have hdiv :
      (shadingMassOn D.shading S.activeFine /
          (selectionLoss : ENNReal)) / (fiberCap : ENNReal) ≤
        (activeFineShading S1 D1.shading).shadingMass /
          (fiberCap : ENNReal) := by
    rw [hactiveMass]
    exact ENNReal.div_le_div_right hselected _
  have hsource :=
    exactPartition_selectedParentMassPopularSourceFactor_floor
      D1 P0 hrho G k r hr label
  exact (mul_le_mul' le_rfl hdiv).trans hsource

#print axioms shadingAwareLogPartition_selectedParentSourceFactor_floor

end
end Family8ShadingAwareLogPartitionSourceFactorFloorV1
