import Family8Grounding.Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
import Family8Grounding.Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
import Mathlib.Tactic

/-!
# The two label scales at a retained winner-side occurrence

This small opaque bridge recovers the common outer label directly from the
literal winner-side bucket and combines it with the occupied inner label at
the already selected occurrence.  Keeping the dependent bucket reduction in
this module prevents later Equation-(32) consumers from repeatedly unfolding
the same label geometry.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8WinnerSideOuterInnerLabelScaleRelationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ActualRefinementSurvivingDenseFiberV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
open Family8SelectedOccurrenceOuterInnerScaleMismatchPowerV1
open Family8SelectedOccurrenceWeightedWinnerSideBucketV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual outer winner label and the actual occupied selected-parent
label satisfy the two endpoint floors.  No equality between the labels is
asserted or used. -/
theorem winnerSide_outerInnerLabelScaleRelation
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (hParent : (activeParentActualTubeDatum S D.shading).IsAdmissible)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (outerLabel : Fin 3 -> Int)
    (hselection : WinnerSideSelectionPayload
      D S P hdelta R Y fineBucket outerLabel)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (labelInner : Fin 3 -> Int)
    (hoccupied : labelInner ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P q).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hdelta P q) r hr)
          S (blockAt S.activeCoarseFamily P q).fiber hdelta p))) :
    Prop66OuterInnerLabelScaleRelation
      (delta / 576) (delta / 11943936) outerLabel labelInner := by
  classical
  let Rside := winnerSideRetainedOccurrences D S P hdelta R outerLabel
  have hRsideNonempty : Rside.Nonempty := by
    simpa only [Rside] using hselection.2.1
  have hlabelOuter : forall k, k ∈ Rside ->
      sideShapeLabel
        (winnerLongSide
          (fine := (activeParentActualTubeDatum S D.shading).family)
          P hdelta k) = outerLabel := by
    intro k hk
    change k ∈ sideShapeBucket R
      (winnerLongSide
        (fine := (activeParentActualTubeDatum S D.shading).family)
        P hdelta) outerLabel at hk
    exact (mem_sideShapeBucket_iff R
      (winnerLongSide
        (fine := (activeParentActualTubeDatum S D.shading).family)
        P hdelta) outerLabel k).mp hk |>.2
  have hdeltaOne : delta <= 1 := hdeltaHalf.trans (by norm_num)
  refine
    { outerFloor_pos := div_pos hdelta (by norm_num)
      innerFloor_pos := div_pos hdelta (by norm_num)
      outerFloor_le_shortA := ?_
      innerFloor_le_shortA := ?_
      outerShortB_le_one := ?_
      innerShortB_le_one := ?_ }
  · exact selectedOccurrenceNormalizedOuter_delta_div_576_le_bucketShortA
      (fine := (activeParentActualTubeDatum S D.shading).family)
      (active := Finset.univ) P hdelta outerLabel Rside hRsideNonempty
      hlabelOuter (fun i _hi => hParent.contained_in_unit_ball i)
  · exact selectedParent_rho_div_11943936_le_bucketShortA
      (fun i => hD.contained_in_unit_ball i)
      S hdelta hdeltaOne P q r hr labelInner hoccupied
  · exact selectedOccurrenceNormalizedOuter_bucketShortB_le_one
      (fineOuter := (activeParentActualTubeDatum S D.shading).family)
      (activeOuter := Finset.univ)
      P hdelta outerLabel Rside hRsideNonempty hlabelOuter
  · exact selectedParent_occupied_bucketShortB_le_one
      S hdelta P q r hr labelInner hoccupied

#print axioms winnerSide_outerInnerLabelScaleRelation

end
end Family8WinnerSideOuterInnerLabelScaleRelationV1
