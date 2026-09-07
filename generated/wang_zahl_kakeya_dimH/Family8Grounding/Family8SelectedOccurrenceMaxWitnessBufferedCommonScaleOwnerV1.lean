import Family8Grounding.Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1
import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleOwnerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem buffered_pullback_radius_eq
    (delta theta : NNReal) :
    theta * bufferedCommonWidth delta / (8 : NNReal)⁻¹ =
      theta * maxWitnessCommonWidth delta := by
  unfold bufferedCommonWidth
  have h8 : (8 : NNReal) ≠ 0 := by norm_num
  field_simp

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

theorem scalarEighth_image_commonScaleTubeBody
    (T : Tube delta) :
    scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num) ''
        (commonScaleTubeBody T : Set Space) =
      (bufferedCommonScaleTubeBody T : Set Space) := by
  rw [← coe_affineImageConvexBody]
  rw [commonScaleTubeBody, affineImageConvexBody_trans]
  rfl

theorem bufferedWitnessThickening_preimage_subset_twoFoldOwner
    (hdelta : 0 < delta) (h2delta : 2 * delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (theta : NNReal) (htheta : theta ≤ 1)
    (i j : {q // q ∈ selectedOccurrenceIndices P R})
    (hcontained :
      (selectedOccurrenceMaxWitnessBufferedFamily C Y R j : Set Space) ⊆
        Metric.cthickening
          (((theta * bufferedCommonWidth delta : NNReal) : Real))
          (selectedOccurrenceMaxWitnessBufferedFamily C Y R i : Set Space)) :
    (fine.tubes (occurrenceMaxShadedWitness C P Y
      (selectedOccurrencePosition C R j))).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)) := by
  let wi := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R i)
  let wj := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R j)
  let d8 := scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num)
  have himage : d8 '' (commonScaleTubeBody (fine.tubes wj) : Set Space) ⊆
      Metric.cthickening
        (((theta * bufferedCommonWidth delta : NNReal) : Real))
        (d8 '' (commonScaleTubeBody (fine.tubes wi) : Set Space)) := by
    rw [scalarEighth_image_commonScaleTubeBody,
      scalarEighth_image_commonScaleTubeBody]
    simpa only [selectedOccurrenceMaxWitnessBufferedFamily_apply, wi, wj]
      using hcontained
  have hpull : (commonScaleTubeBody (fine.tubes wj) : Set Space) ⊆
      Metric.cthickening
        ((((theta * bufferedCommonWidth delta) /
          (8 : NNReal)⁻¹ : NNReal) : Real))
        (commonScaleTubeBody (fine.tubes wi) : Set Space) := by
    exact scalarDilation_preimage_cthickening_subset
      (show (0 : NNReal) < (8 : NNReal)⁻¹ by norm_num)
      (commonScaleTubeBody (fine.tubes wi)).isCompact himage
  apply normalizedWitnessThickening_preimage_subset_twoFoldOwner C
    hdelta h2delta Y R theta htheta i j
  rw [buffered_pullback_radius_eq] at hpull
  simpa only [selectedOccurrenceMaxWitnessCommonScaleFamily_apply, wi, wj]
    using hpull

theorem thickenedPlankUniqueOwner_maxWitnessBuffered_ownedOccurrences
    (hdelta : 0 < delta) (h2delta : 2 * delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)}
      (bufferedCommonWidth delta) (bufferedCommonWidth delta))
    (hfamily : D.family = selectedOccurrenceMaxWitnessBufferedFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected)) :
    ThickenedPlankUniqueOwner D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  intro theta _hthetaLower hthetaUpper i j hj
  by_contra hne
  have hiOwner : selectedOccurrenceMaxOwner C P Y R i ∈ W.selected :=
    selectedOccurrenceMaxOwner_mem_selected_of_owned C P Y R0 loss W i
  have hjOwner : selectedOccurrenceMaxOwner C P Y R j ∈ W.selected :=
    selectedOccurrenceMaxOwner_mem_selected_of_owned C P Y R0 loss W j
  have hjContained : (D.family j : Set Space) ⊆
      Metric.cthickening
        (((theta * bufferedCommonWidth delta : NNReal) : Real))
        (D.family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  have hiDouble :
      (fine.tubes (occurrenceMaxShadedWitness C P Y
        (selectedOccurrencePosition C R j))).carrier ⊆
        twoFoldTubeCarrier
          (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)) := by
    apply bufferedWitnessThickening_preimage_subset_twoFoldOwner C hdelta
      h2delta Y R theta hthetaUpper i j
    simpa only [hfamily] using hjContained
  let witness := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R j)
  have hwitnessActive : witness ∈ C.activeFine :=
    occurrenceMaxShadedWitness_mem_active C P Y _
  have hwitnessParent : C.parent witness =
      selectedOccurrenceMaxOwner C P Y R j := rfl
  have hjParent : (fine.tubes witness).carrier ⊆
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)).carrier := by
    have hp := C.carrier_subset witness hwitnessActive
    rw [hwitnessParent] at hp
    exact hp
  have hjDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)) :=
    hjParent.trans (carrier_subset_twoFoldTubeCarrier
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)))
  exact W.selected_pairwise hiOwner hjOwner (fun h => hne h.symm)
    ⟨witness, hwitnessActive, hiDouble, hjDouble⟩

theorem frostmanThickenedPlankControl_maxWitnessBuffered
    {Delta : NNReal}
    (hdelta : 0 < delta) (h2delta : 2 * delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)}
      (bufferedCommonWidth delta) (bufferedCommonWidth delta))
    (hfamily : D.family = selectedOccurrenceMaxWitnessBufferedFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
    {CF A : ENNReal}
    (hF : IsFrostmanIn CF D.family D.ambient)
    (hbase : containedMass D.family D.ambient ≤
      A * volume (D.ambient : Set Space))
    (hDelta : CF * A ≤ (Delta : ENNReal)) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta
        (bufferedCommonWidth delta) (bufferedCommonWidth delta)) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D
    (selectedOccurrenceMaxOwner C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
  · exact thickenedPlankUniqueOwner_maxWitnessBuffered_ownedOccurrences
      C hdelta h2delta Y R0 loss W D hfamily
  · exact ownerFiberDeltaMax_le_of_ambientFrostman D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) hF hbase hDelta

#print axioms buffered_pullback_radius_eq
#print axioms bufferedWitnessThickening_preimage_subset_twoFoldOwner
#print axioms thickenedPlankUniqueOwner_maxWitnessBuffered_ownedOccurrences
#print axioms frostmanThickenedPlankControl_maxWitnessBuffered

end
end Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleOwnerV1
