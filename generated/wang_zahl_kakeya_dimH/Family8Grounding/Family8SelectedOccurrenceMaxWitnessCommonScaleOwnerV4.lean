import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleV1
import Family8Grounding.Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
import Mathlib.Tactic

/-!
# Actual owner control for the common-scale max-witness refinement

The common scalar normalization is not an isometry, so ownership cannot be
copied from the old hull family by definitional equality.  This file proves
the missing metric statement: pulling a closed thickening back through a
positive scalar dilation divides its radius by that scalar.  Since the
normalized witness width is exactly `scale * (2 * delta)`, every admissible
plank thickening pulls back to radius at most `2 * delta`.

Under `2 * delta <= rho`, the actual sticky parent then contains that pulled
back thickening inside its two-fold carrier.  The existing doubled-parent
conflict selection therefore gives genuine unique ownership for the actual
witness family, without a thick-count or parent-purity callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8TubeClosedThickeningInsideTwoFoldV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Closed thickenings under a positive common scalar -/

/-- If the scalar images of `A` and `B` are within radius `r`, then the
original sets are within radius `r / s`.  Compactness of `B` supplies an
actual nearest-ball witness for the closed thickening. -/
theorem scalarDilation_preimage_cthickening_subset
    {s r : NNReal} (hs : 0 < s) {A B : Set Space} (hB : IsCompact B)
    (h : scalarDilationAffineEquiv s hs '' A ⊆
      Metric.cthickening (r : Real)
        (scalarDilationAffineEquiv s hs '' B)) :
    A ⊆ Metric.cthickening (((r / s : NNReal) : Real)) B := by
  let d := scalarDilationAffineEquiv s hs
  intro x hx
  have hdx : d x ∈ Metric.cthickening (r : Real) (d '' B) :=
    h ⟨x, hx, rfl⟩
  have hdCompact : IsCompact (d '' B) :=
    hB.image d.continuous_of_finiteDimensional
  rw [hdCompact.cthickening_eq_biUnion_closedBall (by positivity)] at hdx
  simp only [mem_iUnion, Metric.mem_closedBall] at hdx
  obtain ⟨y, hyImage, hdist⟩ := hdx
  obtain ⟨z, hz, rfl⟩ := hyImage
  apply Metric.mem_cthickening_of_dist_le x z
    (((r / s : NNReal) : Real)) B hz
  have hsReal : (0 : Real) < (s : Real) := by exact_mod_cast hs
  have hscaled : (s : Real) * dist x z ≤ (r : Real) := by
    simpa only [d, scalarDilationAffineEquiv_apply, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hsReal] using hdist
  rw [NNReal.coe_div]
  exact (le_div_iff₀ hsReal).2 (by simpa [mul_comm] using hscaled)

theorem maxWitnessCommon_thickeningRadius_eq
    (delta theta : NNReal) :
    theta * maxWitnessCommonWidth delta / maxWitnessCommonScale delta =
      theta * (2 * delta) := by
  unfold maxWitnessCommonWidth
  field_simp [ne_of_gt (maxWitnessCommonScale_pos delta)]

/-! ## Unique ownership for the actual selected witness family -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The inverse image of an admissible normalized thickening stays inside
the doubled actual parent of the seed witness. -/
theorem normalizedWitnessThickening_preimage_subset_twoFoldOwner
    (hdelta : 0 < delta) (h2delta : 2 * delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (theta : NNReal) (htheta : theta ≤ 1)
    (i j : {q // q ∈ selectedOccurrenceIndices P R})
    (hcontained :
      (selectedOccurrenceMaxWitnessCommonScaleFamily C Y R j : Set Space) ⊆
        Metric.cthickening
          (((theta * maxWitnessCommonWidth delta : NNReal) : Real))
          (selectedOccurrenceMaxWitnessCommonScaleFamily C Y R i : Set Space)) :
    (fine.tubes (occurrenceMaxShadedWitness C P Y
      (selectedOccurrencePosition C R j))).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)) := by
  let wi := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R i)
  let wj := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R j)
  let s := maxWitnessCommonScale delta
  let d := maxWitnessCommonScaleEquiv delta
  have himage : d '' (fine.tubes wj).carrier ⊆
      Metric.cthickening
        (((theta * maxWitnessCommonWidth delta : NNReal) : Real))
        (d '' (fine.tubes wi).carrier) := by
    simpa only [selectedOccurrenceMaxWitnessCommonScaleFamily_apply,
      commonScaleTubeBody, coe_affineImageConvexBody, Tube.coe_body, wi, wj, d] using hcontained
  have hpull : (fine.tubes wj).carrier ⊆
      Metric.cthickening
        ((((theta * maxWitnessCommonWidth delta) / s : NNReal) : Real))
        (fine.tubes wi).carrier := by
    exact scalarDilation_preimage_cthickening_subset
      (maxWitnessCommonScale_pos delta) (fine.tubes wi).isCompact_carrier
        (by simpa only [s, d, maxWitnessCommonScaleEquiv] using himage)
  have hwiActive : wi ∈ C.activeFine := by
    exact occurrenceMaxShadedWitness_mem_active C P Y _
  have hwiParent : C.parent wi = selectedOccurrenceMaxOwner C P Y R i := rfl
  have hwiSubset : (fine.tubes wi).carrier ⊆
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)).carrier := by
    have hp := C.carrier_subset wi hwiActive
    rw [hwiParent] at hp
    exact hp
  have hradius : (theta * maxWitnessCommonWidth delta) / s ≤ rho := by
    change theta * maxWitnessCommonWidth delta / maxWitnessCommonScale delta ≤ rho
    rw [maxWitnessCommon_thickeningRadius_eq]
    calc
      theta * (2 * delta) ≤ 1 * (2 * delta) := by gcongr
      _ = 2 * delta := one_mul _
      _ ≤ rho := h2delta
  exact hpull.trans
    (cthickening_subset_twoFoldTubeCarrier_of_subset_of_le
      (lt_of_lt_of_le (mul_pos (by norm_num) hdelta) h2delta)
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i))
      hwiSubset hradius)

/-- Conflict-free actual parents force unique ownership for the genuinely
parent-specific common-scale max-witness tubes. -/
theorem thickenedPlankUniqueOwner_maxWitnessCommonScale_ownedOccurrences
    (hdelta : 0 < delta) (h2delta : 2 * delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)}
      (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta))
    (hfamily : D.family = selectedOccurrenceMaxWitnessCommonScaleFamily C Y
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
        (((theta * maxWitnessCommonWidth delta : NNReal) : Real))
        (D.family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  have hiDouble :
      (fine.tubes (occurrenceMaxShadedWitness C P Y
        (selectedOccurrencePosition C R j))).carrier ⊆
        twoFoldTubeCarrier
          (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)) := by
    apply normalizedWitnessThickening_preimage_subset_twoFoldOwner C hdelta
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

/-- Ambient Frostman data now gives the complete unique-owner local-Delta
control on the same common-scale witness datum. -/
theorem frostmanThickenedPlankControl_maxWitnessCommonScale
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
      (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta))
    (hfamily : D.family = selectedOccurrenceMaxWitnessCommonScaleFamily C Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
    {CF A : ENNReal}
    (hF : IsFrostmanIn CF D.family D.ambient)
    (hbase : containedMass D.family D.ambient ≤
      A * volume (D.ambient : Set Space))
    (hDelta : CF * A ≤ (Delta : ENNReal)) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta
        (maxWitnessCommonWidth delta) (maxWitnessCommonWidth delta)) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D
    (selectedOccurrenceMaxOwner C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
  · exact thickenedPlankUniqueOwner_maxWitnessCommonScale_ownedOccurrences
      C hdelta h2delta Y R0 loss W D hfamily
  · exact ownerFiberDeltaMax_le_of_ambientFrostman D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) hF hbase hDelta

#print axioms scalarDilation_preimage_cthickening_subset
#print axioms maxWitnessCommon_thickeningRadius_eq
#print axioms normalizedWitnessThickening_preimage_subset_twoFoldOwner
#print axioms thickenedPlankUniqueOwner_maxWitnessCommonScale_ownedOccurrences
#print axioms frostmanThickenedPlankControl_maxWitnessCommonScale

end
end Family8SelectedOccurrenceMaxWitnessCommonScaleOwnerV4
