import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Occupied-bucket bounds for both adaptive-scale components

This successor transports the unit-axis lower bound to the actual occupied
dyadic label.  It then gives explicit callback-free upper bounds for both
terms in `selectedParentCenteredHalfPostAdaptiveProxyScale`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The long endpoint of an occupied selected-parent shape bucket inherits
the unit-axis lower bound. -/
theorem selectedParent_sideShapeUpper_two_lower
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    r / 41472 ≤ sideShapeUpper label 2 := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side := selectedParentLongRelabeledSide e S B hrho W.1
  have hsidePos : ∀ i, 0 < side i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho W.1 i
  have hlabel : sideShapeLabel side = label := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (fun p => selectedParentLongRelabeledSide e S B hrho p)
      label W.1).mp W.2 |>.2
  have hband := (sideShapeUpper_half_lt_and_le hsidePos 2).2
  rw [hlabel] at hband
  calc
    r / 41472 ≤ side 2 := by
      simpa only [side, e, B] using
        selectedParentContractedLongRelabeledSide_two_lower
          hfineContained S hrho hrhoOne P k r hr W.1
    _ ≤ sideShapeUpper label 2 := hband

/-- The literal centered-half radius floor is only of order `delta / rho`.
The proof uses the actual occupied bucket and no scale callback. -/
theorem selectedParentCenteredHalfPostRadiusFloor_le
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    selectedParentCenteredHalfPostRadiusFloor delta rho r label ≤
      31104 * delta / rho := by
  let u := sideShapeUpper label 2
  have hu := selectedParent_sideShapeUpper_two_lower
    hfineContained S hrho hrhoOne P k r hr label W
  have huReal : (r : Real) / 41472 ≤ (u : Real) := by
    exact_mod_cast hu
  have huPos : (0 : Real) < (u : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have hrhoReal : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  have hru : (r : Real) / (u : Real) ≤ 41472 := by
    apply (div_le_iff₀ huPos).2
    linarith
  apply NNReal.coe_le_coe.mp
  simp only [selectedParentCenteredHalfPostRadiusFloor, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_ofNat]
  have hidentity :
      (3 * (r : Real) * (delta : Real)) /
          (4 * (rho : Real) * (u : Real)) =
        (3 / 4 : Real) * ((r : Real) / (u : Real)) *
          ((delta : Real) / (rho : Real)) := by
    field_simp [huPos.ne', hrhoReal.ne']
  rw [hidentity]
  calc
    (3 / 4 : Real) * ((r : Real) / (u : Real)) *
        ((delta : Real) / (rho : Real)) ≤
      (3 / 4 : Real) * 41472 *
        ((delta : Real) / (rho : Real)) := by gcongr
    _ = (31104 : Real) * (delta : Real) / (rho : Real) := by ring

/-- The canonical component is controlled by the actual short normalized
side.  The fixed constant comes from the explicit upper bound on the occupied
long endpoint. -/
theorem selectedPlankFineCanonicalProxyScale_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    selectedPlankFineCanonicalProxyScale r label ≤
      191102976 * bucketShortA label := by
  let u := sideShapeUpper label 2
  let a := bucketShortA label
  have hu := selectedParent_sideShapeUpper_two_le_3456_mul_r
    S hrho P k r hr label W
  have huReal : (u : Real) ≤ 3456 * (r : Real) := by
    exact_mod_cast hu
  have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have huDiv : (u : Real) / (r : Real) ≤ 3456 := by
    exact (div_le_iff₀ hrReal).2 (by simpa [mul_comm] using huReal)
  apply NNReal.coe_le_coe.mp
  simp only [selectedPlankFineCanonicalProxyScale,
    selectedPlankFineAxisLengthFloor, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_ofNat]
  have hidentity :
      (8 * (a : Real)) /
          ((r : Real) / (6912 * (u : Real))) =
        55296 * (a : Real) * ((u : Real) / (r : Real)) := by
    have huPos : (0 : Real) < (u : Real) := by
      exact_mod_cast sideShapeUpper_pos label 2
    field_simp [hrReal.ne', huPos.ne']
    ring
  rw [hidentity]
  calc
    55296 * (a : Real) * ((u : Real) / (r : Real)) ≤
        55296 * (a : Real) * 3456 := by gcongr
    _ = 191102976 * (a : Real) := by ring

/-- Both literal components of the adaptive maximum are now bounded from
the actual selected-parent definitions. -/
theorem selectedParentCenteredHalfPostAdaptiveProxyScale_le_components
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    selectedParentCenteredHalfPostAdaptiveProxyScale delta rho r label ≤
      max (191102976 * bucketShortA label) (31104 * delta / rho) := by
  apply max_le
  · exact (selectedPlankFineCanonicalProxyScale_le
      S hrho P k r hr label W).trans (le_max_left _ _)
  · exact (selectedParentCenteredHalfPostRadiusFloor_le
      hfineContained S hrho hrhoOne P k r hr label W).trans
        (le_max_right _ _)

#print axioms selectedParent_sideShapeUpper_two_lower
#print axioms selectedParentCenteredHalfPostRadiusFloor_le
#print axioms selectedPlankFineCanonicalProxyScale_le
#print axioms selectedParentCenteredHalfPostAdaptiveProxyScale_le_components

end
end Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
