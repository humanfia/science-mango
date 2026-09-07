import Family8Grounding.Family8PaperEssentialDistinctOwnerClusterRetentionV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictOwnerParentFrameBoundsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8CommonPointTubePackingV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PaperConflictDirectionCoherenceV1
open Family8PaperConflictProjectionStabilityV2
open Family8PaperConflictAnisotropicBoundsV4
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-! Parent-frame geometry for rebuilding parents around conflict owners. -/

def parentFrameTransverseOffset
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) : Space :=
  transverseResidual parent.axis.direction
    (tubeAxisMidpoint owner - tubeAxisMidpoint parent)

def parentFrameLongitudinalOffset
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) : Real :=
  ⟪parent.axis.direction,
    tubeAxisMidpoint owner - tubeAxisMidpoint parent⟫_ℝ

theorem owner_unorientedDirectionClose_parent_fourteen_mul
    {delta rho : NNReal} {fine owner : Tube delta} {parent : Tube rho}
    (hdeltaRho : delta ≤ rho)
    (hfineParent : fine.carrier ⊆ parent.carrier)
    (howner : owner = fine ∨ PaperConflict owner fine) :
    UnorientedDirectionClose owner.axis parent.axis (14 * (rho : Real)) := by
  have haxis : fine.axis.carrier ⊆ parent.carrier :=
    fine.axis_subset_carrier.trans hfineParent
  have hFineParent :
      UnorientedDirectionClose fine.axis parent.axis (6 * (rho : Real)) :=
    (Tube.unorientedDirectionClose_of_commonSegment parent fine.axis haxis).symm
  have hOwnerFine :
      UnorientedDirectionClose owner.axis fine.axis (8 * (delta : Real)) := by
    rcases howner with rfl | hconflict
    · left
      simp only [sub_self, norm_zero]
      positivity
    · exact unorientedDirectionClose_eight_mul_of_paperConflict hconflict
  apply UnorientedDirectionClose.mono
    (UnorientedDirectionClose.trans hOwnerFine hFineParent)
  have hdeltaRhoReal : (delta : Real) ≤ (rho : Real) := by
    exact_mod_cast hdeltaRho
  nlinarith

theorem dist_owner_fine_midpoint_le_two
    {delta : NNReal} (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    {fine owner : Tube delta}
    (howner : owner = fine ∨ PaperConflict owner fine) :
    dist (tubeAxisMidpoint owner) (tubeAxisMidpoint fine) ≤ 2 := by
  rcases howner with rfl | hconflict
  · simp
  · exact dist_midpoint_le_two_of_paperConflict hdeltaSmall hconflict

theorem norm_parentFrameTransverseOffset_le_ninetyFour_mul
    {delta rho : NNReal} {fine owner : Tube delta} {parent : Tube rho}
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho)
    (hfineParent : fine.carrier ⊆ parent.carrier)
    (howner : owner = fine ∨ PaperConflict owner fine) :
    ‖parentFrameTransverseOffset parent owner‖ ≤ 94 * (rho : Real) := by
  let d : Space := tubeAxisMidpoint owner - tubeAxisMidpoint fine
  have hmidFine : tubeAxisMidpoint fine ∈ fine.carrier := by
    change tubeCenter fine ∈ fine.carrier
    exact tubeCenter_mem_carrier fine
  have hmidFineParent : tubeAxisMidpoint fine ∈ parent.carrier :=
    hfineParent hmidFine
  have hparentFineTransverse :
      ‖tubePointTransverse (tubeAxisMidpoint fine) parent‖ ≤
        2 * (rho : Real) :=
    norm_tubePointTransverse_le_two_mul parent hmidFineParent
  have hd : ‖d‖ ≤ 2 := by
    simpa only [d, dist_eq_norm] using
      dist_owner_fine_midpoint_le_two hdeltaSmall howner
  have hownerResidual :
      ‖transverseResidual owner.axis.direction d‖ ≤
        36 * (delta : Real) := by
    rcases howner with hEq | hconflict
    · subst owner
      simpa only [d, sub_self, transverseResidual, inner_zero_right,
        zero_smul, sub_zero, norm_zero] using
        (show 0 ≤ 36 * (delta : Real) by positivity)
    · have hconflict' : PaperConflict fine owner :=
        paperConflict_symm.symm owner fine hconflict
      have h := norm_tubePointTransverse_anchor_le_thirtySix_mul
        hdeltaSmall hconflict'
      rw [tubePointTransverse_eq_transverseResidual] at h
      simpa only [d] using h
  have hdirection := owner_unorientedDirectionClose_parent_fourteen_mul
    hdeltaRho hfineParent howner
  have hprojection :
      ‖transverseResidual parent.axis.direction d -
          transverseResidual owner.axis.direction d‖ ≤
        56 * (rho : Real) := by
    rcases hdirection with hforward | hreverse
    · calc
        ‖transverseResidual parent.axis.direction d -
            transverseResidual owner.axis.direction d‖ ≤
            2 * ‖d‖ *
              ‖parent.axis.direction - owner.axis.direction‖ :=
          norm_transverseResidual_sub_le
            parent.axis.norm_direction owner.axis.norm_direction
        _ ≤ 2 * 2 * (14 * (rho : Real)) := by
          gcongr
          simpa only [norm_sub_rev] using hforward
        _ = 56 * (rho : Real) := by ring
    · calc
        ‖transverseResidual parent.axis.direction d -
            transverseResidual owner.axis.direction d‖ ≤
            2 * ‖d‖ *
              ‖parent.axis.direction + owner.axis.direction‖ :=
          norm_transverseResidual_sub_le_of_neg
            parent.axis.norm_direction owner.axis.norm_direction
        _ ≤ 2 * 2 * (14 * (rho : Real)) := by
          gcongr
          simpa only [add_comm] using hreverse
        _ = 56 * (rho : Real) := by ring
  have hparentResidual :
      ‖transverseResidual parent.axis.direction d‖ ≤
        92 * (rho : Real) := by
    have hdeltaRhoReal : (delta : Real) ≤ (rho : Real) := by
      exact_mod_cast hdeltaRho
    calc
      ‖transverseResidual parent.axis.direction d‖ ≤
          ‖transverseResidual parent.axis.direction d -
              transverseResidual owner.axis.direction d‖ +
            ‖transverseResidual owner.axis.direction d‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le
            (transverseResidual parent.axis.direction d -
              transverseResidual owner.axis.direction d)
            (transverseResidual owner.axis.direction d)
      _ ≤ 56 * (rho : Real) + 36 * (delta : Real) :=
        add_le_add hprojection hownerResidual
      _ ≤ 92 * (rho : Real) := by nlinarith
  have hdecomp :
      parentFrameTransverseOffset parent owner =
        transverseResidual parent.axis.direction d -
          tubePointTransverse (tubeAxisMidpoint fine) parent := by
    simp only [parentFrameTransverseOffset,
      tubePointTransverse_eq_transverseResidual, transverseResidual]
    dsimp only [d]
    simp only [inner_sub_right]
    module
  rw [hdecomp]
  calc
    ‖transverseResidual parent.axis.direction d -
        tubePointTransverse (tubeAxisMidpoint fine) parent‖ ≤
        ‖transverseResidual parent.axis.direction d‖ +
          ‖tubePointTransverse (tubeAxisMidpoint fine) parent‖ :=
      norm_sub_le _ _
    _ ≤ 92 * (rho : Real) + 2 * (rho : Real) :=
      add_le_add hparentResidual hparentFineTransverse
    _ = 94 * (rho : Real) := by ring

theorem abs_parentFrameLongitudinalOffset_le_four
    {delta rho : NNReal} {fine owner : Tube delta} {parent : Tube rho}
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hrhoOne : rho ≤ 1)
    (hfineParent : fine.carrier ⊆ parent.carrier)
    (howner : owner = fine ∨ PaperConflict owner fine) :
    |parentFrameLongitudinalOffset parent owner| ≤ 4 := by
  have hmidFine : tubeAxisMidpoint fine ∈ fine.carrier := by
    change tubeCenter fine ∈ fine.carrier
    exact tubeCenter_mem_carrier fine
  have hmidFineParent : tubeAxisMidpoint fine ∈ parent.carrier :=
    hfineParent hmidFine
  have hownerFine := dist_owner_fine_midpoint_le_two hdeltaSmall howner
  have hfineParentDist :=
    dist_midpoint_le_half_add_radius parent hmidFineParent
  have hownerParent :
      dist (tubeAxisMidpoint owner) (tubeAxisMidpoint parent) ≤
        2 + ((2 : Real)⁻¹ + (rho : Real)) := by
    exact (dist_triangle _ (tubeAxisMidpoint fine) _).trans
      (add_le_add hownerFine hfineParentDist)
  have hinner := abs_real_inner_le_norm parent.axis.direction
    (tubeAxisMidpoint owner - tubeAxisMidpoint parent)
  rw [parent.axis.norm_direction, one_mul] at hinner
  have hrhoReal : (rho : Real) ≤ 1 := by exact_mod_cast hrhoOne
  calc
    |parentFrameLongitudinalOffset parent owner| ≤
        ‖tubeAxisMidpoint owner - tubeAxisMidpoint parent‖ := by
      simpa only [parentFrameLongitudinalOffset] using hinner
    _ = dist (tubeAxisMidpoint owner) (tubeAxisMidpoint parent) := by
      rw [dist_eq_norm]
    _ ≤ 2 + ((2 : Real)⁻¹ + (rho : Real)) := hownerParent
    _ ≤ 4 := by norm_num at *; linarith

theorem scaleCover_owner_parentFrame_bounds
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (k : Fin S.coarseCard) (a : index) (ha : a ∈ S.fiber k) :
    UnorientedDirectionClose (fine.tubes (C.owner a)).axis
        (S.coarse.tubes k).axis (14 * (rho : Real)) ∧
      ‖parentFrameTransverseOffset (S.coarse.tubes k)
          (fine.tubes (C.owner a))‖ ≤ 94 * (rho : Real) ∧
      |parentFrameLongitudinalOffset (S.coarse.tubes k)
          (fine.tubes (C.owner a))| ≤ 4 := by
  have haUniv : a ∈ (Finset.univ : Finset index) := Finset.mem_univ a
  have hownerRaw := C.owner_eq_or_conflict a haUniv
  have howner : fine.tubes (C.owner a) = fine.tubes a ∨
      PaperConflict (fine.tubes (C.owner a)) (fine.tubes a) := by
    rcases hownerRaw with hEq | hconflict
    · exact Or.inl (congrArg fine.tubes hEq)
    · exact Or.inr hconflict
  have hcontain : (fine.tubes a).carrier ⊆ (S.coarse.tubes k).carrier :=
    S.fiber_carrier_subset_parent k ⟨a, ha⟩
  exact ⟨
    owner_unorientedDirectionClose_parent_fourteen_mul
      hdeltaRho hcontain howner,
    norm_parentFrameTransverseOffset_le_ninetyFour_mul
      hdeltaSmall hdeltaRho hcontain howner,
    abs_parentFrameLongitudinalOffset_le_four
      hdeltaSmall hrhoOne hcontain howner⟩

#print axioms owner_unorientedDirectionClose_parent_fourteen_mul
#print axioms norm_parentFrameTransverseOffset_le_ninetyFour_mul
#print axioms abs_parentFrameLongitudinalOffset_le_four
#print axioms scaleCover_owner_parentFrame_bounds

end
end Family8PaperConflictOwnerParentFrameBoundsV2
