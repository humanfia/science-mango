import Family8Grounding.Family8SelectedParentPlankFreshFiveParameterPackingV3
import Family8Grounding.Family8UnequalRadiusDoubledDirectionCoherenceV1
import Family8Grounding.Family8PaperConflictOwnerParentFramePhysicalBridgeV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankStickyDirectionTransportV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Honest Sticky direction transport through the selected-parent bucket map

The source carrier containment gives projective direction coherence.  The
existing parent-frame orientation turns it into an oriented estimate.  The
operator norm of the actual common affine map remains visible because an
arbitrary affine equivalence does not preserve angles.
-/

noncomputable def affineLinearOpNorm (e : Space ≃ᵃ[Real] Space) : Real :=
  ‖LinearMap.toContinuousLinearMap e.linear.toLinearMap‖

theorem affineLinear_norm_le
    (e : Space ≃ᵃ[Real] Space) (v : Space) :
    ‖e.linear v‖ ≤ affineLinearOpNorm e * ‖v‖ := by
  exact ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap e.linear.toLinearMap) v

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal Sticky fibre gives the existing `6*rho` projective direction
bound to its actual coarse parent. -/
theorem selectedPlankFine_unorientedDirectionClose_parent
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    UnorientedDirectionClose (fine.tubes i.1).axis
      (S.coarse.tubes W.1.1.1).axis (6 * (rho : Real)) := by
  have haxis : (fine.tubes i.1).axis.carrier ⊆
      (S.coarse.tubes W.1.1.1).carrier :=
    (fine.tubes i.1).axis_subset_carrier.trans
      (S.fiber_carrier_subset_parent W.1.1.1 i)
  exact UnorientedDirectionClose.symm
    (Tube.unorientedDirectionClose_of_commonSegment
      (S.coarse.tubes W.1.1.1) (fine.tubes i.1).axis haxis)

/-- A reusable coordinate transport inequality.  It is exact up to the
standard parent orientation and the true operator norm of `E`. -/
theorem abs_inner_affineImageAxisVector_le_parent_add_opNorm
    (E : Space ≃ᵃ[Real] Space) (P : Tube rho) (T : Tube delta)
    (frame : OrthonormalBasis (Fin 3) Real Space) (j : Fin 3)
    (hclose : UnorientedDirectionClose T.axis P.axis
      (14 * (rho : Real))) :
    |⟪frame j, affineImageAxisVector E T⟫_Real| ≤
      |⟪frame j, affineImageAxisVector E P⟫_Real| +
        affineLinearOpNorm E * (14 * (rho : Real)) := by
  let d := parentOrientedDirection P T
  have hdir : ‖d - P.axis.direction‖ ≤ 14 * (rho : Real) := by
    exact norm_parentOrientedDirection_sub_parent_le_fourteen_mul hclose
  have horient :
      |⟪frame j, affineImageAxisVector E T⟫_Real| =
        |⟪frame j, E.linear d⟫_Real| := by
    rw [affineImageAxisVector_eq_linear]
    dsimp only [d]
    unfold parentOrientedDirection
    split_ifs
    · rfl
    · rw [map_neg, inner_neg_right, abs_neg]
  rw [horient, affineImageAxisVector_eq_linear]
  have hdecomp : E.linear d = E.linear P.axis.direction +
      E.linear (d - P.axis.direction) := by
    rw [map_sub]
    module
  rw [hdecomp, inner_add_right]
  calc
    |⟪frame j, E.linear P.axis.direction⟫_Real +
        ⟪frame j, E.linear (d - P.axis.direction)⟫_Real| ≤
        |⟪frame j, E.linear P.axis.direction⟫_Real| +
          |⟪frame j, E.linear (d - P.axis.direction)⟫_Real| :=
      abs_add_le _ _
    _ ≤ |⟪frame j, E.linear P.axis.direction⟫_Real| +
        ‖E.linear (d - P.axis.direction)‖ := by
      apply add_le_add le_rfl
      have hinner := abs_real_inner_le_norm
        (frame j) (E.linear (d - P.axis.direction))
      simpa only [OrthonormalBasis.norm_eq_one, one_mul] using hinner
    _ ≤ |⟪frame j, E.linear P.axis.direction⟫_Real| +
        affineLinearOpNorm E * (14 * (rho : Real)) := by
      apply add_le_add le_rfl
      exact (affineLinear_norm_le E (d - P.axis.direction)).trans
        (mul_le_mul_of_nonneg_left hdir (norm_nonneg _))

/-- Specialization to the literal same-`W` Sticky fine fibre and the one
common selected-parent bucket map. -/
theorem selectedPlankFine_rawVector_coord_le_parent_add_opNorm
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W)
    (frame : OrthonormalBasis (Fin 3) Real Space) (j : Fin 3) :
    |⟪frame j,
      affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)⟫_Real| ≤
      |⟪frame j,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (S.coarse.tubes W.1.1.1)⟫_Real| +
        affineLinearOpNorm (bucketNormalizedAffineEquiv e label) *
          (14 * (rho : Real)) := by
  apply abs_inner_affineImageAxisVector_le_parent_add_opNorm
  apply UnorientedDirectionClose.mono
    (selectedPlankFine_unorientedDirectionClose_parent
      e S B hrho label W i)
  have hrhoNonneg : 0 ≤ (rho : Real) := NNReal.zero_le_coe
  nlinarith

/-- In the actual chosen frame, the two raw-vector hypotheses of the
five-parameter cap follow from two scalar budgets containing only the mapped
parent direction and the explicit affine distortion. -/
theorem selectedPlankFine_thetaThin_rawVector_bounds_of_parent_opNorm_budget
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (s : NNReal) (R : Real)
    (ell : SelectedPlankFineIndex S W → Real)
    (hbudget0 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (S.coarse.tubes W.1.1.1)⟫_Real| +
          affineLinearOpNorm (bucketNormalizedAffineEquiv e label) *
            (14 * (rho : Real)) ≤ ell i * ((s : Real) / 8))
    (hbudget1 : ∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (S.coarse.tubes W.1.1.1)⟫_Real| +
          affineLinearOpNorm (bucketNormalizedAffineEquiv e label) *
            (14 * (rho : Real)) ≤
        ell i * (R * ((s : Real) / 8))) :
    (∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤ ell i * ((s : Real) / 8)) ∧
    (∀ i,
      |⟪(chosenPlankCertificate hplank W).box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤
        ell i * (R * ((s : Real) / 8))) := by
  constructor
  · intro i
    exact (selectedPlankFine_rawVector_coord_le_parent_add_opNorm
      e S B hrho label W i
        (chosenPlankCertificate hplank W).box.frame 0).trans (hbudget0 i)
  · intro i
    exact (selectedPlankFine_rawVector_coord_le_parent_add_opNorm
      e S B hrho label W i
        (chosenPlankCertificate hplank W).box.frame 1).trans (hbudget1 i)

#print axioms affineLinear_norm_le
#print axioms selectedPlankFine_unorientedDirectionClose_parent
#print axioms abs_inner_affineImageAxisVector_le_parent_add_opNorm
#print axioms selectedPlankFine_rawVector_coord_le_parent_add_opNorm
#print axioms
  selectedPlankFine_thetaThin_rawVector_bounds_of_parent_opNorm_budget

end
end Family8SelectedParentPlankStickyDirectionTransportV4
