import Family8Grounding.Family8SelectedParentPlankHalfPostKatzTaoV3
import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped ENNReal NNReal

namespace Family8SelectedParentPlankCenteredHalfPostCarrierV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8PaperConflictAnisotropicBoundsV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFreshFiveParameterPackingV3
open Family8SelectedParentPlankHalfPostMapCarrierV2
open Family8SelectedParentPlankHalfPostMapCarrierV3
open Family8SelectedParentPlankHalfPostKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-! The fixed-`W` post-translation sends the half-scaled chosen box center
to the origin.  Translation changes neither vectors nor linear distortion. -/

def centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    Space ≃ᵃ[Real] Space :=
  (halfPostBucketAffineEquiv e label).trans
    (AffineEquiv.constVAdd Real Space
      (-((1 / 2 : Real) • (chosenPlankCertificate hplank W).box.center)))

@[simp] theorem centeredHalfPostBucketAffineEquiv_apply
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (x : Space) :
    centeredHalfPostBucketAffineEquiv e S B hrho label hplank W x =
      (1 / 2 : Real) •
        (bucketNormalizedAffineEquiv e label x -
          (chosenPlankCertificate hplank W).box.center) := by
  rw [centeredHalfPostBucketAffineEquiv, AffineEquiv.trans_apply,
    AffineEquiv.constVAdd_apply, halfPostBucketAffineEquiv_apply]
  simp only [vadd_eq_add]
  module

theorem affineImageAxisVector_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (T : Tube delta) :
    affineImageAxisVector
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T =
      (1 / 2 : Real) •
        affineImageAxisVector (bucketNormalizedAffineEquiv e label) T := by
  unfold affineImageAxisVector
  simp only [centeredHalfPostBucketAffineEquiv_apply]
  module

theorem affineImageAxisCenter_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (T : Tube delta) :
    affineImageAxisCenter
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T =
      (1 / 2 : Real) •
        (affineImageAxisCenter (bucketNormalizedAffineEquiv e label) T -
          (chosenPlankCertificate hplank W).box.center) := by
  unfold affineImageAxisCenter
  simp only [centeredHalfPostBucketAffineEquiv_apply]
  module

theorem affineLinearOperatorNorm_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    affineLinearOperatorNorm
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) =
      affineLinearOperatorNorm (halfPostBucketAffineEquiv e label) := by
  unfold affineLinearOperatorNorm centeredHalfPostBucketAffineEquiv
  congr 2

theorem affineJacobian_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    affineJacobian
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) =
      affineJacobian (halfPostBucketAffineEquiv e label) := by
  unfold affineJacobian centeredHalfPostBucketAffineEquiv
  congr 3

theorem selectedPlankFine_centeredHalfPost_axisVector_norm_le_one
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ‖affineImageAxisVector
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
        (fine.tubes i.1)‖ ≤ 1 := by
  rw [affineImageAxisVector_centeredHalfPostBucketAffineEquiv,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h := selectedPlankFine_bucketAffineImageAxisVector_norm_le_two
    e S B hrho label hplank W i
  nlinarith

theorem selectedPlankFine_centeredHalfPost_axisCenter_norm_le_one
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ‖affineImageAxisCenter
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
        (fine.tubes i.1)‖ ≤ 1 := by
  rw [affineImageAxisCenter_centeredHalfPostBucketAffineEquiv,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h := selectedPlankFine_affineCenter_dist_chosenBoxCenter_le_two
    e S B hrho label hplank W i
  nlinarith

def centeredHalfPostSelectedPlankFineProxyFamily
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    UniformTubeFamily s (SelectedPlankFineIndex S W) where
  tubes i := affineAxisProxyTube s
    (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
      (fine.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem centeredHalfPostSelectedPlankFineProxyFamily_tubes
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    (centeredHalfPostSelectedPlankFineProxyFamily
      s e S B hrho label hplank W).tubes i =
      affineAxisProxyTube s
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
          (fine.tubes i.1) := rfl

theorem centeredHalfPost_image_tubeCarrier_subset_proxy
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (i : SelectedPlankFineIndex S W) :
    centeredHalfPostBucketAffineEquiv e S B hrho label hplank W ''
        (fine.tubes i.1).carrier ⊆
      (centeredHalfPostSelectedPlankFineProxyFamily
        s e S B hrho label hplank W).bodyFamily i := by
  exact image_tubeCarrier_subset_affineAxisProxyTube
    (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
      (fine.tubes i.1)
      (selectedPlankFine_centeredHalfPost_axisVector_norm_le_one
        e S B hrho label hplank W i) hradius

/-- Fixed-`W` centering gives the literal radius-two support required by
the honest B2 normalization. -/
theorem centeredHalfPostSelectedPlankFineProxyFamily_carrier_subset_B2
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hsHalf : s ≤ (2 : NNReal)⁻¹)
    (i : SelectedPlankFineIndex S W) :
    ((centeredHalfPostSelectedPlankFineProxyFamily
      s e S B hrho label hplank W).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro x hx
  let E := centeredHalfPostBucketAffineEquiv
    e S B hrho label hplank W
  let T := affineAxisProxyTube s E (fine.tubes i.1)
  have hxT : x ∈ T.carrier := hx
  have hdist := dist_midpoint_le_half_add_radius T hxT
  have hmid : ‖Family8CommonPointTubePackingV1.tubeAxisMidpoint T‖ ≤ 1 := by
    rw [tubeAxisMidpoint_affineAxisProxyTube]
    exact selectedPlankFine_centeredHalfPost_axisCenter_norm_le_one
      e S B hrho label hplank W i
  have hmidDist : dist (Family8CommonPointTubePackingV1.tubeAxisMidpoint T) (0 : Space) ≤ 1 := by
    simpa only [dist_zero_right] using hmid
  rw [Metric.mem_closedBall]
  calc
    dist x 0 ≤ dist x (Family8CommonPointTubePackingV1.tubeAxisMidpoint T) +
        dist (Family8CommonPointTubePackingV1.tubeAxisMidpoint T) 0 := dist_triangle _ _ _
    _ ≤ ((2 : Real)⁻¹ + (s : Real)) + 1 :=
      add_le_add hdist hmidDist
    _ ≤ 2 := by
      have hsReal : (s : Real) ≤ (1 / 2 : Real) := by
        have h := NNReal.coe_le_coe.mpr hsHalf
        norm_num at h ⊢
        exact h
      linarith

#print axioms centeredHalfPostBucketAffineEquiv_apply
#print axioms affineImageAxisVector_centeredHalfPostBucketAffineEquiv
#print axioms affineImageAxisCenter_centeredHalfPostBucketAffineEquiv
#print axioms affineLinearOperatorNorm_centeredHalfPostBucketAffineEquiv
#print axioms affineJacobian_centeredHalfPostBucketAffineEquiv
#print axioms selectedPlankFine_centeredHalfPost_axisVector_norm_le_one
#print axioms selectedPlankFine_centeredHalfPost_axisCenter_norm_le_one
#print axioms centeredHalfPostSelectedPlankFineProxyFamily
#print axioms centeredHalfPost_image_tubeCarrier_subset_proxy
#print axioms centeredHalfPostSelectedPlankFineProxyFamily_carrier_subset_B2

end
end Family8SelectedParentPlankCenteredHalfPostCarrierV1
