import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostCarrierV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankCenteredHalfPostDirectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem norm_affineImageAxisVector_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (T : Tube delta) :
    ‖affineImageAxisVector
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T‖ =
      (1 / 2 : Real) *
        ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label) T‖ := by
  rw [affineImageAxisVector_centeredHalfPostBucketAffineEquiv,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]

/-- Positive common post-scaling and translation do not change the
normalized direction.  Thus centered-half supplies support, not a hidden
angular gain. -/
theorem affineImageAxisDirection_centeredHalfPostBucketAffineEquiv
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (T : Tube delta) :
    affineImageAxisDirection
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T =
        affineImageAxisDirection (bucketNormalizedAffineEquiv e label) T := by
  change NormedSpace.normalize
      (affineImageAxisVector
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T) =
    NormedSpace.normalize
      (affineImageAxisVector (bucketNormalizedAffineEquiv e label) T)
  rw [affineImageAxisVector_centeredHalfPostBucketAffineEquiv,
    NormedSpace.normalize_smul_of_pos (by norm_num : (0 : Real) < 1 / 2)]

theorem abs_inner_affineImageAxisVector_centeredHalfPost
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (T : Tube delta) (u : Space) :
    |⟪u, affineImageAxisVector
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) T⟫_Real| =
      (1 / 2 : Real) *
        |⟪u, affineImageAxisVector
          (bucketNormalizedAffineEquiv e label) T⟫_Real| := by
  rw [affineImageAxisVector_centeredHalfPostBucketAffineEquiv,
    real_inner_smul_right, abs_mul,
    abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]

/-- The literal chosen-frame raw bounds scale by exactly one half. -/
theorem selectedPlankFine_centeredHalfPost_rawVector_chosenFrame_bounds
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    |⟪(chosenPlankCertificate hplank W).box.frame 0,
      affineImageAxisVector
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
          (fine.tubes i.1)⟫_Real| ≤ (bucketShortA label : Real) / 2 ∧
    |⟪(chosenPlankCertificate hplank W).box.frame 1,
      affineImageAxisVector
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
          (fine.tubes i.1)⟫_Real| ≤ (bucketShortB label : Real) / 2 := by
  have h := selectedPlankFine_rawVector_chosenFrame_bounds
    e S B hrho label hplank W i
  constructor
  · rw [abs_inner_affineImageAxisVector_centeredHalfPost]
    nlinarith [h.1]
  · rw [abs_inner_affineImageAxisVector_centeredHalfPost]
    nlinarith [h.2]

#print axioms norm_affineImageAxisVector_centeredHalfPostBucketAffineEquiv
#print axioms affineImageAxisDirection_centeredHalfPostBucketAffineEquiv
#print axioms abs_inner_affineImageAxisVector_centeredHalfPost
#print axioms selectedPlankFine_centeredHalfPost_rawVector_chosenFrame_bounds

end
end Family8SelectedParentPlankCenteredHalfPostDirectionV1
