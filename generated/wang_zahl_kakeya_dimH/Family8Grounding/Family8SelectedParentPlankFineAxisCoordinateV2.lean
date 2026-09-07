import Family8Grounding.Family8AffineImageAxisPlankCoordinateBridgeV4
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaConnectorV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineAxisCoordinateV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8AffineImageAxisPlankCoordinateBridgeV4
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-! The literal sticky fine fibre of one selected parent plank. -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

abbrev SelectedPlankFineIndex
    (S : StickyScaleCover fine rho)
    {B : Finset (ActiveParentIndex S)}
    {e : Space ≃ᵃ[Real] Space} {hrho : 0 < rho}
    {label : Fin 3 → Int}
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :=
  {i // i ∈ S.fiber W.1.1.1}

/-- The common bucket map sends every real fine axis into the same selected
parent body `W`; the proof is the literal sticky parent containment. -/
theorem selectedPlankFine_axis_image_subset_parent
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    bucketNormalizedAffineEquiv e label '' (fine.tubes i.1).axis.carrier ⊆
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) := by
  change bucketNormalizedAffineEquiv e label ''
      (fine.tubes i.1).axis.carrier ⊆
    bucketNormalizedAffineEquiv e label ''
      (S.coarse.tubes W.1.1.1).carrier
  apply Set.image_mono
  exact (fine.tubes i.1).axis_subset_carrier.trans
    (S.fiber_carrier_subset_parent W.1.1.1 i)

/-- The actual chosen frame of `W` supplies concrete center/vector bounds
for every real fine axis in precisely its own fibre. -/
theorem exists_selectedPlankFine_frame_axis_bounds
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ∃ box : FrameBox,
      box.side = plankSides (bucketShortA label) (bucketShortB label) ∧
      affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) ∈ box.carrier ∧
      ‖affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - box.center‖ ≤ 2 ∧
      |⟪box.frame 0,
        affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - box.center⟫_Real| ≤
        (bucketShortA label : Real) / 2 ∧
      |⟪box.frame 1,
        affineImageAxisCenter (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1) - box.center⟫_Real| ≤
        (bucketShortB label : Real) / 2 ∧
      |⟪box.frame 0,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤ (bucketShortA label : Real) ∧
      |⟪box.frame 1,
        affineImageAxisVector (bucketNormalizedAffineEquiv e label)
          (fine.tubes i.1)⟫_Real| ≤ (bucketShortB label : Real) := by
  exact exists_frameBox_affineImageAxis_bounds_of_isPlank
    (bucketNormalizedAffineEquiv e label) (fine.tubes i.1) (hplank W)
      (selectedPlankFine_axis_image_subset_parent e S B hrho label W i)

#print axioms selectedPlankFine_axis_image_subset_parent
#print axioms exists_selectedPlankFine_frame_axis_bounds

end
end Family8SelectedParentPlankFineAxisCoordinateV2
