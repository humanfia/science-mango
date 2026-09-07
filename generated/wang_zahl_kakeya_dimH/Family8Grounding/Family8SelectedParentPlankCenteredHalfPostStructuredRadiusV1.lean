import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostCarrierV1
import Family8Grounding.Family8SelectedParentBucketMapDistortionV10
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped NNReal

namespace Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentBucketMapDistortionV10
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankHalfPostKatzTaoV3
open Family8SelectedParentPlankStickyDirectionTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-! The winning-block John-side floor and the exact post-half operator norm
turn the remaining carrier condition into one explicit scalar budget. -/

theorem selectedParent_centeredHalfPost_affineLinearOperatorNorm_le
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (B : Finset (ActiveParentIndex S))
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S B hrho label}) :
    affineLinearOperatorNorm
        (centeredHalfPostBucketAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S B hrho label hplank W) ≤
      (1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real))) := by
  rw [affineLinearOperatorNorm_centeredHalfPostBucketAffineEquiv,
    affineLinearOperatorNorm_halfPostBucketAffineEquiv]
  have hop := selectedParentBucket_affineLinearOpNorm_le
    S hrho P k r hr label
  change affineLinearOperatorNorm
      (bucketNormalizedAffineEquiv
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        label) ≤
    3 * (r : Real) /
      ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)) at hop
  exact mul_le_mul_of_nonneg_left hop (by norm_num)

/-- No operator-norm callback remains: the displayed scalar inequality is
the complete transverse-width condition for the centered literal proxy. -/
theorem selectedParent_centeredHalfPost_radius_budget
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (B : Finset (ActiveParentIndex S))
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S B hrho label})
    (s : NNReal)
    (hscalar :
      ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
            (delta : Real) ≤ (s : Real)) :
    affineLinearOperatorNorm
        (centeredHalfPostBucketAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S B hrho label hplank W) * (delta : Real) ≤ (s : Real) := by
  exact (mul_le_mul_of_nonneg_right
    (selectedParent_centeredHalfPost_affineLinearOperatorNorm_le
      S hrho P k r hr label B hplank W)
    (show (0 : Real) ≤ (delta : Real) by positivity)).trans hscalar

#print axioms selectedParent_centeredHalfPost_affineLinearOperatorNorm_le
#print axioms selectedParent_centeredHalfPost_radius_budget

end
end Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
