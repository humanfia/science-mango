import Family8Grounding.Family8SelectedParentCenteredGeometricLossLowerV2
import Mathlib.Tactic

/-!
# The actual centered proxy Katz--Tao constant dominates its source constant

This is the scalar consequence of the exact source-to-proxy factorization and
the geometric lower bound proved from an actual fine tube.  No target-valued
premise or callback is introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCenteredProxyKatzTaoLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8SelectedParentCenteredGeometricLossLowerV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem sourceKatzTaoConstant_le_centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (hplank : forall W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) <= (s : Real))
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsHalf : s <= (2 : NNReal)⁻¹) (C : ENNReal) :
    C <= centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W C := by
  rw [centeredHalfPost_proxyKatzTaoConstant_eq_geometricLoss_mul]
  calc
    C = 1 * C := by simp
    _ <= centeredHalfPostSelectedPlankFineProxyGeometricLoss
          s e S B hrho label hplank W * C :=
      by
        gcongr
        exact one_le_centeredHalfPostSelectedPlankFineProxyGeometricLoss
          s e S B hrho label hplank W hradius hdeltaPos hdeltaHalf hsHalf
#print axioms
  sourceKatzTaoConstant_le_centeredHalfPostSelectedPlankFineProxyKatzTaoConstant

end
end Family8SelectedParentCenteredProxyKatzTaoLowerV1
