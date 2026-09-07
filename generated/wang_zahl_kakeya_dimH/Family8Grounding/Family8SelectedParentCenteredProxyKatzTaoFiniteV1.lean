import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
import Mathlib.Tactic

/-!
# Finiteness of the actual centered selected-plank proxy constant
-/

open scoped ENNReal NNReal

namespace Family8SelectedParentCenteredProxyKatzTaoFiniteV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Positivity of the original tube scale and finiteness of the source
constant automatically make every actual centered proxy constant finite. -/
theorem centeredHalfPostSelectedPlankFineProxyKatzTaoConstant_ne_top
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (hplank : forall W : {p // p ∈ selectedParentPlankBucketIndices
      e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hdelta : 0 < delta) {C : ENNReal} (hCfinite : C ≠ ∞) :
    centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e S B hrho label hplank W C ≠ ∞ := by
  unfold centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
  unfold selectedPlankFineProxyKatzTaoConstant
  apply ENNReal.div_ne_top
  · apply ENNReal.mul_ne_top
    · unfold affineAxisProxyVolumeRatio
      apply ENNReal.div_ne_top
      · exact ENNReal.mul_ne_top (by norm_num)
          (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      · exact ENNReal.div_ne_zero.mpr
          ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
    · exact hCfinite
  · exact (affineJacobian_pos
      (centeredHalfPostBucketAffineEquiv
        e S B hrho label hplank W)).ne'

#print axioms centeredHalfPostSelectedPlankFineProxyKatzTaoConstant_ne_top

end
end Family8SelectedParentCenteredProxyKatzTaoFiniteV1
