import Family8Grounding.Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
import Mathlib.Tactic

/-!
# The actual centered proxy geometric loss is at least one, V2

One genuine fine tube below the selected parent has positive finite volume.
Its exact affine image has volume `J` times the source volume, lies in the
proxy carrier, and the proxy carrier is at most `ratio` times the source
volume.  Cancelling gives `J <= ratio`, hence `1 <= ratio / J`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCenteredGeometricLossLowerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem one_le_centeredHalfPostSelectedPlankFineProxyGeometricLoss
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
    (hsHalf : s <= (2 : NNReal)⁻¹) :
    1 <= centeredHalfPostSelectedPlankFineProxyGeometricLoss
      s e S B hrho label hplank W := by
  let E := centeredHalfPostBucketAffineEquiv
    e S B hrho label hplank W
  let J : ENNReal := affineJacobian E
  let ratio : ENNReal := affineAxisProxyVolumeRatio delta s
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let i : SelectedPlankFineIndex S W :=
    ⟨hfiberNonempty.choose, hfiberNonempty.choose_spec⟩
  let v : ENNReal := volume (fine.tubes i.1).carrier
  have hv0 : v ≠ 0 :=
    ne_of_gt ((fine.tubes i.1).volume_pos hdeltaPos)
  have hvTop : v ≠ ∞ := (fine.tubes i.1).volume_lt_top.ne
  have himage : volume (E '' (fine.tubes i.1).carrier) = J * v := by
    simpa only [E, J, v] using
      (volume_image_affineEquiv E (fine.tubes i.1).carrier)
  have hsubset : E '' (fine.tubes i.1).carrier <=
      (centeredHalfPostSelectedPlankFineProxyFamily
        s e S B hrho label hplank W).bodyFamily i := by
    simpa only [E] using
      centeredHalfPost_image_tubeCarrier_subset_proxy
        s e S B hrho label hplank W hradius i
  have hcross : J * v <= ratio * v := by
    calc
      J * v = volume (E '' (fine.tubes i.1).carrier) := himage.symm
      _ <= volume
          ((centeredHalfPostSelectedPlankFineProxyFamily
            s e S B hrho label hplank W).bodyFamily i : Set Space) :=
        measure_mono hsubset
      _ <= ratio * v := by
        simpa only [UniformTubeFamily.bodyFamily,
          centeredHalfPostSelectedPlankFineProxyFamily_tubes,
          Tube.coe_body, ratio, E, v] using
          (affineAxisProxyTube_volume_le_ratio_mul_source
            E (fine.tubes i.1) hdeltaPos hdeltaHalf hsHalf)
  have hJle : J <= ratio :=
    (ENNReal.mul_le_mul_iff_right hv0 hvTop).mp (by
      simpa only [mul_comm] using hcross)
  unfold centeredHalfPostSelectedPlankFineProxyGeometricLoss
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (affineJacobian_pos E).ne')
    (Or.inl (affineJacobian_ne_top E))).2
  simpa only [one_mul, J, ratio] using hJle

#print axioms one_le_centeredHalfPostSelectedPlankFineProxyGeometricLoss

end
end Family8SelectedParentCenteredGeometricLossLowerV2
