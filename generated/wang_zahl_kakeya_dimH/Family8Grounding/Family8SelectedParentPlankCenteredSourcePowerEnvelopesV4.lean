import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8ContractedJohnActualTubeProxyV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankFineProxyKatzTaoV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Honest source envelopes for the centered selected-parent proxy

The extra selected-plank normalization is not covered by the fixed contracted
John Jacobian estimate. Its exact geometric cost is therefore kept as the
single quotient `affineAxisProxyVolumeRatio / affineJacobian`. The same
quotient controls family volume, shading density, and the transported
Katz--Tao constant; no independent endpoint assumptions are introduced.

V1--V3 are failed mechanical drafts and are intentionally not imported.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def centeredHalfPostSelectedPlankFineProxyGeometricLoss
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    ENNReal :=
  affineAxisProxyVolumeRatio delta s /
    affineJacobian
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)

theorem centeredHalfPost_proxyKatzTaoConstant_eq_geometricLoss_mul
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (C : ENNReal) :
    centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C =
      centeredHalfPostSelectedPlankFineProxyGeometricLoss
        s e S B hrho label hplank W * C := by
  unfold centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
  unfold selectedPlankFineProxyKatzTaoConstant
  unfold centeredHalfPostSelectedPlankFineProxyGeometricLoss
  simp only [ENNReal.div_eq_inv_mul]
  ac_rfl

theorem centeredHalfPost_proxyFamily_familyVolume_le_ratio_mul_source
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hsHalf : s ≤ (2 : NNReal)⁻¹) :
    familyVolume
        (centeredHalfPostSelectedPlankFineProxyFamily
          s e S B hrho label hplank W).bodyFamily ≤
      affineAxisProxyVolumeRatio delta s *
        familyVolume
          (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) := by
  have hsum :
      (∑ i : SelectedPlankFineIndex S W,
        volume
          (affineAxisProxyTube s
            (centeredHalfPostBucketAffineEquiv
              e S B hrho label hplank W)
            (fine.tubes i.1)).carrier) ≤
        ∑ i : SelectedPlankFineIndex S W,
          affineAxisProxyVolumeRatio delta s *
            volume (fine.tubes i.1).carrier := by
    apply Finset.sum_le_sum
    intro i _hi
    exact affineAxisProxyTube_volume_le_ratio_mul_source
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)
      (fine.tubes i.1) hdeltaPos hdeltaHalf hsHalf
  calc
    familyVolume
        (centeredHalfPostSelectedPlankFineProxyFamily
          s e S B hrho label hplank W).bodyFamily ≤
      ∑ i : SelectedPlankFineIndex S W,
        affineAxisProxyVolumeRatio delta s *
          volume (fine.tubes i.1).carrier := by
      simpa only [familyVolume, UniformTubeFamily.bodyFamily,
        centeredHalfPostSelectedPlankFineProxyFamily_tubes,
        Tube.coe_body] using hsum
    _ = affineAxisProxyVolumeRatio delta s *
        familyVolume
          (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) := by
      simp only [familyVolume, UniformTubeFamily.bodyFamily, Tube.coe_body]
      rw [Finset.mul_sum]

theorem selectedPlankFineSource_shadingDensity_div_geometricLoss_le_centered
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hs : 0 < s) (hsHalf : s ≤ (2 : NNReal)⁻¹) :
    (selectedPlankFineSourceShading
        Y e S B hrho label W).shadingDensity /
        centeredHalfPostSelectedPlankFineProxyGeometricLoss
          s e S B hrho label hplank W ≤
      (centeredHalfPostSelectedPlankFineMassDatum
        s Y e S B hrho label hplank W hradius).shading.shadingDensity := by
  let E := centeredHalfPostBucketAffineEquiv
    e S B hrho label hplank W
  let ratio := affineAxisProxyVolumeRatio delta s
  let J := affineJacobian E
  let loss := centeredHalfPostSelectedPlankFineProxyGeometricLoss
    s e S B hrho label hplank W
  let sourceMass := (selectedPlankFineSourceShading
    Y e S B hrho label W).shadingMass
  let sourceVolume := familyVolume
    (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1)
  let D := centeredHalfPostSelectedPlankFineMassDatum
    s Y e S B hrho label hplank W hradius
  let proxyVolume := familyVolume D.family.bodyFamily
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty (SelectedPlankFineIndex S W) :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hsourceVolume0 : sourceVolume ≠ 0 := by
    have hpositive : 0 < sourceVolume := by
      obtain ⟨i, hiActive, hiParent⟩ :=
        S.parent_surjective W.1.1.1 W.1.1.2
      have hiFiber : i ∈ S.fiber W.1.1.1 :=
        (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : SelectedPlankFineIndex S W =>
          volume (fine.tubes j.1).carrier)
        (fun _ _ => bot_le)
        (Finset.mem_univ
          (⟨i, hiFiber⟩ : SelectedPlankFineIndex S W))
      exact (fine.tubes i).volume_pos hdeltaPos |>.trans_le <| by
        simpa only [sourceVolume, familyVolume,
          UniformTubeFamily.bodyFamily, Tube.coe_body] using hsingle
    exact hpositive.ne'
  have hsourceVolumeTop : sourceVolume ≠ ∞ := by
    exact familyVolume_ne_top
      (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1)
  have hproxyVolume0 : proxyVolume ≠ 0 := by
    exact (actualDatum_familyVolume_pos_of_scale D hs).ne'
  have hproxyVolumeTop : proxyVolume ≠ ∞ := by
    exact familyVolume_ne_top D.family.bodyFamily
  have hratio0 : ratio ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    refine ⟨?_, ?_⟩
    · exact mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hs.ne'))
    · exact ENNReal.div_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have hratioTop : ratio ≠ ∞ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hJ0 : J ≠ 0 := (affineJacobian_pos E).ne'
  have hJTop : J ≠ ∞ := affineJacobian_ne_top E
  have hloss0 : loss ≠ 0 := by
    dsimp only [loss, centeredHalfPostSelectedPlankFineProxyGeometricLoss]
    exact ENNReal.div_ne_zero.mpr ⟨hratio0, hJTop⟩
  have hlossTop : loss ≠ ∞ := by
    dsimp only [loss, centeredHalfPostSelectedPlankFineProxyGeometricLoss]
    exact ENNReal.div_ne_top hratioTop hJ0
  have hratioEq : ratio = loss * J := by
    dsimp only [loss, centeredHalfPostSelectedPlankFineProxyGeometricLoss]
    exact (ENNReal.div_mul_cancel hJ0 hJTop).symm
  have hvolume : proxyVolume ≤ ratio * sourceVolume := by
    simpa only [proxyVolume, D, centeredHalfPostSelectedPlankFineMassDatum_family,
      ratio] using
        (centeredHalfPost_proxyFamily_familyVolume_le_ratio_mul_source
          s e S B hrho label hplank W hdeltaPos hdeltaHalf hsHalf)
  have hmass : D.shading.shadingMass = J * sourceMass := by
    simpa only [D, J, sourceMass,
      centeredHalfPostSelectedPlankFineMassDatum] using
        (centeredHalfPostSelectedPlankFineMassShading_shadingMass
          s Y e S B hrho label hplank W hradius)
  unfold Shading.shadingDensity
  change sourceMass / sourceVolume / loss ≤
    D.shading.shadingMass / proxyVolume
  rw [hmass]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hproxyVolume0)
    (Or.inl hproxyVolumeTop)).2
  calc
    (sourceMass / sourceVolume / loss) * proxyVolume ≤
        (sourceMass / sourceVolume / loss) *
          (ratio * sourceVolume) := by gcongr
    _ = (sourceMass / sourceVolume / loss) *
          (loss * (J * sourceVolume)) := by rw [hratioEq]; ac_rfl
    _ = (sourceMass / sourceVolume / loss * loss) *
          (J * sourceVolume) := by ac_rfl
    _ = sourceMass / sourceVolume * (J * sourceVolume) := by
      rw [ENNReal.div_mul_cancel hloss0 hlossTop]
    _ = J * (sourceMass / sourceVolume * sourceVolume) := by ac_rfl
    _ = J * sourceMass := by
      rw [ENNReal.div_mul_cancel hsourceVolume0 hsourceVolumeTop]

theorem centeredHalfPost_proxyKatzTaoConstant_le_power
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hs : 0 < s)
    {C : ENNReal} {geometricEta globalEta : Real}
    (hgeometric : centeredHalfPostSelectedPlankFineProxyGeometricLoss
      s e S B hrho label hplank W ≤
        (s : ENNReal) ^ (-geometricEta))
    (hglobal : C ≤ (s : ENNReal) ^ (-globalEta)) :
    centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
        s e S B hrho label hplank W C ≤
      (s : ENNReal) ^ (-(geometricEta + globalEta)) := by
  have hs0 : (s : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hs.ne'
  have hsTop : (s : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [centeredHalfPost_proxyKatzTaoConstant_eq_geometricLoss_mul]
  calc
    centeredHalfPostSelectedPlankFineProxyGeometricLoss
          s e S B hrho label hplank W * C ≤
        (s : ENNReal) ^ (-geometricEta) *
          (s : ENNReal) ^ (-globalEta) := mul_le_mul' hgeometric hglobal
    _ = (s : ENNReal) ^ ((-geometricEta) + (-globalEta)) :=
      (ENNReal.rpow_add _ _ hs0 hsTop).symm
    _ = (s : ENNReal) ^ (-(geometricEta + globalEta)) := by
      congr 1
      ring

#print axioms centeredHalfPostSelectedPlankFineProxyGeometricLoss
#print axioms centeredHalfPost_proxyKatzTaoConstant_eq_geometricLoss_mul
#print axioms centeredHalfPost_proxyFamily_familyVolume_le_ratio_mul_source
#print axioms
  selectedPlankFineSource_shadingDensity_div_geometricLoss_le_centered
#print axioms centeredHalfPost_proxyKatzTaoConstant_le_power

end
end Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
