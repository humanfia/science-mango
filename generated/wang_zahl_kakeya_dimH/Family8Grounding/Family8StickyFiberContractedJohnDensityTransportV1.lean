import Family8Grounding.Family8ContractedJohnAffineJacobianLowerV3
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnDensityTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8ContractedJohnAffineJacobianLowerV3
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Density transport through the genuine contracted-John fibre proxy

The common affine image multiplies shading mass by its exact Jacobian.  The
actual equal-radius proxy family can enlarge total tube volume, but the
pointwise tube-volume ratio and the fixed John Jacobian estimate show that
this costs at most `93312`.  Eighth normalization then costs only its honest
factor `128`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The genuine proxy family volume is bounded by the fixed Jacobian loss
times the literal source-fibre family volume. -/
theorem stickyFiberContractedJohnProxyFamily_familyVolume_le_fixedJacobian
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (k : {k // k ∈ S.activeCoarse}) :
    familyVolume
        (stickyFiberContractedJohnProxyFamily
          S hrho hrhoOne k).bodyFamily <=
      93312 *
        (affineJacobian
          (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k) *
            familyVolume (S.fiberFamily k.1)) := by
  let ratio := contractedJohnProxyVolumeRatio delta rho
  let J := affineJacobian
    (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
  have hsumExplicit :
      (∑ i : {i // i ∈ S.fiber k.1},
        volume
          (contractedJohnProxyTube (S.coarse.tubes k.1) hrho
            (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
              S hrho hrhoOne k) (fine.tubes i.1)).carrier) <=
        ratio * ∑ i : {i // i ∈ S.fiber k.1},
          volume (fine.tubes i.1).carrier := by
    have hraw :
        (∑ i : {i // i ∈ S.fiber k.1},
          volume
            (contractedJohnProxyTube (S.coarse.tubes k.1) hrho
              (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
                S hrho hrhoOne k) (fine.tubes i.1)).carrier) <=
          ∑ i : {i // i ∈ S.fiber k.1},
            ratio * volume (fine.tubes i.1).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact contractedJohnProxyTube_volume_le_ratio_mul_source
        (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k)
        (fine.tubes i.1) hdelta hdeltaHalf hdeltaRho
    have hrewrite :
        (∑ i : {i // i ∈ S.fiber k.1},
          ratio * volume (fine.tubes i.1).carrier) =
          ratio * ∑ i : {i // i ∈ S.fiber k.1},
            volume (fine.tubes i.1).carrier := by
      rw [Finset.mul_sum]
    exact hraw.trans_eq hrewrite
  have hsum :
      familyVolume
          (stickyFiberContractedJohnProxyFamily
            S hrho hrhoOne k).bodyFamily <=
        ratio * familyVolume (S.fiberFamily k.1) := by
    simpa only [familyVolume, UniformTubeFamily.bodyFamily,
      stickyFiberContractedJohnProxyFamily_tubes,
      StickyScaleCover.fiberFamily, Tube.coe_body] using hsumExplicit
  have hJ0 : J ≠ 0 :=
    (affineJacobian_pos
      (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)).ne'
  have hJTop : J ≠ ∞ :=
    affineJacobian_ne_top
      (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
  have hratioDiv : ratio / J <= 93312 := by
    exact contractedJohnProxyVolumeRatio_div_affineJacobian_le
      (S.coarse.tubes k.1) hdelta hrho hrhoOne
      (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
        S hrho hrhoOne k)
  have hratio : ratio <= 93312 * J :=
    (ENNReal.div_le_iff hJ0 hJTop).mp hratioDiv
  calc
    familyVolume
        (stickyFiberContractedJohnProxyFamily
          S hrho hrhoOne k).bodyFamily <=
        ratio * familyVolume (S.fiberFamily k.1) := hsum
    _ <= (93312 * J) * familyVolume (S.fiberFamily k.1) := by
      gcongr
    _ = 93312 * (J * familyVolume (S.fiberFamily k.1)) := by
      ring

/-- Before eighth normalization, source-fibre shading density loses at most
the fixed factor `93312` in the genuine proxy datum. -/
theorem stickyFiberSource_shadingDensity_div_93312_le_proxy
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberSourceShading S Y k.1).shadingDensity / 93312 <=
      (stickyFiberContractedJohnProxyShading
        S Y hrho hrhoOne k).shadingDensity := by
  let J := affineJacobian
    (stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k)
  let sourceMass := (stickyFiberSourceShading S Y k.1).shadingMass
  let sourceVolume := familyVolume (S.fiberFamily k.1)
  let proxyVolume := familyVolume
    (stickyFiberContractedJohnProxyFamily S hrho hrhoOne k).bodyFamily
  have hfiberNonempty : (S.fiber k.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
    exact ⟨i, (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty {i // i ∈ S.fiber k.1} :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  have hsourceVolume0 : sourceVolume ≠ 0 := by
    have hpositive : 0 < familyVolume (S.fiberFamily k.1) := by
      obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
      have hiFiber : i ∈ S.fiber k.1 :=
        (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : {j // j ∈ S.fiber k.1} =>
          volume (S.fiberFamily k.1 j : Set Space))
        (fun _ _ => bot_le)
        (Finset.mem_univ (⟨i, hiFiber⟩ : {j // j ∈ S.fiber k.1}))
      exact (fine.tubes i).volume_pos hdelta |>.trans_le <| by
        simpa [familyVolume, StickyScaleCover.fiberFamily,
          UniformTubeFamily.bodyFamily, Tube.coe_body] using hsingle
    exact hpositive.ne'
  have hsourceVolumeTop : sourceVolume ≠ ∞ := by
    exact familyVolume_ne_top (S.fiberFamily k.1)
  have hproxyVolume0 : proxyVolume ≠ 0 := by
    have hpositive := actualDatum_familyVolume_pos_of_scale
      (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k)
      (stickyFiberContractedJohnProxyDatum_delta_pos hdelta hrho)
    exact hpositive.ne'
  have hproxyVolumeTop : proxyVolume ≠ ∞ := by
    exact familyVolume_ne_top
      (stickyFiberContractedJohnProxyFamily S hrho hrhoOne k).bodyFamily
  have hfixed0 : (93312 : ENNReal) ≠ 0 := by norm_num
  have hfixedTop : (93312 : ENNReal) ≠ ∞ := by norm_num
  have hvolume :=
    stickyFiberContractedJohnProxyFamily_familyVolume_le_fixedJacobian
      S hdelta hdeltaHalf hrho hrhoOne hdeltaRho k
  unfold Shading.shadingDensity
  rw [stickyFiberContractedJohnProxyShading_shadingMass]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hproxyVolume0)
    (Or.inl hproxyVolumeTop)).2
  calc
    (sourceMass / sourceVolume / 93312) * proxyVolume <=
        (sourceMass / sourceVolume / 93312) *
          (93312 * (J * sourceVolume)) := by
      gcongr
    _ = ((sourceMass / sourceVolume / 93312) * 93312) *
          (J * sourceVolume) := by
      ac_rfl
    _ = sourceMass / sourceVolume * (J * sourceVolume) := by
      rw [ENNReal.div_mul_cancel hfixed0 hfixedTop]
    _ = J * (sourceMass / sourceVolume * sourceVolume) := by
      ac_rfl
    _ = J * sourceMass := by
      rw [ENNReal.div_mul_cancel hsourceVolume0 hsourceVolumeTop]

/-- The full honest transport into the normalized proxy loses only the two
explicit fixed factors `93312` and `128`. -/
theorem stickyFiberSource_shadingDensity_div_93312_div_128_le_normalizedProxy
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (k : {k // k ∈ S.activeCoarse}) :
    (stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128 <=
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne k)).shading.shadingDensity := by
  have hfiberNonempty : (S.fiber k.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ := S.parent_surjective k.1 k.2
    exact ⟨i, (S.mem_fiber i k.1).2 ⟨hiActive, hiParent⟩⟩
  let _ : Nonempty {i // i ∈ S.fiber k.1} :=
    Finset.nonempty_coe_sort.mpr hfiberNonempty
  calc
    (stickyFiberSourceShading S Y k.1).shadingDensity / 93312 / 128 <=
        (stickyFiberContractedJohnProxyShading
          S Y hrho hrhoOne k).shadingDensity / 128 := by
      exact ENNReal.div_le_div_right
        (stickyFiberSource_shadingDensity_div_93312_le_proxy
          S Y hdelta hdeltaHalf hrho hrhoOne hdeltaRho k) 128
    _ <= (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k)).shading.shadingDensity := by
      exact source_shadingDensity_div_128_le_eighthNormalized_of_scale
        (stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k)
        (stickyFiberContractedJohnProxyDatum_delta_pos hdelta hrho)
        (stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho)

#print axioms
  stickyFiberContractedJohnProxyFamily_familyVolume_le_fixedJacobian
#print axioms stickyFiberSource_shadingDensity_div_93312_le_proxy
#print axioms
  stickyFiberSource_shadingDensity_div_93312_div_128_le_normalizedProxy

end
end Family8StickyFiberContractedJohnDensityTransportV1
