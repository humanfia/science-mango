import Family8Grounding.Family8StickyFiberContractedJohnProxyDatumV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnProxyKatzTaoV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAtEveryScaleCoreV1.StickyScaleCover

noncomputable section

/-!
# Katz--Tao transport to the genuine contracted-John proxy datum

Proxy tubes enlarge the common affine images of the source fibre.  Their
volume is nevertheless controlled by the ratio of the standard tube upper
and lower bounds.  If a proxy lies in a convex test body, the corresponding
source tube lies in its affine preimage.  These two facts transport the
source fibre's Katz--Tao estimate with one explicit tube-volume ratio and the
inverse common affine Jacobian.
-/

def contractedJohnProxyVolumeRatio
    (delta rho : NNReal) : ENNReal :=
  (8 * ((contractedJohnProxyRadius delta rho : NNReal) : ENNReal) ^ 2) /
    ((delta : ENNReal) ^ 2 / 2)

def stickyFiberContractedJohnProxyKatzTaoConstant
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (k : {k // k ∈ S.activeCoarse})
    (C : ENNReal) : ENNReal :=
  contractedJohnProxyVolumeRatio delta rho * C /
    affineJacobian (stickyFiberContractedJohnAffineEquiv
      S hrho hrhoOne k)

/-- The genuine proxy tube has at most the explicit source-tube volume
ratio. -/
theorem contractedJohnProxyTube_volume_le_ratio_mul_source
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdeltaRho : delta <= rho) :
    volume (contractedJohnProxyTube P hrho w T).carrier <=
      contractedJohnProxyVolumeRatio delta rho * volume T.carrier := by
  let floor : ENNReal := (delta : ENNReal) ^ 2 / 2
  let upper : ENNReal :=
    8 * ((contractedJohnProxyRadius delta rho : NNReal) : ENNReal) ^ 2
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (by norm_num)
  have hproxyHalf : contractedJohnProxyRadius delta rho <=
      (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hupper :
      volume (contractedJohnProxyTube P hrho w T).carrier <= upper := by
    exact (contractedJohnProxyTube P hrho w T).volume_le_eight_mul_sq_of_le_half
      hproxyHalf
  have hlower : floor <= volume T.carrier := by
    exact T.half_sq_le_volume_of_le_half hdeltaHalf
  calc
    volume (contractedJohnProxyTube P hrho w T).carrier <= upper := hupper
    _ = (upper / floor) * floor := by
      rw [ENNReal.div_mul_cancel hfloor0 hfloorTop]
    _ <= (upper / floor) * volume T.carrier := by gcongr
    _ = contractedJohnProxyVolumeRatio delta rho * volume T.carrier := by
      rfl

/-- Global source Katz--Tao control descends to the literal Sticky fibre. -/
theorem stickyFiberSourceFamily_isKatzTao_of_global
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) {C : ENNReal}
    (hKT : IsKatzTao C fine.bodyFamily) :
    IsKatzTao C (S.fiberFamily k) := by
  let D : ActualTubeDatum delta index :=
    { family := fine
      shading := Y }
  have hrestricted :=
    restrictActualTubeDatum_isKatzTao D (S.fiber k) hKT
  change IsKatzTao C
    (fun i : {i // i ∈ S.fiber k} => fine.bodyFamily i.1)
  change IsKatzTao C
    (fun i : {i // i ∈ S.fiber k} => fine.bodyFamily i.1) at hrestricted
  exact hrestricted

/-- Honest affine-preimage transport of fibre Katz--Tao control to the
literal genuine proxy family. -/
theorem stickyFiberContractedJohnProxyFamily_isKatzTao
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdeltaRho : delta <= rho)
    (k : {k // k ∈ S.activeCoarse}) {C : ENNReal}
    (hKT : IsKatzTao C (S.fiberFamily k.1)) :
    IsKatzTao
      (stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C)
      (stickyFiberContractedJohnProxyFamily
        S hrho hrhoOne k).bodyFamily := by
  classical
  intro K
  unfold IsKatzTaoAt
  let e : Space ≃ᵃ[Real] Space :=
    stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k
  let Kpre : ConvexBody Space := affinePreimageConvexBody e K
  let ratio : ENNReal := contractedJohnProxyVolumeRatio delta rho
  have hsubset :
      containedIndices
          (stickyFiberContractedJohnProxyFamily
            S hrho hrhoOne k).bodyFamily K ⊆
        containedIndices (S.fiberFamily k.1) Kpre := by
    intro i hi
    rw [mem_containedIndices] at hi ⊢
    change (fine.tubes i.1).carrier ⊆ e.symm '' (K : Set Space)
    apply (affineImage_subset_iff_subset_preimage
      e (fine.tubes i.1).carrier (K : Set Space)).mp
    change
      (contractedJohnProxyTube (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1)).carrier ⊆
        (K : Set Space) at hi
    exact (image_child_carrier_subset_contractedJohnProxyTube
      (S.coarse.tubes k.1) hrho
      (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
        S hrho hrhoOne k) (fine.tubes i.1)
      (S.fiber_carrier_subset_parent k.1 i)).trans hi
  have hJ0 : affineJacobian e ≠ 0 :=
    (affineJacobian_pos e).ne'
  have hJTop : affineJacobian e ≠ ∞ := affineJacobian_ne_top e
  calc
    containedMass
        (stickyFiberContractedJohnProxyFamily
          S hrho hrhoOne k).bodyFamily K =
        ∑ i ∈ containedIndices
            (stickyFiberContractedJohnProxyFamily
              S hrho hrhoOne k).bodyFamily K,
          volume ((stickyFiberContractedJohnProxyFamily
            S hrho hrhoOne k).tubes i).carrier := by rfl
    _ <= ∑ i ∈ containedIndices
            (stickyFiberContractedJohnProxyFamily
              S hrho hrhoOne k).bodyFamily K,
          ratio * volume (fine.tubes i.1).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact contractedJohnProxyTube_volume_le_ratio_mul_source
        (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1)
        hdeltaPos hdeltaHalf hdeltaRho
    _ = ratio *
        ∑ i ∈ containedIndices
            (stickyFiberContractedJohnProxyFamily
              S hrho hrhoOne k).bodyFamily K,
          volume (fine.tubes i.1).carrier := by
      rw [Finset.mul_sum]
    _ <= ratio *
        ∑ i ∈ containedIndices (S.fiberFamily k.1) Kpre,
          volume (fine.tubes i.1).carrier := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset hsubset) bot_le
    _ = ratio * containedMass (S.fiberFamily k.1) Kpre := by rfl
    _ <= ratio * (C * volume (Kpre : Set Space)) := by
      exact mul_le_mul_of_nonneg_left (hKT Kpre) bot_le
    _ = stickyFiberContractedJohnProxyKatzTaoConstant
          S hrho hrhoOne k C * volume (K : Set Space) := by
      rw [volume_eq_affineJacobian_mul_preimage e K]
      change ratio * (C * volume (Kpre : Set Space)) =
        (ratio * C / affineJacobian e) *
          (affineJacobian e * volume (Kpre : Set Space))
      calc
        ratio * (C * volume (Kpre : Set Space)) =
            (ratio * C) * volume (Kpre : Set Space) := by ac_rfl
        _ = ((ratio * C / affineJacobian e) * affineJacobian e) *
              volume (Kpre : Set Space) := by
          rw [ENNReal.div_mul_cancel hJ0 hJTop]
        _ = (ratio * C / affineJacobian e) *
              (affineJacobian e * volume (Kpre : Set Space)) := by ac_rfl

/-- Fully automatic specialization from global source Katz--Tao control. -/
theorem stickyFiberContractedJohnProxyFamily_isKatzTao_of_global
    {delta rho : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdeltaRho : delta <= rho)
    (k : {k // k ∈ S.activeCoarse}) {C : ENNReal}
    (hKT : IsKatzTao C fine.bodyFamily) :
    IsKatzTao
      (stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C)
      (stickyFiberContractedJohnProxyFamily
        S hrho hrhoOne k).bodyFamily := by
  apply stickyFiberContractedJohnProxyFamily_isKatzTao
    S hrho hrhoOne hdeltaPos hdeltaHalf hdeltaRho k
  exact stickyFiberSourceFamily_isKatzTao_of_global S Y k.1 hKT

#print axioms contractedJohnProxyTube_volume_le_ratio_mul_source
#print axioms stickyFiberSourceFamily_isKatzTao_of_global
#print axioms stickyFiberContractedJohnProxyFamily_isKatzTao
#print axioms stickyFiberContractedJohnProxyFamily_isKatzTao_of_global

end
end Family8StickyFiberContractedJohnProxyKatzTaoV2
