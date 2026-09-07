import Family8Grounding.Family8StickyFiberContractedJohnProxyKatzTaoV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Mathlib.Tactic

/-!
# Katz--Tao transport for one retained Sticky fibre subtype

The source hypothesis and target proxy use the same literal selected indices.
This is the subtype version of the full-fibre contracted-John transport; no
unselected tube is reintroduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberContractedJohnProxyKatzTaoV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Katz--Tao control on a literal selected source fibre transports to the
same selected genuine contracted-John proxy, with the usual volume-ratio and
inverse-Jacobian constant. -/
theorem selectedFiberContractedJohnProxy_isKatzTao
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hdeltaRho : delta ≤ rho)
    (k : {k // k ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber k.1})
    {C : ENNReal}
    (hKT : IsKatzTao C
      (activeSubtypeFamily (S.fiberFamily k.1) selected)) :
    IsKatzTao
      (stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C)
      (restrictActualTubeDatum
        (stickyFiberContractedJohnProxyDatum
          S Y hrho hrhoOne k) selected).family.bodyFamily := by
  classical
  intro K
  unfold IsKatzTaoAt
  let e : Space ≃ᵃ[Real] Space :=
    stickyFiberContractedJohnAffineEquiv S hrho hrhoOne k
  let Kpre : ConvexBody Space := affinePreimageConvexBody e K
  let ratio : ENNReal := contractedJohnProxyVolumeRatio delta rho
  have hsubset :
      containedIndices
          (restrictActualTubeDatum
            (stickyFiberContractedJohnProxyDatum
              S Y hrho hrhoOne k) selected).family.bodyFamily K ⊆
        containedIndices
          (activeSubtypeFamily (S.fiberFamily k.1) selected) Kpre := by
    intro i hi
    rw [mem_containedIndices] at hi ⊢
    change (fine.tubes i.1.1).carrier ⊆ e.symm '' (K : Set Space)
    apply (affineImage_subset_iff_subset_preimage
      e (fine.tubes i.1.1).carrier (K : Set Space)).mp
    change
      (contractedJohnProxyTube (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1.1)).carrier ⊆
        (K : Set Space) at hi
    exact (image_child_carrier_subset_contractedJohnProxyTube
      (S.coarse.tubes k.1) hrho
      (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
        S hrho hrhoOne k) (fine.tubes i.1.1)
      (S.fiber_carrier_subset_parent k.1 i.1)).trans hi
  have hJ0 : affineJacobian e ≠ 0 := (affineJacobian_pos e).ne'
  have hJTop : affineJacobian e ≠ ∞ := affineJacobian_ne_top e
  calc
    containedMass
        (restrictActualTubeDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k) selected).family.bodyFamily K =
        ∑ i ∈ containedIndices
            (restrictActualTubeDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne k) selected).family.bodyFamily K,
          volume
            ((restrictActualTubeDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne k) selected).family.tubes i).carrier := by
      rfl
    _ ≤ ∑ i ∈ containedIndices
            (restrictActualTubeDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne k) selected).family.bodyFamily K,
          ratio * volume (fine.tubes i.1.1).carrier := by
      apply Finset.sum_le_sum
      intro i _hi
      exact contractedJohnProxyTube_volume_le_ratio_mul_source
        (S.coarse.tubes k.1) hrho
        (Family8TubeJohnUnitRescalingGeometryLeOneV7.StickyScaleCover.tubeJohnWitnessLeOne
          S hrho hrhoOne k) (fine.tubes i.1.1)
        hdeltaPos hdeltaHalf hdeltaRho
    _ = ratio *
        ∑ i ∈ containedIndices
            (restrictActualTubeDatum
              (stickyFiberContractedJohnProxyDatum
                S Y hrho hrhoOne k) selected).family.bodyFamily K,
          volume (fine.tubes i.1.1).carrier := by
      rw [Finset.mul_sum]
    _ ≤ ratio *
        ∑ i ∈ containedIndices
            (activeSubtypeFamily (S.fiberFamily k.1) selected) Kpre,
          volume (fine.tubes i.1.1).carrier := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset hsubset) bot_le
    _ = ratio * containedMass
        (activeSubtypeFamily (S.fiberFamily k.1) selected) Kpre := by
      rfl
    _ ≤ ratio * (C * volume (Kpre : Set Space)) := by
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

#print axioms selectedFiberContractedJohnProxy_isKatzTao

end
end Family8StickySelectedFiberContractedJohnProxyKatzTaoV2
