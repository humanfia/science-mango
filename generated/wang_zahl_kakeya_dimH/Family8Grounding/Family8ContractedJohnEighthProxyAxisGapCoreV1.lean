import Family8Grounding.Family8CommonPointTubePackingV1
import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import FamilyStickyGrounding.FamilyStickyTubeParentDirectionCoherenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnEighthProxyAxisGapCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CommonPointTubePackingV1
open Family8ContractedJohnActualTubeProxyV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Generic positive axis-gap geometry for actual normalized proxies

The two lemmas below isolate the Euclidean geometry needed after a common
affine map.  A lower bound for the two raw image-vector lengths turns raw
closeness, up to sign, into closeness of their normalized directions.  A
midpoint bound and that unoriented direction bound then put the complete unit
axis in an explicit thickening of the other unit axis.

No John inverse estimate is assumed or manufactured here: downstream code
must supply the honest raw-vector lower bound for the map it uses.
-/

/-- Normalizing two nonzero vectors loses at most the factor `2 / ell` when
the first vector has norm at least `ell`. -/
theorem norm_invNorm_smul_sub_invNorm_smul_le
    (v w : Space) {ell eps : Real}
    (hv : v ≠ 0) (hw : w ≠ 0) (hellPos : 0 < ell)
    (hvLower : ell <= ‖v‖) (hraw : ‖v - w‖ <= eps) :
    ‖‖v‖⁻¹ • v - ‖w‖⁻¹ • w‖ <= 2 * eps / ell := by
  have hvPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwPos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have heps : 0 <= eps := (norm_nonneg (v - w)).trans hraw
  have hnormDiff : |‖w‖ - ‖v‖| <= ‖v - w‖ := by
    have hvTriangle : ‖v‖ <= ‖v - w‖ + ‖w‖ := by
      calc
        ‖v‖ = ‖(v - w) + w‖ := by congr 1; module
        _ <= ‖v - w‖ + ‖w‖ := norm_add_le _ _
    have hwTriangle : ‖w‖ <= ‖v - w‖ + ‖v‖ := by
      calc
        ‖w‖ = ‖(w - v) + v‖ := by congr 1; module
        _ <= ‖w - v‖ + ‖v‖ := norm_add_le _ _
        _ = ‖v - w‖ + ‖v‖ := by rw [norm_sub_rev]
    rw [abs_le]
    constructor <;> linarith
  have hinvDiff :
      |‖v‖⁻¹ - ‖w‖⁻¹| * ‖w‖ =
        |‖w‖ - ‖v‖| / ‖v‖ := by
    have hfrac : ‖v‖⁻¹ - ‖w‖⁻¹ =
        (‖w‖ - ‖v‖) / (‖v‖ * ‖w‖) := by
      field_simp [hvPos.ne', hwPos.ne']
    rw [hfrac, abs_div, abs_of_pos (mul_pos hvPos hwPos)]
    field_simp [hvPos.ne', hwPos.ne']
  have hdecomp :
      ‖v‖⁻¹ • v - ‖w‖⁻¹ • w =
        ‖v‖⁻¹ • (v - w) +
          (‖v‖⁻¹ - ‖w‖⁻¹) • w := by
    module
  rw [hdecomp]
  calc
    ‖‖v‖⁻¹ • (v - w) +
        (‖v‖⁻¹ - ‖w‖⁻¹) • w‖ <=
      ‖‖v‖⁻¹ • (v - w)‖ +
        ‖(‖v‖⁻¹ - ‖w‖⁻¹) • w‖ := norm_add_le _ _
    _ = ‖v - w‖ / ‖v‖ + |‖w‖ - ‖v‖| / ‖v‖ := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvPos), hinvDiff]
      ring
    _ <= ‖v - w‖ / ‖v‖ + ‖v - w‖ / ‖v‖ := by
      gcongr
    _ = 2 * ‖v - w‖ / ‖v‖ := by ring
    _ <= 2 * eps / ell := by
      apply (div_le_div_iff₀ hvPos hellPos).2
      have hmul : ‖v - w‖ * ell <= eps * ‖v‖ := by
        exact mul_le_mul hraw hvLower (le_of_lt hellPos) heps
      nlinarith

/-- Raw image vectors which are close up to sign have normalized directions
close up to the same sign. -/
theorem normalizedVector_unoriented_close_of_raw
    (v w : Space) {ell eps : Real}
    (hv : v ≠ 0) (hw : w ≠ 0) (hellPos : 0 < ell)
    (hvLower : ell <= ‖v‖) (_hwLower : ell <= ‖w‖)
    (hraw : ‖v - w‖ <= eps ∨ ‖v + w‖ <= eps) :
    ‖‖v‖⁻¹ • v - ‖w‖⁻¹ • w‖ <= 2 * eps / ell ∨
      ‖‖v‖⁻¹ • v + ‖w‖⁻¹ • w‖ <= 2 * eps / ell := by
  rcases hraw with hforward | hreverse
  · exact Or.inl
      (norm_invNorm_smul_sub_invNorm_smul_le
        v w hv hw hellPos hvLower hforward)
  · right
    have hneg : -w ≠ 0 := neg_ne_zero.mpr hw
    have hrawNeg : ‖v - (-w)‖ <= eps := by
      simpa only [sub_neg_eq_add] using hreverse
    have h := norm_invNorm_smul_sub_invNorm_smul_le
      v (-w) hv hneg hellPos hvLower hrawNeg
    simpa only [norm_neg, smul_neg, sub_neg_eq_add] using h

/-- The vector lemma specialized to the normalized directions of two affine
image-axis extensions. -/
theorem affineImageAxis_unorientedDirectionClose_of_raw
    {delta tau : NNReal} (e : Space ≃ᵃ[Real] Space)
    (T : Tube delta) (U : Tube tau) {ell eps : Real}
    (hellPos : 0 < ell)
    (hTLower : ell <= ‖affineImageAxisVector e T‖)
    (hULower : ell <= ‖affineImageAxisVector e U‖)
    (hraw :
      ‖affineImageAxisVector e T - affineImageAxisVector e U‖ <= eps ∨
      ‖affineImageAxisVector e T + affineImageAxisVector e U‖ <= eps) :
    UnorientedDirectionClose
      (affineImageUnitExtensionAxis e T)
      (affineImageUnitExtensionAxis e U) (2 * eps / ell) := by
  exact normalizedVector_unoriented_close_of_raw
    (affineImageAxisVector e T) (affineImageAxisVector e U)
    (affineImageAxisVector_ne_zero e T)
    (affineImageAxisVector_ne_zero e U) hellPos hTLower hULower hraw

/-- Midpoint distance plus unoriented direction distance controls every point
of a complete unit axis.  The factor `1/2` is the maximal centered axis
parameter. -/
theorem Tube.axis_carrier_subset_cthickening_of_midpoint_unorientedDirectionClose
    {delta tau : NNReal} (T : Tube delta) (U : Tube tau)
    {centerGap directionGap axisGap : Real}
    (hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) <= centerGap)
    (hdir : UnorientedDirectionClose T.axis U.axis directionGap)
    (hbudget : centerGap + (1 / 2 : Real) * directionGap <= axisGap) :
    T.axis.carrier ⊆ Metric.cthickening axisGap U.axis.carrier := by
  intro x hx
  rw [T.axis.carrier_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htCenter : |t - (1 / 2 : Real)| <= (1 / 2 : Real) := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  rcases hdir with hforward | hreverse
  · let y := U.axis.base + t • U.axis.direction
    have hy : y ∈ U.axis.carrier :=
      U.axis.mem_carrier_of_mem_Icc ht
    apply Metric.mem_cthickening_of_dist_le
      (T.axis.base + t • T.axis.direction) y axisGap U.axis.carrier hy
    have hpointT :
        T.axis.base + t • T.axis.direction =
          tubeAxisMidpoint T +
            (t - (1 / 2 : Real)) • T.axis.direction := by
      unfold tubeAxisMidpoint
      module
    have hpointU :
        y = tubeAxisMidpoint U +
          (t - (1 / 2 : Real)) • U.axis.direction := by
      dsimp only [y]
      unfold tubeAxisMidpoint
      module
    rw [hpointT, hpointU, dist_eq_norm]
    have hvec :
        (tubeAxisMidpoint T +
            (t - (1 / 2 : Real)) • T.axis.direction) -
          (tubeAxisMidpoint U +
            (t - (1 / 2 : Real)) • U.axis.direction) =
        (tubeAxisMidpoint T - tubeAxisMidpoint U) +
          (t - (1 / 2 : Real)) •
            (T.axis.direction - U.axis.direction) := by
      module
    rw [hvec]
    calc
      ‖(tubeAxisMidpoint T - tubeAxisMidpoint U) +
          (t - (1 / 2 : Real)) •
            (T.axis.direction - U.axis.direction)‖ <=
        ‖tubeAxisMidpoint T - tubeAxisMidpoint U‖ +
          ‖(t - (1 / 2 : Real)) •
            (T.axis.direction - U.axis.direction)‖ := norm_add_le _ _
      _ = dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) +
          |t - (1 / 2 : Real)| *
            ‖T.axis.direction - U.axis.direction‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ <= centerGap + (1 / 2 : Real) * directionGap := by
        exact add_le_add hmid
          (mul_le_mul htCenter hforward (norm_nonneg _)
            (by linarith [htCenter, hforward]))
      _ <= axisGap := hbudget
  · let s : Real := 1 - t
    have hs : s ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> dsimp only [s] <;> linarith [ht.1, ht.2]
    let y := U.axis.base + s • U.axis.direction
    have hy : y ∈ U.axis.carrier :=
      U.axis.mem_carrier_of_mem_Icc hs
    apply Metric.mem_cthickening_of_dist_le
      (T.axis.base + t • T.axis.direction) y axisGap U.axis.carrier hy
    have hpointT :
        T.axis.base + t • T.axis.direction =
          tubeAxisMidpoint T +
            (t - (1 / 2 : Real)) • T.axis.direction := by
      unfold tubeAxisMidpoint
      module
    have hpointU :
        y = tubeAxisMidpoint U -
          (t - (1 / 2 : Real)) • U.axis.direction := by
      dsimp only [y, s]
      unfold tubeAxisMidpoint
      module
    rw [hpointT, hpointU, dist_eq_norm]
    have hvec :
        (tubeAxisMidpoint T +
            (t - (1 / 2 : Real)) • T.axis.direction) -
          (tubeAxisMidpoint U -
            (t - (1 / 2 : Real)) • U.axis.direction) =
        (tubeAxisMidpoint T - tubeAxisMidpoint U) +
          (t - (1 / 2 : Real)) •
            (T.axis.direction + U.axis.direction) := by
      module
    rw [hvec]
    calc
      ‖(tubeAxisMidpoint T - tubeAxisMidpoint U) +
          (t - (1 / 2 : Real)) •
            (T.axis.direction + U.axis.direction)‖ <=
        ‖tubeAxisMidpoint T - tubeAxisMidpoint U‖ +
          ‖(t - (1 / 2 : Real)) •
            (T.axis.direction + U.axis.direction)‖ := norm_add_le _ _
      _ = dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) +
          |t - (1 / 2 : Real)| *
            ‖T.axis.direction + U.axis.direction‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ <= centerGap + (1 / 2 : Real) * directionGap := by
        exact add_le_add hmid
          (mul_le_mul htCenter hreverse (norm_nonneg _)
            (by linarith [htCenter, hreverse]))
      _ <= axisGap := hbudget

#print axioms norm_invNorm_smul_sub_invNorm_smul_le
#print axioms normalizedVector_unoriented_close_of_raw
#print axioms affineImageAxis_unorientedDirectionClose_of_raw
#print axioms Tube.axis_carrier_subset_cthickening_of_midpoint_unorientedDirectionClose

end
end Family8ContractedJohnEighthProxyAxisGapCoreV1
