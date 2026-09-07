import Family8Grounding.Family8ContractedJohnEighthProxyAxisGapCoreV1
import Family8Grounding.Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1
import Family8Grounding.Family8TubeJohnContractedAxisLengthLowerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyAxisGapCoreV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8TubeJohnContractedAxisLengthLowerV1
open Family8TubeJohnContractedLipschitzV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-!
# Actual selected-ancestor axis gap for contracted-John/eighth proxies

Source carrier nesting gives unoriented source-direction error `6 * tau`.
The common contracted John map sends this to raw-vector error
`9 * tau / (4 * rho)`.  The honest `1/108` transformed-axis lower bound and
the generic normalization lemma then give direction error `486 * tau / rho`.
Together with the proved midpoint error `9 * tau / (64 * rho)`, the complete
normalized child axis lies in the parent-axis thickening of radius
`15561 * tau / (64 * rho)`.

The final tube statement uses a genuine buffered parent.  Its only remaining
input is the explicit scalar comparison between that axis gap and the chosen
buffer; no axis-nesting premise is fed back into the producer.
-/

/-- The common contracted-John map transports the source unoriented direction
error to a raw affine-image-vector error. -/
theorem affineImageAxisVector_contracted_unoriented_close_of_carrier_subset
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hTU : T.carrier ⊆ U.carrier) :
    ‖affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) T -
        affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) U‖ <=
          9 * (tau : Real) / (4 * (rho : Real)) ∨
      ‖affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) T +
        affineImageAxisVector (contractedTubeJohnAffineEquiv P hrho w) U‖ <=
          9 * (tau : Real) / (4 * (rho : Real)) := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hsource : UnorientedDirectionClose T.axis U.axis
      (6 * (tau : Real)) :=
    UnorientedDirectionClose.symm
      (Tube.unorientedDirectionClose_of_commonSegment
        U T.axis (T.axis_subset_carrier.trans hTU))
  have hlinear (a b : Space) (hab : ‖a - b‖ <= 6 * (tau : Real)) :
      ‖e.linear a - e.linear b‖ <=
        9 * (tau : Real) / (4 * (rho : Real)) := by
    have hmap := contractedTubeJohnAffineEquiv_dist_le P hrho w a b
    have heSub : e a - e b = e.linear (a - b) := by
      simpa only [vsub_eq_sub, AffineEquiv.coe_toAffineMap,
        AffineEquiv.linear_toAffineMap, LinearEquiv.coe_coe] using
          (e.toAffineMap.linearMap_vsub a b).symm
    have hlinearSub : e.linear a - e.linear b = e.linear (a - b) := by
      rw [map_sub]
    rw [dist_eq_norm, dist_eq_norm, heSub] at hmap
    rw [hlinearSub]
    calc
      ‖e.linear (a - b)‖ <=
          (3 / (8 * (rho : Real))) * ‖a - b‖ := hmap
      _ <= (3 / (8 * (rho : Real))) * (6 * (tau : Real)) := by
        exact mul_le_mul_of_nonneg_left hab (by positivity)
      _ = 9 * (tau : Real) / (4 * (rho : Real)) := by
        have hrhoReal : (rho : Real) ≠ 0 := by exact_mod_cast hrho.ne'
        field_simp [hrhoReal]
        ring
  rcases hsource with hforward | hreverse
  · left
    rw [affineImageAxisVector_eq_linear,
      affineImageAxisVector_eq_linear]
    exact hlinear T.axis.direction U.axis.direction hforward
  · right
    rw [affineImageAxisVector_eq_linear,
      affineImageAxisVector_eq_linear]
    have hneg := hlinear T.axis.direction (-U.axis.direction) (by
      simpa only [sub_neg_eq_add] using hreverse)
    simpa only [map_neg, sub_neg_eq_add] using hneg

/-- The actual normalized proxy directions are close up to sign with the
explicit scale-ratio constant `486`. -/
theorem contractedJohnEighthProxyTube_unorientedDirectionClose
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (hTU : T.carrier ⊆ U.carrier) :
    UnorientedDirectionClose
      (contractedJohnEighthProxyTube P hrho w T).axis
      (contractedJohnEighthProxyTube P hrho w U).axis
      (486 * (tau : Real) / (rho : Real)) := by
  let e := contractedTubeJohnAffineEquiv P hrho w
  have hraw :
      ‖affineImageAxisVector e T - affineImageAxisVector e U‖ <=
          9 * (tau : Real) / (4 * (rho : Real)) ∨
      ‖affineImageAxisVector e T + affineImageAxisVector e U‖ <=
          9 * (tau : Real) / (4 * (rho : Real)) := by
    simpa only [e] using
      affineImageAxisVector_contracted_unoriented_close_of_carrier_subset
        P hrho w T U hTU
  have hTLower : (1 / 108 : Real) <= ‖affineImageAxisVector e T‖ := by
    simpa only [e] using
      one_div_oneHundredEight_le_norm_affineImageAxisVector_contracted
        P hrho hrhoOne w T
  have hULower : (1 / 108 : Real) <= ‖affineImageAxisVector e U‖ := by
    simpa only [e] using
      one_div_oneHundredEight_le_norm_affineImageAxisVector_contracted
        P hrho hrhoOne w U
  have hnormalized := affineImageAxis_unorientedDirectionClose_of_raw
    e T U (ell := (1 / 108 : Real))
      (eps := 9 * (tau : Real) / (4 * (rho : Real)))
      (by norm_num) hTLower hULower hraw
  have hconstant :
      2 * (9 * (tau : Real) / (4 * (rho : Real))) / (1 / 108 : Real) =
        486 * (tau : Real) / (rho : Real) := by
    have hrhoReal : (rho : Real) ≠ 0 := by exact_mod_cast hrho.ne'
    field_simp [hrhoReal] ; ring
  have hdirT :
      (contractedJohnEighthProxyTube P hrho w T).axis.direction =
        (affineImageUnitExtensionAxis e T).direction := rfl
  have hdirU :
      (contractedJohnEighthProxyTube P hrho w U).axis.direction =
        (affineImageUnitExtensionAxis e U).direction := rfl
  unfold UnorientedDirectionClose at hnormalized ⊢
  rw [hdirT, hdirU, ← hconstant]
  exact hnormalized

/-- The canonical nonnegative axis gap for one source ancestor scale. -/
def contractedJohnEighthSelectedAncestorAxisGap
    (tau rho : NNReal) : NNReal :=
  (15561 * tau) / (64 * rho)

@[simp]
theorem coe_contractedJohnEighthSelectedAncestorAxisGap
    (tau rho : NNReal) :
    (contractedJohnEighthSelectedAncestorAxisGap tau rho : Real) =
      15561 * (tau : Real) / (64 * (rho : Real)) := by
  simp only [contractedJohnEighthSelectedAncestorAxisGap,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]

/-- Source carrier nesting alone now produces the explicit normalized-axis
thickening required by the buffered carrier theorem. -/
theorem contractedJohnEighthProxyTube_axis_subset_selectedAncestorGap
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (hTU : T.carrier ⊆ U.carrier) :
    (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
      Metric.cthickening
        (contractedJohnEighthSelectedAncestorAxisGap tau rho : Real)
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier := by
  have hmidpointEq {s : NNReal} (V : Tube s) :
      Family8CommonPointTubePackingV1.tubeAxisMidpoint V =
        Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint V := by
    unfold Family8CommonPointTubePackingV1.tubeAxisMidpoint
      Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint
    congr 2
    norm_num
  have hmid :
      dist
          (Family8CommonPointTubePackingV1.tubeAxisMidpoint
            (contractedJohnEighthProxyTube P hrho w T))
          (Family8CommonPointTubePackingV1.tubeAxisMidpoint
            (contractedJohnEighthProxyTube P hrho w U)) <=
        9 * (tau : Real) / (64 * (rho : Real)) := by
    rw [hmidpointEq, hmidpointEq]
    exact dist_contractedJohnEighthProxyTube_midpoint_le
      P hrho w T U hTU
  apply
    Family8ContractedJohnEighthProxyAxisGapCoreV1.Tube.axis_carrier_subset_cthickening_of_midpoint_unorientedDirectionClose
      (contractedJohnEighthProxyTube P hrho w T)
      (contractedJohnEighthProxyTube P hrho w U)
      hmid
      (contractedJohnEighthProxyTube_unorientedDirectionClose
        P hrho hrhoOne w T U hTU)
  rw [coe_contractedJohnEighthSelectedAncestorAxisGap]
  have hrhoReal : (rho : Real) ≠ 0 := by exact_mod_cast hrho.ne'
  field_simp [hrhoReal]
  ring_nf
  exact le_rfl

/-- The earliest remaining scalar seam: once the chosen parent buffer is at
least the explicit axis gap, radius monotonicity and the verified CarrierMono
consumer give full child-proxy containment. -/
theorem contractedJohnEighthProxyTube_subset_selectedAncestorContainingTube
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (hdeltaTau : delta <= tau)
    (hTU : T.carrier ⊆ U.carrier) (buffer : NNReal)
    (haxisGapBuffer :
      contractedJohnEighthSelectedAncestorAxisGap tau rho <= buffer) :
    (contractedJohnEighthProxyTube P hrho w T).carrier ⊆
      (contractedJohnEighthProxyContainingTube
        P hrho w U buffer).carrier := by
  apply contractedJohnEighthProxyTube_subset_containingTube_of_axisGap
    P hrho w T U
      (contractedJohnEighthSelectedAncestorAxisGap tau rho) buffer
      (contractedJohnEighthProxyTube_axis_subset_selectedAncestorGap
        P hrho hrhoOne w T U hTU)
  exact add_le_add
    (contractedJohnEighthProxyRadius_mono hdeltaTau) haxisGapBuffer

/-- Complete positive ledger for a selected source ancestor and its honest
buffered normalized proxy. -/
structure ContractedJohnEighthSelectedAncestorBufferedStep
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (buffer : NNReal) : Prop where
  delta_le_tau : delta <= tau
  tau_le_root : tau <= rho
  source_carrier_subset : T.carrier ⊆ U.carrier
  ancestor_carrier_subset_root : U.carrier ⊆ P.carrier
  proxy_direction_close :
    UnorientedDirectionClose
      (contractedJohnEighthProxyTube P hrho w T).axis
      (contractedJohnEighthProxyTube P hrho w U).axis
      (486 * (tau : Real) / (rho : Real))
  proxy_axis_subset_gap :
    (contractedJohnEighthProxyTube P hrho w T).axis.carrier ⊆
      Metric.cthickening
        (contractedJohnEighthSelectedAncestorAxisGap tau rho : Real)
        (contractedJohnEighthProxyTube P hrho w U).axis.carrier
  literal_image_subset_parentProxy :
    contractedJohnEighthCarrierImage P hrho w T ⊆
      (contractedJohnEighthProxyTube P hrho w U).carrier
  actual_proxy_subset_buffered_parent :
    (contractedJohnEighthProxyTube P hrho w T).carrier ⊆
      (contractedJohnEighthProxyContainingTube
        P hrho w U buffer).carrier

/-- Producer for the full selected-ancestor ledger.  The only extra premise
beyond source hierarchy data is the displayed scalar buffer comparison. -/
theorem contractedJohnEighthSelectedAncestorBufferedStep_of_source
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (buffer : NNReal)
    (hdeltaTau : delta <= tau) (htauRho : tau <= rho)
    (hTU : T.carrier ⊆ U.carrier) (hUP : U.carrier ⊆ P.carrier)
    (haxisGapBuffer :
      contractedJohnEighthSelectedAncestorAxisGap tau rho <= buffer) :
    ContractedJohnEighthSelectedAncestorBufferedStep
      P hrho hrhoOne w T U buffer where
  delta_le_tau := hdeltaTau
  tau_le_root := htauRho
  source_carrier_subset := hTU
  ancestor_carrier_subset_root := hUP
  proxy_direction_close :=
    contractedJohnEighthProxyTube_unorientedDirectionClose
      P hrho hrhoOne w T U hTU
  proxy_axis_subset_gap :=
    contractedJohnEighthProxyTube_axis_subset_selectedAncestorGap
      P hrho hrhoOne w T U hTU
  literal_image_subset_parentProxy :=
    contractedJohnEighthCarrierImage_subset_ancestorProxy
      P hrho w T U hTU hUP
  actual_proxy_subset_buffered_parent :=
    contractedJohnEighthProxyTube_subset_selectedAncestorContainingTube
      P hrho hrhoOne w T U hdeltaTau hTU buffer haxisGapBuffer

#print axioms affineImageAxisVector_contracted_unoriented_close_of_carrier_subset
#print axioms contractedJohnEighthProxyTube_unorientedDirectionClose
#print axioms contractedJohnEighthSelectedAncestorAxisGap
#print axioms contractedJohnEighthProxyTube_axis_subset_selectedAncestorGap
#print axioms contractedJohnEighthProxyTube_subset_selectedAncestorContainingTube
#print axioms ContractedJohnEighthSelectedAncestorBufferedStep
#print axioms contractedJohnEighthSelectedAncestorBufferedStep_of_source

end
end Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
