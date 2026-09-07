import Family8Grounding.Family8ContractedJohnEighthProxyCarrierMonoV1
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8StickyActiveCoarseB2SupportV5
open Family8TubeJohnContractedLipschitzV1

noncomputable section

/-!
# Center gap for actual selected-ancestor proxy tubes

Nested source axes have midpoints within three containing radii.  The common
contracted-John map has Lipschitz constant `3/(8*rho)`, and the final eighth
dilation contributes one more factor `1/8`.  Hence the centers of the genuine
normalized proxy axes are within `9*tau/(64*rho)`.
-/

/-- An affine map sends the source axis midpoint to the midpoint of its two
mapped endpoints. -/
theorem affineImageAxisCenter_eq_map_tubeAxisMidpoint
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta) :
    affineImageAxisCenter e T = e (tubeAxisMidpoint T) := by
  have hendpoint :
      e T.axis.endpoint = e T.axis.base + e.linear T.axis.direction := by
    rw [show T.axis.endpoint = T.axis.direction +ᵥ T.axis.base by
      simp only [UnitSegment.endpoint, vadd_eq_add]
      abel]
    rw [e.map_vadd]
    simp only [vadd_eq_add]
    abel
  have hmidpoint :
      e (tubeAxisMidpoint T) =
        e T.axis.base + (1 / 2 : Real) • e.linear T.axis.direction := by
    rw [show tubeAxisMidpoint T =
      ((1 / 2 : Real) • T.axis.direction) +ᵥ T.axis.base by
        simp only [tubeAxisMidpoint, vadd_eq_add]
        abel]
    rw [e.map_vadd, map_smul]
    simp only [vadd_eq_add]
    abel
  rw [affineImageAxisCenter, hendpoint, hmidpoint]
  module

/-- The midpoint of the genuine normalized proxy axis is the literal eighth
dilation of the mapped source midpoint. -/
theorem contractedJohnEighthProxyTube_midpoint
    {delta rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) :
    tubeAxisMidpoint (contractedJohnEighthProxyTube P hrho w T) =
      eighthDilationPoint
        (contractedTubeJohnAffineEquiv P hrho w (tubeAxisMidpoint T)) := by
  rw [← affineImageAxisCenter_eq_map_tubeAxisMidpoint
    (contractedTubeJohnAffineEquiv P hrho w) T]
  simp only [tubeAxisMidpoint, contractedJohnEighthProxyTube,
    eighthNormalizedTube, eighthNormalizedAxis,
    contractedJohnProxyTube, affineImageUnitExtensionAxis,
    eighthDilationPoint]
  module

/-- Eighth dilation scales every distance by exactly `1/8`. -/
theorem dist_eighthDilationPoint
    (x y : Space) :
    dist (eighthDilationPoint x) (eighthDilationPoint y) =
      (1 / 8 : Real) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub :
      eighthDilationPoint x - eighthDilationPoint y =
        (1 / 8 : Real) • (x - y) := by
    simp only [eighthDilationPoint]
    module
  rw [hsub, norm_smul, Real.norm_eq_abs]
  norm_num

/-- Actual source carrier nesting gives the explicit center gap used by the
normalized-axis containing-tube producer. -/
theorem dist_contractedJohnEighthProxyTube_midpoint_le
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (w : JohnAxisWitness P.body) (T : Tube delta) (U : Tube tau)
    (hTU : T.carrier ⊆ U.carrier) :
    dist (tubeAxisMidpoint (contractedJohnEighthProxyTube P hrho w T))
        (tubeAxisMidpoint (contractedJohnEighthProxyTube P hrho w U)) <=
      9 * (tau : Real) / (64 * (rho : Real)) := by
  have hsource :
      dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) <=
        3 * (tau : Real) :=
    by
      have hmidpointEq {s : NNReal} (V : Tube s) :
          Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint V =
            Family8CommonPointTubePackingV1.tubeAxisMidpoint V := by
        unfold
          Family8FiniteRandomRigidMotionB2NormalizationCoreV1.tubeAxisMidpoint
          Family8CommonPointTubePackingV1.tubeAxisMidpoint
        congr 2
        norm_num
      rw [hmidpointEq T, hmidpointEq U]
      exact dist_tubeAxisMidpoint_le_three_mul_of_axis_subset_carrier
        T U (T.axis_subset_carrier.trans hTU)
  have haffine :
      dist
          (contractedTubeJohnAffineEquiv P hrho w (tubeAxisMidpoint T))
          (contractedTubeJohnAffineEquiv P hrho w (tubeAxisMidpoint U)) <=
        (3 / (8 * (rho : Real))) *
          dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) :=
    contractedTubeJohnAffineEquiv_dist_le
      P hrho w (tubeAxisMidpoint T) (tubeAxisMidpoint U)
  rw [contractedJohnEighthProxyTube_midpoint,
    contractedJohnEighthProxyTube_midpoint,
    dist_eighthDilationPoint]
  calc
    (1 / 8 : Real) *
        dist
          (contractedTubeJohnAffineEquiv P hrho w (tubeAxisMidpoint T))
          (contractedTubeJohnAffineEquiv P hrho w (tubeAxisMidpoint U)) <=
      (1 / 8 : Real) *
        ((3 / (8 * (rho : Real))) *
          dist (tubeAxisMidpoint T) (tubeAxisMidpoint U)) := by
        gcongr
    _ <= (1 / 8 : Real) *
        ((3 / (8 * (rho : Real))) * (3 * (tau : Real))) := by
      gcongr
    _ = 9 * (tau : Real) / (64 * (rho : Real)) := by
      have hrhoReal : (rho : Real) ≠ 0 := by exact_mod_cast hrho.ne'
      field_simp [hrhoReal]
      ring

#print axioms affineImageAxisCenter_eq_map_tubeAxisMidpoint
#print axioms contractedJohnEighthProxyTube_midpoint
#print axioms dist_eighthDilationPoint
#print axioms dist_contractedJohnEighthProxyTube_midpoint_le

end
end Family8ContractedJohnEighthProxySelectedAncestorCenterGapV1
