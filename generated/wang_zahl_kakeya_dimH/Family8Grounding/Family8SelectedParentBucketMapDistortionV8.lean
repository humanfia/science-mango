import Family8Grounding.Family8SelectedParentBucketMapDistortionV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped NNReal InnerProductSpace BigOperators

namespace Family8SelectedParentBucketMapDistortionV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8SelectedParentBucketMapDistortionV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8

noncomputable section

theorem bucketNormalized_contractedJohn_linear_apply
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int) (v : Space) :
    (bucketNormalizedAffineEquiv (contractedJohnAffineEquiv J r hr) label).linear v =
      ((sideShapeUpper label 2 : NNReal) : Real)⁻¹ •
        ((r : Real) • J.affineEquiv.linear v) := by
  rfl

/-- Full common bucket map forward distortion under a side floor `m`. -/
theorem bucketNormalized_contractedJohn_linear_norm_le
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (m r : NNReal)
    (hm : 0 < m) (hside : ∀ j, m ≤ J.side j)
    (hr : 0 < r) (label : Fin 3 → Int) (v : Space) :
    ‖(bucketNormalizedAffineEquiv
        (contractedJohnAffineEquiv J r hr) label).linear v‖ ≤
      (3 * (r : Real) /
        ((m : Real) * (sideShapeUpper label 2 : Real))) * ‖v‖ := by
  have hu : (0 : Real) < (sideShapeUpper label 2 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have hmReal : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hJ := positiveJohnFrame_linear_norm_le_three_div_of_side_lower
    J m hm hside v
  rw [bucketNormalized_contractedJohn_linear_apply,
    norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hrReal]
  rw [abs_of_pos hu]
  calc
    (sideShapeUpper label 2 : Real)⁻¹ *
        ((r : Real) * ‖J.affineEquiv.linear v‖) ≤
      (sideShapeUpper label 2 : Real)⁻¹ *
        ((r : Real) * ((3 / (m : Real)) * ‖v‖)) := by
      gcongr
    _ = (3 * (r : Real) /
        ((m : Real) * (sideShapeUpper label 2 : Real))) * ‖v‖ := by
      field_simp [hu.ne', hmReal.ne']

#print axioms bucketNormalized_contractedJohn_linear_apply
#print axioms bucketNormalized_contractedJohn_linear_norm_le

end
end Family8SelectedParentBucketMapDistortionV8
