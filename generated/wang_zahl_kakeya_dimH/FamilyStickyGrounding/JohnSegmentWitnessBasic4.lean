import FamilyStickyGrounding.JohnSegmentWitnessBasic3

open scoped NNReal InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem segment_center_add_axis_eq_lineMap (p q : Space) (z : ℝ) :
    AffineMap.lineMap p q (2 : ℝ)⁻¹ +
        z • ((2 : ℝ)⁻¹ • (q - p)) =
      AffineMap.lineMap p q ((z + 1) / 2) := by
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  module

theorem segment_axis_eq_center_add (p q : Space) (t : ℝ) :
    AffineMap.lineMap p q t =
      AffineMap.lineMap p q (2 : ℝ)⁻¹ +
        (2 * t - 1) • ((2 : ℝ)⁻¹ • (q - p)) := by
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  module

#print axioms segment_center_add_axis_eq_lineMap
#print axioms segment_axis_eq_center_add

end
end Submission.Kakeya.ConvexGeometry
