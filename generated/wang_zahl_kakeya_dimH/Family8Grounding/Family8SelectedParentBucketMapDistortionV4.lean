import Family8Grounding.Family8SelectedParentBucketMapDistortionV1

set_option autoImplicit false
set_option warningAsError true

open scoped NNReal InnerProductSpace

namespace Family8SelectedParentBucketMapDistortionV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8SelectedParentJohnFrameNormalizationV9

noncomputable section

/-- Namespace-stable export of the generic forward John-map bound. -/
theorem positiveJohnFrame_linear_norm_le_three_div_of_side_lower
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (m : NNReal)
    (hm : 0 < m) (hside : ∀ j, m ≤ J.side j) (v : Space) :
    ‖J.affineEquiv.linear v‖ ≤ (3 / (m : Real)) * ‖v‖ :=
  Family8SelectedParentBucketMapDistortionV1.PositiveJohnFrame.linear_norm_le_three_div_of_side_lower J m hm hside v

#print axioms positiveJohnFrame_linear_norm_le_three_div_of_side_lower

end
end Family8SelectedParentBucketMapDistortionV4
