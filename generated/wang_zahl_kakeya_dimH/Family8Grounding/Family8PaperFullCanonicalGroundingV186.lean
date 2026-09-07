import Family8Grounding.Family8PaperFullCanonicalGroundingV185
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostCarrierV1

/-!
# Family 8 full canonical grounding checkpoint V186

The selected-parent normalization can now be centered at the half-scaled
chosen-plank center while retaining the same fixed parent `W`.  Translation
leaves the axis vector, Jacobian, and operator norm unchanged.  The resulting
literal proxy has unit-bounded axis and center, contains the actual transformed
fine carrier under the transverse-radius premise, and is automatically
supported in the radius-two ball whenever its proxy scale is at most one half.

This closes the geometric `B2` seam.  Exact shading-mass transport and the
same-selected Katz--Tao consumer are connected in successor modules.
-/
