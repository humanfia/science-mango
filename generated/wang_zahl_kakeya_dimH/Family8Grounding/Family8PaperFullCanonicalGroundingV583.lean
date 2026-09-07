import Family8Grounding.Family8PaperFullCanonicalGroundingV582
import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1

/-!
# Full canonical grounding interface checkpoint V583

The public scale-only joint selector is now connected to the fresh greedy
restriction.  One literal choice tuple produces a nonempty admissible
eighth-normalized refinement with retained cardinality and shading mass,
Katz--Tao control, restricted full-catalogue Convex Wolff control, and the
source-to-selected average-multiplicity comparison.

This is the verified refinement/CWA connector required on the Family 7 lane.
The remaining scalar payments and the selected outer Equation (45), together
with the labelled-slab large-`b` lane, are still downstream.  No Family 8
closure is claimed here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV583

#print axioms
  Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1.exists_scaleOnlyJointChoice_refinement_CWA

end Family8PaperFullCanonicalGroundingV583
