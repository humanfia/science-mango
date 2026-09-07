import Family8Grounding.Family8PaperFullCanonicalGroundingV315
import Family8Grounding.Family8FiniteRigidMotionOrthogonalActionV2

/-!
# Family 8 full canonical grounding checkpoint V316

The normalized Haar element of `O(3)` is now converted, without a supplied
action or surjectivity premise, into the repository's actual rigid-motion
type.  The star-algebra equivalence sends the orthogonal matrix to a unitary
continuous linear map, and Mathlib's unitary equivalence supplies the linear
isometry and inverse.  Evaluation at zero and preservation of every vector
norm are available for the subsequent orbit-law and direction-cap estimate.
-/
