import Family8Grounding.Family8PaperFullCanonicalGroundingV18
import Family8Grounding.Family8DoubledParentConflictExactDegreeBudgetV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V19

This successor removes the degree-bound callback from the weighted
doubled-parent construction.  It defines the literal finite closed-conflict
neighbourhood and its exact maximum degree, proves that this is the minimal
valid public budget, and constructs the weighted selection and Def. 2.12 scale
endpoint with precisely that loss.  Bounding this explicit quantity by the
paper-size geometric loss still requires separation information not present in
a bare `StickyScaleCover`.
-/
