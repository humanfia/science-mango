import Family8Grounding.Family8PaperCanonicalGroundingV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV3
import Family8Grounding.Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV3

/-!
# Canonical paper-strength Family 8 grounding bundle, admissible-scale endpoint

This successor retains the exact clean geometric and Definition 2.12
dependency bundle from V2, then exposes the sharpened CommonPoint and automatic
conflict endpoints.  The final producer derives the normalized `1/16` radius
bound from datum admissibility, so it has no explicit `delta / 8 <= 1/100`
premise.  The failed numeric V2 draft and all scratch modules are deliberately
absent from this import graph.
-/
