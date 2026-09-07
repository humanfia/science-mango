import Family8Grounding.Family8PaperFullCanonicalGroundingV78
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3

/-!
# Full canonical paper-strength Family 8 grounding bundle, V79

This checkpoint adds the fixed-positive numerical gate from Section 8.
For a paper parameter ladder, the decrement

`nu = eta 0`

is positive, independent of the selected scale and stage, and bounded by
every later ladder exponent.  Two outside Frostman losses costing at most
`delta^(-3 * eta j)` are absorbed by the middle
`delta^(10 * eta j)` gain.  The remaining positive power pays for the fixed
shift from `gamma` to `gamma - nu`, including the genuine source-volume
floor, without requiring `nu` to fit inside an arbitrarily small epsilon
gap.

The remaining substantive producer is geometric: on one actual three-scale
refinement it must supply the outside-loss bound and the middle positive
gain, then transport that same-data estimate back to the source shading.
-/
