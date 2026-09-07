import Family8Grounding.Family8PaperFullCanonicalGroundingV367
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import Family8Grounding.Family8NormalizedLongCoreDensityAwareCanonicalSelectedFrostmanV4

/-!
# Family 8 full canonical grounding checkpoint V368

* The logarithmic parent selector now uses the actual assigned shading mass,
  retains a quantitative selected-fine shading floor, and exposes an honest
  zero-mass branch.
* The canonical long-core hierarchy now provides the exact-degree selected
  Frostman structure required by the buffered inner object, conditional only
  on its literal nonzero shading mass.

These endpoints remove the body-mass/shading-mass substitution that blocked
the long-core analytic branch.  All imported endpoints have exact builds and
only the standard Lean axioms.
-/
