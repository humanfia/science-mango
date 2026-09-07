import Family8Grounding.Family8PaperFullCanonicalGroundingV81
import Family8Grounding.Family8NonzeroMassParameterEndpointOrchestrationV3
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Family8Grounding.Family8FullRefinementActualDatumV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V82

This checkpoint removes three further bookkeeping seams around the actual
three-scale argument:

* zero source mass and the terminal half-scale cap are discharged before the
  geometric producer is called;
* the ambient active-fine restriction, its literal subtype shading, and the
  final frozen refinement are connected by exact union/average identities;
* any admissible Frostman datum may be replaced by a definitionally identical
  full-refinement datum.  Its Sticky active-fine set is the whole finite
  family, and Frostman density automatically supplies nonzero active mass.

The remaining work is therefore confined to producing the two rescaled outer
Frostman bounds and the middle gain on this common actual data, together with
the explicit small-power absorption of the recorded refinement loss.
-/
