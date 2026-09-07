import Family8Grounding.Family8PaperFullCanonicalGroundingV74
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8NormalizedCrossingFrozenComparableAdapterV3

/-!
# Full canonical paper-strength Family 8 grounding bundle, V75

This checkpoint adds the callback-free path from a literal Sticky scale
cover to the collision-free frozen comparable-multiplicity assembly.  It also
specializes that path to the exact coherent interval cover returned by the
normalized first-crossing theorem.  The selected cover is converted to an
actual `CoarseTubePartition`; source mass and density are retained with the
explicit polylogarithmic loss, and the final same-data refinement is bounded
by four times the product of its actual frozen coarse and surviving-fibre
average multiplicities.

The crossing selector itself carries no shading.  Accordingly, the
specialized theorem retains only the necessary input that the supplied
lower-scale shading has nonzero mass on the literal active fine set.  It does
not assume an almost-cover cost, `lotsOfUinW`, or any target retention or
average-multiplicity conclusion.
-/
