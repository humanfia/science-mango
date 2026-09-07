import Family8Grounding.Family8PaperCanonicalGroundingV3
import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import Family8Grounding.Family8PaperConflictWideAnisotropicOverlapV1
import Family8Grounding.Family8PaperConflictOrientedCoreV1
import Family8Grounding.Family8PaperConflictOrientedCoordinatesV5
import Family8Grounding.Family8PaperEssentialDistinctConstantExtractionV2
import Family8Grounding.Family8PaperEssentialDistinctActualDatumConstantExtractionV3

/-!
# Full canonical paper-strength Family 8 grounding bundle, V4

This terminal subaggregate extends the admissible-scale paper bundle with the
exact-clean constant-loss conversion from the repository overlap convention
to the paper full-central-dilation convention.  Its dependency graph contains
only the canonical successors:

* anisotropic paper-conflict geometry (`V4`);
* wide anisotropic overlap and oriented seven-coordinate coding;
* scale-independent finite conflict degree and weighted greedy extraction;
* the genuine selected `ActualTubeDatum` adapter, preserving admissibility,
  full refinement, cardinality, and literal shading mass.

Earlier failed successors and the coarse delta-dependent extraction are not
imported here.
-/
