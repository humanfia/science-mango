import Family8Grounding.Family8PaperFullCanonicalGroundingV68
import Family8Grounding.Family8ComparableMultiplicityBucketsV1
import Family8Grounding.Family8FrozenNeighborhoodAssemblyV1
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8CoarseTubePartitionFrozenComparableAdapterV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V69

This checkpoint replaces the polynomial exact-level pigeonhole in the
Lemma 5.11 multiplicity arrangement by two constructed zero/dyadic comparable
buckets.  The source-to-final loss is now explicitly

`(log₂ (# fine) + 2) * (log₂ (# coarse) + 2)`.

The final fine family is a literal subtype of the surviving indices.  Its
mass and shaded union agree exactly with the constructed refinement, so the
same polylogarithmic bound gives genuine mass and density retention.  For
nonzero source active mass, one actual surviving fibre and the independently
frozen coarse shading realize the two dyadic bases as lower bounds for their
actual average multiplicities.  The final actual refinement therefore obeys

`averageMultiplicity ≤ 4 * outerAverage * fibreAverage`

on the same canonical data.  The `CoarseTubePartition` adapter shows that the
scale-aware logarithmic-branching output of `AlmostCoverTubeFactoring` feeds
this construction definitionally through `asConvexFactorization`; no scale,
retention, or desired-average statement is added as a callback.

The outstanding Family 8 work remains analytic/geometric rather than this
finite pigeonhole: production of the paper-strength angle/container data for
the actual selected plank bucket, followed by the two-scale Section 8
composition and `mainLemmaOne`.
-/
