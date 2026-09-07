import Family8Grounding.Family8PaperFullCanonicalGroundingV65
import Family8Grounding.Family8CanonicalExactAssemblyMassDensityRetentionV1
import Family8Grounding.Family8FullGreedyCanonicalMassDensityAssemblyV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V66

This checkpoint upgrades the finite greedy multiplicity skeleton to literal
source and final subtype families.  For the actual canonical producer, the
final family consists of the same source convex bodies, total shaded mass and
shaded union agree exactly with the ambient-index representation, and family
volume can only decrease.  The constructed retention inequality therefore
implies a genuine density lower bound on the final data.

Specializing to the automatically constructed full greedy partition removes
the source-active bookkeeping entirely: its fine set is `univ`, so the source
subtype mass, family volume, and density are exactly those of the original
shading.  With nonzero source mass, one callback-free producer now returns on
the same canonical final data the mass retention, density retention, exact
body identity, saturated final fibre, and the product of actual induced and
fibre average multiplicities.

The retained factor is still the coarse finite pigeonhole loss
`((#iota + 1)^2) * (#Option(blocks) + 1)`.  Replacing it by the paper-small
`delta^-epsilon` loss through scale-sensitive/dyadic uniformization is the
remaining quantitative part of Lemma 5.11.  The actual two-plank Córdoba
instantiations, Section 8 one-step improvement, and `mainLemmaOne` remain
open.
-/
