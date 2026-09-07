import Family8Grounding.Family8PaperFullCanonicalGroundingV50
import Family8Grounding.Family8GreedyHighPrefixActualOccurrenceV1

/-!
# Full canonical paper-strength Family 8 grounding bundle, V51

This checkpoint strengthens the factor-two high/low split to literal actual
greedy occurrences.  In the low branch the selected restricted datum retains
the sharp Katz--Tao bound and loses at most two in shading mass and average
multiplicity.  In the high branch the retained actual prefix has the same
factor-two guarantees, and every retained fine index is assigned to an
explicit earlier greedy block whose real winning convex body has density
greater than `A`; that block restriction is admissible and is genuinely
`IsFrostmanIn 1` in the winning body.

This is the source-production dichotomy needed by the two downstream
geometric routes.  It does not assert an unconditional sharp Katz--Tao bound
or pass a desired multiplicity conclusion as data.
-/
