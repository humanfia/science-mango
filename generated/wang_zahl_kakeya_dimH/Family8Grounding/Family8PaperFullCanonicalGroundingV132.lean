import Family8Grounding.Family8PaperFullCanonicalGroundingV131
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3

/-!
# Family 8 full canonical grounding checkpoint V132

This import-only checkpoint extends V131 with the audited cross-center
consumer for the concrete-Q/P high branch.  A pointwise estimate for each
literal local right-hand side, together with a bound for the sum of its
packing coefficients, now yields
`sourceMass / 2 <= totalCoefficient * volume D.physical.base`.
The interface keeps the actual projected physical mass and is uniform in
the dependent local `Q/P` proof; it does not assume the desired global
conclusion.  Constructing the two genuine packing estimates remains an
explicit upstream obligation.

V1 and V2 were failed algebra drafts and are intentionally not imported;
V3 is the exact-built successor.
-/
