import Family8Grounding.Family8PaperFullCanonicalGroundingV328
import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1

/-!
# Family 8 full canonical grounding checkpoint V329

The native-high branch now has the correct finite weighted critical-scale
maximizer.  It accepts an arbitrary `ENNReal` weight on tube occurrences and
returns the literal weighted ball together with its scale, center, nonempty
subfamily, and ambient support.  This replaces the generally false attempt
to force first-hit ownership into the old unweighted cardinality filter.
The remaining bridge constructs the occurrence weights from label-first
`Y_2` data and transports this weighted choice into the existing proxy datum.
-/
