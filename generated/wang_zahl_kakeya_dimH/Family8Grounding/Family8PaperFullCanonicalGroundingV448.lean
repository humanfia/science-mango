import Family8Grounding.Family8PaperFullCanonicalGroundingV447
import Family8Grounding.Family8WeightedCanonicalNormFiniteRestrictionV1

/-!
# Family 8 full canonical grounding checkpoint V448

A weighted canonical norm datum can now be restricted to any nonempty finite
subfamily while retaining the metric, occurrence weights, and all scale
parameters.  The FirstCrossing high branch can therefore instantiate its
maximum exact-weight fibre locally in the consumer, avoiding resource-heavy
specialized declarations in the active-pattern layer.

All imported endpoints have exact builds and only the standard Lean axioms.
-/
