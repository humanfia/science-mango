import Family8Grounding.Family8PaperFullCanonicalGroundingV346
import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFiniteBoundsV1
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickNEnvelopeV2
import Family8Grounding.Family8Family7NativeHighArbitraryWeightedProxyGreedyV3

/-!
# Family 8 full canonical grounding checkpoint V347

* The two long-core scalar budgets are reduced to named small-delta power
  envelopes.  The source-mass line can consume the existing Frostman floor;
  the only new upstream input is the honest almost-cover loss envelope.
* The actual selected Equation (45) object now has all needed finite bounds,
  and its literal outer-times-thick loss is bounded by one explicit `N`
  envelope on the same object.
* The arbitrary pattern-weight proxy now has a generic direct-greedy handoff:
  once its radius cap and unit-ball support are supplied, it yields a nonempty
  admissible actual subtype with explicit cardinality, mass, density, and
  average-multiplicity retention.

The failed monolithic Eq45 V1 and failed greedy V1/V2 drafts are not imported.
All imported endpoints have exact builds and only the standard Lean axioms.
-/
