import Family8Grounding.Family8PaperFullCanonicalGroundingV255
import Family8Grounding.Family8FullRefinementSourceTauAdaptiveCardWeightedGlobalEndpointV1
import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV6

/-!
# Family 8 full canonical grounding checkpoint V256

This checkpoint records two independent same-data closures.

* The full-refinement source-to-tau route now feeds the adaptive global
  Equation (46) cap into the card-weighted Proposition 6.6(A) consumer.  The
  greedy-block length and bucket-cardinality losses cancel, leaving one
  explicit scalar inequality rather than an assumed family-level estimate.
* The max-witness Equation (45) partition is transported to the exact
  selected-parent induced shading when the literal upper active fine set is
  `univ`.  The transported average is therefore the same object used by the
  Equation (46) endpoint, with no definitional-equality shortcut.

The next analytic seam is to discharge the remaining explicit scalar from
the parameter power envelope, and then combine the retained-owner local ball
estimate with canonical slab regrouping and the Family 6 incidence bound.
-/
