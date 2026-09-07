import Family8Grounding.Family8PaperFullCanonicalGroundingV347
import Family8Grounding.Family8Family7NativeHighActivePatternOccurrenceProducerV1
import Family8Grounding.Family8Family7NativeHighArbitraryWeightedProxySupportV1
import Family8Grounding.Family8FrostmanSourceMassFineScalarBudgetV2

/-!
# Family 8 full canonical grounding checkpoint V348

* The pattern-first occurrence construction is now instantiated on the
  literal native-high E2 source and supplies the exact occurrence weight,
  total-mass identity, and arbitrary-weight proxy input.
* Unit-ball support for that proxy is reduced to one genuine scale-separation
  fact: a proxy-radius bound by `1/5`; the original-tube support is inherited
  upstream and the greedy `1/2` radius condition then follows numerically.
* The long-core fine scalar budget now consumes the actual Frostman source
  mass floor, leaving only the logarithmic coefficient power envelope and
  exponent room.  The almost-cover loss envelope remains the sole new
  geometric input on the branching scalar line.

All imported endpoints have exact builds and only the standard Lean axioms.
-/
