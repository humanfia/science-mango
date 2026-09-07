import Family8Grounding.Family8PaperFullCanonicalGroundingV269
import Family8Grounding.Family8PlankRetainedOwnerLogCardPowerEnvelopeV1

/-!
# Family 8 full canonical grounding checkpoint V270

The retained-owner logarithmic selection loss now has a datum-uniform power
envelope.  For every positive `kappa` and nonempty finite source cardinality
`n`, the verified endpoint proves

`log₂(n) + 1 ≤ C(kappa) * n ^ kappa`,

with the explicit finite constant
`C(kappa) = 1 / kappa / log(2) + 1`.  This removes the logarithmic retention
factor from the datum-dependent small-radius threshold: it can instead be
charged to an arbitrarily small portion of the count exponent already
present in the Family 6 factor.

The next retained-owner step is to combine this estimate with the canonical
comparison constant `576` and allocate a positive `kappa` inside the
`0 < beta ≤ 1` branch.
-/
