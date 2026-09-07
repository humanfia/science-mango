import Family8Grounding.Family8PaperFullCanonicalGroundingV310
import Family8Grounding.Family8SelectedParentCanonicalBufferedAdaptiveInnerPowerLowerV2
import Family8Grounding.Family8SelectedParentCanonicalBufferedAdaptivePowerResidualV1
import Family8Grounding.Family8NormalizedLongIntervalRelevantDef212InputsV5

/-!
# Family 8 full canonical grounding checkpoint V311

The arbitrary-`tau` selected-parent reserve is now combined with the actual
source Katz--Tao power on the same canonical buffered bucket.  A canonical
choice of `tau` makes the remaining exponent nonpositive and yields the
callback-free local residual inequality consumed by Proposition 66.

The finite Def. 2.12 interface is also sharpened to the exact selector
support: C-uniformity, doubled-parent partitioning, and endpoint CWA are
required only for intervals satisfying `IsLong`.  In particular the terminal
`tau = delta` scale in the automatic-large branch carries no artificial CWA
obligation.  Source, adjacent, stopping, and first-crossing consequences are
all proved from this relevant-only interface.

The remaining work on these strands is object-level: identify the selected
source-tau cover with the canonical buffered bucket (or transport the local
cap monotonically), and construct one common-fine coherent hierarchy for the
single long interval actually read by the selector.
-/
