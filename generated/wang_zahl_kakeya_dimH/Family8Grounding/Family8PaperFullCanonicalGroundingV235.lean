import Family8Grounding.Family8PaperFullCanonicalGroundingV234
import Family8Grounding.Family8CanonicalBufferedGlobalAbsoluteScaleGainV1

/-!
# Family 8 full canonical grounding checkpoint V235

The identified long interval now gives an absolute power bound for the
actual canonical buffered radius:

`canonicalBufferedRadius W <= delta^(epsilon * (1-epsilon))`.

For nonnegative `tau`, its `tau`-power is consequently bounded by the
corresponding `delta` power.  This is the missing geometric transport needed
to replace the `rho^tau` term in the certified adaptive flat branch; only
explicit constant and exponent absorption remains in that branch.
-/
