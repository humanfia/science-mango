import Family8Grounding.Family8PaperFullCanonicalGroundingV125
import Family8Grounding.Family8CanonicalBufferedGlobalRelativeScaleGainV1

/-!
# Family 8 full canonical grounding checkpoint V126

This import-only checkpoint extends V125 with the audited global
fine-to-canonical-buffered scale gain.  The actual long-interval witness now
supplies the sharp comparison `delta / b <= delta ^ (epsilon ^ 2)` at the
canonical buffered radius.  This is the common positive power used by both
fixed-Katz--Tao scalar envelopes in the first outer factor.
-/
