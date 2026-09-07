import Family8Grounding.Family8PaperFullCanonicalGroundingV129
import Family8Grounding.Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1

/-!
# Family 8 full canonical grounding checkpoint V130

This import-only checkpoint extends V129 with the unified pure-power producer
for the first outer factor.  Both the density and base scalar envelopes now
consume the same gain `eta - (2 * p + a)` under the single budget
`2 * etaF + lossExp + xExp + absorbExp <= scaleExp * gain`.  The exact local
Katz--Tao cap cancellation has already removed the artificial scale loss,
and the fixed `3/64` and `/2` constants in the base envelope are handled by
audited algebra rather than by an additional hypothesis.
-/
