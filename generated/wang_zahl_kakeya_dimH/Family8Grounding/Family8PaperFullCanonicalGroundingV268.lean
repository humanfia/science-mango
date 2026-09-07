import Family8Grounding.Family8PaperFullCanonicalGroundingV267
import Family8Grounding.Family8PlankRetainedOwnerFullBallPowerAbsorptionV1

/-!
# Family 8 full canonical grounding checkpoint V268

The retained-owner full-ball coefficient is now absorbed at an explicit
small-radius threshold.  For finite retention loss and positive absorption
exponent, the verified endpoint upgrades the normalized geometric estimate
to

`density * (a * b) * volume (ball 0 rho)`
`  <= rho ^ (-absorbExponent) * localMass`.

The threshold intentionally depends on the literal plank comparison
constant and retention loss.  This module therefore closes the local
power-normalization step without claiming the datum-uniform `b0` required by
the outer Family 6 hypothesis.  The remaining canonical task is to give
those two coefficients a uniform power envelope, or reorganize the analytic
step so the datum-dependent loss is paid outside that quantifier.
-/
