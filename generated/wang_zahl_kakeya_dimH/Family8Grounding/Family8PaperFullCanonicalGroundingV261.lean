import Family8Grounding.Family8PaperFullCanonicalGroundingV260
import Family8Grounding.Family8PlankRetainedOwnerDensityCardCrossV1
import Family8Grounding.Family8PlankRetainedOwnerNormalizedLocalDensityV1

/-!
# Family 8 full canonical grounding checkpoint V261

The retained-owner route now removes both the multiplicity cap and total fine
mass from the local dense-ball comparison.  Actual memberwise plank volume,
source density, and owner-bucket retention give

`density * K * (C⁻³ * a * b) <= loss * fineMass`,

while the same packing/CubeWeight witness gives

`fineMass * volume (ball 0 (rho / 6)) <= 250 * K * w`.

Positivity of the constructed retained `K` permits exact ENNReal
cancellation, producing

`density * (C⁻³ * a * b) * volume (ball 0 (rho / 6)) <= 250 * loss * w`.

Thus `K`, `fineMass`, packing cardinality, and ambient volume are no longer
open seams.  The next step is to combine this inequality with the same
CubeWeight witness's pointwise lower band `w <= localMass`, normalize the
constant and scale powers, and regroup the resulting dense balls into the
canonical slab family consumed by Family 6.
-/
