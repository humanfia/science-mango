import Family8Grounding.Family8PaperFullCanonicalGroundingV261
import Family8Grounding.Family8PlankRetainedOwnerLocalDenseBallEndpointV1

/-!
# Family 8 full canonical grounding checkpoint V262

The retained-owner branch now composes the normalized density cancellation
with the lower half of the very same CubeWeight ball band.  For every point
of the actual final thickened-owner shaded union it proves

`density * (C⁻³ * a * b) * volume (ball 0 (rho / 6))`
`  <= 250 * loss * volume (finalFine ∩ ball x rho)`.

The witness remains the same packing certificate, exponent, selected cells,
fine shading, and coarse shading used by the mass-retention and two-sided
local ball bounds.  No multiplicity-cardinality, total-mass, ambient-volume,
or cell-weight callback remains in this local dense-ball endpoint.

The next retained-owner step is scalar: substitute the paper density and
logarithmic retention loss, normalize the ball/plank powers, then regroup the
actual final coarse balls into the canonical slab family consumed by the
Family 6 analytic estimate.
-/
