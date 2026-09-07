import Family8Grounding.Family8PaperFullCanonicalGroundingV265
import Family8Grounding.Family8PlankRetainedOwnerFullBallDensityEndpointV2

/-!
# Family 8 full canonical grounding checkpoint V266

The retained-owner CubeWeight selection now exposes its final density
estimate directly at the full radius-`rho` ball scale.  On the same packing,
bucket, selected cells, final fine shading, and final coarse shading as the
previous local endpoint, it proves pointwise on the final coarse union

`density * (a * b) * volume (ball 0 rho)`
`  <= 54000 * comparisonConstant^3 * loss *`
`       volume (finalFine.shadedUnion ∩ ball x rho)`.

All six retention, cover, same-cell, source-mass, cell-band, and ball-band
outputs are preserved.  The remaining retained-owner seam is numerical
absorption of the displayed finite/logarithmic loss followed by literal
regrouping into the canonical slab-incidence object used by Family 6.
-/
