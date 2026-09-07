import Family8Grounding.Family8PaperFullCanonicalGroundingV197
import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshAdaptiveScaleThinCountV1

/-!
# Family 8 full canonical grounding checkpoint V198

The centered selected-parent endpoint now uses the actual radius-adaptive
proxy scale: the maximum of the canonical packing scale and the literal
affine-radius floor.  This supplies the radius budget internally and removes
the obsolete quadratic-separation hypothesis `648 * delta <= rho^2`.

Packing estimates at the canonical scale are transported monotonically to the
enlarged adaptive scale.  The same selected family retains the mass, Katz--Tao,
average-multiplicity, and thin-count conclusions, with smallness and thinness
assumed only at the scale actually used by the normalized datum.
-/
