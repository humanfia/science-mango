import Family8Grounding.Family8PaperFullCanonicalGroundingV154
import Family8Grounding.Family8GeneralizedOuterLongIntervalNormalizationV1
import Family8Grounding.Family8ThinPlankFiveParameterPackingV2

/-!
# Family 8 full canonical grounding checkpoint V155

The canonical outer estimate can now be normalized from its literal
`b / 8` generalized Katz--Tao right-hand side to the global-scale ordinary
Katz--Tao right-hand side.  The proof accounts separately for the fixed
eighth-scale constant, the concentration coefficient power, and the final
loss-exponent budget.

The middle thin-plank packing kernel has also been corrected to the genuine
five-parameter geometry.  It encodes three fixed-window parameters and only
two aspect-ratio-dependent parameters, recovering the omitted direction and
transverse coordinates from unit length and perpendicularity.  Consequently
its explicit cap has quadratic, rather than spurious higher-dimensional,
growth in the plank aspect ratio.  The remaining middle task is the actual
FrameBox/thickened-plank coordinate connector.
-/
