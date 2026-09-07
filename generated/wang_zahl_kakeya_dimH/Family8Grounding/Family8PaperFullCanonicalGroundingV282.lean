import Family8Grounding.Family8PaperFullCanonicalGroundingV281
import Family8Grounding.Family8PlankRetainedOwnerActiveCellCommonBallContainerV1

/-!
# Family 8 full canonical grounding checkpoint V282

The retained cell-restricted plank datum is now pruned to its literal active
fine support.  Each active fine plank has a point common to its restricted
fine shading and its selected owner's restricted coarse shading, so the
existing dense-ball lower bound applies at the same point.  Mutual thickening
also places that owner's thickened body inside the controlled double
thickening of every certified slab containing the fine plank.

The remaining Family 6 seam is finite rather than existential: build the
active-support/coarse-owner incidence, remove repeated owners, and feed its
resulting count into the analytic slab estimate.
-/
