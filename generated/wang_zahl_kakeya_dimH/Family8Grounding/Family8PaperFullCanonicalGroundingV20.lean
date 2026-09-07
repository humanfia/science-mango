import Family8Grounding.Family8PaperFullCanonicalGroundingV19
import Family8Grounding.Family8PaperConflictOwnerGlobalActiveOwnerDoubledParentDegreeV3

/-!
# Full canonical paper-strength Family 8 grounding bundle, V20

This successor supplies an explicit doubled-parent degree estimate for the
actual deduplicated active-owner cover.  The estimate follows from its honest
finite parent-frame catalogue and has loss
`S.coarseCard * parentFrameCodeCount rho`.  It is therefore a genuine
callback-free input to the weighted selection, while deliberately exposing
the still-missing cross-parent incidence estimate needed to reduce this to the
paper-size loss.
-/
