import Family8Grounding.Family8PaperFullCanonicalGroundingV483
import Family8Grounding.Family8IsFrostmanInActiveSubtypeRetentionV2
import Family8Grounding.Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2

/-!
# Full canonical grounding checkpoint V484

Adds both fixed-parent atoms for the middle CF dichotomy: explicit
contained-mass-loss Frostman transport on the low branch, and the honest
same-parent maximal hull choice on the high branch.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV484

open Family8IsFrostmanInActiveSubtypeRetentionV2
open Family8StickyScaleCoverSelectedParentCFAtHullChoiceV2

#print axioms isFrostmanIn_activeSubtype_of_ambientMass_retention
#print axioms selectedParentCFAtHullChoice_nonempty
#print axioms
  SelectedParentCFAtHullChoice.lower_mul_fiberVolume_le_winnerDensity_mul_parentVolume

end Family8PaperFullCanonicalGroundingV484
