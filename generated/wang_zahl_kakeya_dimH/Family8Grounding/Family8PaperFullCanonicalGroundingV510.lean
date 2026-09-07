import Family8Grounding.Family8PaperFullCanonicalGroundingV509
import Family8Grounding.Family8FixedConflictLossPowerV3
import Family8Grounding.Family8FixedConflictThirdLossPowerV1

/-!
# Full canonical grounding checkpoint V510

Adds the callback-free fixed-conflict power absorption and its literal
third-factor-loss specialization used by the endpoint LongCore producer.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV510

open Family8FixedConflictLossPowerV3
open Family8FixedConflictThirdLossPowerV1

#print axioms fixedConflictLoss_le_delta_negativePower
#print axioms fixedConflict_thirdLoss_le_delta_negativePower

end Family8PaperFullCanonicalGroundingV510
