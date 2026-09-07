import Family8Grounding.Family8PaperFullCanonicalGroundingV497
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3

/-!
# Full canonical grounding checkpoint V498

Adds the exact endpoint long-core identity first fields.  Since the unique
lower endpoint is `tau = delta`, the count, average, and loss are all one,
and the literal first Section-8 inequality follows without a small-ratio
premise.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV498

open Family8EndpointLongCoreIdentityFirstFieldsV3

#print axioms endpointLongCore_tau_eq_delta
#print axioms sectionEightScaleCountFrostmanFactor_self_one
#print axioms endpointLongCoreIdentityFirstFields
#print axioms EndpointLongCoreIdentityFirstFields.firstLoss_le_zeroPower

end Family8PaperFullCanonicalGroundingV498
