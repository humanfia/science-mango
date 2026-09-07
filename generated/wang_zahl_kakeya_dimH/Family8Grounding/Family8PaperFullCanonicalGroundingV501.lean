import Family8Grounding.Family8PaperFullCanonicalGroundingV500
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5

/-!
# Full canonical grounding checkpoint V501

Adds the exact endpoint source-to-tau average identity.  The identity cover's
active parent map is injective, so parent aggregation is lossless and the
tau-active datum has exactly the original datum's average multiplicity.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV501

open Family8EndpointLongCoreSourceTauIdentityTransportV5

#print axioms endpointLongCore_tauActive_averageMultiplicity_eq_source

end Family8PaperFullCanonicalGroundingV501
