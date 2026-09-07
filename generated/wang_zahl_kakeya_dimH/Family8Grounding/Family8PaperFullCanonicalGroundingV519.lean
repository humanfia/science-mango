import Family8Grounding.Family8PaperFullCanonicalGroundingV518
import Family8Grounding.Family8EndpointIdentityFirstCrossingImpossibleV1

/-!
# Full canonical grounding checkpoint V519

This checkpoint closes the endpoint-identity `FirstCrossing` alternative at
small scale.  Singleton fibres force a lower bound on the crossing scale
ratio, while the existing buffered relative-scale estimate forces the
incompatible upper bound.  Hence every sufficiently small nonzero-mass datum
selected by the endpoint identity construction lies in `LongCore`.

The remaining Family 8 endpoint work is therefore entirely in the genuine
aggregated `LongCore` geometry; no FirstCrossing callback is retained here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV519

open Family8EndpointIdentityFirstCrossingImpossibleV1

#print axioms
  endpointFirstCrossing_identityBufferedIntervalCover_fiber_card_le_one
#print axioms endpointIdentity_fullRefinement_not_firstCrossing
#print axioms endpointIdentity_fullRefinement_longCore_of_small_nonzero

end Family8PaperFullCanonicalGroundingV519
