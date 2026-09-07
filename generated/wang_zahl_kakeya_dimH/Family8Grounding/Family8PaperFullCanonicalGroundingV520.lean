import Family8Grounding.Family8PaperFullCanonicalGroundingV519
import Family8Grounding.Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1

/-!
# Full canonical grounding checkpoint V520

This checkpoint records the endpoint-identity long-core scalar closure.  At
the one-step endpoint, the canonical buffered radius is exactly
`delta^(1-epsilon)`, so the identity Katz--Tao transport costs only two
epsilon powers.  The module also derives the required lower card-scale mass
directly from the source Frostman mass, avoiding the canonical Frostman
constant at this gate.

The remaining long-core obstruction is therefore structural: producing the
source Katz--Tao object (or a dynamic-`b` aggregated cover with the equivalent
branching budgets), not the endpoint radius or lower-`X` numerics.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV520

open Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1

#print axioms endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
#print axioms
  endpointLongCore_canonicalBufferedRadius_div_delta_le_negativePower
#print axioms endpointLongCore_canonicalBufferedRadius_scaleRatio
#print axioms endpointIdentityLongCore_sourceKatzTao_hAKT
#print axioms endpointIdentityLongCoreDirectXLowerThreshold_pos
#print axioms endpointIdentityLongCore_directXLower_of_frostman

end Family8PaperFullCanonicalGroundingV520
