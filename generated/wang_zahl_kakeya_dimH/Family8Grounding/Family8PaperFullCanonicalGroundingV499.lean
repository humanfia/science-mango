import Family8Grounding.Family8PaperFullCanonicalGroundingV498
import Family8Grounding.Family8ParentInjectiveAggregatedAverageIdentityV2
import Family8Grounding.Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2

/-!
# Full canonical grounding checkpoint V499

Adds two exact transport seams needed by the endpoint producers:

* an injective active parent map preserves parent-aggregated shading mass and
  average multiplicity exactly;
* an honest finite-selection ENNReal loss, together with the normalized
  Katz--Tao and scalar budgets, transports the Frostman multiplicity bound
  back to the source datum.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV499

open Family8ParentInjectiveAggregatedAverageIdentityV2
open Family8FiniteRandomRigidMotionB2ENNRealLossFrostmanConnectorV2

#print axioms
  activeIndexFactorization_fiber_card_le_one_of_parent_injective
#print axioms parentAggregatedShading_shadingMass_eq_activeFineShading
#print axioms parentAggregatedShading_averageMultiplicity_eq_activeFineShading
#print axioms
  source_averageMultiplicity_le_normalized_ennrealLoss_mul_frostmanRHS

end Family8PaperFullCanonicalGroundingV499
