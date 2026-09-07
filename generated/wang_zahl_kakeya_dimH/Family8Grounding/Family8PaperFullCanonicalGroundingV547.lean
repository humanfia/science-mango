import Family8Grounding.Family8PaperFullCanonicalGroundingV546
import Family8Grounding.Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2

/-!
# Full canonical grounding interface checkpoint V547

The correlated low/fresh endpoint closure now works on the entire paper
range `gamma <= 1`.  The former `gamma <= 2/3` restriction was used only to
derive elementary bounds on the ladder epsilon and beta; the ladder gap gives
the same bounds from `gamma <= 1`.  The V2 terminal and dichotomy therefore
retain the same objects and the same `DividingScaleOutput` while weakening
that premise.

The sole substantive endpoint branch still open is the unchanged same-core
high payload.  No high-gamma fallback or second greedy selection is hidden in
this checkpoint.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV547

#print axioms
  Family8LowFreshCardScaleParameterLadderBudgetV1.lowGate_freshCardScale_exponent_budget_of_gamma_le_one
#print axioms
  Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV2.endpointIdentity_retainedLowFresh_longInterval_dividingScaleOutput_of_gamma_le_one
#print axioms
  Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2.exists_endpointIdentity_correlated_dividingScaleOutput_or_sameCoreOccurrenceWeightedCordoba_massStrengthened_of_gamma_le_one

end Family8PaperFullCanonicalGroundingV547
