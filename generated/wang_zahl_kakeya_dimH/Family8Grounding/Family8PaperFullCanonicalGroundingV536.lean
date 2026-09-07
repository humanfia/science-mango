import Family8Grounding.Family8PaperFullCanonicalGroundingV535
import Family8Grounding.Family8ParentwiseLongCoreCorrelatedEq66BridgeV1

/-!
# Full canonical grounding interface checkpoint V536

This checkpoint replaces the old max-only LongCore input at the V535
correlated Equation (66) seam by a faithful parentwise witness.

On the literal canonical tau-active cover, its active-fine restriction, and
the same frozen assembly, `CorrelatedInputsWithMassPopularCF` retains both:

* the established `NormalizedLongCoreCorrelatedEq66Inputs` consumed by the
  collapsed-prefix connector; and
* a mass-popular selected parent carrying the canonical LongCore
  normalized-CF lower bound, source-mass estimate, positive fibre union, and
  actual-average product estimate.

The bridge constructs the second component from the parentwise LongCore
barrier.  The existing producer obligations `selectedThird`,
`correlatedPrefixBudget`, `hCount`, and `hAggregateLoss` remain explicit in
the first component.  No unconditional Family8 conclusion is claimed here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV536

#print axioms
  Family8ParentwiseLongCoreCanonicalMassPopularCFIntegrationV2.exists_canonicalTauActiveRestricted_massPopularSelectedParentWithCF
#print axioms
  Family8ParentwiseLongCoreCorrelatedEq66BridgeV1.CorrelatedInputsWithMassPopularCF
#print axioms
  Family8ParentwiseLongCoreCorrelatedEq66BridgeV1.CorrelatedInputsWithMassPopularCF.nonempty_of_correlated
#print axioms
  Family8ParentwiseLongCoreCorrelatedEq66BridgeV1.CorrelatedInputsWithMassPopularCF.hPrefix
#print axioms
  Family8ParentwiseLongCoreCorrelatedEq66BridgeV1.CorrelatedInputsWithMassPopularCF.selectedParent_cf_lower

end Family8PaperFullCanonicalGroundingV536
