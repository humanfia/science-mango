import Family8Grounding.Family8PaperFullCanonicalGroundingV567
import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerDirectHRowDSOV2

/-!
# Full canonical grounding interface checkpoint V568

This checkpoint records the corrected direct-H-row actual-ledger route.
The canonical graph identity is selected first, and the raw Equation-(66)
estimate is consumed internally on that same identity.  Its collapsed prefix
is factored through `R.graphAverage`, which is then controlled by the H-row
selected from the same `R`.  The frozen coarse average occurs only once, as
the third factor in the raw triple estimate.

Consequently this checkpoint deliberately does not import or promote the V1
direct-H-row closure: V1 attached the collapsed prefix to the frozen average
and then used that average again as the third factor.  The displayed-density
producer is likewise not part of this corrected route.

This is not a claim that Family8 is closed.  The remaining route-specific
first/middle analytic seam is exactly `hOuterFactor` in the V2 closure; the
ordinary ledger, Frostman, and numerical gates of the downstream DSO theorem
remain explicit.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV568

#print axioms
  Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1.dividingScaleOutput_of_sameGraphHRow_groundedRun_graphPrefix_actualFrozenLedger_rawEq66
#print axioms
  Family8CanonicalGraphFrozenActualLedgerDirectHRowDSOV2.SameAssemblyGraphFrozenActualLedgerDirectHRowDSOClosure
#print axioms
  Family8CanonicalGraphFrozenActualLedgerDirectHRowDSOV2.exists_canonicalGraphFrozenIdentity_with_actualLedgerDirectHRowDSOClosure

end Family8PaperFullCanonicalGroundingV568
