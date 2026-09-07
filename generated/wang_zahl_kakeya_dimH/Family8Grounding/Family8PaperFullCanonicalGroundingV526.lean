import Family8Grounding.Family8PaperFullCanonicalGroundingV525
import Family8Grounding.Family8CellularCommonInnerLevelV1

/-!
# Full canonical grounding checkpoint V526

This checkpoint adds the repair's common inner-level selection J1.  The
restriction makes one decision for every `(parent, point)` pair, so all child
incidences over that pair survive or disappear together.  It retains source
mass up to the explicit `log₂(card child) + 2` loss; on every retained
incidence the recomputed parent-local child multiplicity is unchanged and
lies in one strictly positive half-open factor-two band.

The pointwise transfer through the final cellular edge set, the concrete
numeric REG1/R2 construction, and the maximal-density nonidentity `b`-cover
remain separate obligations.  No unconditional LongCore, DSO, or
`mainLemmaOne` claim is made here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV526

open Family8CellularCommonInnerLevelV1

#print axioms parentLocalFiberMultiplicity_commonInnerRestriction_eq
#print axioms commonInnerRestriction_wholeIncidence
#print axioms recomputed_parentLocalFiberMultiplicity_positiveBand
#print axioms exists_commonInnerRestriction_with_large_mass

end Family8PaperFullCanonicalGroundingV526
