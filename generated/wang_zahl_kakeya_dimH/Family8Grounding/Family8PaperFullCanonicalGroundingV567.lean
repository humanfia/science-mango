import Family8Grounding.Family8PaperFullCanonicalGroundingV566
import Family8Grounding.Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1
import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstRetainedSourceBudgetV1

/-!
# Full canonical grounding interface checkpoint V567

The selection-first actual-ledger context can now consume the retained source
density of its literal canonical graph.  The formerly opaque comparison
`displayed <= R.graphAverage` is replaced by one division-free budget against
the exact assembly loss, coarse-card loss, and graph-bucket loss stored in the
same `R`.  No graph, assembly, label, source density, or ledger object is
reselected.

This checkpoint does not claim that Family8 is closed: the remaining analytic
input is exactly the displayed-coefficient retained-source budget exposed as
`hBudget` by the successor below.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV567

#print axioms
  Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1.actualLedgerClosure_displayedInput_of_retainedSourceDensityBudget
#print axioms
  Family8CanonicalGraphFrozenActualLedgerSelectionFirstRetainedSourceBudgetV1.consume_actualLedgerContext_of_retainedSourceDensityBudget

end Family8PaperFullCanonicalGroundingV567
