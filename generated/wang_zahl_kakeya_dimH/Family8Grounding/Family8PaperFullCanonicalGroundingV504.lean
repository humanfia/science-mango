import Family8Grounding.Family8PaperFullCanonicalGroundingV503
import Family8Grounding.Family8StickySelectedFiberLowCFPowerBudgetsV2

/-!
# Full canonical grounding checkpoint V504

Adds the source-side power-budget package for the literal selected low-CF
strict-middle branch.  It simultaneously supplies the normalized density,
Katz--Tao base, and closed-loss bounds used by the endpoint producer.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV504

open Family8StickySelectedFiberLowCFPowerBudgetsV2

#print axioms selectedFiberLowCF_density_base_loss_budgets

end Family8PaperFullCanonicalGroundingV504
