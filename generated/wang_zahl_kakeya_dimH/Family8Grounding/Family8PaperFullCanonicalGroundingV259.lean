import Family8Grounding.Family8PaperFullCanonicalGroundingV258
import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13

/-!
# Family 8 full canonical grounding checkpoint V259

The same-object max-witness Equation (45) composition no longer assumes that
the upper cover's active fine set is `univ`.  Its fine family is already the
restriction to the lower cover's active coarse indices, whose refinement is
literally full; `activeFine_eq_refined` therefore proves the required identity
from the constructed cover itself.

Consequently the Equation (45) partition, Q-to-P induced-average transport,
max-witness count, exact assembly, and Equation (46) product are now composed
without an active-set premise.  The remaining cross-DAG seam is precisely the
analytic carrier/scale transport from the adaptive occupied shape bucket to
the actual common-witness `sourceFineLevelShading` fibre.
-/
