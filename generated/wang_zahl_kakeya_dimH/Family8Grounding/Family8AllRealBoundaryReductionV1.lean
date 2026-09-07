import Family8Grounding.Family8KatzTaoNegativeExponentV1
import Family8Grounding.Family8ExponentRangeConsequencesV1

open scoped ENNReal NNReal

namespace Family8AllRealBoundaryReductionV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoNegativeExponentV1
open Family8ExponentRangeConsequencesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Transparent all-real exponent reduction

The paper's substantive middle branch is the unit interval.  This file does
not assert that branch: it accepts its theorem explicitly as an ordinary
function argument.  Negative exponents are impossible by the parallel-grid
obstruction, and exponents at least one are already closed by common-point
packing plus Frostman exponent monotonicity.
-/

/-- Once the genuine unit-interval theorem is supplied, the exact all-real
statement follows.  No callback is stored in a structure and no new
mathematical premise is hidden: `hunit` is precisely the still-substantive
middle theorem. -/
theorem mainLemmaOne_of_unitInterval
    (hunit : ∀ beta : Real, 0 ≤ beta → beta ≤ 1 →
      KatzTaoProperty beta → FrostmanProperty beta)
    (beta : Real) :
    KatzTaoProperty beta → FrostmanProperty beta := by
  intro hKT
  have hbeta0 : 0 ≤ beta :=
    Family8KatzTaoNegativeExponentV1.KatzTaoProperty.nonneg hKT
  by_cases hbeta1 : beta ≤ 1
  · exact hunit beta hbeta0 hbeta1 hKT
  · exact frostmanProperty_of_one_le (le_of_lt (lt_of_not_ge hbeta1))

/-- Equivalent implication-first spelling, convenient for the eventual exact
endpoint. -/
theorem katzTaoProperty_implies_frostmanProperty_of_unitInterval
    (hunit : ∀ beta : Real, 0 ≤ beta → beta ≤ 1 →
      KatzTaoProperty beta → FrostmanProperty beta) :
    ∀ beta : Real, KatzTaoProperty beta → FrostmanProperty beta :=
  mainLemmaOne_of_unitInterval hunit

#print axioms mainLemmaOne_of_unitInterval
#print axioms katzTaoProperty_implies_frostmanProperty_of_unitInterval

end
end Family8AllRealBoundaryReductionV1
