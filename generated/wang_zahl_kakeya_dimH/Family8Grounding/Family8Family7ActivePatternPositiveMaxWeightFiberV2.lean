import Family8Grounding.Family8FiniteENNRealPositiveMaxWeightFiberDataV2
import Family8Grounding.Family8Family7ActivePatternOccurrenceWeightV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal

namespace Family8Family7ActivePatternPositiveMaxWeightFiberV2

open Family8FiniteENNRealPositiveMaxWeightFiberDataV2
open Family8FiniteENNRealPositiveMaxWeightFiberStructureV1
open Family8Family7ActivePatternOccurrenceWeightV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

namespace ActivePatternOccurrenceData

variable {iota : Type u} [DecidableEq iota]
variable {N : CanonicalNormNonconcentrationData iota}
variable {physical localShading : FiniteProjectedShading (Real × Real) iota}
variable {source : Set (Real × Real)}

/-- Nonzero source mass gives a positive, common-weight exact fibre retaining
all occurrence mass up to the original norm-family cardinality. -/
theorem positiveMaxWeightFiberData_of_source_ne_zero
    (P : ActivePatternOccurrenceData N physical localShading source)
    (hsource : volume source ≠ 0) :
    PositiveMaxWeightFiberData N.family P.occurrenceWeight
      N.family_nonempty := by
  apply positiveMaxWeightFiberData N.family P.occurrenceWeight
    N.family_nonempty
  rw [P.sum_occurrenceWeight_eq_source]
  exact hsource

end ActivePatternOccurrenceData

end


end Family8Family7ActivePatternPositiveMaxWeightFiberV2
