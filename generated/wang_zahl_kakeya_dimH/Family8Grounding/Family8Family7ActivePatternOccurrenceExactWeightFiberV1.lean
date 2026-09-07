import Family8Grounding.Family8Family7ActivePatternOccurrenceWeightV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

namespace Family8Family7ActivePatternOccurrenceExactWeightFiberV1

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

/-- The original norm-family fibre on one literal equal-share occurrence
weight, defined before any generic-native-high specialization. -/
def exactWeightFiber
    (P : ActivePatternOccurrenceData N physical localShading source)
    (value : ENNReal) : Finset iota :=
  N.family.filter fun i => P.occurrenceWeight i = value

#print axioms exactWeightFiber

end ActivePatternOccurrenceData

end


end Family8Family7ActivePatternOccurrenceExactWeightFiberV1
