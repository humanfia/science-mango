import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightMassV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
import Family8Grounding.Family8Family7WeightedCriticalBallMassRetentionV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighWeightedCriticalBallMassRetentionV1

open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8Family7GenericNativeHighOccurrenceWeightMassV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7WeightedCriticalBallMassRetentionV2
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Mass retained by the generic occurrence-weighted critical ball

The exact active-pattern occurrence mass and the generic weighted maximizer
combine with only the literal canonical norm-family cardinality loss.
-/

theorem genericActivePatternSource_le_card_mul_criticalBallWeight
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    volume (genericNativeHighActivePatternSource D G c) ≤
      ((genericNativeHighFirstHitNormData D c).family.card : ENNReal) *
        ∑ i ∈
          (genericNativeHighActivePatternWeightedNormData D G c).criticalBall,
          genericNativeHighActivePatternOccurrenceWeight D G c i := by
  rw [← sum_genericNativeHighActivePatternOccurrenceWeight_eq_source D G c]
  simpa only [genericNativeHighActivePatternWeightedNormData,
    genericNativeHighWeightedNormData,
    genericNativeHighFirstHitNormData] using
      totalWeight_le_card_mul_criticalBallWeight
        (genericNativeHighActivePatternWeightedNormData D G c)

#print axioms genericActivePatternSource_le_card_mul_criticalBallWeight

end

end Family8Family7GenericNativeHighWeightedCriticalBallMassRetentionV1
