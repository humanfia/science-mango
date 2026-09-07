import Family8Grounding.Family8Family7ActivePatternPositiveMaxWeightFiberV2
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceWeightMassV1
import Family8Grounding.Family8FiniteENNRealMaxWeightIndexMemV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternMaxWeightValueV2

open Family8FiniteENNRealMaxWeightIndexV1
open Family8FiniteENNRealMaxWeightIndexMemV1
open Family8Family7ActivePatternOccurrenceWeightV1
open Family8Family7GenericNativeHighActivePatternOccurrenceDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7GenericNativeHighOccurrenceWeightDefinitionV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The common weight carried by the literal maximal occurrence-weight
fibre. -/
noncomputable def genericNativeHighActivePatternMaxWeightValue
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) : ENNReal :=
  genericNativeHighActivePatternOccurrenceWeight D G c
    (maxWeightIndex
      (genericNativeHighFirstHitNormData D c).family
      (genericNativeHighActivePatternOccurrenceWeight D G c)
      (genericNativeHighFirstHitNormData D c).family_nonempty)

/-- Positive source mass makes the selected common occurrence weight
strictly nonzero. -/
theorem genericNativeHighActivePatternMaxWeightValue_ne_zero
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    genericNativeHighActivePatternMaxWeightValue D G c ≠ 0 := by
  let P := genericNativeHighActivePatternOccurrenceData D G c
  have H := Family8Family7ActivePatternPositiveMaxWeightFiberV2.ActivePatternOccurrenceData.positiveMaxWeightFiberData_of_source_ne_zero P hsource
  exact H.value_ne_zero

/-- Finite source mass makes the selected common occurrence weight finite.
This is a monotonicity consequence of the exact total-weight identity. -/
theorem genericNativeHighActivePatternMaxWeightValue_ne_top
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsourceTop : volume (genericNativeHighActivePatternSource D G c) ≠ ∞) :
    genericNativeHighActivePatternMaxWeightValue D G c ≠ ∞ := by
  let P := genericNativeHighActivePatternOccurrenceData D G c
  let imax := maxWeightIndex
    (genericNativeHighFirstHitNormData D c).family
    P.occurrenceWeight
    (genericNativeHighFirstHitNormData D c).family_nonempty
  have himax : imax ∈ (genericNativeHighFirstHitNormData D c).family :=
    maxWeightIndex_mem _ _ _
  have hle : P.occurrenceWeight imax ≤
      ∑ i ∈ (genericNativeHighFirstHitNormData D c).family,
        P.occurrenceWeight i :=
    Finset.single_le_sum (fun _ _ => bot_le) himax
  apply ne_top_of_le_ne_top ?_ hle
  rw [P.sum_occurrenceWeight_eq_source]
  exact hsourceTop

end

end Family8Family7GenericNativeHighActivePatternMaxWeightValueV2
