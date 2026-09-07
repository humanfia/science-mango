import Family8Grounding.Family8Family7GenericNativeHighWeightedNormDataV1
import Family8Grounding.Family8WeightedCanonicalNormFiniteRestrictionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighRestrictedWeightedNormDataV1

open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8WeightedCanonicalNormFiniteRestrictionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! The literal restricted equal-weight datum used by the native-high proxy. -/

noncomputable def genericNativeHighRestrictedWeightedNormData
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (center : D.HighCenter) (weight : iota → ENNReal)
    (selected : Finset iota) (hselected : selected.Nonempty)
    (hsubset :
      selected ⊆ (genericNativeHighWeightedNormData D center weight).family) :
    WeightedCanonicalNormBallData iota :=
  restrictWeightedNormData
    (genericNativeHighWeightedNormData D center weight)
    selected hselected hsubset

end

end Family8Family7GenericNativeHighRestrictedWeightedNormDataV1
