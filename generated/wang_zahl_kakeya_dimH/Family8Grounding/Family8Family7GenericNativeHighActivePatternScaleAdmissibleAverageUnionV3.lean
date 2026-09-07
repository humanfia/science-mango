import Family8Grounding.Family8Family7GenericNativeHighActivePatternProxyInputV1
import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyGreedyV1
import Family8Grounding.Family8Family7GenericNativeHighOccurrenceScaleSplitV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternScaleAdmissibleAverageUnionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7GenericNativeHighActivePatternProxyInputV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDatumV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyGreedyV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceScaleSplitV1
open Family8Family7GenericNativeHighOccurrenceWeightedNormDataV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

theorem
    genericNativeHighActivePattern_smallScale_or_admissibleAverageProxy
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    (genericNativeHighActivePatternWeightedNormData D G c).criticalScale <
        10 * G.ballRadius c ∨
      let P := genericNativeHighActivePatternProxyInput D G c
      let A := genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
        D P hambientSource Y
      ∃ selected : Finset
          (GenericNativeHighArbitraryWeightedCriticalBallIndex D P),
        selected.Nonempty ∧
        (restrictActualTubeDatum A selected).IsAdmissible ∧
        A.shading.averageMultiplicity ≤
          (physical.ambient.card + 1 : Nat) *
            (restrictActualTubeDatum
              A selected).shading.averageMultiplicity := by
  rcases
      genericNativeHighActivePattern_scaleRestart_or_proxyRadius_le_one_fifth
        D G c with hsmall | hproxy
  · exact Or.inl hsmall
  · refine Or.inr ?_
    dsimp only
    let P := genericNativeHighActivePatternProxyInput D G c
    obtain ⟨selected, hnonempty, hadmissible, _hcard, _hmass,
        _hdensity, havg⟩ :=
      exists_genericNativeHighArbitraryWeightedProxy_greedyAdmissible
        D P hambientSource Y hcontained (by
          simpa only [P,
            genericNativeHighWeightedNormData_activePatternProxyInput] using
              hproxy)
    exact ⟨selected, hnonempty, hadmissible, havg⟩

#print axioms
  genericNativeHighActivePattern_smallScale_or_admissibleAverageProxy

end

end Family8Family7GenericNativeHighActivePatternScaleAdmissibleAverageUnionV3
