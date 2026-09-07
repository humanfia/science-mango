import Family8Grounding.Family8Family7GenericNativeHighGeometryV1
import Family8Grounding.Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighOccurrenceDefinitionsV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7GenericNativeHighGeometryV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {physical : FiniteProjectedShading (Real × Real) iota}
variable {f : Real → Real} {hfContinuous : Continuous f}

/-!
# Generic native-high occurrence definitions

These are only the three definitional projections needed by the
active-pattern occurrence producer.  Keeping them separate prevents later
weighted critical-ball and proxy constructions from being elaborated in the
same dependent declaration.
-/

/-- The literal spatial E2 incidence datum for an arbitrary physical core. -/
noncomputable def genericNativeHighFirstHitIncidenceData
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :=
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) S.family physical
    f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) S.family physical
      f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    S.family physical H.payload.finalLabel (G.mesh c) f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent

/-- The canonical norm datum selected by the same generic high payload. -/
noncomputable def genericNativeHighFirstHitNormData
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : D.HighCenter) :=
  positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)

/-- The exact positive-multiplicity E2 source partitioned by active pattern. -/
def genericNativeHighActivePatternSource
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter) :
    Set (Real × Real) :=
  projectedPositiveMultiplicityDyadicCell
    (genericNativeHighFirstHitIncidenceData D G c).shading
    (D.chosenHighPayloadAt c).payload.finalLabel

#print axioms genericNativeHighFirstHitIncidenceData
#print axioms genericNativeHighFirstHitNormData
#print axioms genericNativeHighActivePatternSource

end

end Family8Family7GenericNativeHighOccurrenceDefinitionsV1
