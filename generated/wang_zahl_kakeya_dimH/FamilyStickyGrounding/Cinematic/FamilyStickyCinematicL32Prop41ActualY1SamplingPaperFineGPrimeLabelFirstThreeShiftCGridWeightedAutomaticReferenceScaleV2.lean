import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SafeAutomaticReferenceScaleV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SafeAutomaticReferenceScaleV1

noncomputable section

universe u v

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable {fine : UniformTubeFamily radius iota}
variable {N : CanonicalNormNonconcentrationData iota}
variable {D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel}
variable {keep : iota -> fineLabel -> Prop} {left right : iota}
variable {ballRadius : Real}
variable {omega : (N.family -> Fin 1) × (N.family -> Fin 1)}
variable {labelWeight : fineLabel -> ENNReal}
variable {f : Real -> Real} {outerA outerB globalDelta tGlobal : Real}
variable
  (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
    fine N D keep left right ballRadius omega labelWeight f outerA outerB
      globalDelta tGlobal)

/-- The exact coefficient-ball margin demanded by the sampled-lens consumer. -/
def actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin : Real :=
  max ((401 / 100 : Real) *
      actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
        tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)))
    (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
      tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
        (P := P)) + 0)

/-- A reference scale chosen only after the package has fixed its trace shift. -/
def actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale : Real :=
  prop41SafeAutomaticReferenceScale
    (actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin P)

theorem actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale_nonneg :
    0 <= actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P := by
  exact prop41SafeAutomaticReferenceScale_nonneg _

theorem actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin_lt :
    max ((401 / 100 : Real) *
        actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
            (P := P)))
      (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
        tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) + 0) <
      3 * actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P := by
  exact lt_three_mul_prop41SafeAutomaticReferenceScale _

#print axioms actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin
#print axioms actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale
#print axioms actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale_nonneg
#print axioms actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin_lt

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
