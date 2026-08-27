import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFixedCCodePackingAdapterV2

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteValueFibresWeightedV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFixedCCodePackingAdapterV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Actual V2 exact-C weighted mass partition

This module is a thin specialization of the package-free restricted-fibre
identities.  Its inner raw fibres are definitionally the underlying joint
`(C, source-cover-code)` fibres consumed by the V2 fixed-C curvature data.
-/

section Actual

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
variable (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
  fine N D keep left right ballRadius omega labelWeight f outerA outerB
    globalDelta tGlobal)

/-- The globally fixed trace displacement used by the final left endpoint. -/
def actualGPrimeThreeShiftCGridWeightedFinalTraceShift : Real :=
  P.eta *
    (actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius) *
      actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))

/-- Literal occupied final normalized-C values. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedOccupiedCValues :
    Finset Real :=
  actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
    (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P)

/-- Underlying final selected items at one literal normalized C. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedExactCFiber (c : Real) :
    Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :=
  actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
    (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P) c

/-- Occupied source-cover codes inside one literal normalized-C fibre.  This
is exactly the code set carrying the V2 packing bound. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedSourceCodesAtC
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) : Finset (Tube radius) :=
  actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D keep left
    right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
      pointAt tubeAt c

/-- Underlying selected-item fibre at one exact normalized C and one exact
source-cover code. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedExactCSourceCodeFiber
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real)
    (coverCenter : Tube radius) :
    Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :=
  actualY1GridRightCLocalCoverUnderlyingFiber P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius (c, coverCenter)

/-- Arbitrary extended-real mass on `P.selected` decomposes exactly over the
literal final normalized-C fibres. -/
theorem actualGPrimeThreeShiftCGridWeighted_selectedMass_eq_sum_exactCFiberMass
    (weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal) :
    finiteENNRealWeight P.selected weight =
      ∑ c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P,
        finiteENNRealWeight
          (actualGPrimeThreeShiftCGridWeightedExactCFiber P c) weight := by
  simpa only [actualGPrimeThreeShiftCGridWeightedOccupiedCValues,
    actualGPrimeThreeShiftCGridWeightedExactCFiber] using
      finiteENNRealWeight_eq_sum_actualThreeShiftCGridRestrictedFiberWeight
        P.gridSelection P.selected
          (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P) weight

/-- Inside one exact C fibre, arbitrary extended-real mass decomposes exactly
over the source-cover codes and the same raw fibres used by the V2 local
curvature package. -/
theorem actualGPrimeThreeShiftCGridWeighted_exactCFiberMass_eq_sum_sourceCodeFiberMass
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real)
    (weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal) :
    finiteENNRealWeight
        (actualGPrimeThreeShiftCGridWeightedExactCFiber P c) weight =
      ∑ coverCenter ∈
          actualGPrimeThreeShiftCGridWeightedSourceCodesAtC P pointAt tubeAt c,
        finiteENNRealWeight
          (actualGPrimeThreeShiftCGridWeightedExactCSourceCodeFiber P pointAt
            tubeAt c coverCenter) weight := by
  let shift := actualGPrimeThreeShiftCGridWeightedFinalTraceShift P
  have hright : forall a, a ∈ P.selected ->
      tubeGraphC
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel a) =
        actualThreeShiftCGridRestrictedValueAt P.gridSelection shift a := by
    intro a ha
    rw [P.rightTube_eq_restricted]
    exact actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
      P.gridSelection P.selected_subset_grid shift ha
  simpa only [actualGPrimeThreeShiftCGridWeightedExactCFiber,
    actualGPrimeThreeShiftCGridWeightedFinalTraceShift,
    actualGPrimeThreeShiftCGridWeightedSourceCodesAtC,
    actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC,
    actualThreeShiftCGridRestrictedSourceCodesAtC,
    actualGPrimeThreeShiftCGridWeightedExactCSourceCodeFiber,
    actualThreeShiftCGridRestrictedSourceCodeFiberAtC, shift] using
      finiteENNRealWeight_actualThreeShiftCGridRestrictedFiber_eq_sum_sourceCodeFiberWeight
        P.gridSelection P.selected_nonempty
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel)
          hright pointAt tubeAt ballRadius weight

/-- Fully nested lossless decomposition of selected mass: first by exact
normalized C, then by the source-cover code inside that C. -/
theorem actualGPrimeThreeShiftCGridWeighted_selectedMass_eq_sum_exactC_sourceCodeFiberMass
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal) :
    finiteENNRealWeight P.selected weight =
      ∑ c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P,
        ∑ coverCenter ∈
            actualGPrimeThreeShiftCGridWeightedSourceCodesAtC P pointAt tubeAt c,
          finiteENNRealWeight
            (actualGPrimeThreeShiftCGridWeightedExactCSourceCodeFiber P pointAt
              tubeAt c coverCenter)
            weight := by
  rw [actualGPrimeThreeShiftCGridWeighted_selectedMass_eq_sum_exactCFiberMass
    P weight]
  apply Finset.sum_congr rfl
  intro c _hc
  exact actualGPrimeThreeShiftCGridWeighted_exactCFiberMass_eq_sum_sourceCodeFiberMass
    P pointAt tubeAt c weight

#print axioms actualGPrimeThreeShiftCGridWeighted_selectedMass_eq_sum_exactCFiberMass
#print axioms actualGPrimeThreeShiftCGridWeighted_exactCFiberMass_eq_sum_sourceCodeFiberMass
#print axioms actualGPrimeThreeShiftCGridWeighted_selectedMass_eq_sum_exactC_sourceCodeFiberMass

end Actual

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
