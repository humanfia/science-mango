import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Family8Grounding.Family8BufferedCommonScaleTubePlankV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8ActualDatumBufferedCommonScalePlankConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8StickyParentHullVolumeBoundV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- The literal common buffered affine image of an actual tube family. -/
abbrev actualDatumBufferedCommonScaleFamily
    (D : ActualTubeDatum delta iota) : ConvexFamily iota :=
  affineImageFamily (bufferedCommonScaleEquiv delta) D.family.bodyFamily

/-- The shading transported by exactly the same common affine equivalence. -/
def actualDatumBufferedCommonScaleShading
    (D : ActualTubeDatum delta iota) :
    Shading (actualDatumBufferedCommonScaleFamily D) :=
  affineImageShading (bufferedCommonScaleEquiv delta) D.shading

@[simp] theorem actualDatumBufferedCommonScaleFamily_apply
    (D : ActualTubeDatum delta iota) (i : iota) :
    actualDatumBufferedCommonScaleFamily D i =
      bufferedCommonScaleTubeBody (D.family.tubes i) := rfl

theorem actualDatumBufferedCommonScale_all_isPlank
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (i : iota) :
    IsPlank 16 (bufferedCommonWidth delta) (bufferedCommonWidth delta)
      (actualDatumBufferedCommonScaleFamily D i) := by
  rw [actualDatumBufferedCommonScaleFamily_apply]
  exact bufferedCommonScaleTube_isPlank _ hdelta hdeltaHalf

/-- Package every member of an actual tube datum into a common-scale buffered
plank family.  The fixed affine image of the radius-four ball is the shared
unit-scale ambient. -/
def actualDatumBufferedCommonScalePlankFamily
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcontained : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    ShadedConvexPlankFamily iota
      (bufferedCommonWidth delta) (bufferedCommonWidth delta) where
  family := actualDatumBufferedCommonScaleFamily D
  shading := actualDatumBufferedCommonScaleShading D
  comparisonConstant := 16
  all_isPlank := actualDatumBufferedCommonScale_all_isPlank
    D hdelta hdeltaHalf
  ambient := affineImageConvexBody (bufferedCommonScaleEquiv delta)
    closedBallFourBody
  ambientComparisonConstant := 8
  ambient_is_unit_scale :=
    bufferedCommonScale_closedBallFour_isPlank hdeltaHalf
  contained_in_ambient i := by
    apply Set.image_mono
    have hunitFour :
        Metric.closedBall (0 : Space) 1 ⊆ Metric.closedBall 0 4 :=
      Metric.closedBall_subset_closedBall (by norm_num)
    simpa only [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
      coe_closedBallFourBody] using (hcontained i).trans hunitFour

/-- The common affine buffering changes neither shading mass-to-union-volume
ratio nor average multiplicity. -/
theorem actualDatumBufferedCommonScalePlankFamily_averageMultiplicity
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcontained : ∀ i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    (actualDatumBufferedCommonScalePlankFamily D hdelta hdeltaHalf
      hcontained).shading.averageMultiplicity =
        D.shading.averageMultiplicity :=
  affineImageShading_averageMultiplicity
    (bufferedCommonScaleEquiv delta) D.shading

#print axioms actualDatumBufferedCommonScale_all_isPlank
#print axioms actualDatumBufferedCommonScalePlankFamily
#print axioms actualDatumBufferedCommonScalePlankFamily_averageMultiplicity

end
end Family8ActualDatumBufferedCommonScalePlankConnectorV1
