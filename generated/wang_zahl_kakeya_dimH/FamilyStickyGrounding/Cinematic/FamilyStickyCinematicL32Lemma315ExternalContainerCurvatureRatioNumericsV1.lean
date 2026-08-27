import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1

open FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1

noncomputable section

/-!
# Division-free curvature-ratio numerics for the external-container count

If the external container has second-derivative gap
`M <= 2 * curvatureRatio * t`, the slope factor

`K = 8 * containerLambda + 8 * curvatureRatio`

satisfies the exact upper-window hypothesis of the generic external-container
PYZ theorem.  The proof uses only the two scale identities
`t * sqrt(delta/t)^2 = delta` and
`sqrt(delta*t) * sqrt(delta/t) = delta`.
-/

/-- Automatic dimensionless upper-slope factor. -/
def pyzExternalContainerCurvatureSlopeFactor
    (containerLambda curvatureRatio : Real) : Real :=
  8 * containerLambda + 8 * curvatureRatio

/-- Explicit normalized closed-neighbour cap after substituting the automatic
slope factor. -/
def pyzExternalContainerCurvatureClosedNeighbourCap
    (containerLambda curvatureRatio : Real) : ENNReal :=
  ENNReal.ofReal (16 * containerLambda + 16 * curvatureRatio + 1) *
    (ENNReal.ofReal containerLambda *
      ENNReal.ofReal (Real.sqrt containerLambda))

theorem pyzExternalContainerCurvatureSlopeFactor_nonneg
    {containerLambda curvatureRatio : Real}
    (hcontainerLambda : 0 <= containerLambda)
    (hcurvatureRatio : 0 <= curvatureRatio) :
    0 <= pyzExternalContainerCurvatureSlopeFactor
      containerLambda curvatureRatio := by
  unfold pyzExternalContainerCurvatureSlopeFactor
  positivity

/-- The closed-neighbour cap is exactly the generic cap at the automatic
slope factor. -/
theorem pyzExternalContainerClosedNeighbourBound_at_curvatureSlopeFactor
    (containerLambda curvatureRatio : Real) :
    pyzExternalContainerClosedNeighbourBound containerLambda
        (pyzExternalContainerCurvatureSlopeFactor
          containerLambda curvatureRatio) =
      pyzExternalContainerCurvatureClosedNeighbourCap
        containerLambda curvatureRatio := by
  unfold pyzExternalContainerClosedNeighbourBound
    pyzExternalContainerMultiplicityBound
    pyzExternalContainerCurvatureSlopeFactor
    pyzExternalContainerCurvatureClosedNeighbourCap
  congr 3
  ring

/-- Doubling a one-sided external-pivot second-derivative window gives the
division-free curvature-ratio comparison used below.  The nonnegative
reference-scale contribution can simply be discarded after doubling. -/
theorem six_mul_t_add_two_mul_centerGap_le_two_mul_ratio_mul_t
    {t centerGap referenceScale curvatureRatio : Real}
    (hreferenceScale : 0 <= referenceScale)
    (hwindow :
      3 * t + centerGap + 3 * referenceScale <= curvatureRatio * t) :
    6 * t + 2 * centerGap <= 2 * curvatureRatio * t := by
  nlinarith

/-- Division-free production of the exact scalar slope-window hypothesis. -/
theorem externalContainerCurvatureRatio_slopeWindow
    {delta t containerLambda M curvatureRatio : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hMupper : M <= 2 * curvatureRatio * t) :
    4 * (containerLambda * delta) +
          2 * M * (Real.sqrt (delta / t)) ^ 2 <=
      (pyzExternalContainerCurvatureSlopeFactor
          containerLambda curvatureRatio *
        Real.sqrt (delta * t)) *
        (Real.sqrt (delta / t) / 2) := by
  have htL := t_mul_baseScale_sq hdelta ht
  have hSL := slopeScale_mul_baseScale hdelta ht
  have hmul :
      M * (Real.sqrt (delta / t)) ^ 2 <=
        (2 * curvatureRatio * t) *
          (Real.sqrt (delta / t)) ^ 2 :=
    mul_le_mul_of_nonneg_right hMupper (sq_nonneg _)
  have htwomul :
      2 * M * (Real.sqrt (delta / t)) ^ 2 <=
        2 * (2 * curvatureRatio * t) *
          (Real.sqrt (delta / t)) ^ 2 := by
    nlinarith
  have hright :
      (pyzExternalContainerCurvatureSlopeFactor
          containerLambda curvatureRatio *
        Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2) =
        (4 * containerLambda + 4 * curvatureRatio) * delta := by
    calc
      (pyzExternalContainerCurvatureSlopeFactor
          containerLambda curvatureRatio *
        Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2) =
        (4 * containerLambda + 4 * curvatureRatio) *
          (Real.sqrt (delta * t) * Real.sqrt (delta / t)) := by
            unfold pyzExternalContainerCurvatureSlopeFactor
            ring
      _ = (4 * containerLambda + 4 * curvatureRatio) * delta := by
        rw [hSL]
  calc
    4 * (containerLambda * delta) +
          2 * M * (Real.sqrt (delta / t)) ^ 2 <=
        4 * (containerLambda * delta) +
          2 * (2 * curvatureRatio * t) *
            (Real.sqrt (delta / t)) ^ 2 :=
      add_le_add_right htwomul _
    _ = (4 * containerLambda + 4 * curvatureRatio) * delta := by
      rw [show
        2 * (2 * curvatureRatio * t) *
            (Real.sqrt (delta / t)) ^ 2 =
          4 * curvatureRatio *
            (t * (Real.sqrt (delta / t)) ^ 2) by ring, htL]
      ring
    _ = (pyzExternalContainerCurvatureSlopeFactor
          containerLambda curvatureRatio *
        Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2) := hright.symm

/-- Cardinality adapter requiring only the scale-free curvature comparison
`M <= 2 * curvatureRatio * t`; the generic slope-window callback is
discharged automatically. -/
theorem card_le_of_pyz_externalContainerCurvatureRatio_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t containerLambda M curvatureRatio : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcontainerLambda : 0 <= containerLambda)
    (hM : 0 <= M) (hcurvatureRatio : 0 <= curvatureRatio)
    (hMupper : M <= 2 * curvatureRatio * t)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
    (hcontainerLength :
      container.rectangle.right - container.rectangle.left =
        Real.sqrt ((containerLambda * delta) / t))
    (hcontain : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        container.carrier (containerLambda * delta))
    (hsecondPair : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> forall z,
        z ∈ (rectangles i).rectangle.base ∪
          (rectangles j).rectangle.base ->
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
      z ∈ (rectangles i).rectangle.base ->
      |(rectangles i).second z - container.second z| <= M)
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) <=
      pyzExternalContainerCurvatureClosedNeighbourCap
        containerLambda curvatureRatio := by
  rw [← pyzExternalContainerClosedNeighbourBound_at_curvatureSlopeFactor]
  apply card_le_of_pyz_externalContainerSlopeFactor_on_bases
    indices rectangles container hdelta ht hcontainerLambda hM
      (pyzExternalContainerCurvatureSlopeFactor_nonneg
        hcontainerLambda hcurvatureRatio)
      hlength hcontainerLength hcontain hsecondPair hsecondContainer
  · exact externalContainerCurvatureRatio_slopeWindow hdelta ht hMupper
  · exact hincomparable

#print axioms pyzExternalContainerCurvatureSlopeFactor
#print axioms pyzExternalContainerCurvatureClosedNeighbourCap
#print axioms pyzExternalContainerCurvatureSlopeFactor_nonneg
#print axioms pyzExternalContainerClosedNeighbourBound_at_curvatureSlopeFactor
#print axioms six_mul_t_add_two_mul_centerGap_le_two_mul_ratio_mul_t
#print axioms externalContainerCurvatureRatio_slopeWindow
#print axioms card_le_of_pyz_externalContainerCurvatureRatio_on_bases

end

end FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
