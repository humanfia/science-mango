import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleSlopeRangeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RectangleScaleNormalizationV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CurvilinearRectanglePYZSlopeWindowV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeRangeV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32RectangleTangencyV1

noncomputable section

/-!
# Exact PYZ slope window at a common rectangle point

This module specializes the preceding true geometry and scale algebra to
the constants in Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15.
It supplies equation (3.10) from `100`-incomparability and equation (3.9)
from literal containment in one enlarged rectangle.  Neither slope bound is
accepted as a premise.
-/

/-- Exact lower slope gap (PYZ (3.10)): two equal-scale rectangles through
one point that are not `100`-comparable have slope difference greater than
`sqrt(delta*t)`. -/
theorem pyz_slope_separation_of_100_incomparable
    (R S : GraphRectangle)
    (firstR firstS secondR secondS : Real -> Real)
    {delta t y0 theta0 : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hpointR : (y0, theta0) ∈ R.carrier delta)
    (hpointS : (y0, theta0) ∈ S.carrier delta)
    (hlengthR : R.right - R.left = Real.sqrt (delta / t))
    (hlengthS : S.right - S.left = Real.sqrt (delta / t))
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivS : forall z, HasDerivAt S.graph (firstS z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivFirstS : forall z, HasDerivAt firstS (secondS z) z)
    (hsecondDifference : forall z,
      |secondR z - secondS z| <= 6 * t)
    (hincomparable :
      ¬ leftGraphLambdaComparable R S delta t 100) :
    Real.sqrt (delta * t) <
      |firstR theta0 - firstS theta0| := by
  apply slopeThreshold_lt_of_not_leftGraphLambdaComparable
    R S firstR firstS secondR secondS
    (delta := delta) (t := t) (lambda := 100)
    (L := Real.sqrt (delta / t)) (M := 6 * t)
    (slopeThreshold := Real.sqrt (delta * t))
    (y0 := y0) (theta0 := theta0)
  · exact hdelta.le
  · norm_num
  · exact (rectangleBaseScale_pos hdelta ht).le
  · positivity
  · exact hpointR
  · exact hpointS
  · exact le_of_eq hlengthR
  · exact le_of_eq hlengthS
  · exact two_baseScales_le_enlargedBaseScale hdelta ht (by norm_num)
  · exact hderivR
  · exact hderivS
  · exact hderivFirstR
  · exact hderivFirstS
  · exact hsecondDifference
  · exact smallSlope_comparability_constant hdelta ht
  · exact hincomparable

/-- Exact upper slope window (PYZ (3.9)): two equal-scale rectangles in a
common enlarged graph rectangle have slope difference at most
`10 * lambda * sqrt(delta*t)`. -/
theorem pyz_slope_range_of_common_container
    (R S : GraphRectangle)
    (firstR firstS secondR secondS reference
      referenceFirst referenceSecond : Real -> Real)
    (containerBase : Set Real)
    {delta t lambda theta0 : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 100 <= lambda)
    (hpointR : theta0 ∈ R.base) (hpointS : theta0 ∈ S.base)
    (hlengthR : R.right - R.left = Real.sqrt (delta / t))
    (hlengthS : S.right - S.left = Real.sqrt (delta / t))
    (hcontainR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase
        (lambda * delta))
    (hcontainS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase
        (lambda * delta))
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivS : forall z, HasDerivAt S.graph (firstS z) z)
    (hderivReference : forall z,
      HasDerivAt reference (referenceFirst z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivFirstS : forall z, HasDerivAt firstS (secondS z) z)
    (hderivReferenceFirst : forall z,
      HasDerivAt referenceFirst (referenceSecond z) z)
    (hsecondDifferenceR : forall z,
      |secondR z - referenceSecond z| <= 6 * t)
    (hsecondDifferenceS : forall z,
      |secondS z - referenceSecond z| <= 6 * t) :
    |firstR theta0 - firstS theta0| <=
      10 * lambda * Real.sqrt (delta * t) := by
  apply pair_slope_le_of_common_container
    R S firstR firstS secondR secondS reference
    referenceFirst referenceSecond containerBase
    (delta := delta) (V := lambda * delta)
    (L := Real.sqrt (delta / t)) (M := 6 * t)
    (slopeBound := 10 * lambda * Real.sqrt (delta * t))
    (theta0 := theta0)
  · exact hdelta.le
  · exact rectangleBaseScale_pos hdelta ht
  · positivity
  · exact hpointR
  · exact hpointS
  · exact hlengthR
  · exact hlengthS
  · exact hcontainR
  · exact hcontainS
  · exact hderivR
  · exact hderivS
  · exact hderivReference
  · exact hderivFirstR
  · exact hderivFirstS
  · exact hderivReferenceFirst
  · exact hsecondDifferenceR
  · exact hsecondDifferenceS
  · exact commonContainer_slopeRange_constant hdelta ht
      (le_trans (by norm_num) hlambda)

#print axioms pyz_slope_separation_of_100_incomparable
#print axioms pyz_slope_range_of_common_container

end

end FamilyStickyCinematicL32CurvilinearRectanglePYZSlopeWindowV1
