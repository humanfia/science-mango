import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectanglePYZSlopeWindowV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1

open FamilyStickyCinematicL32CriticalPointGrowthV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeRangeV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32RectangleTangencyV1

noncomputable section

/-!
# PYZ slope windows from compact-domain C2 control

The function family in Pramanik--Yang--Zahl is controlled in `C2` on a
fixed compact parameter interval.  The older slope-window wrapper asked
for second-derivative bounds on all of `Real`; that is unnecessarily strong
for the actual tube graphs, whose differences can grow polynomially away
from the parameter interval.

The calculus proofs only inspect unordered intervals whose endpoints lie
in a fine rectangle base.  This module records that exact scope.  No global
extension of a local `C2` bound is assumed.
-/

/-- The upper-slope Taylor argument only needs the curvature difference on
the base of the rectangle being inspected. -/
theorem abs_slope_sub_reference_mul_halfLength_le_on_base
    (R : GraphRectangle)
    (firstR secondR reference referenceFirst referenceSecond : Real -> Real)
    (containerBase : Set Real)
    {delta V L M theta0 : Real}
    (hdelta : 0 <= delta) (hM : 0 <= M)
    (hpoint : theta0 ∈ R.base)
    (hlength : R.right - R.left = L)
    (hcontain : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase V)
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivReference : forall z,
      HasDerivAt reference (referenceFirst z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivReferenceFirst : forall z,
      HasDerivAt referenceFirst (referenceSecond z) z)
    (hsecondDifference : forall z, z ∈ R.base ->
      |secondR z - referenceSecond z| <= M) :
    |firstR theta0 - referenceFirst theta0| * (L / 2) <=
      2 * V + M * L ^ 2 := by
  rcases exists_far_base_endpoint R hpoint with
    ⟨theta, htheta, hfar, hnear⟩
  rw [hlength] at hfar hnear
  have hvalue0 := graph_value_sub_reference_le_of_carrier_subset
    R reference containerBase hdelta hcontain hpoint
  have hvalue := graph_value_sub_reference_le_of_carrier_subset
    R reference containerBase hdelta hcontain htheta
  have hsegment : [[theta0, theta]] ⊆ R.base := by
    exact uIcc_subset_Icc hpoint htheta
  have hproduct := abs_first_mul_distance_le_two_value_add_curvature_sq
    (fun z => R.graph z - reference z)
    (fun z => firstR z - referenceFirst z)
    (fun z => secondR z - referenceSecond z)
    hM
    (fun z _hz => (hderivR z).sub (hderivReference z))
    (fun z _hz => (hderivFirstR z).sub (hderivReferenceFirst z))
    (fun z hz => hsecondDifference z (hsegment hz)) hvalue0 hvalue
  have hleft :
      |firstR theta0 - referenceFirst theta0| * (L / 2) <=
        |firstR theta0 - referenceFirst theta0| *
          |theta - theta0| :=
    mul_le_mul_of_nonneg_left hfar (abs_nonneg _)
  have hL0 : 0 <= L := by
    rw [← hlength]
    exact sub_nonneg.mpr R.left_le_right
  have hsquare : |theta - theta0| ^ 2 <= L ^ 2 := by
    nlinarith [abs_nonneg (theta - theta0)]
  calc
    |firstR theta0 - referenceFirst theta0| * (L / 2) <=
        |firstR theta0 - referenceFirst theta0| *
          |theta - theta0| := hleft
    _ <= 2 * V + M * |theta - theta0| ^ 2 := hproduct
    _ <= 2 * V + M * L ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsquare hM
      linarith

/-- Compact-base form of the common-container upper slope window. -/
theorem pair_slope_le_of_common_container_on_bases
    (R S : GraphRectangle)
    (firstR firstS secondR secondS reference
      referenceFirst referenceSecond : Real -> Real)
    (containerBase : Set Real)
    {delta V L M slopeBound theta0 : Real}
    (hdelta : 0 <= delta) (hL : 0 < L) (hM : 0 <= M)
    (hpointR : theta0 ∈ R.base) (hpointS : theta0 ∈ S.base)
    (hlengthR : R.right - R.left = L)
    (hlengthS : S.right - S.left = L)
    (hcontainR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase V)
    (hcontainS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase V)
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivS : forall z, HasDerivAt S.graph (firstS z) z)
    (hderivReference : forall z,
      HasDerivAt reference (referenceFirst z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivFirstS : forall z, HasDerivAt firstS (secondS z) z)
    (hderivReferenceFirst : forall z,
      HasDerivAt referenceFirst (referenceSecond z) z)
    (hsecondDifferenceR : forall z, z ∈ R.base ->
      |secondR z - referenceSecond z| <= M)
    (hsecondDifferenceS : forall z, z ∈ S.base ->
      |secondS z - referenceSecond z| <= M)
    (hconstant : 4 * V + 2 * M * L ^ 2 <= slopeBound * (L / 2)) :
    |firstR theta0 - firstS theta0| <= slopeBound := by
  have hR := abs_slope_sub_reference_mul_halfLength_le_on_base
    R firstR secondR reference referenceFirst referenceSecond
    containerBase hdelta hM hpointR hlengthR hcontainR
    hderivR hderivReference hderivFirstR hderivReferenceFirst
    hsecondDifferenceR
  have hS := abs_slope_sub_reference_mul_halfLength_le_on_base
    S firstS secondS reference referenceFirst referenceSecond
    containerBase hdelta hM hpointS hlengthS hcontainS
    hderivS hderivReference hderivFirstS hderivReferenceFirst
    hsecondDifferenceS
  have htriangle : |firstR theta0 - firstS theta0| <=
      |firstR theta0 - referenceFirst theta0| +
        |firstS theta0 - referenceFirst theta0| := by
    calc
      |firstR theta0 - firstS theta0| =
          |(firstR theta0 - referenceFirst theta0) -
            (firstS theta0 - referenceFirst theta0)| := by ring_nf
      _ <= |firstR theta0 - referenceFirst theta0| +
          |firstS theta0 - referenceFirst theta0| := by
        have htriangle :=
          abs_sub_le (firstR theta0 - referenceFirst theta0) 0
            (firstS theta0 - referenceFirst theta0)
        rw [sub_zero, zero_sub, abs_neg] at htriangle
        exact htriangle
  have hhalf : 0 <= L / 2 := (half_pos hL).le
  have hproduct : |firstR theta0 - firstS theta0| * (L / 2) <=
      4 * V + 2 * M * L ^ 2 := by
    calc
      |firstR theta0 - firstS theta0| * (L / 2) <=
          (|firstR theta0 - referenceFirst theta0| +
            |firstS theta0 - referenceFirst theta0|) * (L / 2) :=
        mul_le_mul_of_nonneg_right htriangle hhalf
      _ = |firstR theta0 - referenceFirst theta0| * (L / 2) +
          |firstS theta0 - referenceFirst theta0| * (L / 2) := by ring
      _ <= (2 * V + M * L ^ 2) + (2 * V + M * L ^ 2) :=
        add_le_add hR hS
      _ = 4 * V + 2 * M * L ^ 2 := by ring
  apply (mul_le_mul_iff_right₀ (half_pos hL)).mp
  simpa [mul_comm] using hproduct.trans hconstant

/-- The lower-slope argument only needs pairwise curvature control on the
union of the two fine bases. -/
theorem leftGraphLambdaComparable_of_common_point_and_small_slope_on_bases
    (R S : GraphRectangle)
    (firstR firstS secondR secondS : Real -> Real)
    {delta t lambda L M slopeThreshold y0 theta0 : Real}
    (hdelta : 0 <= delta) (hlambda : 1 <= lambda)
    (_hL : 0 <= L) (hM : 0 <= M)
    (hpointR : (y0, theta0) ∈ R.carrier delta)
    (hpointS : (y0, theta0) ∈ S.carrier delta)
    (hlengthR : R.right - R.left <= L)
    (hlengthS : S.right - S.left <= L)
    (henlargedBase : 2 * L <= Real.sqrt (lambda * delta / t))
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivS : forall z, HasDerivAt S.graph (firstS z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivFirstS : forall z, HasDerivAt firstS (secondS z) z)
    (hsecondDifference : forall z, z ∈ R.base ∪ S.base ->
      |secondR z - secondS z| <= M)
    (hslope : |firstR theta0 - firstS theta0| <= slopeThreshold)
    (hconstant : 2 * delta + (slopeThreshold + M * L) * L <=
      (lambda - 1) * delta) :
    leftGraphLambdaComparable R S delta t lambda := by
  have hpointR' : theta0 ∈ R.base ∧
      |y0 - R.graph theta0| <= delta := hpointR
  have hpointS' : theta0 ∈ S.base ∧
      |y0 - S.graph theta0| <= delta := hpointS
  have hanchor := graph_value_close_at_common_point R S hpointR hpointS
  have hgraphClose : forall theta, theta ∈ R.base ∪ S.base ->
      |R.graph theta - S.graph theta| <= (lambda - 1) * delta := by
    intro theta htheta
    have hdistance : |theta - theta0| <= L := by
      rcases htheta with hthetaR | hthetaS
      · exact (abs_sub_le_base_length R hthetaR hpointR'.1).trans hlengthR
      · exact (abs_sub_le_base_length S hthetaS hpointS'.1).trans hlengthS
    have hsegment : [[theta0, theta]] ⊆ R.base ∪ S.base := by
      rcases htheta with hthetaR | hthetaS
      · exact fun z hz => Or.inl (uIcc_subset_Icc hpointR'.1 hthetaR hz)
      · exact fun z hz => Or.inr (uIcc_subset_Icc hpointS'.1 hthetaS hz)
    have hTaylor := abs_value_le_anchor_add_linear_quadratic
      (fun z => R.graph z - S.graph z)
      (fun z => firstR z - firstS z)
      (fun z => secondR z - secondS z)
      (theta0 := theta0) (theta := theta) (M := M) hM
      (fun z _hz => (hderivR z).sub (hderivS z))
      (fun z _hz => (hderivFirstR z).sub (hderivFirstS z))
      (fun z hz => hsecondDifference z (hsegment hz))
    have hd0 : 0 <= |theta - theta0| := abs_nonneg _
    have hs0 : 0 <= slopeThreshold :=
      (abs_nonneg (firstR theta0 - firstS theta0)).trans hslope
    have hlinear :
        |firstR theta0 - firstS theta0| * |theta - theta0| <=
          slopeThreshold * L :=
      mul_le_mul hslope hdistance hd0 hs0
    have hsquare : |theta - theta0| * |theta - theta0| <= L * L :=
      mul_self_le_mul_self hd0 hdistance
    have hquadratic :
        M * (|theta - theta0| * |theta - theta0|) <=
          M * (L * L) := mul_le_mul_of_nonneg_left hsquare hM
    calc
      |R.graph theta - S.graph theta| <=
          |R.graph theta0 - S.graph theta0| +
            (|firstR theta0 - firstS theta0| +
              M * |theta - theta0|) * |theta - theta0| := hTaylor
      _ <= 2 * delta + (slopeThreshold + M * L) * L := by
        nlinarith
      _ <= (lambda - 1) * delta := hconstant
  apply leftGraphLambdaComparable_of_graph_close R S hdelta hlambda
  · exact ⟨theta0, hpointR'.1, hpointS'.1⟩
  · linarith
  · exact hgraphClose

/-- Contrapositive compact-base lower slope gap. -/
theorem slopeThreshold_lt_of_not_leftGraphLambdaComparable_on_bases
    (R S : GraphRectangle)
    (firstR firstS secondR secondS : Real -> Real)
    {delta t lambda L M slopeThreshold y0 theta0 : Real}
    (hdelta : 0 <= delta) (hlambda : 1 <= lambda)
    (hL : 0 <= L) (hM : 0 <= M)
    (hpointR : (y0, theta0) ∈ R.carrier delta)
    (hpointS : (y0, theta0) ∈ S.carrier delta)
    (hlengthR : R.right - R.left <= L)
    (hlengthS : S.right - S.left <= L)
    (henlargedBase : 2 * L <= Real.sqrt (lambda * delta / t))
    (hderivR : forall z, HasDerivAt R.graph (firstR z) z)
    (hderivS : forall z, HasDerivAt S.graph (firstS z) z)
    (hderivFirstR : forall z, HasDerivAt firstR (secondR z) z)
    (hderivFirstS : forall z, HasDerivAt firstS (secondS z) z)
    (hsecondDifference : forall z, z ∈ R.base ∪ S.base ->
      |secondR z - secondS z| <= M)
    (hconstant : 2 * delta + (slopeThreshold + M * L) * L <=
      (lambda - 1) * delta)
    (hincomparable :
      ¬ leftGraphLambdaComparable R S delta t lambda) :
    slopeThreshold < |firstR theta0 - firstS theta0| := by
  by_contra hnot
  apply hincomparable
  exact leftGraphLambdaComparable_of_common_point_and_small_slope_on_bases
    R S firstR firstS secondR secondS hdelta hlambda hL hM
    hpointR hpointS hlengthR hlengthS henlargedBase
    hderivR hderivS hderivFirstR hderivFirstS hsecondDifference
    (le_of_not_gt hnot) hconstant

/-- Exact PYZ lower slope gap from curvature control restricted to the two
fine bases. -/
theorem pyz_slope_separation_of_100_incomparable_on_bases
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
    (hsecondDifference : forall z, z ∈ R.base ∪ S.base ->
      |secondR z - secondS z| <= 6 * t)
    (hincomparable :
      ¬ leftGraphLambdaComparable R S delta t 100) :
    Real.sqrt (delta * t) < |firstR theta0 - firstS theta0| := by
  apply slopeThreshold_lt_of_not_leftGraphLambdaComparable_on_bases
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

/-- Exact PYZ upper slope window from curvature control restricted to each
fine base. -/
theorem pyz_slope_range_of_common_container_on_bases
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
    (hsecondDifferenceR : forall z, z ∈ R.base ->
      |secondR z - referenceSecond z| <= 6 * t)
    (hsecondDifferenceS : forall z, z ∈ S.base ->
      |secondS z - referenceSecond z| <= 6 * t) :
    |firstR theta0 - firstS theta0| <=
      10 * lambda * Real.sqrt (delta * t) := by
  apply pair_slope_le_of_common_container_on_bases
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

#print axioms abs_slope_sub_reference_mul_halfLength_le_on_base
#print axioms pair_slope_le_of_common_container_on_bases
#print axioms leftGraphLambdaComparable_of_common_point_and_small_slope_on_bases
#print axioms slopeThreshold_lt_of_not_leftGraphLambdaComparable_on_bases
#print axioms pyz_slope_separation_of_100_incomparable_on_bases
#print axioms pyz_slope_range_of_common_container_on_bases

end

end FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1
