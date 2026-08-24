import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1

open FamilyStickyCinematicL32CriticalPointGrowthV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1

noncomputable section

/-!
# Small slope difference forces rectangle comparability

This is the genuine calculus-and-carrier producer behind equation (3.10)
in Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15.  Two graph
rectangles through one point have close graph values there.  If their slope
difference is also small, a second-derivative bound and the mean value
theorem keep the graph difference small on both bases.  The preceding
module then constructs a literal enlarged curvilinear rectangle containing
their union.  Taking the contrapositive yields slope separation from actual
incomparability; slope separation is not an input callback.
-/

/-- Second-derivative control gives the elementary first-order Taylor bound
used in PYZ Lemma 3.15. -/
theorem abs_value_le_anchor_add_linear_quadratic
    (h h1 h2 : Real -> Real) {theta0 theta M : Real}
    (hM : 0 <= M)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hsecond : forall z, z ∈ [[theta0, theta]] -> |h2 z| <= M) :
    |h theta| <= |h theta0| +
      (|h1 theta0| + M * |theta - theta0|) * |theta - theta0| := by
  have hfirstBound : forall z, z ∈ [[theta0, theta]] ->
      |h1 z| <= |h1 theta0| + M * |theta - theta0| := by
    intro z hz
    have hosc := abs_sub_le_of_hasDerivAt_bound_on_uIcc
      h1 h2 hz left_mem_uIcc hderiv1 hsecond
    have hdistance := abs_sub_left_of_mem_uIcc hz
    calc
      |h1 z| = |(h1 z - h1 theta0) + h1 theta0| := by ring_nf
      _ <= |h1 z - h1 theta0| + |h1 theta0| := abs_add_le _ _
      _ <= M * |z - theta0| + |h1 theta0| := by
        linarith
      _ <= M * |theta - theta0| + |h1 theta0| := by
        have hmul := mul_le_mul_of_nonneg_left hdistance hM
        linarith
      _ = |h1 theta0| + M * |theta - theta0| := by ring
  have hvalue := abs_sub_le_of_hasDerivAt_bound_on_uIcc
    h h1 right_mem_uIcc left_mem_uIcc hderiv hfirstBound
  calc
    |h theta| = |(h theta - h theta0) + h theta0| := by ring_nf
    _ <= |h theta - h theta0| + |h theta0| := abs_add_le _ _
    _ <= (|h1 theta0| + M * |theta - theta0|) *
        |theta - theta0| + |h theta0| := by
      linarith
    _ = |h theta0| +
        (|h1 theta0| + M * |theta - theta0|) *
          |theta - theta0| := by ring

/-- Two parameters in one rectangle base are separated by at most the base
length. -/
theorem abs_sub_le_base_length
    (R : GraphRectangle) {theta theta0 : Real}
    (htheta : theta ∈ R.base) (htheta0 : theta0 ∈ R.base) :
    |theta - theta0| <= R.right - R.left := by
  rw [abs_le]
  constructor <;> linarith [htheta.1, htheta.2, htheta0.1, htheta0.2]

/-- A point belonging to both `delta`-rectangles makes the two graph values
at its parameter differ by at most `2 * delta`. -/
theorem graph_value_close_at_common_point
    (R S : GraphRectangle) {delta y0 theta0 : Real}
    (hR : (y0, theta0) ∈ R.carrier delta)
    (hS : (y0, theta0) ∈ S.carrier delta) :
    |R.graph theta0 - S.graph theta0| <= 2 * delta := by
  change theta0 ∈ R.base ∧ |y0 - R.graph theta0| <= delta at hR
  change theta0 ∈ S.base ∧ |y0 - S.graph theta0| <= delta at hS
  calc
    |R.graph theta0 - S.graph theta0| =
        |(R.graph theta0 - y0) + (y0 - S.graph theta0)| := by
      ring_nf
    _ <= |R.graph theta0 - y0| + |y0 - S.graph theta0| :=
      abs_add_le _ _
    _ = |y0 - R.graph theta0| + |y0 - S.graph theta0| := by
      rw [abs_sub_comm (R.graph theta0)]
    _ <= delta + delta := add_le_add hR.2 hS.2
    _ = 2 * delta := by ring

/-- A common point, bounded base lengths, actual first and second
derivatives, and a small slope difference produce a literal common enlarged
rectangle. -/
theorem leftGraphLambdaComparable_of_common_point_and_small_slope
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
    (hsecondDifference : forall z, |secondR z - secondS z| <= M)
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
    have hTaylor := abs_value_le_anchor_add_linear_quadratic
      (fun z => R.graph z - S.graph z)
      (fun z => firstR z - firstS z)
      (fun z => secondR z - secondS z)
      (theta0 := theta0) (theta := theta) (M := M) hM
      (fun z _hz => (hderivR z).sub (hderivS z))
      (fun z _hz => (hderivFirstR z).sub (hderivFirstS z))
      (fun z _hz => hsecondDifference z)
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

/-- Contrapositive form: failure of a common enlarged rectangle forces a
strict slope separation.  This is the formal core of PYZ equation (3.10). -/
theorem slopeThreshold_lt_of_not_leftGraphLambdaComparable
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
    (hsecondDifference : forall z, |secondR z - secondS z| <= M)
    (hconstant : 2 * delta + (slopeThreshold + M * L) * L <=
      (lambda - 1) * delta)
    (hincomparable :
      ¬ leftGraphLambdaComparable R S delta t lambda) :
    slopeThreshold < |firstR theta0 - firstS theta0| := by
  by_contra hnot
  apply hincomparable
  exact leftGraphLambdaComparable_of_common_point_and_small_slope
    R S firstR firstS secondR secondS hdelta hlambda hL hM
    hpointR hpointS hlengthR hlengthS henlargedBase
    hderivR hderivS hderivFirstR hderivFirstS hsecondDifference
    (le_of_not_gt hnot) hconstant

#print axioms abs_value_le_anchor_add_linear_quadratic
#print axioms abs_sub_le_base_length
#print axioms graph_value_close_at_common_point
#print axioms leftGraphLambdaComparable_of_common_point_and_small_slope
#print axioms slopeThreshold_lt_of_not_leftGraphLambdaComparable

end

end FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
