import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32CurvilinearRectangleSlopeRangeV1

open FamilyStickyCinematicL32CriticalPointGrowthV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32RectangleTangencyV1

noncomputable section

/-!
# A common enlarged rectangle bounds slopes at a common point

This is the genuine geometric/calculus producer behind equation (3.9) in
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15.  Literal containment
in one graph rectangle bounds each graph relative to the container
reference on its whole base.  A far endpoint and a second-derivative bound
then control the slope at any chosen base point.  Applying this to two
rectangles through one point gives their pairwise slope range.
-/

/-- Taylor's theorem in a denominator-free form: if both endpoint values
are bounded by `V`, then the anchor slope times the endpoint distance is
controlled by `2V` plus a quadratic curvature error. -/
theorem abs_first_mul_distance_le_two_value_add_curvature_sq
    (h h1 h2 : Real -> Real) {theta0 theta M V : Real}
    (hM : 0 <= M)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hsecond : forall z, z ∈ [[theta0, theta]] -> |h2 z| <= M)
    (hvalue0 : |h theta0| <= V) (hvalue : |h theta| <= V) :
    |h1 theta0| * |theta - theta0| <=
      2 * V + M * |theta - theta0| ^ 2 := by
  let remainder : Real -> Real := fun z => h z - h1 theta0 * z
  let remainderFirst : Real -> Real := fun z => h1 z - h1 theta0
  have hremainderDeriv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt remainder (remainderFirst z) z := by
    intro z hz
    convert! (hderiv z hz).sub
      ((hasDerivAt_id z).const_mul (h1 theta0)) using 1
    simp [remainderFirst]
  have hremainderFirstDeriv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt remainderFirst (h2 z) z := by
    intro z hz
    simpa [remainderFirst] using (hderiv1 z hz).sub_const (h1 theta0)
  have hcritical : remainderFirst theta0 = 0 := by
    simp [remainderFirst]
  have herror := abs_value_sub_critical_le_curvature_mul_sq
    remainder remainderFirst h2 hM hcritical
    hremainderDeriv hremainderFirstDeriv hsecond
  have hvalueDifference : |h theta - h theta0| <= 2 * V := by
    calc
      |h theta - h theta0| <= |h theta| + |h theta0| := by
        simpa using (abs_sub_le (h theta) 0 (h theta0))
      _ <= V + V := add_le_add hvalue hvalue0
      _ = 2 * V := by ring
  have hrewrite : h1 theta0 * (theta - theta0) =
      (h theta - h theta0) -
        (remainder theta - remainder theta0) := by
    simp only [remainder]
    ring
  calc
    |h1 theta0| * |theta - theta0| =
        |h1 theta0 * (theta - theta0)| := by rw [abs_mul]
    _ = |(h theta - h theta0) -
        (remainder theta - remainder theta0)| := by rw [hrewrite]
    _ <= |h theta - h theta0| +
        |remainder theta - remainder theta0| := by
      have htriangle := abs_sub_le (h theta - h theta0) 0
        (remainder theta - remainder theta0)
      rw [sub_zero, zero_sub, abs_neg] at htriangle
      exact htriangle
    _ <= 2 * V + M * |theta - theta0| ^ 2 :=
      add_le_add hvalueDifference herror

/-- From any point of a closed interval, one endpoint is at least half the
interval length away, and at most the full length away. -/
theorem exists_far_base_endpoint
    (R : GraphRectangle) {theta0 : Real} (htheta0 : theta0 ∈ R.base) :
    exists theta, theta ∈ R.base ∧
      (R.right - R.left) / 2 <= |theta - theta0| ∧
      |theta - theta0| <= R.right - R.left := by
  by_cases hleft : (R.right - R.left) / 2 <= theta0 - R.left
  · refine ⟨R.left, ⟨le_rfl, R.left_le_right⟩, ?_, ?_⟩
    · rw [abs_of_nonpos]
      · linarith
      · linarith [htheta0.1]
    · rw [abs_of_nonpos]
      · linarith [htheta0.2]
      · linarith [htheta0.1]
  · refine ⟨R.right, ⟨R.left_le_right, le_rfl⟩, ?_, ?_⟩
    · rw [abs_of_nonneg]
      · linarith
      · linarith [htheta0.2]
    · rw [abs_of_nonneg]
      · linarith [htheta0.1]
      · linarith [htheta0.2]

/-- Literal carrier containment bounds the center graph relative to the
container reference at every parameter of its base. -/
theorem graph_value_sub_reference_le_of_carrier_subset
    (R : GraphRectangle) (reference : Real -> Real)
    (containerBase : Set Real) {delta V theta : Real}
    (hdelta : 0 <= delta)
    (hcontain : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference containerBase V)
    (htheta : theta ∈ R.base) :
    |R.graph theta - reference theta| <= V := by
  have hcenter : (R.graph theta, theta) ∈ R.carrier delta := by
    exact ⟨htheta, by simpa using hdelta⟩
  have hbound := (hcontain hcenter).2
  simpa [abs_sub_comm] using hbound

/-- One graph rectangle of exact base length `L`, contained in a common
container, has anchor slope relative to the reference controlled after
multiplication by `L/2`. -/
theorem abs_slope_sub_reference_mul_halfLength_le
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
    (hsecondDifference : forall z,
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
  have hproduct := abs_first_mul_distance_le_two_value_add_curvature_sq
    (fun z => R.graph z - reference z)
    (fun z => firstR z - referenceFirst z)
    (fun z => secondR z - referenceSecond z)
    hM
    (fun z _hz => (hderivR z).sub (hderivReference z))
    (fun z _hz => (hderivFirstR z).sub (hderivReferenceFirst z))
    (fun z _hz => hsecondDifference z) hvalue0 hvalue
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

/-- Two equal-scale rectangles contained in one literal graph container
have a bounded slope difference at a common parameter.  This is the generic
constant form of PYZ equation (3.9). -/
theorem pair_slope_le_of_common_container
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
    (hsecondDifferenceR : forall z,
      |secondR z - referenceSecond z| <= M)
    (hsecondDifferenceS : forall z,
      |secondS z - referenceSecond z| <= M)
    (hconstant : 4 * V + 2 * M * L ^ 2 <= slopeBound * (L / 2)) :
    |firstR theta0 - firstS theta0| <= slopeBound := by
  have hR := abs_slope_sub_reference_mul_halfLength_le
    R firstR secondR reference referenceFirst referenceSecond
    containerBase hdelta hM hpointR hlengthR hcontainR
    hderivR hderivReference hderivFirstR hderivReferenceFirst
    hsecondDifferenceR
  have hS := abs_slope_sub_reference_mul_halfLength_le
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

#print axioms abs_first_mul_distance_le_two_value_add_curvature_sq
#print axioms exists_far_base_endpoint
#print axioms graph_value_sub_reference_le_of_carrier_subset
#print axioms abs_slope_sub_reference_mul_halfLength_le
#print axioms pair_slope_le_of_common_container

end

end FamilyStickyCinematicL32CurvilinearRectangleSlopeRangeV1
