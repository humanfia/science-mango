import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
open FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
open FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1
open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
open FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1

noncomputable section

/-!
# Compact-domain common C2 ball rectangle count

PYZ's function family is a `C2` ball on one fixed compact parameter
interval `J`.  Actual tube graphs need not remain uniformly close outside
`J`.  This module threads precisely that local input through the pointwise
multiplicity, measure double-counting, and cardinality arguments.

The only domain compatibility hypothesis is that every fine rectangle base
is contained in `J`.  The calculus kernel proves this is enough: every
unordered interval inspected by Taylor's theorem remains in the relevant
fine base.
-/

/-- Membership in one pointwise `C2` ball, restricted to an explicit
parameter domain. -/
def InPointwiseC2BallOn
    (domain : Set Real) (center R : C2GraphRectangle)
    (radius : Real) : Prop :=
  forall z, z ∈ domain ->
    |R.rectangle.graph z - center.rectangle.graph z| <= radius ∧
    |R.first z - center.first z| <= radius ∧
    |R.second z - center.second z| <= radius

/-- Two members of one local `C2` ball have second derivatives separated
by at most twice the radius at every point of the declared domain. -/
theorem abs_second_sub_le_two_mul_radius_of_mem_common_c2BallOn
    {domain : Set Real} {center R S : C2GraphRectangle}
    {radius z : Real}
    (hR : InPointwiseC2BallOn domain center R radius)
    (hS : InPointwiseC2BallOn domain center S radius)
    (hz : z ∈ domain) :
    |R.second z - S.second z| <= 2 * radius := by
  calc
    |R.second z - S.second z| =
        |(R.second z - center.second z) +
          (center.second z - S.second z)| := by
      congr 1
      ring
    _ <= |R.second z - center.second z| +
        |center.second z - S.second z| := abs_add_le _ _
    _ = |R.second z - center.second z| +
        |S.second z - center.second z| := by
      rw [abs_sub_comm (center.second z) (S.second z)]
    _ <= radius + radius :=
      add_le_add (hR z hz).2.2 (hS z hz).2.2
    _ = 2 * radius := by ring

/-- Radius `3*t` gives the exact local `6*t` curvature bound. -/
theorem abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
    {domain : Set Real} {center R S : C2GraphRectangle}
    {t z : Real}
    (hR : InPointwiseC2BallOn domain center R (3 * t))
    (hS : InPointwiseC2BallOn domain center S (3 * t))
    (hz : z ∈ domain) :
    |R.second z - S.second z| <= 6 * t := by
  convert abs_second_sub_le_two_mul_radius_of_mem_common_c2BallOn
    hR hS hz using 1
  ring

/-- Compact-domain point multiplicity form of PYZ Lemma 3.15. -/
theorem pointMultiplicity_le_of_pyz_rectangle_geometry_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 100 <= lambda)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
    (hcontain : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        container.carrier (lambda * delta))
    (hsecondPair : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> forall z,
        z ∈ (rectangles i).rectangle.base ∪
          (rectangles j).rectangle.base ->
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
      z ∈ (rectangles i).rectangle.base ->
      |(rectangles i).second z - container.second z| <= 6 * t)
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100)
    (x : Real × Real) :
    (pointMultiplicity indices
        (fun i => (rectangles i).carrier delta) x : ENNReal) <=
      ENNReal.ofReal (20 * lambda + 1) := by
  classical
  rcases x with ⟨y0, theta0⟩
  let active := indices.filter
    (fun i => (y0, theta0) ∈ (rectangles i).carrier delta)
  change (active.card : ENNReal) <= ENNReal.ofReal (20 * lambda + 1)
  by_cases hactive : active.Nonempty
  · rcases hactive with ⟨i0, hi0⟩
    have hi0Data := Finset.mem_filter.mp hi0
    have hrange : forall i, i ∈ active ->
        |(rectangles i).first theta0 -
          (rectangles i0).first theta0| <=
            10 * lambda * Real.sqrt (delta * t) := by
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      have hiPoint : (y0, theta0) ∈
          (rectangles i).rectangle.carrier delta := hiData.2
      have hi0Point : (y0, theta0) ∈
          (rectangles i0).rectangle.carrier delta := hi0Data.2
      have hiBase : theta0 ∈ (rectangles i).rectangle.base := hiPoint.1
      have hi0Base : theta0 ∈ (rectangles i0).rectangle.base := hi0Point.1
      exact pyz_slope_range_of_common_container_on_bases
        (rectangles i).rectangle (rectangles i0).rectangle
        (rectangles i).first (rectangles i0).first
        (rectangles i).second (rectangles i0).second
        container.rectangle.graph container.first container.second
        container.rectangle.base hdelta ht hlambda hiBase hi0Base
        (hlength i hiData.1) (hlength i0 hi0Data.1)
        (hcontain i hiData.1) (hcontain i0 hi0Data.1)
        (rectangles i).graph_hasDeriv
        (rectangles i0).graph_hasDeriv container.graph_hasDeriv
        (rectangles i).first_hasDeriv
        (rectangles i0).first_hasDeriv container.first_hasDeriv
        (hsecondContainer i hiData.1)
        (hsecondContainer i0 hi0Data.1)
    have hseparated : forall i, i ∈ active -> forall j, j ∈ active ->
        i ≠ j -> Real.sqrt (delta * t) <=
          |(rectangles i).first theta0 -
            (rectangles j).first theta0| := by
      intro i hi j hj hij
      have hiData := Finset.mem_filter.mp hi
      have hjData := Finset.mem_filter.mp hj
      exact (pyz_slope_separation_of_100_incomparable_on_bases
        (rectangles i).rectangle (rectangles j).rectangle
        (rectangles i).first (rectangles j).first
        (rectangles i).second (rectangles j).second
        hdelta ht hiData.2 hjData.2
        (hlength i hiData.1) (hlength j hjData.1)
        (rectangles i).graph_hasDeriv
        (rectangles j).graph_hasDeriv
        (rectangles i).first_hasDeriv
        (rectangles j).first_hasDeriv
        (hsecondPair i hiData.1 j hjData.1 hij)
        (hincomparable i hiData.1 j hjData.1 hij)).le
    have hpacking := card_mul_sep_le_of_slopes_near
      active (fun i => (rectangles i).first theta0)
      (Real.sqrt_nonneg _) hrange hseparated
    have hBnonneg : 0 <= 20 * lambda + 1 := by nlinarith
    have hnormalized :
        (active.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt (delta * t)) <=
          ENNReal.ofReal (20 * lambda + 1) *
            ENNReal.ofReal (Real.sqrt (delta * t)) := by
      calc
        (active.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt (delta * t)) <=
          ENNReal.ofReal
            (2 * (10 * lambda * Real.sqrt (delta * t)) +
              Real.sqrt (delta * t)) := hpacking
        _ = ENNReal.ofReal
            ((20 * lambda + 1) * Real.sqrt (delta * t)) := by
          congr 1
          ring
        _ = ENNReal.ofReal (20 * lambda + 1) *
            ENNReal.ofReal (Real.sqrt (delta * t)) :=
          ENNReal.ofReal_mul hBnonneg
    have hscale0 : ENNReal.ofReal (Real.sqrt (delta * t)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr
        (rectangleSlopeScale_pos hdelta ht)
    have hscaleTop : ENNReal.ofReal (Real.sqrt (delta * t)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    apply (ENNReal.mul_le_mul_iff_right hscale0 hscaleTop).mp
    simpa [mul_comm] using hnormalized
  · have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact bot_le

/-- Denominator-free measure double count from compact-base curvature
control. -/
theorem card_mul_fineArea_le_of_pyz_rectangle_geometry_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 100 <= lambda)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
    (hcontainerLength :
      container.rectangle.right - container.rectangle.left =
        Real.sqrt ((lambda * delta) / t))
    (hcontain : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        container.carrier (lambda * delta))
    (hsecondPair : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> forall z,
        z ∈ (rectangles i).rectangle.base ∪
          (rectangles j).rectangle.base ->
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
      z ∈ (rectangles i).rectangle.base ->
      |(rectangles i).second z - container.second z| <= 6 * t)
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) *
        (ENNReal.ofReal (2 * delta) *
          ENNReal.ofReal (Real.sqrt (delta / t))) <=
      ENNReal.ofReal (20 * lambda + 1) *
        (ENNReal.ofReal (2 * (lambda * delta)) *
          ENNReal.ofReal (Real.sqrt ((lambda * delta) / t))) := by
  have hdoubleCount :=
    card_mul_pieceMeasure_le_ennrealMultiplicity_mul_targetMeasure
      volume indices (fun i => (rectangles i).carrier delta)
      (container.carrier (lambda * delta))
      (area := ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal (Real.sqrt (delta / t)))
      (B := ENNReal.ofReal (20 * lambda + 1))
      (fun i _hi => by
        simpa [C2GraphRectangle.carrier] using
          measurableSet_graphRectangle_carrier
            (rectangles i).rectangle delta
            (measurable_c2GraphRectangle_graph (rectangles i)))
      (fun i hi => by
        rw [volume_c2GraphRectangle_carrier, hlength i hi])
      hcontain
      (fun x _hx => pointMultiplicity_le_of_pyz_rectangle_geometry_on_bases
        indices rectangles container hdelta ht hlambda hlength hcontain
        hsecondPair hsecondContainer hincomparable x)
  rw [volume_c2GraphRectangle_carrier, hcontainerLength] at hdoubleCount
  exact hdoubleCount

/-- Explicit cardinality bound with curvature assumptions scoped only to
the fine bases. -/
theorem card_le_of_pyz_rectangle_geometry_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 100 <= lambda)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
    (hcontainerLength :
      container.rectangle.right - container.rectangle.left =
        Real.sqrt ((lambda * delta) / t))
    (hcontain : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        container.carrier (lambda * delta))
    (hsecondPair : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> forall z,
        z ∈ (rectangles i).rectangle.base ∪
          (rectangles j).rectangle.base ->
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
      z ∈ (rectangles i).rectangle.base ->
      |(rectangles i).second z - container.second z| <= 6 * t)
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) <=
      ENNReal.ofReal (20 * lambda + 1) *
        (ENNReal.ofReal lambda *
          ENNReal.ofReal (Real.sqrt lambda)) := by
  have hlambda0 : 0 <= lambda := le_trans (by norm_num) hlambda
  have hglobal := card_mul_fineArea_le_of_pyz_rectangle_geometry_on_bases
    indices rectangles container hdelta ht hlambda hlength
    hcontainerLength hcontain hsecondPair hsecondContainer hincomparable
  rw [enlargedArea_eq_lambda_sqrtLambda_mul_fineArea hlambda0] at hglobal
  apply (ENNReal.mul_le_mul_iff_right
    (fineArea_ne_zero hdelta ht) fineArea_ne_top).mp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hglobal

/-- Faithful common-ball producer: one `C2` ball on a fixed domain `J`,
together with actual fine-base localization in `J`, supplies all analytic
inputs of the rectangle count. -/
theorem card_le_of_pyz_rectangle_geometry_of_mem_common_c2BallOn
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container center : C2GraphRectangle)
    (domain : Set Real)
    {delta t lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda : 100 <= lambda)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
    (hcontainerLength :
      container.rectangle.right - container.rectangle.left =
        Real.sqrt ((lambda * delta) / t))
    (hcontain : forall i, i ∈ indices ->
      (rectangles i).carrier delta ⊆
        container.carrier (lambda * delta))
    (hbase : forall i, i ∈ indices ->
      (rectangles i).rectangle.base ⊆ domain)
    (hballFine : forall i, i ∈ indices ->
      InPointwiseC2BallOn domain center (rectangles i) (3 * t))
    (hballContainer :
      InPointwiseC2BallOn domain center container (3 * t))
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) <=
      ENNReal.ofReal (20 * lambda + 1) *
        (ENNReal.ofReal lambda *
          ENNReal.ofReal (Real.sqrt lambda)) := by
  apply card_le_of_pyz_rectangle_geometry_on_bases
    indices rectangles container hdelta ht hlambda hlength
    hcontainerLength hcontain
  · intro i hi j hj _hij z hz
    rcases hz with hzi | hzj
    · exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
        (hballFine i hi) (hballFine j hj) (hbase i hi hzi)
    · exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
        (hballFine i hi) (hballFine j hj) (hbase j hj hzj)
  · intro i hi z hz
    exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
      (hballFine i hi) hballContainer (hbase i hi hz)
  · exact hincomparable

#print axioms InPointwiseC2BallOn
#print axioms abs_second_sub_le_two_mul_radius_of_mem_common_c2BallOn
#print axioms abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
#print axioms pointMultiplicity_le_of_pyz_rectangle_geometry_on_bases
#print axioms card_mul_fineArea_le_of_pyz_rectangle_geometry_on_bases
#print axioms card_le_of_pyz_rectangle_geometry_on_bases
#print axioms card_le_of_pyz_rectangle_geometry_of_mem_common_c2BallOn

end

end FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
