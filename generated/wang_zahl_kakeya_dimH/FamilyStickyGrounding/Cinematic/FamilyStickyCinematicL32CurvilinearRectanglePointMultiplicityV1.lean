import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectanglePYZSlopeWindowV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteMeasureMultiplicityV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePYZSlopeWindowV1
open FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1
open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1

noncomputable section

/-!
# Point multiplicity of incomparable curvilinear rectangles

This is the finite fixed-point counting step of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.15.  The preceding geometry modules supply
both sides of the slope window at a point.  Separated-slope packing then
bounds the actual `Finset.filter` of rectangles containing that point.
-/

/-- A graph rectangle together with explicit first and second derivative
functions and kernel-checked derivative certificates. -/
structure C2GraphRectangle where
  rectangle : GraphRectangle
  first : Real -> Real
  second : Real -> Real
  graph_hasDeriv : forall z,
    HasDerivAt rectangle.graph (first z) z
  first_hasDeriv : forall z,
    HasDerivAt first (second z) z

/-- Actual carrier of a `C2GraphRectangle`. -/
def C2GraphRectangle.carrier
    (R : C2GraphRectangle) (delta : Real) : Set (Real × Real) :=
  R.rectangle.carrier delta

/-- At one point, pairwise `100`-incomparability and containment in one
enlarged rectangle bound the actual incidence multiplicity by
`20*lambda+1`.  The factor `20` comes from centering all slopes at one
chosen incident rectangle; no order statistic is needed. -/
theorem pointMultiplicity_le_of_pyz_rectangle_geometry
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
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
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
      exact pyz_slope_range_of_common_container
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
      exact (pyz_slope_separation_of_100_incomparable
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
      (Real.sqrt_nonneg _)
      hrange hseparated
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

#print axioms pointMultiplicity_le_of_pyz_rectangle_geometry

end

end FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
