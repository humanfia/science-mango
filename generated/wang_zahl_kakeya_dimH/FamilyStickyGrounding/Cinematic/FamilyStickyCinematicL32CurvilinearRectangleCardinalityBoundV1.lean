import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1

noncomputable section

/-!
# Explicit cardinality form of the curvilinear rectangle count

This module cancels the positive finite fine-rectangle area from the
denominator-free measure estimate.  The resulting factor
`(20*lambda+1) * lambda * sqrt(lambda)` is the explicit constant form of
the `lambda^(5/2)` bound in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.15.
-/

/-- The enlarged base scale is `sqrt(lambda)` times the fine base scale. -/
theorem enlargedBaseScale_eq_sqrtLambda_mul
    {delta t lambda : Real} (hlambda : 0 <= lambda) :
    Real.sqrt ((lambda * delta) / t) =
      Real.sqrt lambda * Real.sqrt (delta / t) := by
  calc
    Real.sqrt ((lambda * delta) / t) =
        Real.sqrt (lambda * (delta / t)) := by
      congr 1
      ring
    _ = Real.sqrt lambda * Real.sqrt (delta / t) := by
      rw [Real.sqrt_mul hlambda]

/-- Exact factorization of enlarged rectangle area by fine rectangle area. -/
theorem enlargedArea_eq_lambda_sqrtLambda_mul_fineArea
    {delta t lambda : Real} (hlambda : 0 <= lambda) :
    ENNReal.ofReal (2 * (lambda * delta)) *
        ENNReal.ofReal (Real.sqrt ((lambda * delta) / t)) =
      (ENNReal.ofReal lambda * ENNReal.ofReal (Real.sqrt lambda)) *
        (ENNReal.ofReal (2 * delta) *
          ENNReal.ofReal (Real.sqrt (delta / t))) := by
  rw [show 2 * (lambda * delta) = lambda * (2 * delta) by ring]
  rw [ENNReal.ofReal_mul hlambda]
  rw [enlargedBaseScale_eq_sqrtLambda_mul hlambda]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg lambda)]
  ring

/-- The fine rectangle area factor is nonzero. -/
theorem fineArea_ne_zero {delta t : Real}
    (hdelta : 0 < delta) (ht : 0 < t) :
    ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal (Real.sqrt (delta / t)) ≠ 0 := by
  apply mul_ne_zero
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  · exact ENNReal.ofReal_ne_zero_iff.mpr
      (rectangleBaseScale_pos hdelta ht)

/-- The fine rectangle area factor is finite. -/
theorem fineArea_ne_top {delta t : Real} :
    ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal (Real.sqrt (delta / t)) ≠ ⊤ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- Explicit finite cardinality bound for pairwise incomparable rectangles
inside one enlarged rectangle.  No cardinality conclusion or multiplicity
bound is assumed: both are produced by the preceding geometry and
double-counting chain. -/
theorem card_le_of_pyz_rectangle_geometry
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
        |(rectangles i).second z - (rectangles j).second z| <= 6 * t)
    (hsecondContainer : forall i, i ∈ indices -> forall z,
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
  have hglobal := card_mul_fineArea_le_of_pyz_rectangle_geometry
    indices rectangles container hdelta ht hlambda hlength
    hcontainerLength hcontain hsecondPair hsecondContainer hincomparable
  rw [enlargedArea_eq_lambda_sqrtLambda_mul_fineArea hlambda0] at hglobal
  apply (ENNReal.mul_le_mul_iff_right
    (fineArea_ne_zero hdelta ht) fineArea_ne_top).mp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hglobal

#print axioms enlargedBaseScale_eq_sqrtLambda_mul
#print axioms enlargedArea_eq_lambda_sqrtLambda_mul_fineArea
#print axioms fineArea_ne_zero
#print axioms fineArea_ne_top
#print axioms card_le_of_pyz_rectangle_geometry

end

end FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
