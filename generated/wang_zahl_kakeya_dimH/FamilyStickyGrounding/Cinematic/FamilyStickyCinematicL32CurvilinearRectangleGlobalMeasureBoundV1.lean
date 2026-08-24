import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
open FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1

noncomputable section

/-!
# Finite global count for incomparable curvilinear rectangles

This is the measure double-counting conclusion of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.15, before cancellation of the common fine
rectangle area.  The input is literal finite rectangle data: exact fine
and container base lengths, actual carrier containment, second-derivative
bounds, and pairwise `100`-incomparability.
-/

/-- The graph carried by a `C2GraphRectangle` is measurable. -/
theorem measurable_c2GraphRectangle_graph (R : C2GraphRectangle) :
    Measurable R.rectangle.graph := by
  exact (continuous_iff_continuousAt.mpr
    (fun z => (R.graph_hasDeriv z).continuousAt)).measurable

/-- Exact area of the actual carrier of a `C2GraphRectangle`. -/
theorem volume_c2GraphRectangle_carrier
    (R : C2GraphRectangle) {delta : Real} :
    volume (R.carrier delta) =
      ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal
          (R.rectangle.right - R.rectangle.left) := by
  simpa [C2GraphRectangle.carrier] using
    volume_graphRectangle_carrier R.rectangle
      (measurable_c2GraphRectangle_graph R) (delta := delta)

/-- Global finite measure bound obtained by integrating the genuine
point-multiplicity estimate.  This denominator-free form remains valid in
`ENNReal` without any division or finiteness side conditions. -/
theorem card_mul_fineArea_le_of_pyz_rectangle_geometry
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
      (fun i hi => by
        simpa [C2GraphRectangle.carrier] using
          measurableSet_graphRectangle_carrier
            (rectangles i).rectangle delta
            (measurable_c2GraphRectangle_graph (rectangles i)))
      (fun i hi => by
        rw [volume_c2GraphRectangle_carrier, hlength i hi])
      hcontain
      (fun x _ => pointMultiplicity_le_of_pyz_rectangle_geometry
        indices rectangles container hdelta ht hlambda hlength hcontain
        hsecondPair hsecondContainer hincomparable x)
  rw [volume_c2GraphRectangle_carrier, hcontainerLength] at hdoubleCount
  exact hdoubleCount

#print axioms measurable_c2GraphRectangle_graph
#print axioms volume_c2GraphRectangle_carrier
#print axioms card_mul_fineArea_le_of_pyz_rectangle_geometry

end

end FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
