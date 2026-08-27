import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectangleCardinalityBoundV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
open FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1
open FamilyStickyCinematicL32FiniteMeasureMultiplicityV1
open FamilyStickyCinematicL32FiniteENNRealMeasureMultiplicityV1
open FamilyStickyCinematicL32RectangleScaleNormalizationV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainSlopeWindowV1

noncomputable section

/-!
# Lemma 3.15 with an external container and an explicit slope factor

For one cover-code slice the fine rectangles remain pairwise curvature-close
at scale `6 * t`, so their `100`-incomparability still gives the natural
`sqrt (delta * t)` lower slope separation.  The container, however, may be
centred at an external AtScales pivot and need only have an arbitrary
second-derivative gap `M` from the slice.

The upper slope window is therefore exposed as an independent factor `K`.
The exact hypothesis is

`4 * (containerLambda * delta) + 2 * M * L^2
  <= (K * sqrt(delta*t)) * (L/2)`,

where `L = sqrt(delta/t)`.  The resulting point multiplicity is `2*K+1`.
This decoupling is what permits honest cross-cover-code neighbour packing.
-/

/-- The point-multiplicity factor associated with a `K`-slope window. -/
def pyzExternalContainerMultiplicityBound (K : Real) : Real :=
  2 * K + 1

/-- The normalized rectangle-card bound after the area double count. -/
def pyzExternalContainerClosedNeighbourBound
    (containerLambda K : Real) : ENNReal :=
  ENNReal.ofReal (pyzExternalContainerMultiplicityBound K) *
    (ENNReal.ofReal containerLambda *
      ENNReal.ofReal (Real.sqrt containerLambda))

/-- Point multiplicity when pairwise curvature is local but the containing
rectangle has an independent second-derivative gap. -/
theorem pointMultiplicity_le_of_pyz_externalContainerSlopeFactor_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t containerLambda M K : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hM : 0 <= M) (hK : 0 <= K)
    (hlength : forall i, i ∈ indices ->
      (rectangles i).rectangle.right - (rectangles i).rectangle.left =
        Real.sqrt (delta / t))
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
    (hslopeWindow :
      4 * (containerLambda * delta) +
          2 * M * (Real.sqrt (delta / t)) ^ 2 <=
        (K * Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2))
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100)
    (x : Real × Real) :
    (pointMultiplicity indices
        (fun i => (rectangles i).carrier delta) x : ENNReal) <=
      ENNReal.ofReal (pyzExternalContainerMultiplicityBound K) := by
  classical
  rcases x with ⟨y0, theta0⟩
  let active := indices.filter
    (fun i => (y0, theta0) ∈ (rectangles i).carrier delta)
  change (active.card : ENNReal) <=
    ENNReal.ofReal (pyzExternalContainerMultiplicityBound K)
  by_cases hactive : active.Nonempty
  · rcases hactive with ⟨i0, hi0⟩
    have hi0Data := Finset.mem_filter.mp hi0
    have hLpos := rectangleBaseScale_pos hdelta ht
    have hrange : forall i, i ∈ active ->
        |(rectangles i).first theta0 -
          (rectangles i0).first theta0| <=
            K * Real.sqrt (delta * t) := by
      intro i hi
      have hiData := Finset.mem_filter.mp hi
      have hiPoint : (y0, theta0) ∈
          (rectangles i).rectangle.carrier delta := hiData.2
      have hi0Point : (y0, theta0) ∈
          (rectangles i0).rectangle.carrier delta := hi0Data.2
      exact pair_slope_le_of_common_container_on_bases
        (rectangles i).rectangle (rectangles i0).rectangle
        (rectangles i).first (rectangles i0).first
        (rectangles i).second (rectangles i0).second
        container.rectangle.graph container.first container.second
        container.rectangle.base hdelta.le hLpos hM
        hiPoint.1 hi0Point.1
        (hlength i hiData.1) (hlength i0 hi0Data.1)
        (hcontain i hiData.1) (hcontain i0 hi0Data.1)
        (rectangles i).graph_hasDeriv
        (rectangles i0).graph_hasDeriv container.graph_hasDeriv
        (rectangles i).first_hasDeriv
        (rectangles i0).first_hasDeriv container.first_hasDeriv
        (hsecondContainer i hiData.1)
        (hsecondContainer i0 hi0Data.1) hslopeWindow
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
    have hBnonneg : 0 <= pyzExternalContainerMultiplicityBound K := by
      unfold pyzExternalContainerMultiplicityBound
      nlinarith
    have hnormalized :
        (active.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt (delta * t)) <=
          ENNReal.ofReal (pyzExternalContainerMultiplicityBound K) *
            ENNReal.ofReal (Real.sqrt (delta * t)) := by
      calc
        (active.card : ENNReal) *
            ENNReal.ofReal (Real.sqrt (delta * t)) <=
          ENNReal.ofReal
            (2 * (K * Real.sqrt (delta * t)) +
              Real.sqrt (delta * t)) := hpacking
        _ = ENNReal.ofReal
            (pyzExternalContainerMultiplicityBound K *
              Real.sqrt (delta * t)) := by
          congr 1
          unfold pyzExternalContainerMultiplicityBound
          ring
        _ = ENNReal.ofReal (pyzExternalContainerMultiplicityBound K) *
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

/-- Denominator-free measure double count for the external-container
slope-factor estimate. -/
theorem card_mul_fineArea_le_of_pyz_externalContainerSlopeFactor_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t containerLambda M K : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hM : 0 <= M) (hK : 0 <= K)
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
    (hslopeWindow :
      4 * (containerLambda * delta) +
          2 * M * (Real.sqrt (delta / t)) ^ 2 <=
        (K * Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2))
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) *
        (ENNReal.ofReal (2 * delta) *
          ENNReal.ofReal (Real.sqrt (delta / t))) <=
      ENNReal.ofReal (pyzExternalContainerMultiplicityBound K) *
        (ENNReal.ofReal (2 * (containerLambda * delta)) *
          ENNReal.ofReal (Real.sqrt ((containerLambda * delta) / t))) := by
  have hdoubleCount :=
    card_mul_pieceMeasure_le_ennrealMultiplicity_mul_targetMeasure
      volume indices (fun i => (rectangles i).carrier delta)
      (container.carrier (containerLambda * delta))
      (area := ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal (Real.sqrt (delta / t)))
      (B := ENNReal.ofReal (pyzExternalContainerMultiplicityBound K))
      (fun i _hi => by
        simpa [C2GraphRectangle.carrier] using
          measurableSet_graphRectangle_carrier
            (rectangles i).rectangle delta
            (measurable_c2GraphRectangle_graph (rectangles i)))
      (fun i hi => by
        rw [volume_c2GraphRectangle_carrier, hlength i hi])
      hcontain
      (fun x _hx =>
        pointMultiplicity_le_of_pyz_externalContainerSlopeFactor_on_bases
          indices rectangles container hdelta ht hM hK hlength hcontain
            hsecondPair hsecondContainer hslopeWindow hincomparable x)
  rw [volume_c2GraphRectangle_carrier, hcontainerLength] at hdoubleCount
  exact hdoubleCount

/-- Normalized cardinality form.  The new loss is precisely the explicit
factor `2*K+1`; the container area contributes the usual
`lambda * sqrt lambda`. -/
theorem card_le_of_pyz_externalContainerSlopeFactor_on_bases
    {index : Type*} (indices : Finset index)
    (rectangles : index -> C2GraphRectangle)
    (container : C2GraphRectangle)
    {delta t containerLambda M K : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcontainerLambda : 0 <= containerLambda)
    (hM : 0 <= M) (hK : 0 <= K)
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
    (hslopeWindow :
      4 * (containerLambda * delta) +
          2 * M * (Real.sqrt (delta / t)) ^ 2 <=
        (K * Real.sqrt (delta * t)) *
          (Real.sqrt (delta / t) / 2))
    (hincomparable : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j ->
        ¬ leftGraphLambdaComparable
          (rectangles i).rectangle (rectangles j).rectangle delta t 100) :
    (indices.card : ENNReal) <=
      pyzExternalContainerClosedNeighbourBound containerLambda K := by
  have hglobal :=
    card_mul_fineArea_le_of_pyz_externalContainerSlopeFactor_on_bases
      indices rectangles container hdelta ht hM hK hlength
        hcontainerLength hcontain hsecondPair hsecondContainer
          hslopeWindow hincomparable
  rw [enlargedArea_eq_lambda_sqrtLambda_mul_fineArea hcontainerLambda]
    at hglobal
  apply (ENNReal.mul_le_mul_iff_right
    (fineArea_ne_zero hdelta ht) fineArea_ne_top).mp
  simpa [pyzExternalContainerClosedNeighbourBound,
    mul_assoc, mul_comm, mul_left_comm] using hglobal

#print axioms pointMultiplicity_le_of_pyz_externalContainerSlopeFactor_on_bases
#print axioms card_mul_fineArea_le_of_pyz_externalContainerSlopeFactor_on_bases
#print axioms card_le_of_pyz_externalContainerSlopeFactor_on_bases

end

end FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
