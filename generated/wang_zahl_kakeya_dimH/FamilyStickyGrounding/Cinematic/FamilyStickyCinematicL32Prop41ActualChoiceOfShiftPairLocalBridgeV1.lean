import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1RepoV2

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
open FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1
open FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# The actual three-shift `choiceOfShift` bridge

This is the finite, geometric part of PYZ Corollary `choiceOfShift`.  Each
input rectangle comes with an honestly selected first/second actual-tube
pair and literal tangency containments.  The analytic shift lemma constructs
one of the three shifts for every rectangle.  Pigeonholing then chooses one
common shift on at least one third of the rectangles.

Unlike the earlier root-fiber interface, the output is packaged as the
`PairLocalActualLensRectangleData` consumed by the Marcus--Tardos endpoint:
the translated first tube remains tangent after the exact radius loss, the
second tube remains tangent, the shifted pair stays `t`-separated, and its
root set on `[A,B]` is literally the two selected roots.

The subsequent infinitesimal general-position perturbation from the paper
(endpoint distinctness A2 and no tangential intersections A3) is not part of
this theorem; those are still separate global inputs to the endpoint.
-/

/-- Rectangle-local witnesses before the common three-shift choice.  The
factor `2` in `coefficient_lower` is the paper's initial `2t` separation;
after a shift of size strictly below `t`, the output remains `t` separated.
-/
structure ActualTwoFamilyRectangleTangencyData
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (R : C2GraphRectangle) (A B delta t rho : Real) : Prop where
  left_mem_quarter : R.rectangle.left ∈
    centeredFractionIcc A B (1 / 4 : Real)
  right_mem_quarter : R.rectangle.right ∈
    centeredFractionIcc A B (1 / 4 : Real)
  rectangle_width : Real.sqrt (delta / t) <=
    R.rectangle.right - R.rectangle.left
  common_c : tubeGraphC T = tubeGraphC U
  coefficient_lower : 2 * t <= tubePairCoefficientDistance T U
  tangent_first : R.carrier delta ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T)) R.rectangle.base (rho * delta)
  tangent_second : R.carrier delta ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U)) R.rectangle.base (rho * delta)

/-- Every three-shift label has absolute value at most one. -/
theorem abs_threeShiftValue_le_one (k : Fin 3) :
    |threeShiftValue k| <= (1 : Real) := by
  fin_cases k <;> simp [threeShiftValue]

/-- Translating only the first tube can decrease the reduced coefficient
distance by at most the absolute displacement. -/
theorem tubePairCoefficientDistance_sub_abs_le_traceTranslateTube
    {radius : NNReal} (T U : Tube radius) (s : Real) :
    tubePairCoefficientDistance T U - |s| <=
      tubePairCoefficientDistance (traceTranslateTube T s) U := by
  have ha :
      |tubeGraphA T - tubeGraphA U| <=
        |(tubeGraphA T + s) - tubeGraphA U| + |s| := by
    calc
      |tubeGraphA T - tubeGraphA U| =
          |((tubeGraphA T + s) - tubeGraphA U) - s| := by ring_nf
      _ <= |(tubeGraphA T + s) - tubeGraphA U| + |s| := abs_sub _ _
  simp only [tubePairCoefficientDistance, coefficientDistance,
    tubePairDeltaA, tubePairDeltaB, tubePairDeltaD,
    tubeGraphA_traceTranslateTube, tubeGraphB_traceTranslateTube,
    tubeGraphD_traceTranslateTube]
  linarith

/-- A three-shift displacement has size strictly below `t` under the exact
small-scale hypothesis used by the analytic perturbation theorem. -/
theorem abs_threeShift_displacement_lt_t
    (k : Fin 3) {delta t q lambda : Real}
    (hdelta : 0 < delta) (hq : 1 <= q)
    (hlambda : 0 < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080) :
    |threeShiftValue k * (lambda * delta)| < t := by
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hfactorPos : 0 < prop41TangencyScaleFactor q := by
    rw [prop41TangencyScaleFactor]
    exact div_pos (mul_pos (by norm_num) (pow_pos hqPos 2))
      prop41TangencyProductCoefficient_pos
  have hlambdaDelta : lambda * delta < t / 46080 := by
    calc
      lambda * delta <
          (10 * prop41TangencyScaleFactor q + lambda) * delta := by
        apply mul_lt_mul_of_pos_right _ hdelta
        nlinarith
      _ < t / 46080 := hstrengthenedScale
  have hlambdaDeltaPos : 0 < lambda * delta := mul_pos hlambda hdelta
  calc
    |threeShiftValue k * (lambda * delta)| =
        |threeShiftValue k| * (lambda * delta) := by
      rw [abs_mul, abs_of_pos hlambdaDeltaPos]
    _ <= 1 * (lambda * delta) :=
      mul_le_mul_of_nonneg_right (abs_threeShiftValue_le_one k)
        hlambdaDeltaPos.le
    _ < t / 46080 := by simpa using hlambdaDelta
    _ < t := by nlinarith

/-- Monotonicity of a literal vertical graph neighborhood in its radius. -/
theorem cinematicVerticalNeighborhood_mono_radius
    (g : Real -> Real) (I : Set Real) {r R : Real} (h : r <= R) :
    cinematicVerticalNeighborhood g I r ⊆
      cinematicVerticalNeighborhood g I R := by
  rintro p ⟨hpI, hp⟩
  exact ⟨hpI, hp.trans h⟩

/-- Two distinct members of an at-most-two set exhaust that set. -/
theorem set_eq_pair_of_encard_le_two_of_mem
    {alpha : Type*} (s : Set alpha) {x y : alpha}
    (hcard : s.encard <= (2 : ENat))
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    s = {x, y} := by
  have hsub : ({x, y} : Set alpha) ⊆ s := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpairCard : ({x, y} : Set alpha).encard = (2 : ENat) :=
    Set.encard_pair hxy
  exact ((Set.finite_singleton y).insert x).eq_of_subset_of_encard_le hsub
    (by simpa only [hpairCard] using hcard) |>.symm

/-- Honest actual version of PYZ `choiceOfShift`: one uniform translation
retains at least one third of the input rectangles and produces the complete
pair-local two-root/tangency records used by the proper-intersection count.

The input `rho` is the original tangency enlargement.  The hypotheses
`rho <= lambda` and `2 * (rho * delta) <= q * delta` respectively pay for
the translated tangency radius and enter the analytic trace estimate.
-/
theorem exists_uniform_threeShift_pairLocalActualLensRectangleData
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (items : Finset alpha) (T U : alpha -> Tube radius)
    (rectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    {A B delta t rho q lambda : Real}
    (hitems : items.Nonempty)
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda) (hrhoLambda : rho <= lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (htraceRadius : 2 * (rho * delta) <= q * delta)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (data : forall i, i ∈ items ->
      ActualTwoFamilyRectangleTangencyData
        (T i) (U i) f (rectangles i) A B delta t rho) :
    exists (k : Fin 3) (eta : Real) (fiber : Finset alpha)
      (_D : forall i, i ∈ fiber ->
        PairLocalActualLensRectangleData
          (traceTranslateTube (T i) (eta * (lambda * delta)))
          (U i) f (rectangles i) A B delta t lambda),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      items.card <= 3 * fiber.card := by
  let good : alpha -> Fin 3 -> Prop := fun i k =>
    Nonempty (PairLocalActualLensRectangleData
      (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
      (U i) f (rectangles i) A B delta t lambda)
  have hgood : forall i, i ∈ items -> exists k : Fin 3, good i k := by
    intro i hi
    let d := data i hi
    obtain ⟨etaInt, theta0, thetaLeft, thetaRight, hetaInt,
        _htheta0, _hcritical, _hendpoints, hthetaLeft, hrootLeft,
        hthetaRight, hrootRight⟩ :=
      actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots_automaticSharp
        (T i) (U i) f f1 f2 (rectangles i).rectangle.graph
        hdelta ht hq hlambda hshiftDominates hstrengthenedScale hwidth
        (rectangles i).rectangle.left_le_right d.left_mem_quarter
        d.right_mem_quarter d.rectangle_width d.common_c
        (by linarith [d.coefficient_lower]) hfDeriv hf1Deriv hparameter
        hft hf1Lower hf1Upper hf2 hf2Continuous hdelta.le
        (by
          simpa only [C2GraphRectangle.carrier, GraphRectangle.carrier,
            GraphRectangle.base]
            using d.tangent_first)
        (by
          simpa only [C2GraphRectangle.carrier, GraphRectangle.carrier,
            GraphRectangle.base]
            using d.tangent_second)
        htraceRadius
    have hetaReal : (etaInt : Real) ∈
        ({(-1 : Real), 0, 1} : Set Real) :=
      intCast_mem_real_threeShiftSet etaInt hetaInt
    obtain ⟨k, hk⟩ := exists_threeShiftLabel_of_mem hetaReal
    refine ⟨k, ?_⟩
    dsimp only [good]
    let shift : Real := threeShiftValue k * (lambda * delta)
    have hshiftEq : shift = (etaInt : Real) * (lambda * delta) := by
      dsimp only [shift]
      rw [hk]
    have hshiftSmall : |shift| < t := by
      exact abs_threeShift_displacement_lt_t k hdelta hq hlambda
        hstrengthenedScale
    have hcoefficientLower : t <=
        tubePairCoefficientDistance (traceTranslateTube (T i) shift) (U i) := by
      exact (calc
        t < 2 * t - |shift| := by linarith
        _ <= tubePairCoefficientDistance (T i) (U i) - |shift| := by
          linarith [d.coefficient_lower]
        _ <= tubePairCoefficientDistance
            (traceTranslateTube (T i) shift) (U i) :=
          tubePairCoefficientDistance_sub_abs_le_traceTranslateTube
            (T i) (U i) shift).le
    have hcommonShift :
        tubeGraphC (traceTranslateTube (T i) shift) = tubeGraphC (U i) := by
      simpa only [tubeGraphC_traceTranslateTube] using d.common_c
    have hactualLeft :
        cinematicTraceValue f
              (tubeGraphA (traceTranslateTube (T i) shift))
              (tubeGraphB (traceTranslateTube (T i) shift))
              (tubeGraphC (traceTranslateTube (T i) shift))
              (tubeGraphD (traceTranslateTube (T i) shift)) thetaLeft =
          cinematicTraceValue f
              (tubeGraphA (U i)) (tubeGraphB (U i))
              (tubeGraphC (U i)) (tubeGraphD (U i)) thetaLeft := by
      apply sub_eq_zero.mp
      apply actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
        (T i) (U i) f shift thetaLeft d.common_c
      simpa only [hshiftEq] using hrootLeft
    have hactualRight :
        cinematicTraceValue f
              (tubeGraphA (traceTranslateTube (T i) shift))
              (tubeGraphB (traceTranslateTube (T i) shift))
              (tubeGraphC (traceTranslateTube (T i) shift))
              (tubeGraphD (traceTranslateTube (T i) shift)) thetaRight =
          cinematicTraceValue f
              (tubeGraphA (U i)) (tubeGraphB (U i))
              (tubeGraphC (U i)) (tubeGraphD (U i)) thetaRight := by
      apply sub_eq_zero.mp
      apply actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
        (T i) (U i) f shift thetaRight d.common_c
      simpa only [hshiftEq] using hrootRight
    have hthetaOrder : thetaLeft < thetaRight :=
      hthetaLeft.2.trans hthetaRight.1
    have hleftMem : thetaLeft ∈ Icc A B :=
      ⟨hthetaLeft.1.le, hthetaOrder.le.trans hthetaRight.2.le⟩
    have hrightMem : thetaRight ∈ Icc A B :=
      ⟨hthetaLeft.1.le.trans hthetaOrder.le, hthetaRight.2.le⟩
    have hrootCard :
        (pairLocalActualRootSet
          (traceTranslateTube (T i) shift) (U i) f A B).encard <=
            (2 : ENat) := by
      change {z | z ∈ Icc A B ∧
        cinematicTraceValue f
            (tubeGraphA (traceTranslateTube (T i) shift))
            (tubeGraphB (traceTranslateTube (T i) shift))
            (tubeGraphC (traceTranslateTube (T i) shift))
            (tubeGraphD (traceTranslateTube (T i) shift)) z =
          cinematicTraceValue f
            (tubeGraphA (U i)) (tubeGraphB (U i))
            (tubeGraphC (U i)) (tubeGraphD (U i)) z}.encard <= 2
      exact tubeCinematicTrace_pair_rootSet_encard_le_two_global
          (traceTranslateTube (T i) shift) (U i) f f1 f2
          (show A <= B by linarith [hwidth]) hcommonShift
          (lt_of_lt_of_le ht hcoefficientLower) hparameter hft hf1Lower
          hf1Upper hf2 hfDeriv hf1Deriv
    have hrootSet : pairLocalActualRootSet
        (traceTranslateTube (T i) shift) (U i) f A B =
          {thetaLeft, thetaRight} := by
      apply set_eq_pair_of_encard_le_two_of_mem _ hrootCard
      · exact ⟨hleftMem, hactualLeft⟩
      · exact ⟨hrightMem, hactualRight⟩
      · exact ne_of_lt hthetaOrder
    have hshiftAbsLe : |shift| <= lambda * delta := by
      calc
        |shift| = |threeShiftValue k| * (lambda * delta) := by
          dsimp only [shift]
          rw [abs_mul, abs_of_pos (mul_pos hlambda hdelta)]
        _ <= 1 * (lambda * delta) :=
          mul_le_mul_of_nonneg_right (abs_threeShiftValue_le_one k)
            (mul_pos hlambda hdelta).le
        _ = lambda * delta := one_mul _
    have hfirstRadius : rho * delta + |shift| <=
        2 * lambda * delta := by
      have hrhoScale : rho * delta <= lambda * delta :=
        mul_le_mul_of_nonneg_right hrhoLambda hdelta.le
      linarith
    have hsecondRadius : rho * delta <= 2 * lambda * delta := by
      have hrhoScale : rho * delta <= lambda * delta :=
        mul_le_mul_of_nonneg_right hrhoLambda hdelta.le
      have hlambdaScale : 0 <= lambda * delta := (mul_pos hlambda hdelta).le
      linarith
    have htangentFirst : (rectangles i).carrier delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (traceTranslateTube (T i) shift))
            (tubeGraphB (traceTranslateTube (T i) shift))
            (tubeGraphC (traceTranslateTube (T i) shift))
            (tubeGraphD (traceTranslateTube (T i) shift)))
          (rectangles i).rectangle.base (2 * lambda * delta) := by
      exact (subset_cinematicVerticalNeighborhood_traceTranslateTube
        (T i) shift f (rectangles i).rectangle.base (rho * delta)
        ((rectangles i).carrier delta) d.tangent_first).trans
          (cinematicVerticalNeighborhood_mono_radius _ _ hfirstRadius)
    have htangentSecond : (rectangles i).carrier delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (U i)) (tubeGraphB (U i))
            (tubeGraphC (U i)) (tubeGraphD (U i)))
          (rectangles i).rectangle.base (2 * lambda * delta) := by
      exact d.tangent_second.trans
        (cinematicVerticalNeighborhood_mono_radius _ _ hsecondRadius)
    exact ⟨{
      thetaLeft := thetaLeft
      thetaRight := thetaRight
      theta_order := hthetaOrder
      thetaLeft_mem := hleftMem
      thetaRight_mem := hrightMem
      left_mem_quarter := d.left_mem_quarter
      right_mem_quarter := d.right_mem_quarter
      rectangle_width := d.rectangle_width
      common_c := hcommonShift
      root_left := hactualLeft
      root_right := hactualRight
      exact_root_set := hrootSet
      coefficient_lower := hcoefficientLower
      tangent_first := htangentFirst
      tangent_second := htangentSecond
    }⟩
  obtain ⟨k, hkNonempty, hkCard, hkGood⟩ :=
    exists_uniform_threeShift_fiber items good hitems hgood
  let fiber : Finset alpha :=
    threeShiftFiber items (chosenThreeShiftLabel items good hgood) k
  have hfiberSubset : fiber ⊆ items := by
    intro i hi
    exact (mem_threeShiftFiber_iff items
      (chosenThreeShiftLabel items good hgood) k i).mp hi |>.1
  let D : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData
        (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
        (U i) f (rectangles i) A B delta t lambda := fun i hi => by
    have hi' : i ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using hi
    exact Classical.choice (hkGood i hi')
  refine ⟨k, threeShiftValue k, fiber, D, rfl, threeShiftValue_mem k,
    ?_, hfiberSubset, ?_⟩
  · simpa only [fiber] using hkNonempty
  · simpa only [fiber] using hkCard

#print axioms abs_threeShiftValue_le_one
#print axioms tubePairCoefficientDistance_sub_abs_le_traceTranslateTube
#print axioms abs_threeShift_displacement_lt_t
#print axioms cinematicVerticalNeighborhood_mono_radius
#print axioms set_eq_pair_of_encard_le_two_of_mem
#print axioms exists_uniform_threeShift_pairLocalActualLensRectangleData

end

end FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
