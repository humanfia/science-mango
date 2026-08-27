import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
open FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
open FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1
open FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
open FamilyStickyCinematicL32Prop41ContinuousTransverseRootParityV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section
local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Reproducing exact roots after finite general-position perturbation

Individual vertical translations do not preserve an exact root set
literally: the ordered pair difference acquires the constant
`epsilon * (weight T - weight U)`.  What is stable is a strict three-point
sign bracket.  This module extracts such a bracket from the two-root
cinematic geometry, chooses an explicit positive perturbation margin, and
reruns the two-root producer after translation.
-/

/-- Three ordered samples whose consecutive values have opposite strict
signs.  This is the minimal open certificate needed to reproduce two roots
after a sufficiently small constant vertical perturbation. -/
structure StrictThreePointRootBracket (h : Real -> Real) (A B : Real) where
  left : Real
  middle : Real
  right : Real
  left_mem : left ∈ Icc A B
  middle_mem : middle ∈ Icc A B
  right_mem : right ∈ Icc A B
  left_lt_middle : left < middle
  middle_lt_right : middle < right
  left_middle_neg : h left * h middle < 0
  middle_right_neg : h middle * h right < 0

/-- The absolute sign margin of a strict three-point bracket. -/
def StrictThreePointRootBracket.margin
    {h : Real -> Real} {A B : Real}
    (C : StrictThreePointRootBracket h A B) : Real :=
  min |h C.left| (min |h C.middle| |h C.right|)

theorem StrictThreePointRootBracket.margin_pos
    {h : Real -> Real} {A B : Real}
    (C : StrictThreePointRootBracket h A B) :
    0 < C.margin := by
  have hleft : h C.left ≠ 0 := by
    intro hz
    have hneg := C.left_middle_neg
    rw [hz, zero_mul] at hneg
    linarith
  have hmiddle : h C.middle ≠ 0 := by
    intro hz
    have hneg := C.left_middle_neg
    rw [hz, mul_zero] at hneg
    linarith
  have hright : h C.right ≠ 0 := by
    intro hz
    have hneg := C.middle_right_neg
    rw [hz, mul_zero] at hneg
    linarith
  rw [StrictThreePointRootBracket.margin, lt_min_iff, lt_min_iff]
  exact ⟨abs_pos.mpr hleft, abs_pos.mpr hmiddle,
    abs_pos.mpr hright⟩

/-- Exact two roots, strict interiority, and uniqueness of the Rolle
critical point produce a robust outer--inner--outer sign bracket. -/
theorem strictThreePointRootBracket_of_exact_two_roots_and_uniqueCritical
    (h h1 : Real -> Real)
    {A B thetaLeft thetaRight theta0 : Real}
    (hAleft : A < thetaLeft) (hleftRight : thetaLeft < thetaRight)
    (hrightB : thetaRight < B)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hroots : {z | z ∈ Icc A B ∧ h z = 0} =
      ({thetaLeft, thetaRight} : Set Real))
    (htheta0 : theta0 ∈ Ioo thetaLeft thetaRight)
    (_hcritical : h1 theta0 = 0)
    (hcriticalUnique : forall z, z ∈ Icc A B -> h1 z = 0 ->
      z = theta0) :
    Nonempty (StrictThreePointRootBracket h A B) := by
  have hAB : A < B := hAleft.trans (hleftRight.trans hrightB)
  have hleftMem : thetaLeft ∈ Icc A B :=
    ⟨hAleft.le, hleftRight.le.trans hrightB.le⟩
  have hrightMem : thetaRight ∈ Icc A B :=
    ⟨hAleft.le.trans hleftRight.le, hrightB.le⟩
  have htheta0Mem : theta0 ∈ Icc A B :=
    ⟨hAleft.trans htheta0.1 |>.le, htheta0.2.trans hrightB |>.le⟩
  have hleftRoot : h thetaLeft = 0 := by
    have hmem : thetaLeft ∈ ({thetaLeft, thetaRight} : Set Real) := by simp
    rw [← hroots] at hmem
    exact hmem.2
  have hrightRoot : h thetaRight = 0 := by
    have hmem : thetaRight ∈ ({thetaLeft, thetaRight} : Set Real) := by simp
    rw [← hroots] at hmem
    exact hmem.2
  have hleftDerivativeNe : h1 thetaLeft ≠ 0 := by
    intro hzero
    have heq := hcriticalUnique thetaLeft hleftMem hzero
    linarith [htheta0.1]
  have hrightDerivativeNe : h1 thetaRight ≠ 0 := by
    intro hzero
    have heq := hcriticalUnique thetaRight hrightMem hzero
    linarith [htheta0.2]
  have hAne : h A ≠ 0 := by
    intro hzero
    have hmem : A ∈ ({thetaLeft, thetaRight} : Set Real) := by
      rw [← hroots]
      exact ⟨⟨le_rfl, hAB.le⟩, hzero⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> linarith
  have htheta0Ne : h theta0 ≠ 0 := by
    intro hzero
    have hmem : theta0 ∈ ({thetaLeft, thetaRight} : Set Real) := by
      rw [← hroots]
      exact ⟨htheta0Mem, hzero⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact (ne_of_gt htheta0.1) h
    · exact (ne_of_lt htheta0.2) h
  have hBne : h B ≠ 0 := by
    intro hzero
    have hmem : B ∈ ({thetaLeft, thetaRight} : Set Real) := by
      rw [← hroots]
      exact ⟨⟨hAB.le, le_rfl⟩, hzero⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> linarith
  have hleftRestricted :
      {z | z ∈ Icc A theta0 ∧ h z = 0} = ({thetaLeft} : Set Real) := by
    ext z
    constructor
    · rintro ⟨hz, hzero⟩
      have hglobal : z ∈ ({thetaLeft, thetaRight} : Set Real) := by
        rw [← hroots]
        exact ⟨⟨hz.1, hz.2.trans htheta0Mem.2⟩, hzero⟩
      rcases hglobal with h | h
      · simp [h]
      · subst z
        exfalso
        linarith [hz.2, htheta0.2]
    · intro hz
      have hzEq : z = thetaLeft := by simpa using hz
      subst z
      exact ⟨⟨hAleft.le, htheta0.1.le⟩, hleftRoot⟩
  have hrightRestricted :
      {z | z ∈ Icc theta0 B ∧ h z = 0} = ({thetaRight} : Set Real) := by
    ext z
    constructor
    · rintro ⟨hz, hzero⟩
      have hglobal : z ∈ ({thetaLeft, thetaRight} : Set Real) := by
        rw [← hroots]
        exact ⟨⟨htheta0Mem.1.trans hz.1, hz.2⟩, hzero⟩
      rcases hglobal with h | h
      · subst z
        exfalso
        linarith [hz.1, htheta0.1]
      · simp [h]
    · intro hz
      have hzEq : z = thetaRight := by simpa using hz
      subst z
      exact ⟨⟨htheta0.2.le, hrightB.le⟩, hrightRoot⟩
  have hleftProduct : h A * h theta0 < 0 :=
    endpoint_product_neg_of_unique_transverse_root
      h (hAleft.trans htheta0.1)
      (HasDerivAt.continuousOn fun z hz =>
        hderiv z ⟨hz.1, hz.2.trans htheta0Mem.2⟩)
      hAne htheta0Ne (by rw [hleftRestricted, ncard_singleton])
      (by
        intro z hz hzero
        have hzSingleton : z ∈ ({thetaLeft} : Set Real) := by
          rw [← hleftRestricted]
          exact ⟨hz, hzero⟩
        have hzEq : z = thetaLeft := by simpa using hzSingleton
        subst z
        exact ⟨h1 thetaLeft, hderiv thetaLeft hleftMem,
          hleftDerivativeNe⟩)
  have hrightProduct : h theta0 * h B < 0 :=
    endpoint_product_neg_of_unique_transverse_root
      h (htheta0.2.trans hrightB)
      (HasDerivAt.continuousOn fun z hz =>
        hderiv z ⟨htheta0Mem.1.trans hz.1, hz.2⟩)
      htheta0Ne hBne (by rw [hrightRestricted, ncard_singleton])
      (by
        intro z hz hzero
        have hzSingleton : z ∈ ({thetaRight} : Set Real) := by
          rw [← hrightRestricted]
          exact ⟨hz, hzero⟩
        have hzEq : z = thetaRight := by simpa using hzSingleton
        subst z
        exact ⟨h1 thetaRight, hderiv thetaRight hrightMem,
          hrightDerivativeNe⟩)
  exact ⟨{
    left := A
    middle := theta0
    right := B
    left_mem := ⟨le_rfl, hAB.le⟩
    middle_mem := htheta0Mem
    right_mem := ⟨hAB.le, le_rfl⟩
    left_lt_middle := hAleft.trans htheta0.1
    middle_lt_right := htheta0.2.trans hrightB
    left_middle_neg := hleftProduct
    middle_right_neg := hrightProduct
  }⟩

/-- Ordered difference of two literal actual-tube graphs. -/
def actualTubePairGraphDifference {radius : NNReal}
    (T U : Tube radius) (f : Real -> Real) (theta : Real) : Real :=
  cinematicTraceValue f
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
    cinematicTraceValue f
      (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta

/-- The exact two-root pair-local data produced before general position has a
strict sign bracket, provided its two roots retain the strict interiority
proved by the three-shift producer.  Sharp curvature and uniqueness of the
Rolle critical point are derived from the existing cinematic hypotheses. -/
theorem pairLocalActualData_strictThreePointRootBracket
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    {R : C2GraphRectangle} {A B delta t lambda0 : Real}
    (ht : 0 < t)
    (D : PairLocalActualLensRectangleData T U f R
      A B delta t lambda0)
    (hleftInterior : A < D.thetaLeft)
    (hrightInterior : D.thetaRight < B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    Nonempty (StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B) := by
  let da := tubePairDeltaA T U
  let db := tubePairDeltaB T U
  let dd := tubePairDeltaD T U
  let h : Real -> Real := traceFunction f da db dd
  let h1 : Real -> Real := traceFirstDerivative f f1 db dd
  have hcoefficient : 0 < coefficientDistance da db dd := by
    have hpositive : 0 < tubePairCoefficientDistance T U :=
      lt_of_lt_of_le ht D.coefficient_lower
    simpa only [tubePairCoefficientDistance, da, db, dd] using hpositive
  have hrootLeft : h D.thetaLeft = 0 := by
    dsimp only [h, da, db, dd]
    rw [← tube_cinematicTraceValue_sub_eq_traceFunction
      T U f D.common_c D.thetaLeft, D.root_left, sub_self]
  have hrootRight : h D.thetaRight = 0 := by
    dsimp only [h, da, db, dd]
    rw [← tube_cinematicTraceValue_sub_eq_traceFunction
      T U f D.common_c D.thetaRight, D.root_right, sub_self]
  have hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z (hfDeriv z hz)
  have hcurvature : forall z, z ∈ Icc A B ->
      coefficientDistance da db dd / 45 <
        |traceSecondDerivative f1 f2 db dd z| :=
    trace_two_ordered_roots_force_sharp_curvature
      f f1 f2 da db dd D.theta_order D.thetaLeft_mem D.thetaRight_mem
      hcoefficient hrootLeft hrootRight hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv
  obtain ⟨theta0, htheta0, hcritical⟩ :=
    exists_derivative_zero_between_zeros h h1 D.theta_order
      (fun z hz => hderiv z
        ⟨D.thetaLeft_mem.1.trans hz.1,
          hz.2.trans D.thetaRight_mem.2⟩)
      hrootLeft hrootRight
  have htheta0Mem : theta0 ∈ Icc A B :=
    ⟨D.thetaLeft_mem.1.trans htheta0.1.le,
      htheta0.2.le.trans D.thetaRight_mem.2⟩
  have hcriticalUnique : forall z, z ∈ Icc A B -> h1 z = 0 ->
      z = theta0 := by
    exact trace_criticalPoint_unique_of_sharp_curvature
      f f1 f2 db dd (coefficientDistance da db dd)
      htheta0Mem hcritical hcoefficient hfDeriv hf1Deriv hcurvature
  have hrootsTrace :
      {z | z ∈ Icc A B ∧ h z = 0} =
        ({D.thetaLeft, D.thetaRight} : Set Real) := by
    calc
      {z | z ∈ Icc A B ∧ h z = 0} =
          pairLocalActualRootSet T U f A B := by
        ext z
        constructor
        · rintro ⟨hz, hzero⟩
          refine ⟨hz, ?_⟩
          have hdiff := tube_cinematicTraceValue_sub_eq_traceFunction
            T U f D.common_c z
          change actualTubePairGraphDifference T U f z = h z at hdiff
          have hzeroDiff : actualTubePairGraphDifference T U f z = 0 :=
            hdiff.trans hzero
          exact sub_eq_zero.mp (by
            simpa only [actualTubePairGraphDifference] using hzeroDiff)
        · rintro ⟨hz, heq⟩
          refine ⟨hz, ?_⟩
          have hdiff := tube_cinematicTraceValue_sub_eq_traceFunction
            T U f D.common_c z
          change actualTubePairGraphDifference T U f z = h z at hdiff
          have hzeroDiff : actualTubePairGraphDifference T U f z = 0 := by
            simp only [actualTubePairGraphDifference, heq, sub_self]
          exact hdiff.symm.trans hzeroDiff
      _ = {D.thetaLeft, D.thetaRight} := D.exact_root_set
  obtain ⟨C⟩ :=
    strictThreePointRootBracket_of_exact_two_roots_and_uniqueCritical
      h h1 hleftInterior D.theta_order hrightInterior hderiv hrootsTrace
      htheta0 hcritical hcriticalUnique
  have hdiffEq : forall z,
      actualTubePairGraphDifference T U f z = h z := by
    intro z
    exact tube_cinematicTraceValue_sub_eq_traceFunction
      T U f D.common_c z
  exact ⟨{
    left := C.left
    middle := C.middle
    right := C.right
    left_mem := C.left_mem
    middle_mem := C.middle_mem
    right_mem := C.right_mem
    left_lt_middle := C.left_lt_middle
    middle_lt_right := C.middle_lt_right
    left_middle_neg := by
      rw [hdiffEq, hdiffEq]
      exact C.left_middle_neg
    middle_right_neg := by
      rw [hdiffEq, hdiffEq]
      exact C.middle_right_neg
  }⟩

/-- Adding a quantity smaller than both absolute values preserves a strict
opposite-sign pair. -/
theorem add_same_preserves_mul_neg
    {x y s : Real} (hxy : x * y < 0)
    (hsx : |s| < |x|) (hsy : |s| < |y|) :
    (x + s) * (y + s) < 0 := by
  rcases mul_neg_iff.mp hxy with h | h
  · have hx : 0 < x + s := by
      rw [abs_of_pos h.1] at hsx
      linarith [neg_abs_le s]
    have hy : y + s < 0 := by
      rw [abs_of_neg h.2] at hsy
      linarith [le_abs_self s]
    exact mul_neg_of_pos_of_neg hx hy
  · have hx : x + s < 0 := by
      rw [abs_of_neg h.1] at hsx
      linarith [le_abs_self s]
    have hy : 0 < y + s := by
      rw [abs_of_pos h.2] at hsy
      linarith [neg_abs_le s]
    exact mul_neg_of_neg_of_pos hx hy

theorem StrictThreePointRootBracket.signs_after_add
    {h : Real -> Real} {A B s : Real}
    (C : StrictThreePointRootBracket h A B)
    (hs : |s| < C.margin) :
    (h C.left + s) * (h C.middle + s) < 0 ∧
      (h C.middle + s) * (h C.right + s) < 0 := by
  have hsLeft : |s| < |h C.left| :=
    hs.trans_le (by
      rw [StrictThreePointRootBracket.margin]
      exact min_le_left _ _)
  have hsMiddle : |s| < |h C.middle| :=
    hs.trans_le (by
      rw [StrictThreePointRootBracket.margin]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hsRight : |s| < |h C.right| :=
    hs.trans_le (by
      rw [StrictThreePointRootBracket.margin]
      exact (min_le_right _ _).trans (min_le_right _ _))
  exact ⟨add_same_preserves_mul_neg C.left_middle_neg hsLeft hsMiddle,
    add_same_preserves_mul_neg C.middle_right_neg hsMiddle hsRight⟩

/-- Rerun the two-root producer after a small constant shift.  The two IVT
roots are automatically the entire root set once the cinematic root bound
is supplied. -/
theorem exists_ordered_exact_two_roots_after_small_add
    (h : Real -> Real) {A B s : Real}
    (C : StrictThreePointRootBracket h A B)
    (hcontinuous : ContinuousOn h (Icc A B))
    (hs : |s| < C.margin)
    (hcard : {z | z ∈ Icc A B ∧ h z + s = 0}.encard <=
      (2 : ENat)) :
    ∃ thetaLeft thetaRight,
      thetaLeft < thetaRight ∧
      thetaLeft ∈ Icc A B ∧ h thetaLeft + s = 0 ∧
      thetaRight ∈ Icc A B ∧ h thetaRight + s = 0 ∧
      {z | z ∈ Icc A B ∧ h z + s = 0} =
        {thetaLeft, thetaRight} := by
  have hsigns := C.signs_after_add hs
  have hcontinuousShift :
      ContinuousOn (fun z => h z + s) (Icc A B) :=
    hcontinuous.add continuousOn_const
  have hleftSignChange :
      (h C.left + s < 0 ∧ 0 < h C.middle + s) ∨
        (h C.middle + s < 0 ∧ 0 < h C.left + s) := by
    rcases mul_neg_iff.mp hsigns.1 with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl h
  have hrightSignChange :
      (h C.middle + s < 0 ∧ 0 < h C.right + s) ∨
        (h C.right + s < 0 ∧ 0 < h C.middle + s) := by
    rcases mul_neg_iff.mp hsigns.2 with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl h
  obtain ⟨thetaLeft, hthetaLeft, hrootLeft⟩ :=
    exists_root_Ioo_of_strict_sign_change
      (fun z => h z + s) C.left_lt_middle
      (hcontinuousShift.mono
        (Icc_subset_Icc C.left_mem.1 C.middle_mem.2))
      hleftSignChange
  obtain ⟨thetaRight, hthetaRight, hrootRight⟩ :=
    exists_root_Ioo_of_strict_sign_change
      (fun z => h z + s) C.middle_lt_right
      (hcontinuousShift.mono
        (Icc_subset_Icc C.middle_mem.1 C.right_mem.2))
      hrightSignChange
  have hthetaOrder : thetaLeft < thetaRight :=
    hthetaLeft.2.trans hthetaRight.1
  have hleftMem : thetaLeft ∈ Icc A B :=
    ⟨C.left_mem.1.trans hthetaLeft.1.le,
      hthetaLeft.2.le.trans C.middle_mem.2⟩
  have hrightMem : thetaRight ∈ Icc A B :=
    ⟨C.middle_mem.1.trans hthetaRight.1.le,
      hthetaRight.2.le.trans C.right_mem.2⟩
  have hrootSet :
      {z | z ∈ Icc A B ∧ h z + s = 0} =
        {thetaLeft, thetaRight} := by
    exact set_eq_pair_of_encard_le_two_of_mem _
      hcard ⟨hleftMem, hrootLeft⟩ ⟨hrightMem, hrootRight⟩
      (ne_of_lt hthetaOrder)
  exact ⟨thetaLeft, thetaRight, hthetaOrder, hleftMem, hrootLeft,
    hrightMem, hrootRight, hrootSet⟩

@[simp] theorem actualTubePairGraphDifference_individuallyTracePerturbedTube
    {radius : NNReal} (weight : Tube radius -> Real) (epsilon : Real)
    (T U : Tube radius) (f : Real -> Real) (theta : Real) :
    actualTubePairGraphDifference
        (individuallyTracePerturbedTube weight epsilon T)
        (individuallyTracePerturbedTube weight epsilon U) f theta =
      actualTubePairGraphDifference T U f theta +
        epsilon * (weight T - weight U) := by
  simp only [actualTubePairGraphDifference,
    individuallyTracePerturbedTube,
    cinematicTraceValue_traceTranslateTube]
  ring

/-- Explicit epsilon budget for preserving the two-root sign bracket of one
ordered retained pair.  Adding one to the denominator makes it positive
without a case split when the two weights happen to agree. -/
def pairRootReproductionTolerance
    {radius : NNReal} {f : Real -> Real} {A B : Real}
    (weight : Tube radius -> Real) (T U : Tube radius)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B) : Real :=
  C.margin / (|weight T - weight U| + 1)

theorem pairRootReproductionTolerance_pos
    {radius : NNReal} {f : Real -> Real} {A B : Real}
    (weight : Tube radius -> Real) (T U : Tube radius)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B) :
    0 < pairRootReproductionTolerance weight T U C := by
  apply div_pos C.margin_pos
  linarith [abs_nonneg (weight T - weight U)]

theorem abs_pair_perturbation_lt_margin
    {radius : NNReal} {f : Real -> Real} {A B epsilon : Real}
    (weight : Tube radius -> Real) (T U : Tube radius)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon <
      pairRootReproductionTolerance weight T U C) :
    |epsilon * (weight T - weight U)| < C.margin := by
  have hden : 0 < |weight T - weight U| + 1 := by
    linarith [abs_nonneg (weight T - weight U)]
  have hmul : epsilon * (|weight T - weight U| + 1) < C.margin := by
    exact (lt_div_iff₀ hden).mp hepsilon
  calc
    |epsilon * (weight T - weight U)| =
        epsilon * |weight T - weight U| := by
      rw [abs_mul, abs_of_pos hepsilonPos]
    _ < epsilon * (|weight T - weight U| + 1) := by
      apply mul_lt_mul_of_pos_left
      linarith
      exact hepsilonPos
    _ < C.margin := hmul

/-- Literal ordered roots and exact root carrier regenerated for a perturbed
actual-tube pair. -/
structure ReproducedPairLocalActualRoots
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (A B : Real) where
  thetaLeft : Real
  thetaRight : Real
  theta_order : thetaLeft < thetaRight
  thetaLeft_mem : thetaLeft ∈ Icc A B
  thetaRight_mem : thetaRight ∈ Icc A B
  root_left :
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) thetaLeft =
      cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U) thetaLeft
  root_right :
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) thetaRight =
      cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U) thetaRight
  exact_root_set : pairLocalActualRootSet T U f A B =
    {thetaLeft, thetaRight}

/-- A small individual tube perturbation does not keep the old roots fixed,
but the strict bracket and global cinematic root bound regenerate exactly
two new ordered roots for the already-perturbed tubes. -/
theorem exists_reproducedPairLocalActualRoots_after_individualPerturbation
    {radius : NNReal} (weight : Tube radius -> Real)
    (epsilon : Real) (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B : Real}
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon <
      pairRootReproductionTolerance weight T U C)
    (hAB : A <= B)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hcoefficient : 0 < tubePairCoefficientDistance
      (individuallyTracePerturbedTube weight epsilon T)
      (individuallyTracePerturbedTube weight epsilon U))
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    Nonempty (ReproducedPairLocalActualRoots
      (individuallyTracePerturbedTube weight epsilon T)
      (individuallyTracePerturbedTube weight epsilon U) f A B) := by
  let shiftedT := individuallyTracePerturbedTube weight epsilon T
  let shiftedU := individuallyTracePerturbedTube weight epsilon U
  let s := epsilon * (weight T - weight U)
  have hs : |s| < C.margin :=
    abs_pair_perturbation_lt_margin weight T U C hepsilonPos hepsilon
  have hcommonShift : tubeGraphC shiftedT = tubeGraphC shiftedU := by
    simpa only [shiftedT, shiftedU, individuallyTracePerturbedTube,
      tubeGraphC_traceTranslateTube] using hcommonC
  have hcontinuous :
      ContinuousOn (actualTubePairGraphDifference T U f) (Icc A B) := by
    apply HasDerivAt.continuousOn
    intro z hz
    exact (hasDerivAt_cinematicTraceValue f f1
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
      (hfDeriv z hz)).sub
      (hasDerivAt_cinematicTraceValue f f1
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
        (hfDeriv z hz))
  have hcardShift :
      {z | z ∈ Icc A B ∧
        actualTubePairGraphDifference T U f z + s = 0}.encard <=
          (2 : ENat) := by
    have hset :
        {z | z ∈ Icc A B ∧
          actualTubePairGraphDifference T U f z + s = 0} =
        {z | z ∈ Icc A B ∧
          cinematicTraceValue f
              (tubeGraphA shiftedT) (tubeGraphB shiftedT)
              (tubeGraphC shiftedT) (tubeGraphD shiftedT) z =
            cinematicTraceValue f
              (tubeGraphA shiftedU) (tubeGraphB shiftedU)
              (tubeGraphC shiftedU) (tubeGraphD shiftedU) z} := by
      ext z
      constructor
      · rintro ⟨hz, hzero⟩
        refine ⟨hz, ?_⟩
        have hdiff :
            actualTubePairGraphDifference shiftedT shiftedU f z = 0 := by
          simpa only [shiftedT, shiftedU, s,
            actualTubePairGraphDifference_individuallyTracePerturbedTube]
            using hzero
        exact sub_eq_zero.mp (by
          simpa only [actualTubePairGraphDifference] using hdiff)
      · rintro ⟨hz, heq⟩
        refine ⟨hz, ?_⟩
        have hdiff :
            actualTubePairGraphDifference shiftedT shiftedU f z = 0 := by
          simp only [actualTubePairGraphDifference, heq, sub_self]
        simpa only [shiftedT, shiftedU, s,
          actualTubePairGraphDifference_individuallyTracePerturbedTube]
          using hdiff
    rw [hset]
    exact tubeCinematicTrace_pair_rootSet_encard_le_two_global
      shiftedT shiftedU f f1 f2 hAB hcommonShift hcoefficient
      hparameter hft hf1Lower hf1Upper hf2 hfDeriv hf1Deriv
  obtain ⟨thetaLeft, thetaRight, hthetaOrder, hleftMem, hrootLeft,
      hrightMem, hrootRight, hrootSet⟩ :=
    exists_ordered_exact_two_roots_after_small_add
      (actualTubePairGraphDifference T U f) C hcontinuous hs hcardShift
  have hactualLeft :
      cinematicTraceValue f
          (tubeGraphA shiftedT) (tubeGraphB shiftedT)
          (tubeGraphC shiftedT) (tubeGraphD shiftedT) thetaLeft =
        cinematicTraceValue f
          (tubeGraphA shiftedU) (tubeGraphB shiftedU)
          (tubeGraphC shiftedU) (tubeGraphD shiftedU) thetaLeft := by
    apply sub_eq_zero.mp
    have hdiff :
        actualTubePairGraphDifference shiftedT shiftedU f thetaLeft = 0 := by
      simpa only [shiftedT, shiftedU, s,
        actualTubePairGraphDifference_individuallyTracePerturbedTube]
        using hrootLeft
    simpa only [actualTubePairGraphDifference] using hdiff
  have hactualRight :
      cinematicTraceValue f
          (tubeGraphA shiftedT) (tubeGraphB shiftedT)
          (tubeGraphC shiftedT) (tubeGraphD shiftedT) thetaRight =
        cinematicTraceValue f
          (tubeGraphA shiftedU) (tubeGraphB shiftedU)
          (tubeGraphC shiftedU) (tubeGraphD shiftedU) thetaRight := by
    apply sub_eq_zero.mp
    have hdiff :
        actualTubePairGraphDifference shiftedT shiftedU f thetaRight = 0 := by
      simpa only [shiftedT, shiftedU, s,
        actualTubePairGraphDifference_individuallyTracePerturbedTube]
        using hrootRight
    simpa only [actualTubePairGraphDifference] using hdiff
  have hrootSetActual :
      pairLocalActualRootSet shiftedT shiftedU f A B =
        {thetaLeft, thetaRight} := by
    rw [← hrootSet]
    ext z
    constructor
    · rintro ⟨hz, heq⟩
      refine ⟨hz, ?_⟩
      have hdiff :
          actualTubePairGraphDifference shiftedT shiftedU f z = 0 := by
        simp only [actualTubePairGraphDifference, heq, sub_self]
      simpa only [shiftedT, shiftedU, s,
        actualTubePairGraphDifference_individuallyTracePerturbedTube]
        using hdiff
    · rintro ⟨hz, hzero⟩
      refine ⟨hz, ?_⟩
      have hdiff :
          actualTubePairGraphDifference shiftedT shiftedU f z = 0 := by
        simpa only [shiftedT, shiftedU, s,
          actualTubePairGraphDifference_individuallyTracePerturbedTube]
          using hzero
      exact sub_eq_zero.mp (by
        simpa only [actualTubePairGraphDifference] using hdiff)
  exact ⟨{
    thetaLeft := thetaLeft
    thetaRight := thetaRight
    theta_order := hthetaOrder
    thetaLeft_mem := hleftMem
    thetaRight_mem := hrightMem
    root_left := hactualLeft
    root_right := hactualRight
    exact_root_set := hrootSetActual
  }⟩

/-- Translating both tubes decreases their reduced coefficient distance by at
most the sum of the two absolute vertical displacements. -/
theorem tubePairCoefficientDistance_sub_abs_sub_abs_le_translateBoth
    {radius : NNReal} (T U : Tube radius) (s r : Real) :
    tubePairCoefficientDistance T U - |s| - |r| <=
      tubePairCoefficientDistance
        (traceTranslateTube T s) (traceTranslateTube U r) := by
  have hfirst :=
    tubePairCoefficientDistance_sub_abs_le_traceTranslateTube T U s
  have hsecond :=
    tubePairCoefficientDistance_sub_abs_le_traceTranslateTube
      U (traceTranslateTube T s) r
  rw [tubePairCoefficientDistance_comm U (traceTranslateTube T s),
    tubePairCoefficientDistance_comm
      (traceTranslateTube U r) (traceTranslateTube T s)] at hsecond
  linarith

/-- Complete pair-local data are rebuilt on the perturbed tubes.  Root
stability is proved internally; the remaining displayed inequalities are
the literal coefficient and tangency-radius losses caused by Euclidean
translation. -/
theorem exists_pairLocalActualLensRectangleData_after_individualPerturbation
    {radius : NNReal} (weight : Tube radius -> Real)
    (epsilon : Real) (T U : Tube radius)
    (f f1 f2 : Real -> Real) (R : C2GraphRectangle)
    {A B delta t lambda0 lambda1 : Real}
    (ht : 0 < t)
    (D : PairLocalActualLensRectangleData T U f R
      A B delta t lambda0)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon <
      pairRootReproductionTolerance weight T U C)
    (hcoefficientLoss :
      |epsilon * weight T| + |epsilon * weight U| <=
        tubePairCoefficientDistance T U - t)
    (hfirstRadius :
      2 * lambda0 * delta + |epsilon * weight T| <=
        2 * lambda1 * delta)
    (hsecondRadius :
      2 * lambda0 * delta + |epsilon * weight U| <=
        2 * lambda1 * delta)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    Nonempty (PairLocalActualLensRectangleData
      (individuallyTracePerturbedTube weight epsilon T)
      (individuallyTracePerturbedTube weight epsilon U)
      f R A B delta t lambda1) := by
  let shiftedT := individuallyTracePerturbedTube weight epsilon T
  let shiftedU := individuallyTracePerturbedTube weight epsilon U
  have hAB : A <= B :=
    D.thetaLeft_mem.1.trans
      (D.theta_order.le.trans D.thetaRight_mem.2)
  have hcoefficientLower : t <=
      tubePairCoefficientDistance shiftedT shiftedU := by
    have hloss :=
      tubePairCoefficientDistance_sub_abs_sub_abs_le_translateBoth
        T U (epsilon * weight T) (epsilon * weight U)
    change t <= tubePairCoefficientDistance
      (traceTranslateTube T (epsilon * weight T))
      (traceTranslateTube U (epsilon * weight U))
    linarith
  have hcoefficientPositive : 0 <
      tubePairCoefficientDistance shiftedT shiftedU :=
    ht.trans_le hcoefficientLower
  obtain ⟨roots⟩ :=
    exists_reproducedPairLocalActualRoots_after_individualPerturbation
      weight epsilon T U f f1 f2 C hepsilonPos hepsilon hAB D.common_c
      hcoefficientPositive hfDeriv hf1Deriv hparameter hft hf1Lower
      hf1Upper hf2
  have hcommonShift : tubeGraphC shiftedT = tubeGraphC shiftedU := by
    simpa only [shiftedT, shiftedU, individuallyTracePerturbedTube,
      tubeGraphC_traceTranslateTube] using D.common_c
  have htangentFirst : R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA shiftedT) (tubeGraphB shiftedT)
          (tubeGraphC shiftedT) (tubeGraphD shiftedT))
        R.rectangle.base (2 * lambda1 * delta) := by
    exact (subset_cinematicVerticalNeighborhood_traceTranslateTube
      T (epsilon * weight T) f R.rectangle.base
      (2 * lambda0 * delta) (R.carrier delta) D.tangent_first).trans
        (cinematicVerticalNeighborhood_mono_radius _ _ hfirstRadius)
  have htangentSecond : R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA shiftedU) (tubeGraphB shiftedU)
          (tubeGraphC shiftedU) (tubeGraphD shiftedU))
        R.rectangle.base (2 * lambda1 * delta) := by
    exact (subset_cinematicVerticalNeighborhood_traceTranslateTube
      U (epsilon * weight U) f R.rectangle.base
      (2 * lambda0 * delta) (R.carrier delta) D.tangent_second).trans
        (cinematicVerticalNeighborhood_mono_radius _ _ hsecondRadius)
  exact ⟨{
    thetaLeft := roots.thetaLeft
    thetaRight := roots.thetaRight
    theta_order := roots.theta_order
    thetaLeft_mem := roots.thetaLeft_mem
    thetaRight_mem := roots.thetaRight_mem
    left_mem_quarter := D.left_mem_quarter
    right_mem_quarter := D.right_mem_quarter
    rectangle_width := D.rectangle_width
    common_c := hcommonShift
    root_left := roots.root_left
    root_right := roots.root_right
    exact_root_set := roots.exact_root_set
    coefficient_lower := hcoefficientLower
    tangent_first := htangentFirst
    tangent_second := htangentSecond
  }⟩

/-- A single explicit epsilon budget paying simultaneously for root
reproduction, coefficient separation, and both tangency-radius enlargements. -/
def pairLocalPerturbationTolerance
    {radius : NNReal} {f : Real -> Real} {A B : Real}
    (weight : Tube radius -> Real) (T U : Tube radius)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    (delta t lambda0 lambda1 : Real) : Real :=
  min (pairRootReproductionTolerance weight T U C)
    (min
      ((tubePairCoefficientDistance T U - t) /
        (|weight T| + |weight U| + 1))
      (min
        ((2 * lambda1 * delta - 2 * lambda0 * delta) /
          (|weight T| + 1))
        ((2 * lambda1 * delta - 2 * lambda0 * delta) /
          (|weight U| + 1))))

theorem pairLocalPerturbationTolerance_pos
    {radius : NNReal} {f : Real -> Real} {A B : Real}
    (weight : Tube radius -> Real) (T U : Tube radius)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    {delta t lambda0 lambda1 : Real}
    (hcoefficientStrict : t < tubePairCoefficientDistance T U)
    (htangencySlack :
      2 * lambda0 * delta < 2 * lambda1 * delta) :
    0 < pairLocalPerturbationTolerance
      weight T U C delta t lambda0 lambda1 := by
  have hcoeffDen : 0 < |weight T| + |weight U| + 1 := by
    linarith [abs_nonneg (weight T), abs_nonneg (weight U)]
  have hfirstDen : 0 < |weight T| + 1 := by
    linarith [abs_nonneg (weight T)]
  have hsecondDen : 0 < |weight U| + 1 := by
    linarith [abs_nonneg (weight U)]
  rw [pairLocalPerturbationTolerance, lt_min_iff, lt_min_iff,
    lt_min_iff]
  exact ⟨pairRootReproductionTolerance_pos weight T U C,
    div_pos (sub_pos.mpr hcoefficientStrict) hcoeffDen,
    div_pos (sub_pos.mpr htangencySlack) hfirstDen,
    div_pos (sub_pos.mpr htangencySlack) hsecondDen⟩

/-- The explicit local budget discharges all stability inequalities and
directly rebuilds complete pair-local data. -/
theorem exists_pairLocalActualLensRectangleData_after_individualPerturbation_of_lt_tolerance
    {radius : NNReal} (weight : Tube radius -> Real)
    (epsilon : Real) (T U : Tube radius)
    (f f1 f2 : Real -> Real) (R : C2GraphRectangle)
    {A B delta t lambda0 lambda1 : Real}
    (ht : 0 < t)
    (D : PairLocalActualLensRectangleData T U f R
      A B delta t lambda0)
    (C : StrictThreePointRootBracket
      (actualTubePairGraphDifference T U f) A B)
    (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon <
      pairLocalPerturbationTolerance
        weight T U C delta t lambda0 lambda1)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    Nonempty (PairLocalActualLensRectangleData
      (individuallyTracePerturbedTube weight epsilon T)
      (individuallyTracePerturbedTube weight epsilon U)
      f R A B delta t lambda1) := by
  have hepsilonRoot : epsilon <
      pairRootReproductionTolerance weight T U C :=
    hepsilon.trans_le (by
      rw [pairLocalPerturbationTolerance]
      exact min_le_left _ _)
  have hepsilonCoefficient : epsilon <
      (tubePairCoefficientDistance T U - t) /
        (|weight T| + |weight U| + 1) :=
    hepsilon.trans_le (by
      rw [pairLocalPerturbationTolerance]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hepsilonFirst : epsilon <
      (2 * lambda1 * delta - 2 * lambda0 * delta) /
        (|weight T| + 1) :=
    hepsilon.trans_le (by
      rw [pairLocalPerturbationTolerance]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsilonSecond : epsilon <
      (2 * lambda1 * delta - 2 * lambda0 * delta) /
        (|weight U| + 1) :=
    hepsilon.trans_le (by
      rw [pairLocalPerturbationTolerance]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hcoeffDen : 0 < |weight T| + |weight U| + 1 := by
    linarith [abs_nonneg (weight T), abs_nonneg (weight U)]
  have hfirstDen : 0 < |weight T| + 1 := by
    linarith [abs_nonneg (weight T)]
  have hsecondDen : 0 < |weight U| + 1 := by
    linarith [abs_nonneg (weight U)]
  have hcoeffBudget :
      epsilon * (|weight T| + |weight U| + 1) <
        tubePairCoefficientDistance T U - t :=
    (lt_div_iff₀ hcoeffDen).mp hepsilonCoefficient
  have hfirstBudget :
      epsilon * (|weight T| + 1) <
        2 * lambda1 * delta - 2 * lambda0 * delta :=
    (lt_div_iff₀ hfirstDen).mp hepsilonFirst
  have hsecondBudget :
      epsilon * (|weight U| + 1) <
        2 * lambda1 * delta - 2 * lambda0 * delta :=
    (lt_div_iff₀ hsecondDen).mp hepsilonSecond
  have hcoefficientLoss :
      |epsilon * weight T| + |epsilon * weight U| <=
        tubePairCoefficientDistance T U - t := by
    apply le_of_lt
    calc
      |epsilon * weight T| + |epsilon * weight U| =
          epsilon * (|weight T| + |weight U|) := by
        rw [abs_mul, abs_mul, abs_of_pos hepsilonPos]
        ring
      _ < epsilon * (|weight T| + |weight U| + 1) := by
        apply mul_lt_mul_of_pos_left
        · linarith
        · exact hepsilonPos
      _ < tubePairCoefficientDistance T U - t := hcoeffBudget
  have hfirstRadius :
      2 * lambda0 * delta + |epsilon * weight T| <=
        2 * lambda1 * delta := by
    apply le_of_lt
    rw [abs_mul, abs_of_pos hepsilonPos]
    nlinarith [abs_nonneg (weight T)]
  have hsecondRadius :
      2 * lambda0 * delta + |epsilon * weight U| <=
        2 * lambda1 * delta := by
    apply le_of_lt
    rw [abs_mul, abs_of_pos hepsilonPos]
    nlinarith [abs_nonneg (weight U)]
  exact exists_pairLocalActualLensRectangleData_after_individualPerturbation
    weight epsilon T U f f1 f2 R ht D C hepsilonPos hepsilonRoot
    hcoefficientLoss hfirstRadius hsecondRadius hfDeriv hf1Deriv
    hparameter hft hf1Lower hf1Upper hf2

/-- Finite-family endpoint: choose one arbitrarily small positive epsilon
which simultaneously gives A2--A3 on the literal perturbed tube family and
rebuilds exact pair-local root/lens data for every retained pair.  No
perturbation-stability proposition is assumed. -/
theorem exists_small_positive_actualTubeGeneralPosition_and_pairLocalData
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (rectangles : alpha -> C2GraphRectangle)
    (weight : Tube radius -> Real)
    (f f1 f2 : Real -> Real)
    {A B delta t lambda0 lambda1 externalTolerance : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (ht : 0 < t)
    (D : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData
        (T i) (U i) f (rectangles i) A B delta t lambda0)
    (hleftInterior : forall i (hi : i ∈ fiber),
      A < (D i hi).thetaLeft)
    (hrightInterior : forall i (hi : i ∈ fiber),
      (D i hi).thetaRight < B)
    (hcoefficientStrict : forall i, i ∈ fiber ->
      t < tubePairCoefficientDistance (T i) (U i))
    (htangencySlack :
      2 * lambda0 * delta < 2 * lambda1 * delta)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hweight : Set.InjOn weight
      (retainedPairTubeFamily fiber T U : Set (Tube radius)))
    (hcritical : forall V,
      V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> V ≠ W ->
        (criticalHeightDifferenceSet
          (fun X => actualTubeGraph X f)
          (fun X => actualTubeGraphFirst X f f1) A B V W).Finite) :
    ∃ epsilon, 0 < epsilon ∧ epsilon < externalTolerance ∧
      Set.InjOn (individuallyTracePerturbedTube weight epsilon)
        (retainedPairTubeFamily fiber T U : Set (Tube radius)) ∧
      (individuallyTracePerturbedTubeFamily
        (retainedPairTubeFamily fiber T U) weight epsilon).card =
          (retainedPairTubeFamily fiber T U).card ∧
      EndpointValuesDistinct
        (individuallyTracePerturbedTubeFamily
          (retainedPairTubeFamily fiber T U) weight epsilon)
        (fun V => actualTubeGraph V f) A B ∧
      NoTangentialGraphIntersections
        (individuallyTracePerturbedTubeFamily
          (retainedPairTubeFamily fiber T U) weight epsilon)
        (fun V => actualTubeGraph V f)
        (fun V => actualTubeGraphFirst V f f1) A B ∧
      Nonempty (forall i, i ∈ fiber ->
        PairLocalActualLensRectangleData
          (individuallyTracePerturbedTube weight epsilon (T i))
          (individuallyTracePerturbedTube weight epsilon (U i))
          f (rectangles i) A B delta t lambda1) := by
  classical
  let attached := fiber.attach
  have hattached : attached.Nonempty := by
    obtain ⟨i, hi⟩ := hfiber
    exact ⟨⟨i, hi⟩, by simp [attached]⟩
  let bracket : forall i : {i // i ∈ fiber},
      StrictThreePointRootBracket
        (actualTubePairGraphDifference (T i.1) (U i.1) f) A B :=
    fun i => Classical.choice
      (pairLocalActualData_strictThreePointRootBracket
        (T i.1) (U i.1) f f1 f2 ht (D i.1 i.2)
        (hleftInterior i.1 i.2) (hrightInterior i.1 i.2)
        hfDeriv hf1Deriv hparameter hft hf1Lower hf1Upper hf2)
  let localTolerance : {i // i ∈ fiber} -> Real := fun i =>
    pairLocalPerturbationTolerance weight (T i.1) (U i.1)
      (bracket i) delta t lambda0 lambda1
  have hlocalTolerance : forall i : {i // i ∈ fiber},
      0 < localTolerance i := by
    intro i
    exact pairLocalPerturbationTolerance_pos
      weight (T i.1) (U i.1) (bracket i)
      (hcoefficientStrict i.1 i.2) htangencySlack
  let geometricTolerance : Real :=
    attached.inf' hattached localTolerance
  have hgeometricTolerance : 0 < geometricTolerance := by
    dsimp only [geometricTolerance]
    rw [Finset.lt_inf'_iff]
    intro i _hi
    exact hlocalTolerance i
  let tolerance := min externalTolerance geometricTolerance
  have htolerance : 0 < tolerance := by
    dsimp only [tolerance]
    rw [lt_min_iff]
    exact ⟨hexternalTolerance, hgeometricTolerance⟩
  obtain ⟨epsilon, hepsilonPos, hepsilonSmall, hinjective, hcard,
      hA2, hA3⟩ :=
    exists_small_positive_actualTubeGeneralPosition
      (retainedPairTubeFamily fiber T U) weight f f1 A B tolerance
      htolerance hweight hcritical
  have hepsilonExternal : epsilon < externalTolerance :=
    hepsilonSmall.trans_le (by
      dsimp only [tolerance]
      exact min_le_left _ _)
  have hepsilonLocal : forall i : {i // i ∈ fiber},
      epsilon < localTolerance i := by
    intro i
    have hepsilonGeometric : epsilon < geometricTolerance :=
      hepsilonSmall.trans_le (by
        dsimp only [tolerance]
        exact min_le_right _ _)
    exact hepsilonGeometric.trans_le
      (Finset.inf'_le localTolerance (by simp [attached]))
  have hdata : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData
        (individuallyTracePerturbedTube weight epsilon (T i))
        (individuallyTracePerturbedTube weight epsilon (U i))
        f (rectangles i) A B delta t lambda1 := by
    intro i hi
    exact Classical.choice
      (exists_pairLocalActualLensRectangleData_after_individualPerturbation_of_lt_tolerance
        weight epsilon (T i) (U i) f f1 f2 (rectangles i) ht
        (D i hi) (bracket ⟨i, hi⟩) hepsilonPos
        (hepsilonLocal ⟨i, hi⟩) hfDeriv hf1Deriv hparameter hft
        hf1Lower hf1Upper hf2)
  exact ⟨epsilon, hepsilonPos, hepsilonExternal, hinjective, hcard,
    hA2, hA3, ⟨hdata⟩⟩


/-! ## Zero-bookkeeping connector from the three-shift producer -/

/-- Pair-local data together with exactly the open conditions needed to
rerun its two-root construction after a sufficiently small perturbation.
The last field records the radius enlargement budget once, rather than
asking a downstream caller to reconstruct it from `lambda0`, `lambda1`,
and `delta`. -/
structure PerturbationReadyPairLocalActualLensRectangleData
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (R : C2GraphRectangle)
    (A B delta t lambda0 lambda1 : Real) where
  data : PairLocalActualLensRectangleData
    T U f R A B delta t lambda0
  thetaLeft_interior : A < data.thetaLeft
  thetaRight_interior : data.thetaRight < B
  coefficient_strict : t < tubePairCoefficientDistance T U
  tangency_slack : 2 * lambda0 * delta < 2 * lambda1 * delta

/-- Strengthened form of the actual uniform three-shift producer.  It
retains the strict root-interiority and coefficient inequalities already
proved inside the old construction, and chooses the concrete enlarged
radius parameter `2 * lambda`.  Thus none of the open perturbation budgets
are discarded at the producer boundary. -/
theorem exists_uniform_threeShift_perturbationReadyPairLocalActualLensRectangleData
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
      (_P : forall i, i ∈ fiber ->
        PerturbationReadyPairLocalActualLensRectangleData
          (traceTranslateTube (T i) (eta * (lambda * delta)))
          (U i) f (rectangles i) A B delta t lambda (2 * lambda)),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      items.card <= 3 * fiber.card := by
  let good : alpha -> Fin 3 -> Prop := fun i k =>
    Nonempty (PerturbationReadyPairLocalActualLensRectangleData
      (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
      (U i) f (rectangles i) A B delta t lambda (2 * lambda))
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
    have hcoefficientStrict : t <
        tubePairCoefficientDistance
          (traceTranslateTube (T i) shift) (U i) := by
      calc
        t < 2 * t - |shift| := by linarith
        _ <= tubePairCoefficientDistance (T i) (U i) - |shift| := by
          linarith [d.coefficient_lower]
        _ <= tubePairCoefficientDistance
            (traceTranslateTube (T i) shift) (U i) :=
          tubePairCoefficientDistance_sub_abs_le_traceTranslateTube
            (T i) (U i) shift
    have hcoefficientLower : t <=
        tubePairCoefficientDistance
          (traceTranslateTube (T i) shift) (U i) :=
      hcoefficientStrict.le
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
      have hlambdaScale : 0 <= lambda * delta :=
        (mul_pos hlambda hdelta).le
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
      data := {
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
      }
      thetaLeft_interior := hthetaLeft.1
      thetaRight_interior := hthetaRight.2
      coefficient_strict := hcoefficientStrict
      tangency_slack := by
        nlinarith [mul_pos hlambda hdelta]
    }⟩
  obtain ⟨k, hkNonempty, hkCard, hkGood⟩ :=
    exists_uniform_threeShift_fiber items good hitems hgood
  let fiber : Finset alpha :=
    threeShiftFiber items (chosenThreeShiftLabel items good hgood) k
  have hfiberSubset : fiber ⊆ items := by
    intro i hi
    exact (mem_threeShiftFiber_iff items
      (chosenThreeShiftLabel items good hgood) k i).mp hi |>.1
  let P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
        (U i) f (rectangles i) A B delta t lambda (2 * lambda) :=
    fun i hi => by
      have hi' : i ∈ threeShiftFiber items
          (chosenThreeShiftLabel items good hgood) k := by
        simpa only [fiber] using hi
      exact Classical.choice (hkGood i hi')
  refine ⟨k, threeShiftValue k, fiber, P, rfl, threeShiftValue_mem k,
    ?_, hfiberSubset, ?_⟩
  · simpa only [fiber] using hkNonempty
  · simpa only [fiber] using hkCard

/-- A perturbation-ready family feeds the finite general-position theorem
without any separately supplied root-interiority, coefficient, or tangency
slack proofs. -/
theorem exists_small_positive_actualTubeGeneralPosition_and_pairLocalData_of_perturbationReady
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (rectangles : alpha -> C2GraphRectangle)
    (weight : Tube radius -> Real)
    (f f1 f2 : Real -> Real)
    {A B delta t lambda0 lambda1 externalTolerance : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (ht : 0 < t)
    (P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T i) (U i) f (rectangles i)
          A B delta t lambda0 lambda1)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hweight : Set.InjOn weight
      (retainedPairTubeFamily fiber T U : Set (Tube radius)))
    (hcritical : forall V,
      V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> V ≠ W ->
        (criticalHeightDifferenceSet
          (fun X => actualTubeGraph X f)
          (fun X => actualTubeGraphFirst X f f1) A B V W).Finite) :
    ∃ epsilon, 0 < epsilon ∧ epsilon < externalTolerance ∧
      Set.InjOn (individuallyTracePerturbedTube weight epsilon)
        (retainedPairTubeFamily fiber T U : Set (Tube radius)) ∧
      (individuallyTracePerturbedTubeFamily
        (retainedPairTubeFamily fiber T U) weight epsilon).card =
          (retainedPairTubeFamily fiber T U).card ∧
      EndpointValuesDistinct
        (individuallyTracePerturbedTubeFamily
          (retainedPairTubeFamily fiber T U) weight epsilon)
        (fun V => actualTubeGraph V f) A B ∧
      NoTangentialGraphIntersections
        (individuallyTracePerturbedTubeFamily
          (retainedPairTubeFamily fiber T U) weight epsilon)
        (fun V => actualTubeGraph V f)
        (fun V => actualTubeGraphFirst V f f1) A B ∧
      Nonempty (forall i, i ∈ fiber ->
        PairLocalActualLensRectangleData
          (individuallyTracePerturbedTube weight epsilon (T i))
          (individuallyTracePerturbedTube weight epsilon (U i))
          f (rectangles i) A B delta t lambda1) := by
  obtain ⟨i0, hi0⟩ := hfiber
  exact exists_small_positive_actualTubeGeneralPosition_and_pairLocalData
    fiber ⟨i0, hi0⟩ T U rectangles weight f f1 f2 hexternalTolerance ht
    (fun i hi => (P i hi).data)
    (fun i hi => (P i hi).thetaLeft_interior)
    (fun i hi => (P i hi).thetaRight_interior)
    (fun i hi => (P i hi).coefficient_strict)
    (P i0 hi0).tangency_slack hfDeriv hf1Deriv hparameter hft
    hf1Lower hf1Upper hf2 hweight hcritical

#print axioms exists_uniform_threeShift_perturbationReadyPairLocalActualLensRectangleData
#print axioms exists_small_positive_actualTubeGeneralPosition_and_pairLocalData_of_perturbationReady
#print axioms StrictThreePointRootBracket.margin_pos
#print axioms strictThreePointRootBracket_of_exact_two_roots_and_uniqueCritical
#print axioms pairLocalActualData_strictThreePointRootBracket
#print axioms add_same_preserves_mul_neg
#print axioms exists_ordered_exact_two_roots_after_small_add
#print axioms actualTubePairGraphDifference_individuallyTracePerturbedTube
#print axioms pairRootReproductionTolerance_pos
#print axioms exists_reproducedPairLocalActualRoots_after_individualPerturbation
#print axioms tubePairCoefficientDistance_sub_abs_sub_abs_le_translateBoth
#print axioms exists_pairLocalActualLensRectangleData_after_individualPerturbation
#print axioms pairLocalPerturbationTolerance_pos
#print axioms exists_pairLocalActualLensRectangleData_after_individualPerturbation_of_lt_tolerance
#print axioms exists_small_positive_actualTubeGeneralPosition_and_pairLocalData

end

end FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
