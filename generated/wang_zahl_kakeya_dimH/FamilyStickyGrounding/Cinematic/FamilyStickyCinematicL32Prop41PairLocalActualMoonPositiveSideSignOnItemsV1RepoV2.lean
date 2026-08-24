import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PositiveBetweenTwoTransverseRootsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonPositiveSideSignOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41PositiveBetweenTwoTransverseRootsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Exact sign characterization of an actual positive moon side

The positive side carrier is first identified with the neighbor graph arc.
The pair-local exact two-root set, A2 endpoint separation, and A3
transversality then prove that this open support is exactly the parameter set
on which the neighbor graph lies strictly below the host graph.
-/

theorem pairLocalActualMoonPositiveSideSet_eq_neighborGraphArc_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items host neighbor) :
    moonPositiveSideSet arc =
      graphArc (actualTubeGraph neighbor.1 f)
        (Ioo (D arc.pair arc.pair_mem).thetaLeft (D arc.pair arc.pair_mem).thetaRight) := by
  classical
  have hother := pairLocalActualItemSelectedOtherCurve_eq_of_pair T U hT hU hpair
    arc.pair host neighbor arc.pair_eq
  by_cases hfirst : host = pairLocalActualItemSelectedFirstCurve T hT arc.pair
  · have hneighbor : pairLocalActualItemSelectedSecondCurve U hU arc.pair = neighbor := by
      simpa [pairLocalActualItemSelectedOtherCurve, hfirst] using hother
    have hraw : U arc.pair = neighbor.1 := congrArg Subtype.val hneighbor
    rw [moonPositiveSideSet, if_pos]
    · rw [pairLocalActualSelectedLensLocalAngleGeometryOnItems_secondOpenSide
        curves items T U hT hU hpair rectangles f f1 A B M depth D
          arc.pair arc.pair_mem]
      exact congrArg
        (fun V : Tube radius => graphArc (actualTubeGraph V f)
          (Ioo (D arc.pair arc.pair_mem).thetaLeft (D arc.pair arc.pair_mem).thetaRight)) hraw
    · exact hfirst
  · have hneighbor : pairLocalActualItemSelectedFirstCurve T hT arc.pair = neighbor := by
      simpa [pairLocalActualItemSelectedOtherCurve, hfirst] using hother
    have hraw : T arc.pair = neighbor.1 := congrArg Subtype.val hneighbor
    rw [moonPositiveSideSet, if_neg]
    · rw [pairLocalActualSelectedLensLocalAngleGeometryOnItems_firstOpenSide
        curves items T U hT hU hpair rectangles f f1 A B M depth D
          arc.pair arc.pair_mem]
      exact congrArg
        (fun V : Tube radius => graphArc (actualTubeGraph V f)
          (Ioo (D arc.pair arc.pair_mem).thetaLeft (D arc.pair arc.pair_mem).thetaRight)) hraw
    · exact hfirst

theorem actualTubeGraph_root_right_of_itemSelected_pair
    {radius : NNReal} {curves : Finset (Tube radius)}
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f : Real -> Real) (A B : Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (p : FirstGenerationCurvePair curves) (hpMem : p ∈ items)
    (host neighbor : FirstGenerationCurve curves)
    (hhostNeighbor : p.1 = s(host, neighbor)) :
    actualTubeGraph host.1 f (D p hpMem).thetaRight =
      actualTubeGraph neighbor.1 f (D p hpMem).thetaRight := by
  have hroot : actualTubeGraph (T p) f (D p hpMem).thetaRight =
      actualTubeGraph (U p) f (D p hpMem).thetaRight := by
    simpa only [actualTubeGraph, cinematicTraceValue,
      skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
      tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using (D p hpMem).root_right
  have horient :
      s(pairLocalActualItemSelectedFirstCurve T hT p,
          pairLocalActualItemSelectedSecondCurve U hU p) = s(host, neighbor) :=
    (hpair p).symm.trans hhostNeighbor
  rw [Sym2.eq_iff] at horient
  rcases horient with horient | horient
  · have hTv : T p = host.1 := congrArg Subtype.val horient.1
    have hUv : U p = neighbor.1 := congrArg Subtype.val horient.2
    simpa [hTv, hUv] using hroot
  · have hTv : T p = neighbor.1 := congrArg Subtype.val horient.1
    have hUv : U p = host.1 := congrArg Subtype.val horient.2
    simpa [hTv, hUv] using hroot.symm

/-- Exact parameter/sign characterization for one literal actual positive
moon side. -/
theorem pairLocalActualMoonPositiveSide_mem_iff_neighbor_lt_host_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) {A B : Real} (_hAB : A < B) (M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (hendpoint : EndpointValuesDistinct curves
      (fun V => actualTubeGraph V f) A B)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items host neighbor)
    {theta : Real} (htheta : theta ∈ Icc A B) :
    theta ∈ Ioo (D arc.pair arc.pair_mem).thetaLeft (D arc.pair arc.pair_mem).thetaRight ↔
      actualTubeGraph neighbor.1 f theta < actualTubeGraph host.1 f theta := by
  have hhostNeighborNe : host ≠ neighbor := by
    intro heq
    apply arc.pair.2
    rw [arc.pair_eq, Sym2.mk_isDiag_iff]
    exact heq
  have hrawNe : host.1 ≠ neighbor.1 := by
    intro heq
    exact hhostNeighborNe (Subtype.ext heq)
  have hleftRoot := actualTubeGraph_root_left_of_itemSelected_pair items T U hT hU
    hpair rectangles f A B D arc.pair arc.pair_mem host neighbor arc.pair_eq
  have hrightRoot := actualTubeGraph_root_right_of_itemSelected_pair items T U hT hU
    hpair rectangles f A B D arc.pair arc.pair_mem host neighbor arc.pair_eq
  have hleftNeA : (D arc.pair arc.pair_mem).thetaLeft ≠ A := by
    intro heq
    apply hrawNe
    apply hendpoint.1 host.2 neighbor.2
    simpa [heq] using hleftRoot
  have hrightNeB : (D arc.pair arc.pair_mem).thetaRight ≠ B := by
    intro heq
    apply hrawNe
    apply hendpoint.2 host.2 neighbor.2
    simpa [heq] using hrightRoot
  have hAleft : A < (D arc.pair arc.pair_mem).thetaLeft :=
    lt_of_le_of_ne (D arc.pair arc.pair_mem).thetaLeft_mem.1 (Ne.symm hleftNeA)
  have hrightB : (D arc.pair arc.pair_mem).thetaRight < B :=
    lt_of_le_of_ne (D arc.pair arc.pair_mem).thetaRight_mem.2 hrightNeB
  let roots : Set Real := {z | z ∈ Icc A B ∧
    actualTubeGraph host.1 f z = actualTubeGraph neighbor.1 f z}
  have hroots : roots =
      ({(D arc.pair arc.pair_mem).thetaLeft, (D arc.pair arc.pair_mem).thetaRight} : Set Real) := by
    have horient :
        s(pairLocalActualItemSelectedFirstCurve T hT arc.pair,
            pairLocalActualItemSelectedSecondCurve U hU arc.pair) = s(host, neighbor) :=
      (hpair arc.pair).symm.trans arc.pair_eq
    rw [Sym2.eq_iff] at horient
    rcases horient with horient | horient
    · have hTv : T arc.pair = host.1 := congrArg Subtype.val horient.1
      have hUv : U arc.pair = neighbor.1 := congrArg Subtype.val horient.2
      simpa only [roots, pairLocalActualRootSet, hTv, hUv,
        actualTubeGraph, cinematicTraceValue, skirtTubeGraphA,
        skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA,
        tubeGraphB, tubeGraphC, tubeGraphD] using
        (D arc.pair arc.pair_mem).exact_root_set
    · have hTv : T arc.pair = neighbor.1 := congrArg Subtype.val horient.1
      have hUv : U arc.pair = host.1 := congrArg Subtype.val horient.2
      have hswapped :
          {z | z ∈ Icc A B ∧
            actualTubeGraph neighbor.1 f z = actualTubeGraph host.1 f z} =
            ({(D arc.pair arc.pair_mem).thetaLeft,
              (D arc.pair arc.pair_mem).thetaRight} : Set Real) := by
        simpa only [pairLocalActualRootSet, hTv, hUv,
          actualTubeGraph, cinematicTraceValue, skirtTubeGraphA,
          skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA,
          tubeGraphB, tubeGraphC, tubeGraphD] using
          (D arc.pair arc.pair_mem).exact_root_set
      rw [← hswapped]
      ext z
      constructor
      · rintro ⟨hz, heq⟩
        exact ⟨hz, heq.symm⟩
      · rintro ⟨hz, heq⟩
        exact ⟨hz, heq.symm⟩
  have hpositive : forall z,
      z ∈ Ioo (D arc.pair arc.pair_mem).thetaLeft (D arc.pair arc.pair_mem).thetaRight ->
      0 < actualTubeGraph host.1 f z - actualTubeGraph neighbor.1 f z := by
    intro z hz
    have hsideEq := pairLocalActualMoonPositiveSideSet_eq_neighborGraphArc_onItems curves items
      T U hT hU hpair rectangles f f1 A B M depth D arc
    have hqSide :
        (actualTubeGraph neighbor.1 f z, z) ∈ moonPositiveSideSet arc := by
      rw [hsideEq]
      exact ⟨hz, rfl⟩
    have hqInterior := moonPositiveSideSet_subset_hostInterior arc hqSide
    change (actualTubeGraph neighbor.1 f z, z) ∈
      pairLocalItemRectangularSkirtInterior (actualTubeGraph host.1 f) A B M (depth host)
      at hqInterior
    rcases hqInterior with ⟨_, _, hupper⟩
    have hzAB : z ∈ Ioo A B :=
      ⟨hAleft.trans hz.1, hz.2.trans hrightB⟩
    have htop : pairLocalItemRectangularSkirtTopGraph
        (actualTubeGraph host.1 f) A B z = actualTubeGraph host.1 f z := by
      simp [pairLocalItemRectangularSkirtTopGraph, not_lt.mpr hzAB.1.le, hzAB.2.le]
    rw [htop] at hupper
    linarith
  have hhostContinuous : ContinuousOn (actualTubeGraph host.1 f) (Icc A B) :=
    fun z _ =>
      (hasDerivAt_actualTubeGraph host.1 (hfDeriv z)).continuousAt.continuousWithinAt
  have hneighborContinuous :
      ContinuousOn (actualTubeGraph neighbor.1 f) (Icc A B) :=
    fun z _ =>
      (hasDerivAt_actualTubeGraph neighbor.1 (hfDeriv z)).continuousAt.continuousWithinAt
  have hcontinuous : ContinuousOn
      (fun z => actualTubeGraph host.1 f z - actualTubeGraph neighbor.1 f z)
      (Icc A B) :=
    hhostContinuous.sub hneighborContinuous
  have htransverse : forall z, z ∈ Icc A B ->
      actualTubeGraph host.1 f z - actualTubeGraph neighbor.1 f z = 0 ->
      exists derivative : Real,
        HasDerivAt
          (fun w => actualTubeGraph host.1 f w - actualTubeGraph neighbor.1 f w)
          derivative z ∧ derivative ≠ 0 := by
    intro z hz hzero
    refine ⟨actualTubeGraphFirst host.1 f f1 z -
        actualTubeGraphFirst neighbor.1 f f1 z,
      (hasDerivAt_actualTubeGraph host.1 (hfDeriv z)).sub
        (hasDerivAt_actualTubeGraph neighbor.1 (hfDeriv z)), ?_⟩
    intro hfirstZero
    exact hA3 host.1 host.2 neighbor.1 neighbor.2 hrawNe z hz
      ⟨sub_eq_zero.mp hzero, sub_eq_zero.mp hfirstZero⟩
  have hscalar := mem_Ioo_iff_pos_of_exact_two_transverse_roots
    (fun z => actualTubeGraph host.1 f z - actualTubeGraph neighbor.1 f z)
    hAleft (D arc.pair arc.pair_mem).theta_order hrightB hcontinuous
    (by simpa only [roots, sub_eq_zero] using hroots) hpositive htransverse htheta
  simpa only [sub_pos] using hscalar

#print axioms pairLocalActualMoonPositiveSideSet_eq_neighborGraphArc_onItems
#print axioms actualTubeGraph_root_right_of_itemSelected_pair
#print axioms pairLocalActualMoonPositiveSide_mem_iff_neighbor_lt_host_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonPositiveSideSignOnItemsV1
