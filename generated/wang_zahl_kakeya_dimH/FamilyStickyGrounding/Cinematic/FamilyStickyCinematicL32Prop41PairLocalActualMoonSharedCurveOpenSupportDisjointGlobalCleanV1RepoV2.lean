import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CommonGraphArcSupportOverlapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonSharedCurveOpenSupportDisjointGlobalCleanV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1
open FamilyStickyCinematicL32Prop41CommonGraphArcSupportOverlapV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

private def actualTrace {radius : NNReal} (V : Tube radius)
    (f : Real -> Real) : Real -> Real :=
  cinematicTraceValue f (tubeGraphA V) (tubeGraphB V)
    (tubeGraphC V) (tubeGraphD V)

private theorem actualPairGraphBoundary_contains_curveArc
    {radius : NNReal} (T U V : Tube radius) (f : Real -> Real)
    {left right : Real} (hV : T = V ∨ U = V) :
    graphArc (actualTrace V f) (Icc left right) ⊆
      actualPairGraphBoundary T U f left right := by
  intro q hq
  rcases hV with rfl | rfl
  · exact Or.inl hq
  · exact Or.inr hq

theorem pairLocalActualMoon_actualPairBoundary_contains_hostArc_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items host neighbor) :
    graphArc (actualTrace host.1 f)
        (Icc (D arc.pair arc.pair_mem).thetaLeft
          (D arc.pair arc.pair_mem).thetaRight) ⊆
      actualPairGraphBoundary (T arc.pair) (U arc.pair) f
        (D arc.pair arc.pair_mem).thetaLeft
        (D arc.pair arc.pair_mem).thetaRight := by
  have horient :
      s(pairLocalActualItemSelectedFirstCurve T hT arc.pair,
          pairLocalActualItemSelectedSecondCurve U hU arc.pair) =
        s(host, neighbor) :=
    (hpair arc.pair).symm.trans arc.pair_eq
  rw [Sym2.eq_iff] at horient
  apply actualPairGraphBoundary_contains_curveArc
  rcases horient with horient | horient
  · exact Or.inl (congrArg Subtype.val horient.1)
  · exact Or.inr (congrArg Subtype.val horient.2)

theorem pairLocalActualMoon_actualPairBoundary_contains_neighborArc_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items host neighbor) :
    graphArc (actualTrace neighbor.1 f)
        (Icc (D arc.pair arc.pair_mem).thetaLeft
          (D arc.pair arc.pair_mem).thetaRight) ⊆
      actualPairGraphBoundary (T arc.pair) (U arc.pair) f
        (D arc.pair arc.pair_mem).thetaLeft
        (D arc.pair arc.pair_mem).thetaRight := by
  have horient :
      s(pairLocalActualItemSelectedFirstCurve T hT arc.pair,
          pairLocalActualItemSelectedSecondCurve U hU arc.pair) =
        s(host, neighbor) :=
    (hpair arc.pair).symm.trans arc.pair_eq
  rw [Sym2.eq_iff] at horient
  apply actualPairGraphBoundary_contains_curveArc
  rcases horient with horient | horient
  · exact Or.inr (congrArg Subtype.val horient.2)
  · exact Or.inl (congrArg Subtype.val horient.1)

theorem pairLocalActualMoon_sameHost_openSupports_disjoint_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {host neighborE neighborF : FirstGenerationCurve curves}
    (arcE : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items host neighborE)
    (arcF : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items host neighborF)
    (hnot : Not (sharePositiveGraphSegment
      (actualPairGraphBoundary (T arcE.pair) (U arcE.pair) f
        (D arcE.pair arcE.pair_mem).thetaLeft (D arcE.pair arcE.pair_mem).thetaRight)
      (actualPairGraphBoundary (T arcF.pair) (U arcF.pair) f
        (D arcF.pair arcF.pair_mem).thetaLeft (D arcF.pair arcF.pair_mem).thetaRight))) :
    ¬ (Ioo (D arcE.pair arcE.pair_mem).thetaLeft
          (D arcE.pair arcE.pair_mem).thetaRight ∩
        Ioo (D arcF.pair arcF.pair_mem).thetaLeft
          (D arcF.pair arcF.pair_mem).thetaRight).Nonempty := by
  intro hoverlap
  apply hnot
  exact sharePositiveGraphSegment_of_common_graphArc_Ioo_inter_nonempty
    (actualTrace host.1 f)
    (pairLocalActualMoon_actualPairBoundary_contains_hostArc_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D arcE)
    (pairLocalActualMoon_actualPairBoundary_contains_hostArc_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D arcF)
    hoverlap

theorem pairLocalActualMoon_sameNeighbor_openSupports_disjoint_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {hostE hostF neighbor : FirstGenerationCurve curves}
    (arcE : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items hostE neighbor)
    (arcF : MoonPositiveSideArc
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
        rectangles f f1 A B M depth D) items hostF neighbor)
    (hnot : Not (sharePositiveGraphSegment
      (actualPairGraphBoundary (T arcE.pair) (U arcE.pair) f
        (D arcE.pair arcE.pair_mem).thetaLeft (D arcE.pair arcE.pair_mem).thetaRight)
      (actualPairGraphBoundary (T arcF.pair) (U arcF.pair) f
        (D arcF.pair arcF.pair_mem).thetaLeft (D arcF.pair arcF.pair_mem).thetaRight))) :
    ¬ (Ioo (D arcE.pair arcE.pair_mem).thetaLeft
          (D arcE.pair arcE.pair_mem).thetaRight ∩
        Ioo (D arcF.pair arcF.pair_mem).thetaLeft
          (D arcF.pair arcF.pair_mem).thetaRight).Nonempty := by
  intro hoverlap
  apply hnot
  exact sharePositiveGraphSegment_of_common_graphArc_Ioo_inter_nonempty
    (actualTrace neighbor.1 f)
    (pairLocalActualMoon_actualPairBoundary_contains_neighborArc_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D arcE)
    (pairLocalActualMoon_actualPairBoundary_contains_neighborArc_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D arcF)
    hoverlap

#print axioms pairLocalActualMoon_actualPairBoundary_contains_hostArc_onItems
#print axioms pairLocalActualMoon_actualPairBoundary_contains_neighborArc_onItems
#print axioms pairLocalActualMoon_sameHost_openSupports_disjoint_onItems
#print axioms pairLocalActualMoon_sameNeighbor_openSupports_disjoint_onItems

end


end FamilyStickyCinematicL32Prop41PairLocalActualMoonSharedCurveOpenSupportDisjointGlobalCleanV1
