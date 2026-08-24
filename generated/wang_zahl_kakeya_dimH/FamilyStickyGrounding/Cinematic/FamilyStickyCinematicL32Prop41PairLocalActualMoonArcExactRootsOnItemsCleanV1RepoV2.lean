import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonArcExactRootsOnItemsCleanV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-! Literal host-neighbor equality is transported directly from the
item-local pair's exact two-root field. -/

theorem pairLocalActualMoonArc_graph_eq_iff_endpoint_onItems
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
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items host neighbor)
    {theta : Real} (htheta : theta ∈ Icc A B) :
    actualTubeGraph host.1 f theta = actualTubeGraph neighbor.1 f theta <->
      theta = (D arc.pair arc.pair_mem).thetaLeft ∨
        theta = (D arc.pair arc.pair_mem).thetaRight := by
  have hroots := (D arc.pair arc.pair_mem).exact_root_set
  have horient :
      s(pairLocalActualItemSelectedFirstCurve T hT arc.pair,
          pairLocalActualItemSelectedSecondCurve U hU arc.pair) =
        s(host, neighbor) :=
    (hpair arc.pair).symm.trans arc.pair_eq
  rw [Sym2.eq_iff] at horient
  rcases horient with horient | horient
  · have hTv : T arc.pair = host.1 := congrArg Subtype.val horient.1
    have hUv : U arc.pair = neighbor.1 := congrArg Subtype.val horient.2
    constructor
    · intro heq
      have hm : theta ∈ pairLocalActualRootSet (T arc.pair) (U arc.pair)
          f A B := ⟨htheta, by simpa [hTv, hUv, actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using heq⟩
      rw [hroots] at hm
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    · intro hend
      have hm : theta ∈ pairLocalActualRootSet (T arc.pair) (U arc.pair)
          f A B := by
        rw [hroots]
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hend
      simpa [pairLocalActualRootSet, hTv, hUv, actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using hm.2
  · have hTv : T arc.pair = neighbor.1 := congrArg Subtype.val horient.1
    have hUv : U arc.pair = host.1 := congrArg Subtype.val horient.2
    constructor
    · intro heq
      have hm : theta ∈ pairLocalActualRootSet (T arc.pair) (U arc.pair)
          f A B :=
        ⟨htheta, by simpa [hTv, hUv, actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD, eq_comm] using heq⟩
      rw [hroots] at hm
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    · intro hend
      have hm : theta ∈ pairLocalActualRootSet (T arc.pair) (U arc.pair)
          f A B := by
        rw [hroots]
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hend
      simpa [pairLocalActualRootSet, hTv, hUv, actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD, eq_comm] using hm.2

#print axioms pairLocalActualMoonArc_graph_eq_iff_endpoint_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonArcExactRootsOnItemsCleanV1
