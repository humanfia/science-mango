import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ContinuousExactTwoRootSignV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensMoonClassificationOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41ContinuousExactTwoRootSignV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual graph lenses are moon-faces

The rectangular skirt interior is the region below its graph.  Between two
consecutive proper roots, one actual tube graph is strictly above the other;
therefore exactly one lens side is positive.  The pair-local record already
carries the literal exact two-root set, so no separate root-cardinality
callback is needed.
-/

/-- The actual root carrier for one selected unordered tube pair. -/
def pairLocalActualItemSelectedPairRootSet
    {radius : NNReal} {curves : Finset (Tube radius)}
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (f : Real -> Real) (A B : Real)
    (p : FirstGenerationCurvePair curves) : Set Real :=
  {theta | theta ∈ Icc A B ∧
    actualTubeGraph (T p) f theta = actualTubeGraph (U p) f theta}

theorem pairLocalActualSelectedLens_kind_eq_moonFace_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) {A B : Real} (_hAB : A < B) (M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    (hdepth : forall c, 0 < depth c)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B))
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items) :
    selectedProperLensKind
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).toSelectedFixedSlotLensGeometry p =
      ProperLensKind.moonFace := by
  let G := (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
    rectangles f f1 A B M depth D).toSelectedFixedSlotLensGeometry
  let gT := actualTubeGraph (T p) f
  let gU := actualTubeGraph (U p) f
  let left := (D p hp).thetaLeft
  let right := (D p hp).thetaRight
  have hfirstSide : G.firstOpenSide p = graphArc gT (Ioo left right) := by
    simpa [G, gT, left, right] using
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems_firstOpenSide
        curves items T U hT hU hpair rectangles f f1 A B M depth D p hp)
  have hsecondSide : G.secondOpenSide p = graphArc gU (Ioo left right) := by
    simpa [G, gU, left, right] using
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems_secondOpenSide
        curves items T U hT hU hpair rectangles f f1 A B M depth D p hp)
  have hrootLeft : gT left = gU left := by
    simpa only [gT, gU, left, actualTubeGraph, cinematicTraceValue,
      skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
      tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using (D p hp).root_left
  have hrootRight : gT right = gU right := by
    simpa only [gT, gU, right, actualTubeGraph, cinematicTraceValue,
      skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
      tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using (D p hp).root_right
  let roots := pairLocalActualItemSelectedPairRootSet T U f A B p
  have hleftMem : left ∈ roots := by
    exact ⟨(D p hp).thetaLeft_mem, hrootLeft⟩
  have hrightMem : right ∈ roots := by
    exact ⟨(D p hp).thetaRight_mem, hrootRight⟩
  have hlr : left ≠ right := (D p hp).theta_order.ne
  have hroots : roots = ({left, right} : Set Real) := by
    simpa only [roots, left, right, pairLocalActualItemSelectedPairRootSet,
      pairLocalActualRootSet, actualTubeGraph, cinematicTraceValue,
      skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
      tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using
      (D p hp).exact_root_set
  have hnoRoot : forall theta, theta ∈ Ioo left right ->
      gU theta - gT theta ≠ 0 := by
    intro theta htheta hzero
    have hthetaAB : theta ∈ Icc A B :=
      ⟨(D p hp).thetaLeft_mem.1.trans htheta.1.le,
        htheta.2.le.trans (D p hp).thetaRight_mem.2⟩
    have hthetaRoot : theta ∈ roots := by
      refine ⟨hthetaAB, ?_⟩
      linarith
    rw [hroots] at hthetaRoot
    rcases hthetaRoot with hthetaEq | hthetaEq
    · exact (ne_of_gt htheta.1) hthetaEq
    · exact (ne_of_lt htheta.2) hthetaEq
  have hintervalSub : Icc left right ⊆ Icc A B :=
    Icc_subset_Icc (D p hp).thetaLeft_mem.1 (D p hp).thetaRight_mem.2
  have hdiffContinuous : ContinuousOn (fun theta => gU theta - gT theta)
      (Icc left right) :=
    ((hcontinuous (U p) (hU p)).sub
      (hcontinuous (T p) (hT p))).mono hintervalSub
  rcases strict_sign_dichotomy_of_continuousOn_of_ne_zero_Ioo
      (fun theta => gU theta - gT theta) (D p hp).theta_order
      hdiffContinuous hnoRoot with hpositive | hnegative
  · rw [selectedProperLensKind_eq_moonFace_iff]
    right
    constructor
    · intro hfirstPositive
      let mid := (left + right) / 2
      have hmid : mid ∈ Ioo left right := by
        dsimp [mid]
        constructor <;> linarith [(D p hp).theta_order]
      have hside : (gU mid, mid) ∈ G.secondOpenSide p := by
        rw [hsecondSide]
        exact ⟨hmid, rfl⟩
      have hinterior := hfirstPositive hside
      change (gU mid, mid) ∈ pairLocalItemRectangularSkirtInterior gT A B M
        (depth (pairLocalActualItemSelectedFirstCurve T hT p)) at hinterior
      have hmidAB : mid ∈ Ioo A B :=
        ⟨(D p hp).thetaLeft_mem.1.trans_lt hmid.1,
          hmid.2.trans_le (D p hp).thetaRight_mem.2⟩
      have htop : pairLocalItemRectangularSkirtTopGraph gT A B mid = gT mid := by
        simp [pairLocalItemRectangularSkirtTopGraph, not_lt.mpr hmidAB.1.le,
          hmidAB.2.le]
      rcases hinterior with ⟨_, _, hinterior⟩
      rw [htop] at hinterior
      linarith [hpositive mid hmid]
    · intro q hq
      rw [hfirstSide] at hq
      change q ∈ pairLocalItemRectangularSkirtInterior gU A B M
        (depth (pairLocalActualItemSelectedSecondCurve U hU p))
      have hthetaAB : q.2 ∈ Ioo A B :=
        ⟨(D p hp).thetaLeft_mem.1.trans_lt hq.1.1,
          hq.1.2.trans_le (D p hp).thetaRight_mem.2⟩
      have hdepthU := hdepth (pairLocalActualItemSelectedSecondCurve U hU p)
      have hboundT := (abs_le.mp
        (hgraphBound (T p) (hT p) q.2 ⟨hthetaAB.1.le, hthetaAB.2.le⟩)).1
      have htop : pairLocalItemRectangularSkirtTopGraph gU A B q.2 = gU q.2 := by
        simp [pairLocalItemRectangularSkirtTopGraph, not_lt.mpr hthetaAB.1.le,
          hthetaAB.2.le]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · linarith [hthetaAB.1, hdepthU]
      · linarith [hthetaAB.2, hdepthU]
      · rw [hq.2]
        linarith
      · rw [hq.2, htop]
        linarith [hpositive q.2 hq.1]
  · rw [selectedProperLensKind_eq_moonFace_iff]
    left
    constructor
    · intro q hq
      rw [hsecondSide] at hq
      change q ∈ pairLocalItemRectangularSkirtInterior gT A B M
        (depth (pairLocalActualItemSelectedFirstCurve T hT p))
      have hthetaAB : q.2 ∈ Ioo A B :=
        ⟨(D p hp).thetaLeft_mem.1.trans_lt hq.1.1,
          hq.1.2.trans_le (D p hp).thetaRight_mem.2⟩
      have hdepthT := hdepth (pairLocalActualItemSelectedFirstCurve T hT p)
      have hboundU := (abs_le.mp
        (hgraphBound (U p) (hU p) q.2 ⟨hthetaAB.1.le, hthetaAB.2.le⟩)).1
      have htop : pairLocalItemRectangularSkirtTopGraph gT A B q.2 = gT q.2 := by
        simp [pairLocalItemRectangularSkirtTopGraph, not_lt.mpr hthetaAB.1.le,
          hthetaAB.2.le]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · linarith [hthetaAB.1, hdepthT]
      · linarith [hthetaAB.2, hdepthT]
      · rw [hq.2]
        linarith
      · rw [hq.2, htop]
        linarith [hnegative q.2 hq.1]
    · intro hsecondPositive
      let mid := (left + right) / 2
      have hmid : mid ∈ Ioo left right := by
        dsimp [mid]
        constructor <;> linarith [(D p hp).theta_order]
      have hside : (gT mid, mid) ∈ G.firstOpenSide p := by
        rw [hfirstSide]
        exact ⟨hmid, rfl⟩
      have hinterior := hsecondPositive hside
      change (gT mid, mid) ∈ pairLocalItemRectangularSkirtInterior gU A B M
        (depth (pairLocalActualItemSelectedSecondCurve U hU p)) at hinterior
      have hmidAB : mid ∈ Ioo A B :=
        ⟨(D p hp).thetaLeft_mem.1.trans_lt hmid.1,
          hmid.2.trans_le (D p hp).thetaRight_mem.2⟩
      have htop : pairLocalItemRectangularSkirtTopGraph gU A B mid = gU mid := by
        simp [pairLocalItemRectangularSkirtTopGraph, not_lt.mpr hmidAB.1.le,
          hmidAB.2.le]
      rcases hinterior with ⟨_, _, hinterior⟩
      rw [htop] at hinterior
      linarith [hnegative mid hmid]

#print axioms pairLocalActualItemSelectedPairRootSet
#print axioms pairLocalActualSelectedLens_kind_eq_moonFace_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensMoonClassificationOnItemsV1
