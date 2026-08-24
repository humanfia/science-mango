import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1
open FamilyStickyCinematicL32Prop41RectangularSkirtLocalAngleOrderV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- The cinematic first derivative, restricted to actual project tubes. -/
def pairLocalActualItemSelectedGraphFirst {radius : NNReal} (T : Tube radius)
    (f f1 : Real -> Real) (theta : Real) : Real :=
  FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1.actualTubeGraphFirst
    T f f1 theta

theorem pairLocalActualItemSelectedFirstCurve_ne_second
    {radius : NNReal} {curves : Finset (Tube radius)}
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (p : FirstGenerationCurvePair curves) :
    pairLocalActualItemSelectedFirstCurve T hT p ≠ pairLocalActualItemSelectedSecondCurve U hU p := by
  intro heq
  apply p.2
  rw [hpair p, Sym2.mk_isDiag_iff]
  exact heq

/-- The oriented other endpoint agrees with either presentation of the
literal unordered pair. -/
theorem pairLocalActualItemSelectedOtherCurve_eq_of_pair
    {radius : NNReal} {curves : Finset (Tube radius)}
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (p : FirstGenerationCurvePair curves)
    (host neighbor : FirstGenerationCurve curves)
    (hhostNeighbor : p.1 = s(host, neighbor)) :
    pairLocalActualItemSelectedOtherCurve T U hT hU p host = neighbor := by
  have hhostNe : host ≠ neighbor := by
    intro heq
    apply p.2
    rw [hhostNeighbor, Sym2.mk_isDiag_iff]
    exact heq
  have horient :
      s(pairLocalActualItemSelectedFirstCurve T hT p,
          pairLocalActualItemSelectedSecondCurve U hU p) = s(host, neighbor) :=
    (hpair p).symm.trans hhostNeighbor
  rw [Sym2.eq_iff] at horient
  rcases horient with horient | horient
  · rw [pairLocalActualItemSelectedOtherCurve, if_pos horient.1.symm, horient.2]
  · have hhostFirst : host ≠ pairLocalActualItemSelectedFirstCurve T hT p := by
      intro heq
      exact hhostNe (heq.trans horient.1)
    rw [pairLocalActualItemSelectedOtherCurve, if_neg hhostFirst, horient.1]

/-- The actual left-root equality transported through either orientation of
the unordered pair. -/
theorem actualTubeGraph_root_left_of_itemSelected_pair
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
    actualTubeGraph host.1 f (D p hpMem).thetaLeft =
      actualTubeGraph neighbor.1 f (D p hpMem).thetaLeft := by
  have hroot : actualTubeGraph (T p) f (D p hpMem).thetaLeft =
      actualTubeGraph (U p) f (D p hpMem).thetaLeft := by
    simpa only [actualTubeGraph, cinematicTraceValue,
      skirtTubeGraphA, skirtTubeGraphB, skirtTubeGraphC, skirtTubeGraphD,
      tubeGraphA, tubeGraphB, tubeGraphC, tubeGraphD] using (D p hpMem).root_left
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

/-- The secondary key of an actual pair is literally the host-versus-other
oriented tangent determinant at its left root. -/
theorem pairLocalActualSelectedLens_entryAngleKey_eq_of_pair_onItems
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
    (p : FirstGenerationCurvePair curves) (hpMem : p ∈ items)
    (host neighbor : FirstGenerationCurve curves)
    (hhostNeighbor : p.1 = s(host, neighbor)) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D).entryAngleKey p host =
      graphSideEntryLocalAngleKey
        (fun c theta => pairLocalActualItemSelectedGraphFirst c.1 f f1 theta)
        host neighbor (D p hpMem).thetaLeft := by
  rw [pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryAngleKey
      curves items T U hT hU hpair rectangles f f1 A B M depth D p hpMem host,
    pairLocalActualItemSelectedOtherCurve_eq_of_pair T U hT hU hpair p host neighbor
      hhostNeighbor]
  rfl

/-- Equality of the actual loop-entry keys is exactly equality of left-root
parameters. -/
theorem pairLocalActualSelectedLens_thetaLeft_eq_of_entryKey_eq_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) {A B : Real} (hAB : A < B) (M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (p q : FirstGenerationCurvePair curves)
    (hpMem : p ∈ items) (hqMem : q ∈ items)
    (host : FirstGenerationCurve curves)
    (hentry :
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryKey p host =
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryKey q host) :
    (D p hpMem).thetaLeft = (D q hqMem).thetaLeft := by
  rw [pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryKey
      curves items T U hT hU hpair rectangles f f1 A B M depth D p hpMem host,
    pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryKey
      curves items T U hT hU hpair rectangles f f1 A B M depth D q hqMem host] at hentry
  have hden : 32 * (B - A) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hAB.ne')
  unfold rectangularSkirtGraphEntryParameter at hentry
  have hsub := (div_left_inj' hden).mp hentry
  linarith

/-- Hence the finite tertiary key is never consulted at a common entry:
different neighbors have distinct determinant keys by A3. -/
theorem pairLocalActualSelectedLens_entryAngleKey_ne_of_same_entry_A3_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p, pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) {A B : Real} (hAB : A < B) (M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V theta => pairLocalActualItemSelectedGraphFirst V f f1 theta) A B)
    (p q : FirstGenerationCurvePair curves)
    (hpMem : p ∈ items) (hqMem : q ∈ items)
    (host left right : FirstGenerationCurve curves)
    (hp : p.1 = s(host, left)) (hq : q.1 = s(host, right))
    (hlr : left ≠ right)
    (hentry :
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryKey p host =
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryKey q host) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryAngleKey p host ≠
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D).entryAngleKey q host := by
  have htheta := pairLocalActualSelectedLens_thetaLeft_eq_of_entryKey_eq_onItems curves
    items T U hT hU hpair rectangles f f1 hAB M depth D
    p q hpMem hqMem host hentry
  have hrootLeft := actualTubeGraph_root_left_of_itemSelected_pair items T U hT hU
    hpair rectangles f A B D p hpMem host left hp
  have hrootRight := actualTubeGraph_root_left_of_itemSelected_pair items T U hT hU
    hpair rectangles f A B D q hqMem host right hq
  rw [← htheta] at hrootRight
  rw [pairLocalActualSelectedLens_entryAngleKey_eq_of_pair_onItems curves items T U hT hU hpair
    rectangles f f1 A B M depth D p hpMem host left hp,
    pairLocalActualSelectedLens_entryAngleKey_eq_of_pair_onItems curves items T U hT hU hpair
      rectangles f f1 A B M depth D q hqMem host right hq,
    ← htheta]
  apply graphSideEntryLocalAngleKey_ne_of_A3
    (curves := curves) (fun V => actualTubeGraph V f)
    (fun V theta => pairLocalActualItemSelectedGraphFirst V f f1 theta) A B hA3
    left.2 right.2
  · intro hval
    exact hlr (Subtype.ext hval)
  · exact (D p hpMem).thetaLeft_mem
  · exact hrootLeft
  · exact hrootRight

#print axioms pairLocalActualItemSelectedGraphFirst
#print axioms pairLocalActualItemSelectedFirstCurve_ne_second
#print axioms pairLocalActualItemSelectedOtherCurve_eq_of_pair
#print axioms actualTubeGraph_root_left_of_itemSelected_pair
#print axioms pairLocalActualSelectedLens_entryAngleKey_eq_of_pair_onItems
#print axioms pairLocalActualSelectedLens_thetaLeft_eq_of_entryKey_eq_onItems
#print axioms pairLocalActualSelectedLens_entryAngleKey_ne_of_same_entry_A3_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1
