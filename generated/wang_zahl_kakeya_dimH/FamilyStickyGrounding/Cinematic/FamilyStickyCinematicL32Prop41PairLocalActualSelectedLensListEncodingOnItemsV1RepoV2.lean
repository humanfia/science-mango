import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual faithful lens-list encoding

This facade feeds the literal actual graph sides, explicit rectangular-skirt
interiors, literal skirt-loop entry parameter, and oriented tangent
determinant into the finite Marcus--Tardos list encoding.  A3 proves that the
tertiary finite key is never used between distinct neighbors at one entry.
-/

/-- The complete actual `LensListEncoding`; neither the class labels, the
host assignment, the list order, nor the injection is supplied by a caller. -/
noncomputable def pairLocalActualSelectedLensListEncodingOnItems
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
      (rectangles p) A B delta t lambda0) :
    LensListEncoding (FirstGenerationCurve curves)
      (LocalAngleSelectedFixedSlotLens items) :=
  localAngleSelectedLensListEncoding
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D) items

/-- At a common actual loop entry, A3 makes the two neighbor angle keys
strictly different.  Thus the finite enumeration in the general linear-order
construction is provably invisible on every actual neighbor list. -/
theorem pairLocalActualSelectedLensNeighborAngleKey_ne_of_sameEntry_onItems
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
    (k : ProperLensKind) (host left right : FirstGenerationCurve curves)
    (hleft : localAngleSelectedLensNeighborRelation
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host left)
    (hright : localAngleSelectedLensNeighborRelation
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host right)
    (hlr : left ≠ right)
    (hentry : localAngleSelectedLensNeighborEntryKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host left =
      localAngleSelectedLensNeighborEntryKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host right) :
    localAngleSelectedLensNeighborAngleKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host left ≠
      localAngleSelectedLensNeighborAngleKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items k host right := by
  let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
    rectangles f f1 A B M depth D
  let p : FirstGenerationCurvePair curves := Classical.choose hleft
  let q : FirstGenerationCurvePair curves := Classical.choose hright
  have hpMem : p ∈ items := (Classical.choose_spec hleft).1
  have hqMem : q ∈ items := (Classical.choose_spec hright).1
  have hp : p.1 = s(host, left) := (Classical.choose_spec hleft).2.2
  have hq : q.1 = s(host, right) := (Classical.choose_spec hright).2.2
  have hentryPair : G.entryKey p host = G.entryKey q host := by
    simpa [G, p, q, localAngleSelectedLensNeighborEntryKey,
      dif_pos hleft, dif_pos hright] using hentry
  have hanglePair : G.entryAngleKey p host ≠ G.entryAngleKey q host := by
    exact pairLocalActualSelectedLens_entryAngleKey_ne_of_same_entry_A3_onItems curves
      items T U hT hU hpair rectangles f f1 hAB M depth D hA3
      p q hpMem hqMem host left right hp hq hlr hentryPair
  simpa [G, p, q, localAngleSelectedLensNeighborAngleKey,
    dif_pos hleft, dif_pos hright] using hanglePair

/-- The literal actual selected pair carrier obeys the finite curve plus
three cyclic-list length reduction. -/
theorem pairLocalActualSelectedFixedSlotLens_card_le_curve_add_sum_list_length_onItems
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
      (rectangles p) A B delta t lambda0) :
    items.card <= curves.card +
      ∑ k : ProperLensKind, ∑ c : FirstGenerationCurve curves,
        (localAngleSelectedLensNeighborSequence
          (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
            rectangles f f1 A B M depth D) items k c).order.length := by
  exact localAngleSelectedFixedSlotLens_card_le_curve_add_sum_list_length
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D) items

/-- After the sole remaining five-curve statement is proved for the three
actual classes, the actual encoding satisfies intersection reverse. -/
theorem pairLocalActualSelectedLensListEncodingOnItems_pairwiseIntersectionReverse
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
    (hfive : forall k,
      FixedKindForbidsSameTriple
        (localAngleSelectedLensNeighborSequence
          (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
            rectangles f f1 A B M depth D) items k)) :
    (pairLocalActualSelectedLensListEncodingOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D).ListsPairwiseIntersectionReverse := by
  exact localAngleSelectedLensListEncoding_pairwiseIntersectionReverse
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D) items hfive

#print axioms pairLocalActualSelectedLensListEncodingOnItems
#print axioms pairLocalActualSelectedLensNeighborAngleKey_ne_of_sameEntry_onItems
#print axioms pairLocalActualSelectedFixedSlotLens_card_le_curve_add_sum_list_length_onItems
#print axioms pairLocalActualSelectedLensListEncodingOnItems_pairwiseIntersectionReverse

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
