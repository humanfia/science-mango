import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonOrderedPortSelectionOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- The chosen finite neighbor-list witness is the literal moon pair. -/
theorem pairLocalActualMoon_neighborEntryKey_eq_onItems
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
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items leftHost rightHost x y z)
    (h : Fin 2) (j : Fin 3) :
    localAngleSelectedLensNeighborEntryKey
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
          f f1 A B M depth D)
        items ProperLensKind.moonFace (moonHost C h) (moonNeighbor C j) =
      rectangularSkirtGraphEntryParameter A B
        (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaLeft := by
  let arc := moonSixArc C h j
  have hrelation : localAngleSelectedLensNeighborRelation
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items ProperLensKind.moonFace
      (moonHost C h) (moonNeighbor C j) :=
    ⟨arc.pair, arc.pair_mem, arc.assigned, arc.pair_eq⟩
  rw [localAngleSelectedLensNeighborEntryKey]
  split
  · rename_i hrel
    have hchosen : Classical.choose hrel = moonSixPair C (h, j) := by
      apply Subtype.ext
      exact (Classical.choose_spec hrel).2.2.trans
        (moonSixPair_pair_eq C (h, j)).symm
    rw [hchosen]
    exact pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryKey
      curves items T U hT hU hpair rectangles f f1 A B M depth D
      (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j)) (moonHost C h)
  · rename_i hnot
    exact (hnot hrelation).elim

/-- The actual two-key order on the three incidences at one host.  The
tertiary finite key is unreachable for distinct actual neighbors once A3 is
used downstream. -/
@[instance_reducible] noncomputable def pairLocalActualMoonHostPortLinearOrderOnItems
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
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items leftHost rightHost x y z)
    (h : Fin 2) : LinearOrder (Fin 3) :=
  keyedFiniteEntryAngleLinearOrder
    (fun j => localAngleSelectedLensNeighborEntryKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items ProperLensKind.moonFace
      (moonHost C h) (moonNeighbor C j))
    (fun j => localAngleSelectedLensNeighborAngleKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items ProperLensKind.moonFace
      (moonHost C h) (moonNeighbor C j))

/-- For one host, choose one parameter strictly inside every actual moon
root interval.  The three selected parameters are strictly ordered by the
faithful entry-parameter/local-angle lexicographic order, including mixed
distinct-root and tied-root configurations. -/
theorem exists_pairLocalActualMoon_hostOrderedPorts_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 : Real -> Real) {A B : Real} (hAB : A < B) (M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items leftHost rightHost x y z)
    (h : Fin 2) :
    exists port : Fin 3 -> Real,
      (forall j, port j ∈ Ioo
        (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaLeft
        (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaRight) ∧
      (forall {j k},
        @LT.lt (Fin 3)
          (pairLocalActualMoonHostPortLinearOrderOnItems curves items T U hT hU hpair
            rectangles f f1 A B M depth D C h).toLT j k ->
        port j < port k) := by
  let entry : Fin 3 -> Real := fun j =>
    localAngleSelectedLensNeighborEntryKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items ProperLensKind.moonFace
      (moonHost C h) (moonNeighbor C j)
  let angle : Fin 3 -> Real := fun j =>
    localAngleSelectedLensNeighborAngleKey
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items ProperLensKind.moonFace
      (moonHost C h) (moonNeighbor C j)
  let portOrder : LinearOrder (Fin 3) := keyedFiniteEntryAngleLinearOrder entry angle
  let left : Fin 3 -> Real := fun j =>
    (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaLeft
  let right : Fin 3 -> Real := fun j =>
    (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaRight
  have hentry (j : Fin 3) : entry j =
      rectangularSkirtGraphEntryParameter A B (left j) := by
    exact pairLocalActualMoon_neighborEntryKey_eq_onItems curves items T U hT hU hpair
      rectangles f f1 A B M depth D C h j
  have hleftMono :
      @Monotone (Fin 3) Real portOrder.toPreorder Real.instPreorder left := by
    intro j k hjk
    by_contra hnot
    have hkjLeft : left k < left j := lt_of_not_ge hnot
    have hkjEntry : entry k < entry j := by
      rw [hentry k, hentry j, rectangularSkirtGraphEntryParameter_lt_iff hAB]
      exact hkjLeft
    have hentryNe : entry k ≠ entry j := ne_of_lt hkjEntry
    have hkj : @LT.lt (Fin 3) portOrder.toLT k j :=
      (keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
        entry angle hentryNe).2 hkjEntry
    exact (@not_lt_of_ge (Fin 3) portOrder.toPreorder j k hjk hkj).elim
  have hinterval : forall j, left j < right j := fun j =>
    (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).theta_order
  rcases @exists_strictMono_interval_choice (Fin 3) inferInstance portOrder
      left right hleftMono hinterval with
    ⟨port, hport, hstrict⟩
  refine ⟨port, hport, ?_⟩
  intro j k hjk
  apply hstrict
  simpa [portOrder, pairLocalActualMoonHostPortLinearOrderOnItems, entry, angle]
    using hjk

#print axioms pairLocalActualMoon_neighborEntryKey_eq_onItems
#print axioms pairLocalActualMoonHostPortLinearOrderOnItems
#print axioms exists_pairLocalActualMoon_hostOrderedPorts_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonOrderedPortSelectionOnItemsV1
