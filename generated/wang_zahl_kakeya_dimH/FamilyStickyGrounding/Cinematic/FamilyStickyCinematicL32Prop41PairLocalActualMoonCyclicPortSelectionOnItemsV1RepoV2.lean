import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonOrderedPortSelectionOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CyclicSortedTripleOrderV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonOrderedPortSelectionOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1
open FamilyStickyCinematicL32Prop41CyclicSortedTripleOrderV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- Positive cyclic order of the three scalar host ports. -/
def PortCyclicPositive (port : Fin 3 -> Real) : Prop :=
  (port 0 < port 1 ∧ port 1 < port 2) ∨
  (port 1 < port 2 ∧ port 2 < port 0) ∨
  (port 2 < port 0 ∧ port 0 < port 1)

theorem moonSix_canonical_cyclic_order_clean
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {G : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration G items leftHost rightHost x y z)
    (h : Fin 2) :
    CyclicallyOrdered
      (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
        (moonHost C h))
      (moonNeighbor C 0) (moonNeighbor C 1) (moonNeighbor C 2) := by
  fin_cases h
  · change CyclicallyOrdered
      (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
        leftHost) x y z
    exact C.cyclicLeft
  · change CyclicallyOrdered
      (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
        rightHost) x y z
    exact C.cyclicRight

/-- The honest cyclic order on the actual three neighbors transports to the
item-local keyed order on `Fin 3`.  Primary entry ties are resolved by the
literal A3 tangent-angle key, never by the tertiary finite enumeration. -/
theorem pairLocalActualMoon_neighbor_lt_iff_hostPort_lt_onItems
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
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V theta => pairLocalActualItemSelectedGraphFirst V f f1 theta) A B)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
        hpair rectangles f f1 A B M depth D) items leftHost rightHost x y z)
    (h : Fin 2) (j k : Fin 3) (hjk : j ≠ k) :
    let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U
      hT hU hpair rectangles f f1 A B M depth D
    let curveOrder := keyedFiniteEntryAngleLinearOrder
      (localAngleSelectedLensNeighborEntryKey G items ProperLensKind.moonFace
        (moonHost C h))
      (localAngleSelectedLensNeighborAngleKey G items ProperLensKind.moonFace
        (moonHost C h))
    @LT.lt (FirstGenerationCurve curves) curveOrder.toLT
        (moonNeighbor C j) (moonNeighbor C k) ↔
      @LT.lt (Fin 3)
        (pairLocalActualMoonHostPortLinearOrderOnItems curves items T U hT hU
          hpair rectangles f f1 A B M depth D C h).toLT j k := by
  let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U
    hT hU hpair rectangles f f1 A B M depth D
  let entry : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborEntryKey G items ProperLensKind.moonFace
      (moonHost C h)
  let angle : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborAngleKey G items ProperLensKind.moonFace
      (moonHost C h)
  let entryFin : Fin 3 -> Real := fun i => entry (moonNeighbor C i)
  let angleFin : Fin 3 -> Real := fun i => angle (moonNeighbor C i)
  change @LT.lt (FirstGenerationCurve curves)
      (keyedFiniteEntryAngleLinearOrder entry angle).toLT
        (moonNeighbor C j) (moonNeighbor C k) ↔
    @LT.lt (Fin 3) (keyedFiniteEntryAngleLinearOrder entryFin angleFin).toLT j k
  by_cases hentry : entry (moonNeighbor C j) = entry (moonNeighbor C k)
  · have hrelationJ : localAngleSelectedLensNeighborRelation G items
        ProperLensKind.moonFace (moonHost C h) (moonNeighbor C j) := by
      let arc := moonSixArc C h j
      exact ⟨arc.pair, arc.pair_mem, arc.assigned, arc.pair_eq⟩
    have hrelationK : localAngleSelectedLensNeighborRelation G items
        ProperLensKind.moonFace (moonHost C h) (moonNeighbor C k) := by
      let arc := moonSixArc C h k
      exact ⟨arc.pair, arc.pair_mem, arc.assigned, arc.pair_eq⟩
    have hneighborNe : moonNeighbor C j ≠ moonNeighbor C k := by
      intro hEq
      exact hjk ((moonNeighbor_injective C) hEq)
    have hangle : angle (moonNeighbor C j) ≠ angle (moonNeighbor C k) := by
      exact pairLocalActualSelectedLensNeighborAngleKey_ne_of_sameEntry_onItems
        curves items T U hT hU hpair rectangles f f1 hAB M depth D hA3
        ProperLensKind.moonFace (moonHost C h) (moonNeighbor C j)
        (moonNeighbor C k) hrelationJ hrelationK hneighborNe hentry
    rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
      entry angle hentry hangle]
    rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
      entryFin angleFin (by exact hentry) (by exact hangle)]
  · rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
      entry angle hentry]
    rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
      entryFin angleFin (by exact hentry)]

/-- Choose one actual parameter in every moon support at one host, in the
same positive cyclic order as the original local-angle neighbor list. -/
theorem exists_pairLocalActualMoon_hostCyclicPorts_onItems
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
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V theta => pairLocalActualItemSelectedGraphFirst V f f1 theta) A B)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
        hpair rectangles f f1 A B M depth D) items leftHost rightHost x y z)
    (h : Fin 2) :
    exists port : Fin 3 -> Real,
      (forall j, port j ∈ Ioo
        (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaLeft
        (D (moonSixPair C (h, j)) (moonSixPair_mem_items C (h, j))).thetaRight) ∧
      PortCyclicPositive port := by
  let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U
    hT hU hpair rectangles f f1 A B M depth D
  let entry : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborEntryKey G items ProperLensKind.moonFace
      (moonHost C h)
  let angle : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborAngleKey G items ProperLensKind.moonFace
      (moonHost C h)
  let curveOrder : LinearOrder (FirstGenerationCurve curves) :=
    keyedFiniteEntryAngleLinearOrder entry angle
  have hsorted :
      @List.Pairwise (FirstGenerationCurve curves)
        (fun a b => @LT.lt (FirstGenerationCurve curves) curveOrder.toLT a b)
        (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
          (moonHost C h)).order := by
    change List.Pairwise
      (fun a b : FirstGenerationCurve curves =>
        @LT.lt (FirstGenerationCurve curves) curveOrder.toLT a b)
      ((localAngleSelectedLensNeighborFinset G items ProperLensKind.moonFace
        (moonHost C h)).sort (fun a b =>
          @LE.le (FirstGenerationCurve curves) curveOrder.toLE a b))
    exact (@Finset.sortedLT_sort
      (FirstGenerationCurve curves) curveOrder
      (localAngleSelectedLensNeighborFinset G items ProperLensKind.moonFace
        (moonHost C h))).pairwise
  have hcyclic : CyclicallyOrdered
      (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
        (moonHost C h))
      (moonNeighbor C 0) (moonNeighbor C 1) (moonNeighbor C 2) := by
    exact moonSix_canonical_cyclic_order_clean C h
  have horder := @cyc3_of_cyclicallyOrdered_of_pairwise_lt
    (FirstGenerationCurve curves) inferInstance curveOrder
    (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
      (moonHost C h))
    (moonNeighbor C 0) (moonNeighbor C 1) (moonNeighbor C 2)
    hsorted hcyclic
  rcases exists_pairLocalActualMoon_hostOrderedPorts_onItems curves items T U hT hU
      hpair rectangles f f1 hAB M depth D C h with ⟨port, hport, hstrict⟩
  refine ⟨port, hport, ?_⟩
  have hlt (j k : Fin 3) (hjk : j ≠ k)
      (hcurve : @LT.lt (FirstGenerationCurve curves) curveOrder.toLT
        (moonNeighbor C j) (moonNeighbor C k)) : port j < port k := by
    apply hstrict
    exact (pairLocalActualMoon_neighbor_lt_iff_hostPort_lt_onItems
      curves items T U hT hU hpair rectangles f f1 hAB M depth D hA3
      C h j k hjk).mp hcurve
  rcases horder with h012 | h120 | h201
  · exact Or.inl ⟨hlt 0 1 (by decide) h012.1,
      hlt 1 2 (by decide) h012.2⟩
  · exact Or.inr (Or.inl ⟨hlt 1 2 (by decide) h120.1,
      hlt 2 0 (by decide) h120.2⟩)
  · exact Or.inr (Or.inr ⟨hlt 2 0 (by decide) h201.1,
      hlt 0 1 (by decide) h201.2⟩)

#print axioms PortCyclicPositive
#print axioms moonSix_canonical_cyclic_order_clean
#print axioms pairLocalActualMoon_neighbor_lt_iff_hostPort_lt_onItems
#print axioms exists_pairLocalActualMoon_hostCyclicPorts_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1
