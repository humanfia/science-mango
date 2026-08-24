import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonGlobalCyclicPortSelectionOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41CyclicSortedTripleOrderV1
open FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonCyclicPortSelectionOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonOrderedPortSelectionOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- One global order on all six host incidences.  Its restriction to either
host is the faithful entry/tangent-angle order, while the finite tertiary
key only resolves coincidences between unrelated hosts. -/
@[instance_reducible] noncomputable def pairLocalActualMoonGlobalPortLinearOrderOnItems
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
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
        hpair rectangles f f1 A B M depth D) items leftHost rightHost x y z) :
    LinearOrder K23Edge :=
  let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U
    hT hU hpair rectangles f f1 A B M depth D
  keyedFiniteEntryAngleLinearOrder
    (fun e => localAngleSelectedLensNeighborEntryKey G items
      ProperLensKind.moonFace (moonHost C e.1) (moonNeighbor C e.2))
    (fun e => localAngleSelectedLensNeighborAngleKey G items
      ProperLensKind.moonFace (moonHost C e.1) (moonNeighbor C e.2))

/-- Select all six host ports simultaneously.  They are globally distinct,
lie in their literal pair-local root intervals, and at each host retain the
positive cyclic order forced by the actual local-angle list. -/
theorem exists_pairLocalActualMoon_globalHostCyclicPorts_onItems
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
    (hA3 : FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1.NoTangentialGraphIntersections
      curves (fun V => actualTubeGraph V f)
      (fun V theta => pairLocalActualItemSelectedGraphFirst V f f1 theta) A B)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
        hpair rectangles f f1 A B M depth D) items leftHost rightHost x y z) :
    exists port : K23Edge -> Real,
      (forall e, port e ∈ Ioo
        (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft
        (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight) ∧
      Function.Injective port ∧
      (forall h, PortCyclicPositive (fun j => port (h, j))) := by
  let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U
    hT hU hpair rectangles f f1 A B M depth D
  let entry : K23Edge -> Real := fun e =>
    localAngleSelectedLensNeighborEntryKey G items ProperLensKind.moonFace
      (moonHost C e.1) (moonNeighbor C e.2)
  let angle : K23Edge -> Real := fun e =>
    localAngleSelectedLensNeighborAngleKey G items ProperLensKind.moonFace
      (moonHost C e.1) (moonNeighbor C e.2)
  let portOrder : LinearOrder K23Edge :=
    keyedFiniteEntryAngleLinearOrder entry angle
  let left : K23Edge -> Real := fun e =>
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft
  let right : K23Edge -> Real := fun e =>
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight
  have hentry (e : K23Edge) : entry e =
      rectangularSkirtGraphEntryParameter A B (left e) := by
    exact pairLocalActualMoon_neighborEntryKey_eq_onItems curves items T U hT hU
      hpair rectangles f f1 A B M depth D C e.1 e.2
  have hleftMono :
      @Monotone K23Edge Real portOrder.toPreorder Real.instPreorder left := by
    intro e q heq
    by_contra hnot
    have hqeLeft : left q < left e := lt_of_not_ge hnot
    have hqeEntry : entry q < entry e := by
      rw [hentry q, hentry e, rectangularSkirtGraphEntryParameter_lt_iff hAB]
      exact hqeLeft
    have hentryNe : entry q ≠ entry e := ne_of_lt hqeEntry
    have hqe : @LT.lt K23Edge portOrder.toLT q e :=
      (keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
        entry angle hentryNe).2 hqeEntry
    exact (@not_lt_of_ge K23Edge portOrder.toPreorder e q heq hqe).elim
  have hinterval : forall e, left e < right e := fun e =>
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).theta_order
  rcases @exists_strictMono_interval_choice K23Edge inferInstance portOrder
      left right hleftMono hinterval with ⟨port, hport, hstrict⟩
  refine ⟨port, hport, hstrict.injective, ?_⟩
  intro h
  let curveEntry : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborEntryKey G items ProperLensKind.moonFace
      (moonHost C h)
  let curveAngle : FirstGenerationCurve curves -> Real :=
    localAngleSelectedLensNeighborAngleKey G items ProperLensKind.moonFace
      (moonHost C h)
  let curveOrder : LinearOrder (FirstGenerationCurve curves) :=
    keyedFiniteEntryAngleLinearOrder curveEntry curveAngle
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
      (moonNeighbor C 0) (moonNeighbor C 1) (moonNeighbor C 2) :=
    moonSix_canonical_cyclic_order_clean C h
  have horder := @cyc3_of_cyclicallyOrdered_of_pairwise_lt
    (FirstGenerationCurve curves) inferInstance curveOrder
    (localAngleSelectedLensNeighborSequence G items ProperLensKind.moonFace
      (moonHost C h))
    (moonNeighbor C 0) (moonNeighbor C 1) (moonNeighbor C 2)
    hsorted hcyclic
  have hlt (j k : Fin 3)
      (hcurve : @LT.lt (FirstGenerationCurve curves) curveOrder.toLT
        (moonNeighbor C j) (moonNeighbor C k)) : port (h, j) < port (h, k) := by
    apply hstrict
    change @LT.lt K23Edge
      (keyedFiniteEntryAngleLinearOrder entry angle).toLT (h, j) (h, k)
    by_cases hentryEq : entry (h, j) = entry (h, k)
    · have hjk : j ≠ k := by
        intro hjk
        subst k
        exact (lt_irrefl _ hcurve).elim
      have hrelationJ : localAngleSelectedLensNeighborRelation G items
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
      have hangleNe : angle (h, j) ≠ angle (h, k) := by
        exact pairLocalActualSelectedLensNeighborAngleKey_ne_of_sameEntry_onItems
          curves items T U hT hU hpair rectangles f f1 hAB M depth D hA3
          ProperLensKind.moonFace (moonHost C h) (moonNeighbor C j)
          (moonNeighbor C k) hrelationJ hrelationK hneighborNe hentryEq
      rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
        entry angle hentryEq hangleNe]
      rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
        curveEntry curveAngle (by exact hentryEq) (by exact hangleNe)] at hcurve
      exact hcurve
    · rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
        entry angle hentryEq]
      rw [keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
        curveEntry curveAngle (by exact hentryEq)] at hcurve
      exact hcurve
  rcases horder with h012 | h120 | h201
  · exact Or.inl ⟨hlt 0 1 h012.1, hlt 1 2 h012.2⟩
  · exact Or.inr (Or.inl ⟨hlt 1 2 h120.1, hlt 2 0 h120.2⟩)
  · exact Or.inr (Or.inr ⟨hlt 2 0 h201.1, hlt 0 1 h201.2⟩)

#print axioms pairLocalActualMoonGlobalPortLinearOrderOnItems
#print axioms exists_pairLocalActualMoon_globalHostCyclicPorts_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonGlobalCyclicPortSelectionOnItemsV1
