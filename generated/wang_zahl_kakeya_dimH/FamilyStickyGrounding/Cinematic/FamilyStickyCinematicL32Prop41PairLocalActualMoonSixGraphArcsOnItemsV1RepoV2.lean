import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensRegionV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Literal positive graph arcs for the six moon incidences

For a moon assigned to `host`, the positive lens side is the *other* curve's
open arc lying in the host interior.  The definition and first two lemmas are
generic.  The final specialization proves that these are the literal actual
tube graph arcs over the ordered root interval and lie in the corresponding
closed two-arc lens boundary.
-/

/-- The side of a selected moon that lies inside its assigned host. -/
def moonPositiveSideSet
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc D items host neighbor) : Set point :=
  if host = D.firstCurve arc.pair then D.secondOpenSide arc.pair
  else D.firstOpenSide arc.pair

theorem moonPositiveSideSet_subset_hostInterior
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc D items host neighbor) :
    moonPositiveSideSet arc ⊆ D.curveInterior host := by
  classical
  rcases arc.host_positive with hfirst | hsecond
  · intro q hq
    rw [moonPositiveSideSet, if_pos hfirst.1] at hq
    simpa [hfirst.1] using hfirst.2 hq
  · have hfirstNeSecond : D.firstCurve arc.pair ≠ D.secondCurve arc.pair := by
      intro heq
      apply arc.pair.2
      rw [D.pair_eq arc.pair, Sym2.mk_isDiag_iff]
      exact heq
    have hnotFirst : host ≠ D.firstCurve arc.pair := by
      intro heq
      exact hfirstNeSecond (heq.symm.trans hsecond.1)
    intro q hq
    rw [moonPositiveSideSet, if_neg hnotFirst] at hq
    simpa [hsecond.1] using hsecond.2 hq

theorem moonPositiveSideSet_subset_selectedOpenBoundary
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {D : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {host neighbor : FirstGenerationCurve curves}
    (arc : MoonPositiveSideArc D items host neighbor) :
    moonPositiveSideSet arc ⊆
      D.firstOpenSide arc.pair ∪ D.secondOpenSide arc.pair := by
  classical
  by_cases hfirst : host = D.firstCurve arc.pair
  · rw [moonPositiveSideSet, if_pos hfirst]
    exact subset_union_right
  · rw [moonPositiveSideSet, if_neg hfirst]
    exact subset_union_left

/-- The literal closed two-graph-arc boundary of one actual selected pair. -/
def pairLocalActualItemSelectedPairGraphBoundary
    {radius : NNReal} {curves : Finset (Tube radius)}
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (f : Real -> Real)
    {rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle}
    {A B delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData (T p) (U p) f
      (rectangles p) A B delta t lambda0)
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items) : Set (Real × Real) :=
  graphLensBoundaryArcs
    (actualTubeGraph (T p) f) (actualTubeGraph (U p) f)
    (D p hp).thetaLeft (D p hp).thetaRight

/-- Every selected open side of the actual geometry lies in the literal
closed two-arc graph boundary. -/
theorem pairLocalActualSelectedOpenBoundary_subset_pairGraphBoundary_onItems
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
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items) :
    let G := pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair
      rectangles f f1 A B M depth D
    G.firstOpenSide p ∪ G.secondOpenSide p ⊆
      pairLocalActualItemSelectedPairGraphBoundary items T U f D p hp := by
  dsimp only
  intro q hq
  rw [pairLocalActualSelectedLensLocalAngleGeometryOnItems_firstOpenSide
      curves items T U hT hU hpair rectangles f f1 A B M depth D p hp,
    pairLocalActualSelectedLensLocalAngleGeometryOnItems_secondOpenSide
      curves items T U hT hU hpair rectangles f f1 A B M depth D p hp] at hq
  rcases hq with hfirst | hsecond
  · left
    exact ⟨⟨hfirst.1.1.le, hfirst.1.2.le⟩, hfirst.2⟩
  · right
    exact ⟨⟨hsecond.1.1.le, hsecond.1.2.le⟩, hsecond.2⟩

/-- Actual specialization of the finite six-arc producer. -/
noncomputable def pairLocalActualMoonFiveCurveConfigurationOfSameCyclicTriple_onItems
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
    (leftHost rightHost x y z : FirstGenerationCurve curves)
    (hhost : leftHost ≠ rightHost)
    (htriple : SameCyclicTriple
      (localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
          f f1 A B M depth D) items
        ProperLensKind.moonFace leftHost)
      (localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
          f f1 A B M depth D) items
        ProperLensKind.moonFace rightHost) x y z) :
    MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
        f f1 A B M depth D) items leftHost rightHost x y z :=
  moonFiveCurveConfigurationOfSameCyclicTriple
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
      f f1 A B M depth D) items leftHost rightHost x y z
    hhost htriple

/-- Each one of the six produced positive sides is simultaneously inside its
host interior and inside its own literal actual two-graph-arc boundary. -/
theorem pairLocalActualMoonPositiveSideArc_subsets_onItems
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
    moonPositiveSideSet arc ⊆
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU hpair rectangles
          f f1 A B M depth D).curveInterior host ∧
      moonPositiveSideSet arc ⊆
        pairLocalActualItemSelectedPairGraphBoundary items T U f D arc.pair arc.pair_mem := by
  constructor
  · exact moonPositiveSideSet_subset_hostInterior arc
  · exact (moonPositiveSideSet_subset_selectedOpenBoundary arc).trans
      (pairLocalActualSelectedOpenBoundary_subset_pairGraphBoundary_onItems curves items T U hT hU
        hpair rectangles f f1 A B M depth D arc.pair arc.pair_mem)

#print axioms moonPositiveSideSet
#print axioms moonPositiveSideSet_subset_hostInterior
#print axioms pairLocalActualItemSelectedPairGraphBoundary
#print axioms pairLocalActualSelectedOpenBoundary_subset_pairGraphBoundary_onItems
#print axioms pairLocalActualMoonFiveCurveConfigurationOfSameCyclicTriple_onItems
#print axioms pairLocalActualMoonPositiveSideArc_subsets_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonSixGraphArcsOnItemsV1
