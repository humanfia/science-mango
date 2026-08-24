import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtLocalAngleOrderV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41RectangularSkirtGraphEntryParameterV1
open FamilyStickyCinematicL32Prop41RectangularSkirtLocalAngleOrderV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Item-local actual selected-lens geometry

The analytic two-root record is required only for pairs retained in `items`.
Outside `items` the generic finite lens-classification carrier is completed by
empty open sides and zero keys.  None of the selected-lens definitions query
those defaults: their defining relation always includes membership in `items`.
This avoids extending exact-two-root data to ambient unordered pairs by choice.
-/

def pairLocalItemRectangularSkirtTopGraph
    (g : Real -> Real) (A B theta : Real) : Real :=
  if theta < A then g A else if theta <= B then g theta else g B

def pairLocalItemRectangularSkirtInterior
    (g : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  {q | q.2 ∈ Ioo (A - depth) (B + depth) ∧
    -M - depth < q.1 ∧
      q.1 < pairLocalItemRectangularSkirtTopGraph g A B q.2}

def pairLocalActualItemSelectedFirstCurve
    {radius : NNReal} {curves : Finset (Tube radius)}
    (T : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (p : FirstGenerationCurvePair curves) :
    FirstGenerationCurve curves :=
  ⟨T p, hT p⟩

def pairLocalActualItemSelectedSecondCurve
    {radius : NNReal} {curves : Finset (Tube radius)}
    (U : FirstGenerationCurvePair curves -> Tube radius)
    (hU : forall p, U p ∈ curves) (p : FirstGenerationCurvePair curves) :
    FirstGenerationCurve curves :=
  ⟨U p, hU p⟩

def pairLocalActualItemSelectedOtherCurve
    {radius : NNReal} {curves : Finset (Tube radius)}
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (p : FirstGenerationCurvePair curves) (host : FirstGenerationCurve curves) :
    FirstGenerationCurve curves :=
  if host = pairLocalActualItemSelectedFirstCurve T hT p then
    pairLocalActualItemSelectedSecondCurve U hU p
  else pairLocalActualItemSelectedFirstCurve T hT p

/-- The faithful actual geometry completed harmlessly away from `items`.
The only analytic input is `D p hp` for an actual retained membership proof. -/
noncomputable def pairLocalActualSelectedLensLocalAngleGeometryOnItems
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
      (T p) (U p) f (rectangles p) A B delta t lambda0) :
    SelectedFixedSlotLensLocalAngleGeometry
      (Real × Real) (Tube radius) curves where
  firstCurve := pairLocalActualItemSelectedFirstCurve T hT
  secondCurve := pairLocalActualItemSelectedSecondCurve U hU
  pair_eq := hpair
  firstOpenSide := fun p =>
    if hp : p ∈ items then
      graphArc (actualTubeGraph (T p) f)
        (Ioo (D p hp).thetaLeft (D p hp).thetaRight)
    else ∅
  secondOpenSide := fun p =>
    if hp : p ∈ items then
      graphArc (actualTubeGraph (U p) f)
        (Ioo (D p hp).thetaLeft (D p hp).thetaRight)
    else ∅
  curveInterior := fun c =>
    pairLocalItemRectangularSkirtInterior
      (actualTubeGraph c.1 f) A B M (depth c)
  entryKey := fun p _ =>
    if hp : p ∈ items then
      rectangularSkirtGraphEntryParameter A B (D p hp).thetaLeft
    else 0
  entryAngleKey := fun p host =>
    if hp : p ∈ items then
      graphSideEntryLocalAngleKey
        (fun c theta =>
          FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1.actualTubeGraphFirst
            c.1 f f1 theta)
        host (pairLocalActualItemSelectedOtherCurve T U hT hU p host)
        (D p hp).thetaLeft
    else 0

@[simp]
theorem pairLocalActualSelectedLensLocalAngleGeometryOnItems_firstOpenSide
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
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
      hpair rectangles f f1 A B M depth D).firstOpenSide p =
      graphArc (actualTubeGraph (T p) f)
        (Ioo (D p hp).thetaLeft (D p hp).thetaRight) := by
  simp [pairLocalActualSelectedLensLocalAngleGeometryOnItems, hp]

@[simp]
theorem pairLocalActualSelectedLensLocalAngleGeometryOnItems_secondOpenSide
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
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
      hpair rectangles f f1 A B M depth D).secondOpenSide p =
      graphArc (actualTubeGraph (U p) f)
        (Ioo (D p hp).thetaLeft (D p hp).thetaRight) := by
  simp [pairLocalActualSelectedLensLocalAngleGeometryOnItems, hp]

@[simp]
theorem pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryKey
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
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items)
    (host : FirstGenerationCurve curves) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
      hpair rectangles f f1 A B M depth D).entryKey p host =
      rectangularSkirtGraphEntryParameter A B (D p hp).thetaLeft := by
  simp [pairLocalActualSelectedLensLocalAngleGeometryOnItems, hp]

@[simp]
theorem pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryAngleKey
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
    (p : FirstGenerationCurvePair curves) (hp : p ∈ items)
    (host : FirstGenerationCurve curves) :
    (pairLocalActualSelectedLensLocalAngleGeometryOnItems curves items T U hT hU
      hpair rectangles f f1 A B M depth D).entryAngleKey p host =
      graphSideEntryLocalAngleKey
        (fun c theta =>
          FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1.actualTubeGraphFirst
            c.1 f f1 theta)
        host (pairLocalActualItemSelectedOtherCurve T U hT hU p host)
        (D p hp).thetaLeft := by
  simp [pairLocalActualSelectedLensLocalAngleGeometryOnItems, hp]

#print axioms pairLocalActualSelectedLensLocalAngleGeometryOnItems
#print axioms pairLocalActualSelectedLensLocalAngleGeometryOnItems_firstOpenSide
#print axioms pairLocalActualSelectedLensLocalAngleGeometryOnItems_secondOpenSide
#print axioms pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryKey
#print axioms pairLocalActualSelectedLensLocalAngleGeometryOnItems_entryAngleKey

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
