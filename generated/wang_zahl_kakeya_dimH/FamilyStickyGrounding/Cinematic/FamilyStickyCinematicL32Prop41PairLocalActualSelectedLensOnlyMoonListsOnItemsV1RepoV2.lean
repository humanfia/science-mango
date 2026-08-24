import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensMoonClassificationOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensOnlyMoonListsOnItemsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensMoonClassificationOnItemsV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# The two non-moon actual neighbor-list classes are empty

Every pair-local actual selected lens is a moon-face by the exact two-root
sign theorem.  Therefore a neighbor-relation witness in either other class
would assign the same literal item two different kinds.  This file derives
the empty relation, empty support, and the resulting fixed-kind forbidden
triple statement; none is accepted as an input.
-/

theorem pairLocalActualSelectedLens_neighborRelation_false_of_ne_moonFace_onItems
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
    (hdepth : forall c, 0 < depth c)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B))
    {k : ProperLensKind} (hk : k ≠ ProperLensKind.moonFace)
    (host neighbor : FirstGenerationCurve curves) :
    ¬ localAngleSelectedLensNeighborRelation
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items k host neighbor := by
  rintro ⟨p, hp, hassigned, _⟩
  have hkind := hassigned.1
  have hmoon := pairLocalActualSelectedLens_kind_eq_moonFace_onItems
    curves items T U hT hU hpair rectangles f f1 hAB M depth hdepth D
    hgraphBound hcontinuous p hp
  exact hk (hkind.symm.trans hmoon)

theorem pairLocalActualSelectedLens_neighborSupport_eq_empty_of_ne_moonFace_onItems
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
    (hdepth : forall c, 0 < depth c)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B))
    {k : ProperLensKind} (hk : k ≠ ProperLensKind.moonFace)
    (host : FirstGenerationCurve curves) :
    (localAngleSelectedLensNeighborSequence
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items k host).support = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro neighbor hneighbor
  have hrelation :=
    (mem_localAngleSelectedLensNeighborSequence_support_iff
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items k host neighbor).mp hneighbor
  exact pairLocalActualSelectedLens_neighborRelation_false_of_ne_moonFace_onItems
    curves items T U hT hU hpair rectangles f f1 hAB M depth hdepth D
    hgraphBound hcontinuous hk host neighbor hrelation

theorem pairLocalActualSelectedLens_nonMoon_fixedKindForbidsSameTriple_onItems
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
    (hdepth : forall c, 0 < depth c)
    {delta t lambda0 : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B))
    {k : ProperLensKind} (hk : k ≠ ProperLensKind.moonFace) :
    FixedKindForbidsSameTriple
      (fun host => localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems
          curves items T U hT hU hpair rectangles f f1 A B M depth D)
        items k host) := by
  intro host host' _
  rintro ⟨x, y, z, _, _, _, hx, _, _, _, _⟩
  have hempty :=
    pairLocalActualSelectedLens_neighborSupport_eq_empty_of_ne_moonFace_onItems
      curves items T U hT hU hpair rectangles f f1 hAB M depth hdepth D
      hgraphBound hcontinuous hk host
  have hxHost := (Finset.mem_inter.mp hx).1
  rw [hempty] at hxHost
  simp at hxHost

#print axioms pairLocalActualSelectedLens_neighborRelation_false_of_ne_moonFace_onItems
#print axioms pairLocalActualSelectedLens_neighborSupport_eq_empty_of_ne_moonFace_onItems
#print axioms pairLocalActualSelectedLens_nonMoon_fixedKindForbidsSameTriple_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensOnlyMoonListsOnItemsV1
