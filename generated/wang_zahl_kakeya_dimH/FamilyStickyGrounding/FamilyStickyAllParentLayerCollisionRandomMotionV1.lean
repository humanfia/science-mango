import FamilyStickyGrounding.FamilyStickyAllParentLayerRandomMotionV1
import FamilyStickyGrounding.FamilyStickyRandomTwoFamilyTailV1
import FamilyStickyGrounding.FamilyStickyRandomWZSingleTranslationCapV1
import FamilyStickyGrounding.FamilyStickyRandomAllSourceWZCollisionChernoffV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAllParentLayerCollisionRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickyPaperRandomMotionNondegeneracyV1.ActualTubeTestData
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingExistenceV1
open FamilyStickySharedTranslationPackingExistenceV1.ActualTubeTranslationGrid
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyRandomWZSingleTranslationCapV1
open FamilyStickyRandomAllSourceWZCollisionChernoffV1
open FamilyStickyRandomTwoFamilyTailV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# One shared layer outcome with analytic and collision control

Faithful source provenance: GWZ Appendix lines 2655--2677 place the
`100 T₀` collision events inside the same fixed-parent application of
`lemrandommotion` as the convex-body events of lines 2681--2706.  At hierarchy
lines 1520--1524 the resulting translations are shared across all parents of
the layer.  Consequently the correct finite event index is

`(parent, analytic test) ⊔ (parent, model-tube collision candidate)`

on one packing and one product outcome.  There is no extra translation of the
already composed final occurrence family in this module.
-/

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

/-- The common motion-ball packing attached to one parent's literal fibre. -/
def parentPackingGrid
    (L : AllParentLayerData delta parent tubeIndex)
    {motionRadius : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta)
    (p : parent) :
    ActualTubeTranslationGrid delta (↥C.centers) tubeIndex :=
  ofMotionBallPackingCertificate (L.parentSeedGrid p) C

/-- Collision expectation majorant of a literal parent fibre.  It is
definitionally independent of the chosen finite packing. -/
def parentCollisionMean
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) (p : parent) : Real :=
  (297 * ((L.parentData p).data.tubes.card : Real) *
      (Tube.frameBoxSides (hundredRadius delta) 0 : Real) *
      (Tube.frameBoxSides (hundredRadius delta) 1 : Real)) /
    (motionRadius : Real) ^ 2

theorem parentCollisionMean_nonneg
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) (p : parent) :
    0 <= parentCollisionMean L motionRadius p := by
  unfold parentCollisionMean
  positivity

theorem allSourceWZCollisionMean_parentPackingGrid
    (L : AllParentLayerData delta parent tubeIndex)
    {motionRadius : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta)
    (p : parent) :
    allSourceWZCollisionMean (parentPackingGrid L C p) motionRadius =
      parentCollisionMean L motionRadius p := rfl

/-- All model-tube tests in all active parents, still on the one common
translation type supplied by `C`. -/
abbrev ParentCollisionTest
    (L : AllParentLayerData delta parent tubeIndex)
    {motionRadius : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta) :=
  Sigma fun p : parent => ModelCandidate (parentPackingGrid L C p)

def activeCollisionTests
    (L : AllParentLayerData delta parent tubeIndex)
    {motionRadius : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta) :
    Finset (ParentCollisionTest L C) := by
  classical
  exact L.activeParents.sigma fun _p => Finset.univ

theorem mem_activeCollisionTests_iff
    (L : AllParentLayerData delta parent tubeIndex)
    {motionRadius : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta)
    (q : ParentCollisionTest L C) :
    q ∈ activeCollisionTests L C ↔ q.1 ∈ L.activeParents := by
  classical
  simp [activeCollisionTests]

/-- The GWZ source tail reserves one full exponential unit, which is exactly
what is needed to add the collision event family without enlarging the
analytic threshold. -/
theorem sourceTail_reserved_unit
    (L : AllParentLayerData delta parent tubeIndex) :
    (L.activeTests.card : Real) * chordCost + 1 <=
      Real.exp (sourceTailParameter L) := by
  let x : Real := (L.activeTests.card : Real) * chordCost
  have hx : 0 <= x :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hx1 : 0 < x + 1 := by linarith
  have hlog : x + 1 = Real.exp (Real.log (x + 1)) := by
    rw [Real.exp_log hx1]
  have hmono : Real.exp (Real.log (x + 1)) <=
      Real.exp (max 1 (Real.log (x + 1))) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  change x + 1 <= Real.exp (max 1 (Real.log (x + 1)))
  calc
    x + 1 = Real.exp (Real.log (x + 1)) := hlog
    _ <= Real.exp (max 1 (Real.log (x + 1))) := hmono

/-- One hierarchy layer's faithful shared-motion output.  Its repetition
count is the existing analytic paper count; collision control is an added
property of the same chosen vectors. -/
structure AllParentLayerCollisionOutput
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) where
  certificate : PackingCertificate
    (Metric.closedBall (0 : Space) (motionRadius : Real)) delta
  omega : Fin (paperRepetitions L (L.paperMean motionRadius)) ->
    ↥certificate.centers
  repetitions_one_le :
    1 <= paperRepetitions L (L.paperMean motionRadius)
  allParentLoad : forall q, q ∈ L.activeTests ->
    (∑ j, (L.singleLoadAt q ((omega j).1 : Space) : Real)) <=
      sourceTailParameter L * L.paperCap q
  allParentCollisionLoad : forall p, p ∈ L.activeParents ->
    forall a : ModelCandidate (parentPackingGrid L certificate p),
      (∑ j, candidateCollisionLoad
        (parentPackingGrid L certificate p) a (omega j)) <=
        Nat.ceil
          (completionTail (activeCollisionTests L certificate).card
              (sourceTailParameter L) *
            commonHundredNeighbourPackingConstant)
  vector_norm_le : forall j,
    ‖((omega j).1 : Space)‖ <= (motionRadius : Real)

/-- Same-parent source separation, inherited in the hierarchy application
from the levelwise WZ-separated refined family. -/
def ParentFibreWZSeparated
    (L : AllParentLayerData delta parent tubeIndex) : Prop :=
  ∀ p, p ∈ L.activeParents →
    Set.Pairwise ((L.parentData p).data.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated
        ((L.parentData p).data.tube i)
        ((L.parentData p).data.tube j)

/-- The sole collision-specific scale hypothesis for the *existing* analytic
repetition count.  This is the formal location of the Appendix condition
`J m <= C_WZ`; it is not renamed as a probabilistic conclusion. -/
def ParentCollisionScale
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) : Prop :=
  ∀ p, p ∈ L.activeParents →
    (paperRepetitions L (L.paperMean motionRadius) : Real) *
        parentCollisionMean L motionRadius p <=
      (commonHundredNeighbourPackingConstant : Real)

/-- Geometry- and probability-complete producer for one faithful hierarchy
layer.  Analytic and collision events are selected by one two-family
Chernoff union bound over a single maximal packing of `B_rho`. -/
theorem exists_allParentLayerCollisionOutput
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hdeltaRadius : delta <= motionRadius)
    (hsmall : hundredRadius delta <= (2 : NNReal)⁻¹)
    (hdelta0 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 0)
    (hdelta1 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 1)
    (hsourceScale : forall q, q ∈ L.activeTests ->
      SourceMeanScale (L.parentData q.1).data
        (L.parentData q.1).Cbox (L.parentData q.1).side
        motionRadius q.2)
    (hpair : ParentFibreWZSeparated L)
    (hcollisionScale : ParentCollisionScale L motionRadius) :
    Nonempty (AllParentLayerCollisionOutput L motionRadius) := by
  classical
  let C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta :=
    Classical.choice
      (exists_motionBallPackingCertificate motionRadius delta hdeltaPos)
  have : Nonempty (↥C.centers) :=
    FamilyStickySharedTranslationPackingNonemptyV1.motionBallPackingCertificate_translation_nonempty C
  let mean : L.Test -> Real := L.paperMean motionRadius
  let J : Nat := paperRepetitions L mean
  let A : Real := sourceTailParameter L
  let B : Real := completionTail (activeCollisionTests L C).card A
  let collisionMean : ParentCollisionTest L C -> Real :=
    fun q => parentCollisionMean L motionRadius q.1
  have hRadius : 0 < motionRadius := hdeltaPos.trans_le hdeltaRadius
  have hmean : forall q, q ∈ L.activeTests -> 0 <= mean q := by
    intro q _hq
    exact L.paperMean_nonneg motionRadius q
  have hunit : forall q, q ∈ L.activeTests -> mean q <= L.paperCap q := by
    intro q hq
    have hq' := (L.mem_activeTests_iff q).1 hq
    exact
      FamilyStickyPaperRandomMotionNondegeneracyV1.ActualTubeTestData.paperIncidenceMean_le_canonicalPaperSingleLoadCap
        (L.parentData q.1).data (L.parentData q.1).hasBoxDimensions
        hdeltaPos hRadius q.2 (hsourceScale q hq)
  have hJ : 1 <= J := by
    exact one_le_paperRepetitions_of_mean_le_cap L mean hunit
  have hcapAnalytic : forall q, q ∈ L.activeTests -> 0 <= L.paperCap q := by
    intro q _hq
    unfold AllParentLayerData.paperCap
    unfold FamilyStickyActualTubeTestDataV1.ActualTubeTestData.canonicalPaperSingleLoadCap
    exact ENNReal.toReal_nonneg
  have hmeanCollision : forall q, q ∈ activeCollisionTests L C ->
      0 <= collisionMean q := by
    intro q _hq
    exact parentCollisionMean_nonneg L motionRadius q.1
  have hcapCollision : forall q : ParentCollisionTest L C,
      q ∈ activeCollisionTests L C ->
      0 <= (commonHundredNeighbourPackingConstant : Real) := by
    intro _q _hq
    exact Nat.cast_nonneg _
  have hloadCapCollision : forall q : ParentCollisionTest L C,
      q ∈ activeCollisionTests L C -> forall g : ↥C.centers,
      (candidateCollisionLoad (parentPackingGrid L C q.1) q.2 g : Real) <=
        commonHundredNeighbourPackingConstant := by
    intro q hq g
    have hp : q.1 ∈ L.activeParents :=
      (mem_activeCollisionTests_iff L C q).1 hq
    have hpairGrid : Set.Pairwise
        ((parentPackingGrid L C q.1).tubes : Set tubeIndex) fun i j =>
          WZEndpointParameterSeparated
            ((parentPackingGrid L C q.1).tube i)
            ((parentPackingGrid L C q.1).tube j) := by
      intro i hi j hj hij
      change WZEndpointParameterSeparated
        ((L.parentData q.1).data.tube i)
        ((L.parentData q.1).data.tube j)
      exact hpair q.1 hp hi hj hij
    exact_mod_cast candidateCollisionLoad_le_WZConstant
      (parentPackingGrid L C q.1) hdeltaPos hpairGrid q.2 g
  have hsumCollision : forall q, q ∈ activeCollisionTests L C ->
      (∑ g : ↥C.centers,
        (candidateCollisionLoad (parentPackingGrid L C q.1) q.2 g : Real)) <=
        (Fintype.card (↥C.centers) : Real) * collisionMean q := by
    intro q hq
    let PG := parentPackingGrid L C q.1
    let CG := collisionGrid PG
    have P : IsSharedTranslationPacking PG delta motionRadius :=
      ofMotionBallPackingCertificate_isSharedTranslationPacking
        (L.parentSeedGrid q.1) hdeltaPos C
    have PC : IsSharedTranslationPacking CG delta motionRadius :=
      FamilyStickyRandomModelTubeCollisionGridV1.IsSharedTranslationPacking.collisionGrid P
    have hdim : forall K, HasBoxDimensions 2 (collisionSide PG K)
        (CG.testBody K) := collisionGrid_hasBoxDimensions PG hsmall
    have hsum :=
      FamilyStickyActualSharedLocalExpectationV1.sum_singleLoad_le_card_mul_mean
        PC hdim (modelCandidateIndex PG q.2)
        (by exact Finset.mem_univ _)
        (allSourceWZCollisionMean_nonneg PG motionRadius)
        (delta_le_collisionSide_zero PG _)
        (delta_le_collisionSide_one PG _)
        hdeltaRadius
        (allSourceWZCollision_explicit_297 PG hRadius _)
    simpa only [PG, CG, collisionGrid_singleLoad_candidate,
      collisionMean, allSourceWZCollisionMean_parentPackingGrid] using hsum
  obtain ⟨choice, hchoiceAnalytic, hchoiceCollision⟩ :=
    FamilyStickyRandomTwoFamilyChernoffV1.exists_product_choice_two_load_bounds
      L.activeTests (activeCollisionTests L C) J
      (fun q (g : ↥C.centers) =>
        (L.singleLoadAt q ((g.1 : Space)) : Real))
      L.paperCap mean
      (fun q (g : ↥C.centers) =>
        (candidateCollisionLoad (parentPackingGrid L C q.1) q.2 g : Real))
      (fun _q => (commonHundredNeighbourPackingConstant : Real))
      collisionMean A B
      hcapAnalytic hmean
      (fun _q _hq _g => Nat.cast_nonneg _)
      (fun q hq g => by
        let PG := parentPackingGrid L C q.1
        have hload :=
          FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
            PG q.2 g hdelta hdeltaPos
        simpa [PG, parentPackingGrid, AllParentLayerData.singleLoadAt,
          AllParentLayerData.paperCap, AllParentLayerData.parentSeedGrid] using hload)
      (fun q hq => by
        have hq' := (L.mem_activeTests_iff q).1 hq
        let PG := parentPackingGrid L C q.1
        have P : IsSharedTranslationPacking PG delta motionRadius :=
          ofMotionBallPackingCertificate_isSharedTranslationPacking
            (L.parentSeedGrid q.1) hdeltaPos C
        have hsum :=
          FamilyStickyActualSharedLocalExpectationV1.sum_singleLoad_le_card_mul_mean
            P (L.parentData q.1).hasBoxDimensions q.2 hq'.2
            (L.paperMean_nonneg motionRadius q)
            (hdelta0 q hq) (hdelta1 q hq) hdeltaRadius
            (FamilyStickyPaperRandomMotionNumericalChoicesV1.ActualTubeTestData.explicit_297_le_motionRadius_sq_mul_paperIncidenceMean
              (L.parentData q.1).data (L.parentData q.1).side hRadius q.2)
        simpa [PG, mean, AllParentLayerData.paperMean,
          AllParentLayerData.singleLoadAt, AllParentLayerData.parentSeedGrid,
          parentPackingGrid] using hsum)
      (paperRepetitions_mul_mean_le_cap L mean hmean)
      hcapCollision hmeanCollision
      (fun _q _hq _g => Nat.cast_nonneg _)
      hloadCapCollision hsumCollision
      (fun q hq => by
        have hp : q.1 ∈ L.activeParents :=
          (mem_activeCollisionTests_iff L C q).1 hq
        simpa [J, collisionMean] using hcollisionScale q.1 hp)
      (two_family_tail_room L.activeTests.card
        (activeCollisionTests L C).card A
        (by simpa [A] using sourceTail_reserved_unit L))
  refine ⟨{
    certificate := C
    omega := choice
    repetitions_one_le := hJ
    allParentLoad := ?_
    allParentCollisionLoad := ?_
    vector_norm_le := ?_ }⟩
  · intro q hq
    simpa [J, A, FamilyStickyRandomFiniteChernoffV3.productLoad] using
      hchoiceAnalytic q hq
  · intro p hp a
    let q : ParentCollisionTest L C := ⟨p, a⟩
    have hq : q ∈ activeCollisionTests L C :=
      (mem_activeCollisionTests_iff L C q).2 hp
    have hreal := hchoiceCollision q hq
    have hreal' :
        ((∑ j, candidateCollisionLoad
            (parentPackingGrid L C p) a (choice j) : Nat) : Real) <=
          B * commonHundredNeighbourPackingConstant := by
      rw [Nat.cast_sum]
      simpa only [q, FamilyStickyRandomFiniteChernoffV3.productLoad] using hreal
    have hceil := hreal'.trans (Nat.le_ceil _)
    exact_mod_cast (show
      ((∑ j, candidateCollisionLoad
          (parentPackingGrid L C p) a (choice j) : Nat) : Real) <=
        (Nat.ceil (B * commonHundredNeighbourPackingConstant) : Nat) from hceil)
  · intro j
    have hj : ((choice j).1 : Space) ∈
        Metric.closedBall (0 : Space) (motionRadius : Real) :=
      C.centers_subset (choice j).2
    simpa [Metric.mem_closedBall, dist_zero_right] using hj

#print axioms sourceTail_reserved_unit
#print axioms exists_allParentLayerCollisionOutput

end

end FamilyStickyAllParentLayerCollisionRandomMotionV1
