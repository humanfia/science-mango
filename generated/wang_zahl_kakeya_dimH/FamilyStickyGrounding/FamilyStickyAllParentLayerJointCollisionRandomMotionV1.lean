import FamilyStickyGrounding.FamilyStickyAllParentLayerJointRepetitionsV1
import FamilyStickyGrounding.FamilyStickyRandomTwoFamilyTailV1
import FamilyStickyGrounding.FamilyStickyRandomCollisionOuterFrameExpectationV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAllParentLayerJointCollisionRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointRepetitionsV1
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
open FamilyStickyRandomCollisionOuterFrameExpectationV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Faithful one-layer random motion with the joint repetition count

This is the source-faithful replacement for the conditional analytic-only-J
layer certificate.  The one product outcome has length `jointRepetitions`, so
both the collision and analytic moment scales hold by construction.  The only
new numerical source input is the one-step condition
`parentCollisionMean <= C_WZ`, needed to prove `J >= 1`.
-/

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

structure AllParentLayerJointCollisionOutput
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal) where
  certificate : PackingCertificate
    (Metric.closedBall (0 : Space) (motionRadius : Real)) delta
  omega : Fin (jointRepetitions L motionRadius) -> ↥certificate.centers
  repetitions_one_le : 1 <= jointRepetitions L motionRadius
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

theorem exists_allParentLayerJointCollisionOutput_without_hundred_small
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hdeltaRadius : delta <= motionRadius)
    (hdelta0 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 0)
    (hdelta1 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 1)
    (hsourceScale : forall q, q ∈ L.activeTests ->
      SourceMeanScale (L.parentData q.1).data
        (L.parentData q.1).Cbox (L.parentData q.1).side
        motionRadius q.2)
    (hpair : ParentFibreWZSeparated L)
    (hcollisionUnit : forall p, p ∈ L.activeParents ->
      parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real)) :
    Nonempty (AllParentLayerJointCollisionOutput L motionRadius) := by
  classical
  let C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta :=
    Classical.choice
      (exists_motionBallPackingCertificate motionRadius delta hdeltaPos)
  have : Nonempty (↥C.centers) :=
    FamilyStickySharedTranslationPackingNonemptyV1.motionBallPackingCertificate_translation_nonempty C
  let mean : L.Test -> Real := L.paperMean motionRadius
  let J : Nat := jointRepetitions L motionRadius
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
    exact
      paperIncidenceMean_le_canonicalPaperSingleLoadCap
        (L.parentData q.1).data (L.parentData q.1).hasBoxDimensions
        hdeltaPos hRadius q.2 (hsourceScale q hq)
  have hJ : 1 <= J := by
    exact one_le_jointRepetitions L motionRadius hunit hcollisionUnit
  have hcapAnalytic : forall q, q ∈ L.activeTests -> 0 <= L.paperCap q := by
    intro q _hq
    unfold AllParentLayerData.paperCap canonicalPaperSingleLoadCap
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
    intro q _hq
    let PG := parentPackingGrid L C q.1
    let CG := collisionGrid PG
    have P : IsSharedTranslationPacking PG delta motionRadius :=
      ofMotionBallPackingCertificate_isSharedTranslationPacking
        (L.parentSeedGrid q.1) hdeltaPos C
    have PC : IsSharedTranslationPacking CG delta motionRadius :=
      FamilyStickyRandomModelTubeCollisionGridV1.IsSharedTranslationPacking.collisionGrid P
    have hsum :=
      sum_singleLoad_le_card_mul_mean_of_outerBox
        PC (modelCandidateIndex PG q.2) (by exact Finset.mem_univ _)
        (collisionOuterBox PG (modelCandidateIndex PG q.2))
        (collisionTest_subset_collisionOuterBox PG
          (modelCandidateIndex PG q.2))
        (allSourceWZCollisionMean_nonneg PG motionRadius)
        (by
          rw [collisionOuterBox_side]
          exact delta_le_collisionSide_zero PG (modelCandidateIndex PG q.2))
        (by
          rw [collisionOuterBox_side]
          exact delta_le_collisionSide_one PG (modelCandidateIndex PG q.2))
        hdeltaRadius
        (by
          simp only [collisionOuterBox_side]
          exact allSourceWZCollision_explicit_297 PG hRadius
            (modelCandidateIndex PG q.2))
    simpa only [PG, CG, collisionGrid_singleLoad_candidate,
      collisionMean, allSourceWZCollisionMean_parentPackingGrid] using hsum
  obtain ⟨choice, hchoiceAnalytic, hchoiceCollision⟩ :=
    FamilyStickyRandomTwoFamilyChernoffV1.exists_product_choice_two_load_bounds
      L.activeTests (activeCollisionTests L C) J
      (fun q (g : ↥C.centers) =>
        (L.singleLoadAt q (g.1 : Space) : Real))
      L.paperCap mean
      (fun q (g : ↥C.centers) =>
        (candidateCollisionLoad (parentPackingGrid L C q.1) q.2 g : Real))
      (fun _q => (commonHundredNeighbourPackingConstant : Real))
      collisionMean A B
      hcapAnalytic hmean
      (fun _q _hq _g => Nat.cast_nonneg _)
      (fun q _hq g => by
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
      (by simpa [J, mean] using
        jointRepetitions_mul_analyticMean_le_cap L motionRadius)
      hcapCollision hmeanCollision
      (fun _q _hq _g => Nat.cast_nonneg _)
      hloadCapCollision hsumCollision
      (fun q hq => by
        have hp : q.1 ∈ L.activeParents :=
          (mem_activeCollisionTests_iff L C q).1 hq
        simpa [J, collisionMean] using
          jointRepetitions_mul_collisionMean_le_cap
            L motionRadius q.1 hp)
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

/-- Backwards-compatible wrapper.  The `100 delta <= 1/2` premise is no
longer consumed: collision expectation needs only the unconditional aligned
outer box, not a two-sided `HasBoxDimensions` certificate. -/
theorem exists_allParentLayerJointCollisionOutput
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hdeltaRadius : delta <= motionRadius)
    (_hsmall : hundredRadius delta <= (2 : NNReal)⁻¹)
    (hdelta0 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 0)
    (hdelta1 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 1)
    (hsourceScale : forall q, q ∈ L.activeTests ->
      SourceMeanScale (L.parentData q.1).data
        (L.parentData q.1).Cbox (L.parentData q.1).side
        motionRadius q.2)
    (hpair : ParentFibreWZSeparated L)
    (hcollisionUnit : forall p, p ∈ L.activeParents ->
      parentCollisionMean L motionRadius p <=
        (commonHundredNeighbourPackingConstant : Real)) :
    Nonempty (AllParentLayerJointCollisionOutput L motionRadius) :=
  exists_allParentLayerJointCollisionOutput_without_hundred_small
    L motionRadius hdelta hdeltaPos hdeltaRadius hdelta0 hdelta1
    hsourceScale hpair hcollisionUnit

#print axioms exists_allParentLayerJointCollisionOutput_without_hundred_small
#print axioms exists_allParentLayerJointCollisionOutput

end

end FamilyStickyAllParentLayerJointCollisionRandomMotionV1
