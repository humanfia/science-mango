import FamilyStickyGrounding.FamilyStickyHierarchyPreMotionHullTestSupportV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchySuppliedPackingJointRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointRepetitionsV1
open FamilyStickyAllParentLayerJointCollisionRandomMotionV1
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
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyCollisionTestGeometryProducerV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1

noncomputable section

/-!
# Joint random motion using a supplied packing plan

The original one-layer selector first chooses a maximal packing certificate
internally.  Here the same probability argument is run over a certificate
supplied as an argument.  Consequently the multiscale output uses a packing
plan fixed before any random center is selected, and the pre-motion hull
catalogue has definitional certificate coherence with the selector.
-/

namespace SuppliedLayer

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

/-- The existing joint two-family selector, with its packing certificate
supplied before the product choice is made. -/
theorem exists_output_with_certificate
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta)
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
    Nonempty {O : AllParentLayerJointCollisionOutput L motionRadius //
      O.certificate = C} := by
  classical
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
  refine ⟨⟨{
    certificate := C
    omega := choice
    repetitions_one_le := hJ
    allParentLoad := ?_
    allParentCollisionLoad := ?_
    vector_norm_le := ?_ }, rfl⟩⟩
  · intro q hq
    simpa [J, A, FamilyStickyRandomFiniteChernoffV3.productLoad] using
      hchoiceAnalytic q hq
  · intro p hp a
    let q : ParentCollisionTest L C := ⟨p, a⟩
    have hq : q ∈ activeCollisionTests L C :=
      (mem_activeCollisionTests_iff L C q).2 hp
    have hreal := hchoiceCollision q hq
    have hreal' :
        (((∑ j, candidateCollisionLoad
            (parentPackingGrid L C p) a (choice j) : Nat) : Real)) <=
          B * commonHundredNeighbourPackingConstant := by
      rw [Nat.cast_sum]
      simpa only [q, FamilyStickyRandomFiniteChernoffV3.productLoad] using hreal
    have hceil := hreal'.trans (Nat.le_ceil _)
    exact_mod_cast (show
      (((∑ j, candidateCollisionLoad
          (parentPackingGrid L C p) a (choice j) : Nat) : Real)) <=
        (Nat.ceil (B * commonHundredNeighbourPackingConstant) : Nat) from hceil)
  · intro j
    have hj : ((choice j).1 : Space) ∈
        Metric.closedBall (0 : Space) (motionRadius : Real) :=
      C.centers_subset (choice j).2
    simpa [Metric.mem_closedBall, dist_zero_right] using hj

end SuppliedLayer

namespace SuppliedMultiscale

variable {depth : Nat} {Parent Child : Fin depth -> Type*}
  [forall k, Fintype (Parent k)]
  [forall k, DecidableEq (Parent k)]
  [forall k, DecidableEq (Child k)]

/-- Assemble one supplied-certificate selector at every scale. -/
theorem exists_output_with_certificates
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (C : forall k : Fin depth,
      PackingCertificate
        (Metric.closedBall (0 : Space) (D.motionRadius k : Real))
        (D.delta k))
    (hpair : forall k, ParentFibreWZSeparated (D.layer k))
    (hcollisionUnit : forall k p, p ∈ (D.layer k).activeParents ->
      parentCollisionMean (D.layer k) (D.motionRadius k) p <=
        (commonHundredNeighbourPackingConstant : Real)) :
    Nonempty {O : FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output D //
      forall k, (O.layerOutput k).certificate = C k} := by
  classical
  have hk : forall k,
      Nonempty {O : AllParentLayerJointCollisionOutput
          (D.layer k) (D.motionRadius k) //
        O.certificate = C k} := by
    intro k
    exact SuppliedLayer.exists_output_with_certificate
      (D.layer k) (D.motionRadius k) (C k)
      (D.delta_le_half k) (D.delta_pos k)
      (D.delta_le_motionRadius k)
      (D.delta_le_side_zero k) (D.delta_le_side_one k)
      (D.sourceMeanScale k) (hpair k) (hcollisionUnit k)
  let selected := fun k => Classical.choice (hk k)
  refine ⟨⟨{ layerOutput := fun k => (selected k).1 }, ?_⟩⟩
  intro k
  exact (selected k).2

end SuppliedMultiscale

namespace SuppliedHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}

/-- A faithful hierarchy certificate together with proof that every layer
uses the packing plan fixed before random selection. -/
structure Certificate
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (P : HierarchyPackingPlan.Plan H) where
  joint : HierarchyJointRandomMotionCertificate H G
  usesPlan : JointCertificateAdapter.UsesPackingPlan joint P

namespace Certificate

variable {P : HierarchyPackingPlan.Plan H}
  (Q : Certificate H G P)

abbrev Path := Q.joint.Path

/-- The supplied-plan selector feeds directly into the pre-motion finite
catalogue endpoint; no certificate transport hypothesis remains external. -/
theorem prefixFiber_isKatzTao_of_preMotion_finite_tests
    (path : Q.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (A : ENNReal)
    (hfinite : ∀ q,
      IsKatzTaoAt A
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (JointCertificateAdapter.plannedOmega
            Q.joint P Q.usesPlan k))
        ((HierarchyPackingPlan.parentCanonicalTestFamily H P G k p).testBody q)) :
    IsKatzTao A
      (FamilyStickyConvexBodyTranslationConcentrationV1.translateFamily
        (FixedPackingPotentialFamily.selectedFamily
          (hierarchyFiberSeedData H k p) (P.certificate k)
          (JointCertificateAdapter.plannedOmega
            Q.joint P Q.usesPlan k))
        (Q.joint.output.prefixVector path k)) := by
  exact JointCertificateAdapter.prefixFiber_isKatzTao_of_preMotion_finite_tests
    Q.joint P Q.usesPlan path k p A hfinite

end Certificate

/-- Hierarchy-level supplied-plan selector. -/
theorem exists_certificate_with_plan
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (P : HierarchyPackingPlan.Plan H)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H G) :
    Nonempty (Certificate H G P) := by
  obtain ⟨O, hO⟩ :=
    SuppliedMultiscale.exists_output_with_certificates
      G.toDependentSource P.certificate
      (hierarchy_parentFibreWZSeparated H G W)
      (fun k p hp => by
        have hp' : p ∈ (H.step k.1 k.2).combinatorics.index.coarse := by
          simpa [HierarchyRandomMotionGeometry.toDependentSource,
            hierarchyLayer] using hp
        exact hcollisionUnit k p hp')
  refine ⟨{ joint := ⟨O⟩, usesPlan := ?_ }⟩
  intro k
  exact hO k

/-- Specialization to the fixed canonical hull tests built from the same
preselected packing plan. -/
theorem exists_preMotion_certificate_with_plan
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (P : HierarchyPackingPlan.Plan H)
    (M : HierarchyPackingPlan.MeanScaleData H P G)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H
      (HierarchyPackingPlan.toPreMotionGeometry H P G M)) :
    Nonempty (Certificate H
      (HierarchyPackingPlan.toPreMotionGeometry H P G M) P) :=
  exists_certificate_with_plan H
    (HierarchyPackingPlan.toPreMotionGeometry H P G M) P W hcollisionUnit

end SuppliedHierarchy

#print axioms SuppliedLayer.exists_output_with_certificate
#print axioms SuppliedMultiscale.exists_output_with_certificates
#print axioms SuppliedHierarchy.exists_certificate_with_plan
#print axioms SuppliedHierarchy.exists_preMotion_certificate_with_plan
#print axioms SuppliedHierarchy.Certificate.prefixFiber_isKatzTao_of_preMotion_finite_tests

end
end FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
