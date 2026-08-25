import FamilyStickyGrounding.FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
import FamilyStickyGrounding.FamilyStickyHierarchyRandomMotionAdapterV1
import FamilyStickyGrounding.FamilyStickyHierarchyTranslatedFamilyV1
import FamilyStickyGrounding.FamilyStickyHierarchyLevelWZSeparationCoreV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyJointRandomMotionCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyTranslatedFamilyV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
open FamilyStickyHierarchyLevelWZSeparationCoreV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Source-faithful hierarchy motion certificate with joint `J_k`

The path at each layer has the joint analytic/collision repetition count.
Thus final occurrences, prefix analytic loads, local collision loads, and the
total-radius statement all concern one literal multiscale family.  No
analytic-only hierarchy certificate is used or projected to.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

def HierarchyJointHundredRadiusSmall : Prop :=
  forall k : Fin depth,
    FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
        (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹

/-- One-step source volume condition ensuring the collision selector is
nonzero.  The multiplication by `J_k` is produced internally. -/
def HierarchyParentCollisionUnitScale : Prop :=
  forall (k : Fin depth) (p : Index (k.1 + 1)),
    p ∈ (H.step k.1 k.2).combinatorics.index.coarse ->
      parentCollisionMean (G.toDependentSource.layer k)
          (G.toDependentSource.motionRadius k) p <=
        (FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant : Real)

theorem hierarchy_parentFibreWZSeparated
    (W : HierarchyLevelWZSeparationData H)
    (k : Fin depth) :
    ParentFibreWZSeparated (G.toDependentSource.layer k) := by
  let S := H.step k.1 k.2
  have hsep : Set.Pairwise (S.combinatorics.index.fine : Set (Index k.1))
      fun i j => FamilyStickyRandomWZLineParameterGeometryV1.WZEndpointParameterSeparated
        ((H.effectiveFamily k.1).tubes i)
        ((H.effectiveFamily k.1).tubes j) := by
    rw [S.combinatorics.fine_eq_refined]
    exact W.separated k.1 (Nat.le_of_lt k.2)
  intro p hp
  change Set.Pairwise (S.combinatorics.index.fiber p : Set (Index k.1))
    fun i j => FamilyStickyRandomWZLineParameterGeometryV1.WZEndpointParameterSeparated
      ((H.effectiveFamily k.1).tubes i)
      ((H.effectiveFamily k.1).tubes j)
  intro i hi j hj hij
  exact hsep
    ((S.combinatorics.index.mem_fiber i p).1 hi).1
    ((S.combinatorics.index.mem_fiber j p).1 hj).1 hij

structure HierarchyJointRandomMotionCertificate where
  output : FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
    G.toDependentSource

namespace HierarchyJointRandomMotionCertificate

variable {H G} (C : HierarchyJointRandomMotionCertificate H G)

abbrev Path := C.output.Path

/-- Occurrence index for the one joint multiscale family.  No pairwise
distinctness premise is imposed on this index. -/
abbrev FinalIndex :=
  C.Path × {i // i ∈ (H.family 0).refinement.refined}

def finalTube (a : C.FinalIndex) : Tube (H.effectiveRadius 0) :=
  translateTube ((H.effectiveFamily 0).tubes a.2.1)
    (C.output.toComposition.composedVector a.1)

theorem finalIndex_card :
    Fintype.card C.FinalIndex =
      (∏ k, FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
          G.toDependentSource k) *
        (H.family 0).refinement.refined.card := by
  classical
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_coe]
  simp only [Fintype.card_fin]
  rfl

theorem finalTube_carrier_subset_totalRadius (a : C.FinalIndex) :
    (C.finalTube a).carrier ⊆
      Metric.cthickening
        ((∑ k : Fin depth, H.effectiveRadius (k.1 + 1) : NNReal) : Real)
        ((H.effectiveFamily 0).tubes a.2.1).carrier := by
  simpa [finalTube, FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.toComposition,
    FamilyStickyMultiscaleSharedMotionCompositionV1.MultiscaleSharedMotionComposition.totalRadius,
    HierarchyRandomMotionGeometry.toDependentSource] using
    C.output.toComposition.composed_translateTube_carrier_subset_cthickening
      ((H.effectiveFamily 0).tubes a.2.1) a.1

theorem path_nonempty : Nonempty C.Path := C.output.path_nonempty

theorem repetitions_one_le
    (Q : HierarchyJointRandomMotionCertificate H G) (k : Fin depth) :
    1 <= FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
      G.toDependentSource k :=
  (Q.output.layerOutput k).repetitions_one_le

theorem actual_prefix_fiber_load
    (path : C.Path) (k : Fin depth)
    (p : Index (k.1 + 1))
    (hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (K : Fin (G.tests k p).testCard)
    (hK : K ∈ (G.tests k p).activeTests) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.ActualTubeTestData.commonPrefixSingleLoad
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data K
        (C.output.prefixVector path k)
        (C.output.omega k j) : Real)) <=
      FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
          (G.toDependentSource.layer k) *
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data.canonicalPaperSingleLoadCap K := by
  let q : (G.toDependentSource.layer k).Test := ⟨p, K⟩
  have hq : q ∈ (G.toDependentSource.layer k).activeTests := by
    exact ((G.toDependentSource.layer k).mem_activeTests_iff q).2 ⟨hp, hK⟩
  have hload := C.output.allParentCommonPrefixLoad path k q hq
  simpa [q, HierarchyRandomMotionGeometry.toDependentSource,
    hierarchyLayer, FamilyStickyAllParentLayerDataV1.AllParentLayerData.paperCap,
    FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt]
    using hload

theorem parentCollisionLoad
    (k : Fin depth) (p : Index (k.1 + 1))
    (hp : p ∈ (G.toDependentSource.layer k).activeParents)
    (a : FamilyStickyRandomModelTubeCollisionGridV1.ModelCandidate
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate p)) :
    (∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        a ((C.output.layerOutput k).omega j)) <=
      Nat.ceil
        (FamilyStickyRandomTwoFamilyTailV1.completionTail
            (activeCollisionTests (G.toDependentSource.layer k)
              (C.output.layerOutput k).certificate).card
            (FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
              (G.toDependentSource.layer k)) *
          FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant) :=
  C.output.allParentCollisionLoad k p hp a

theorem stage_child_subset_parentCthickening
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (i : Index k.1)
    (hi : i ∈ (H.step k.1 k.2).combinatorics.index.fiber p)
    (j : Fin (FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.repetitions
      G.toDependentSource k)) :
    (translateTube
        (translateTube ((H.effectiveFamily k.1).tubes i)
          (C.output.omega k j))
        (C.output.prefixVector path k)).carrier ⊆
      Metric.cthickening (H.effectiveRadius (k.1 + 1) : Real)
        (translateTube ((H.effectiveFamily (k.1 + 1)).tubes p)
          (C.output.prefixVector path k)).carrier := by
  let S := H.step k.1 k.2
  have hi' : i ∈ S.combinatorics.index.fine ∧
      S.combinatorics.index.parent i = p :=
    (S.combinatorics.index.mem_fiber i p).1 hi
  have hiRef : i ∈ (H.family k.1).refinement.refined := by
    rw [← S.combinatorics.fine_eq_refined]
    exact hi'.1
  have hparent := H.effective_carrier_subset_parent k.1 k.2 i hiRef
  have hpEq : (H.step k.1 k.2).parentIndex i = p := by
    simpa [AdjacentTubeStep.parentIndex, S] using hi'.2
  have hparent' :
      ((H.effectiveFamily k.1).tubes i).carrier ⊆
        ((H.effectiveFamily (k.1 + 1)).tubes p).carrier := by
    simpa [hpEq] using hparent
  exact commonPrefix_localTranslate_subset_parentCthickening
    ((H.effectiveFamily k.1).tubes i)
    ((H.effectiveFamily (k.1 + 1)).tubes p)
    (C.output.omega k j) (C.output.prefixVector path k)
    (H.effectiveRadius (k.1 + 1)) hparent'
    ((C.output.layerOutput k).vector_norm_le j)

#print axioms finalIndex_card
#print axioms finalTube_carrier_subset_totalRadius
#print axioms actual_prefix_fiber_load
#print axioms parentCollisionLoad
#print axioms stage_child_subset_parentCthickening

end HierarchyJointRandomMotionCertificate

theorem exists_certificate
    (hsmall : HierarchyJointHundredRadiusSmall H)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H G) :
    Nonempty (HierarchyJointRandomMotionCertificate H G) := by
  obtain ⟨O⟩ :=
    FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.exists_output
      G.toDependentSource
      (fun k => by
        simpa [HierarchyRandomMotionGeometry.toDependentSource] using hsmall k)
      (hierarchy_parentFibreWZSeparated H G W)
      (fun k p hp => by
        have hp' : p ∈ (H.step k.1 k.2).combinatorics.index.coarse := by
          simpa [HierarchyRandomMotionGeometry.toDependentSource,
            hierarchyLayer] using hp
        exact hcollisionUnit k p hp')
  exact ⟨⟨O⟩⟩

/-- Hierarchy certificate with the collision outer box produced directly;
no `100 delta <= 1/2` cutoff remains. -/
theorem exists_certificate_without_hundred_small
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionUnit : HierarchyParentCollisionUnitScale H G) :
    Nonempty (HierarchyJointRandomMotionCertificate H G) := by
  obtain ⟨O⟩ :=
    FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.exists_output_without_hundred_small
      G.toDependentSource
      (hierarchy_parentFibreWZSeparated H G W)
      (fun k p hp => by
        have hp' : p ∈ (H.step k.1 k.2).combinatorics.index.coarse := by
          simpa [HierarchyRandomMotionGeometry.toDependentSource,
            hierarchyLayer] using hp
        exact hcollisionUnit k p hp')
  exact ⟨⟨O⟩⟩

#print axioms hierarchy_parentFibreWZSeparated
#print axioms exists_certificate_without_hundred_small
#print axioms exists_certificate

end

end FamilyStickyHierarchyJointRandomMotionCertificateV1
