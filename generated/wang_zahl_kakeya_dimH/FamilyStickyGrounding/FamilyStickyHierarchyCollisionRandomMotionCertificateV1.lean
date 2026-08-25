import FamilyStickyGrounding.FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1
import FamilyStickyGrounding.FamilyStickyHierarchyRandomMotionCertificateV1
import FamilyStickyGrounding.FamilyStickyHierarchyLevelWZSeparationCoreV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyCollisionRandomMotionCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData
open FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1.Output
open FamilyStickyHierarchyRandomMotionCertificateV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Hierarchy certificate with faithful layerwise collision events

This is the hierarchy-level replacement for the non-final construction that
translated the already composed occurrence family once more.  Each collision
catalogue is attached to one original parent fibre at its own hierarchy layer,
exactly where GWZ lines 1506--1524 invoke `lemrandommotion`.  The analytic
projection is an ordinary `HierarchySharedMotionCertificate`, so existing
prefix load, stage containment, and total-radius theorems apply unchanged.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

/-- Literal Appendix collision scale for the repetition count already chosen
by the analytic tests at every parent fibre. -/
def HierarchyParentCollisionScale : Prop :=
  forall k : Fin depth,
    ParentCollisionScale (G.toDependentSource.layer k)
      (G.toDependentSource.motionRadius k)

/-- Source smallness needed by the aligned box certificate for `100 T₀`. -/
def HierarchyHundredRadiusSmall : Prop :=
  forall k : Fin depth,
    FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius
        (H.effectiveRadius k.1) <= (2 : NNReal)⁻¹

/-- Levelwise WZ separation restricts to every literal parent fibre. -/
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

/-- Collision-enhanced hierarchy output with a canonical projection to all
pre-existing analytic hierarchy APIs. -/
structure HierarchyCollisionSharedMotionCertificate where
  output : FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1.Output
    G.toDependentSource

namespace HierarchyCollisionSharedMotionCertificate

variable {H G}
  (C : HierarchyCollisionSharedMotionCertificate H G)

def toHierarchySharedMotionCertificate :
    HierarchySharedMotionCertificate H G where
  output := C.output.toAnalyticOutput

abbrev Path :=
  (toHierarchySharedMotionCertificate C).Path

theorem repetitions_one_le
    (Q : HierarchyCollisionSharedMotionCertificate H G) (k : Fin depth) :
    1 <= G.toDependentSource.repetitions k :=
  FamilyStickyHierarchyRandomMotionCertificateV1.HierarchySharedMotionCertificate.repetitions_one_le
    H G (toHierarchySharedMotionCertificate Q) k

/-- The actual collision load bound in one hierarchy parent, on the same
vectors used by the projected analytic certificate. -/
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

/-- Existing prefix load is inherited literally, not reproved with a larger
joint tail. -/
theorem actual_prefix_fiber_load
    (path : C.Path) (k : Fin depth)
    (p : Index (k.1 + 1))
    (hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (K : Fin (G.tests k p).testCard)
    (hK : K ∈ (G.tests k p).activeTests) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.ActualTubeTestData.commonPrefixSingleLoad
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data K
        (FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData.Output.prefixVector
          G.toDependentSource
          (toHierarchySharedMotionCertificate C).output path k)
        ((toHierarchySharedMotionCertificate C).output.omega k j) : Real)) <=
      G.toDependentSource.tailParameter k *
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data.canonicalPaperSingleLoadCap K :=
  (toHierarchySharedMotionCertificate C).actual_prefix_fiber_load
    H G path k p hp K hK

#print axioms toHierarchySharedMotionCertificate
#print axioms parentCollisionLoad
#print axioms actual_prefix_fiber_load

end HierarchyCollisionSharedMotionCertificate

/-- Fully automatic hierarchy selection from the actual hierarchy geometry,
level WZ separation, and the two explicit collision scale conditions. -/
theorem exists_certificate
    (hsmall : HierarchyHundredRadiusSmall H)
    (W : HierarchyLevelWZSeparationData H)
    (hcollisionScale : HierarchyParentCollisionScale H G) :
    Nonempty (HierarchyCollisionSharedMotionCertificate H G) := by
  obtain ⟨O⟩ :=
    FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1.exists_output
      G.toDependentSource
      (fun k => by
        simpa [HierarchyRandomMotionGeometry.toDependentSource] using hsmall k)
      (hierarchy_parentFibreWZSeparated H G W)
      hcollisionScale
  exact ⟨⟨O⟩⟩

#print axioms hierarchy_parentFibreWZSeparated
#print axioms exists_certificate

end

end FamilyStickyHierarchyCollisionRandomMotionCertificateV1
