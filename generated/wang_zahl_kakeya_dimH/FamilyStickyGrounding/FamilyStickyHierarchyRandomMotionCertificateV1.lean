import FamilyStickyGrounding.FamilyStickyHierarchyTranslatedFamilyV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyRandomMotionCertificateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyCommonPrefixLoadInvarianceV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyTranslatedFamilyV1
open FamilyStickyHierarchyTranslatedFamilyV1.HierarchyRandomMotionGeometry
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Hierarchy shared-motion certificate before the distinctness refinement

This is the first top-level, actual-family output of the random-motion branch
of GWZ `lemmasubsticky` (pinned source lines 1506--1524).  A certificate owns
the vectors produced simultaneously at every hierarchy level.  Its final
family is the literal occurrence family indexed by a translation path and an
active fine tube.  At every scale the same chosen vectors work for every
coarse parent and every supplied convex test after the already chosen common
prefix is applied.

The result deliberately stops before three later source arguments: essential
distinctness/deduplication (`lemrandommotion`), replacement of the finite test
list by all convex bodies, and arbitrary-radius Frostman interpolation.  Thus
the exact cardinality below is an occurrence count, not the source's final
deduplicated `card T'` estimate.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

/-- The complete, nondegenerate hierarchy motion selected by the proved
finite packing/Chernoff construction at every scale. -/
structure HierarchySharedMotionCertificate where
  output : G.toDependentSource.Output

namespace HierarchySharedMotionCertificate

variable (C : HierarchySharedMotionCertificate H G)

abbrev Path := (Output.toComposition G.toDependentSource C.output).Path

abbrev FinalIndex := FinalFineIndex H G C.output

def finalTube (a : C.FinalIndex) : Tube (H.effectiveRadius 0) :=
  finalFineTube H G C.output a

/-- The endpoint is automatic from the hierarchy geometry; it does not take
per-layer existence, packing, probability, or final-load callbacks. -/
theorem exists_certificate :
    Nonempty (HierarchySharedMotionCertificate H G) := by
  exact G.exists_output.map fun O => ⟨O⟩

include C in
theorem repetitions_one_le (k : Fin depth) :
    1 <= G.toDependentSource.repetitions k :=
  Output.repetitions_one_le C.output k

/-- Exact cardinality of the occurrence-indexed final translated family. -/
theorem finalIndex_card :
    Fintype.card C.FinalIndex =
      (∏ k, G.toDependentSource.repetitions k) *
        (H.family 0).refinement.refined.card :=
  finalFineIndex_card H G C.output

theorem finalIndex_nonempty (hdepth : 0 < depth) :
    Nonempty C.FinalIndex :=
  finalFineIndex_nonempty H G C.output hdepth

/-- Every final tube moves by at most the sum of the hierarchy parent
radii. -/
theorem finalTube_carrier_subset_totalRadius (a : C.FinalIndex) :
    (finalTube H G C a).carrier ⊆
      Metric.cthickening
        ((∑ k : Fin depth, H.effectiveRadius (k.1 + 1) : NNReal) : Real)
        ((H.effectiveFamily 0).tubes a.2.1).carrier :=
  finalFineTube_carrier_subset_totalRadius H G C.output a

/-- Actual common-prefix load for the literal hierarchy fiber.  This is the
finite-test Frostman-style estimate available before deduplication and the
all-convex-test reduction.  The right side is the source tail factor times
the canonical untranslated maximal-concentration cap
`Delta_max * volume(K) / (delta^2/2)`.
-/
theorem actual_prefix_fiber_load
    (path : C.Path) (k : Fin depth)
    (p : Index (k.1 + 1))
    (hp : p ∈ (H.step k.1 k.2).combinatorics.index.coarse)
    (K : Fin (G.tests k p).testCard)
    (hK : K ∈ (G.tests k p).activeTests) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.ActualTubeTestData.commonPrefixSingleLoad
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data K
        (Output.prefixVector G.toDependentSource C.output path k)
        (C.output.omega k j) : Real)) <=
      G.toDependentSource.tailParameter k *
        ((G.tests k p).attachHierarchyFiber H k.1 k.2 p).data.canonicalPaperSingleLoadCap K := by
  let q : (G.toDependentSource.layer k).Test := ⟨p, K⟩
  have hq : q ∈ (G.toDependentSource.layer k).activeTests := by
    exact ((G.toDependentSource.layer k).mem_activeTests_iff q).2 ⟨hp, hK⟩
  have hload := C.output.allParentCommonPrefixLoad
    G.toDependentSource path k q hq
  simpa [q, HierarchyRandomMotionGeometry.toDependentSource,
    hierarchyLayer, AllParentLayerData.paperCap,
    AllParentLayerData.commonPrefixSingleLoadAt] using hload

/-- Stagewise actual child/parent geometry under the same prefix used by the
load estimate. -/
theorem stage_child_subset_parentCthickening
    (path : C.Path) (k : Fin depth) (p : Index (k.1 + 1))
    (i : Index k.1)
    (hi : i ∈ (H.step k.1 k.2).combinatorics.index.fiber p)
    (j : Fin (G.toDependentSource.repetitions k)) :
    (translateTube
        (translateTube ((H.effectiveFamily k.1).tubes i)
          (C.output.omega k j))
        (Output.prefixVector G.toDependentSource C.output path k)).carrier ⊆
      Metric.cthickening (H.effectiveRadius (k.1 + 1) : Real)
        (translateTube ((H.effectiveFamily (k.1 + 1)).tubes p)
          (Output.prefixVector G.toDependentSource C.output path k)).carrier :=
  stage_child_subset_translatedParentCthickening H G C.output path k p i hi j

#print axioms exists_certificate
#print axioms repetitions_one_le
#print axioms finalIndex_card
#print axioms finalTube_carrier_subset_totalRadius
#print axioms actual_prefix_fiber_load
#print axioms stage_child_subset_parentCthickening

end HierarchySharedMotionCertificate

end
end FamilyStickyHierarchyRandomMotionCertificateV1
