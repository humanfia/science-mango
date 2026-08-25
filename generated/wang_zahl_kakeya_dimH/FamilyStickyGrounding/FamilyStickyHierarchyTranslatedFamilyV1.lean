import FamilyStickyGrounding.FamilyStickyHierarchyRandomMotionAdapterV1
import FamilyStickyGrounding.FamilyStickyLatticeMotionRadiusV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyTranslatedFamilyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyActualTubeTranslationV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Actual translated occurrences from a hierarchy motion output

The source final family is indexed by a choice of one translation at every
scale and one active fine tube.  We expose exactly that occurrence-indexed
family, its cardinality before deduplication, its total-radius control, and
the stagewise child/parent containment after a common earlier prefix.

No distinctness or deduplicated-cardinality claim is made here: that is the
separate `lemrandommotion` collision/refinement obligation.
-/

/-- Applying a local motion to a child and then a common old prefix keeps it
inside the corresponding translated parent thickened by the local radius. -/
theorem commonPrefix_localTranslate_subset_parentCthickening
    {childRadius parentRadius : NNReal}
    (child : Tube childRadius) (parent : Tube parentRadius)
    (v pfx : Space) (r : NNReal)
    (hchild : child.carrier ⊆ parent.carrier)
    (hv : ‖v‖ <= (r : Real)) :
    (translateTube (translateTube child v) pfx).carrier ⊆
      Metric.cthickening (r : Real) (translateTube parent pfx).carrier := by
  rw [translateTube_carrier (translateTube child v) pfx]
  rw [translateTube_carrier parent pfx]
  rw [FamilyStickyActualTubeTranslationV1.cthickening_translate]
  apply Set.image_mono
  exact
    (FamilyStickyLatticeMotionRadiusV1.translateTube_carrier_subset_cthickening_of_norm_le
      child v r hv).trans
      (Metric.cthickening_subset_of_subset (r : Real) hchild)

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)

namespace HierarchyRandomMotionGeometry

/-- One occurrence in the final translated fine family. -/
abbrev FinalFineIndex (O : G.toDependentSource.Output) :=
  (Output.toComposition G.toDependentSource O).Path ×
    {i // i ∈ (H.family 0).refinement.refined}

/-- Literal final fine tube for one translation path and one active index. -/
def finalFineTube (O : G.toDependentSource.Output)
    (a : FinalFineIndex H G O) : Tube (H.effectiveRadius 0) :=
  translateTube ((H.effectiveFamily 0).tubes a.2.1)
    ((Output.toComposition G.toDependentSource O).composedVector a.1)

/-- Exact occurrence count.  It deliberately precedes the source's
essential-distinctness refinement. -/
theorem finalFineIndex_card (O : G.toDependentSource.Output) :
    Fintype.card (FinalFineIndex H G O) =
      (∏ k, G.toDependentSource.repetitions k) *
        (H.family 0).refinement.refined.card := by
  classical
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_coe]
  simp only [Fintype.card_fin]
  rfl

/-- Every final occurrence remains within the sum-radius thickening of its
original active fine tube. -/
theorem finalFineTube_carrier_subset_totalRadius
    (O : G.toDependentSource.Output) (a : FinalFineIndex H G O) :
    (finalFineTube H G O a).carrier ⊆
      Metric.cthickening
        ((∑ k : Fin depth, H.effectiveRadius (k.1 + 1) : NNReal) : Real)
        ((H.effectiveFamily 0).tubes a.2.1).carrier := by
  exact
    (Output.toComposition G.toDependentSource O).composed_translateTube_carrier_subset_cthickening
      ((H.effectiveFamily 0).tubes a.2.1) a.1

/-- An honest positive-depth hierarchy has a nonempty active fine set. -/
theorem activeFine_nonempty_of_depth_pos (hdepth : 0 < depth) :
    (H.family 0).refinement.refined.Nonempty := by
  let C := (H.step 0 hdepth).combinatorics
  obtain ⟨p, hp⟩ := C.coarse_nonempty
  obtain ⟨i, hi, _hparent⟩ := C.parent_surjective p hp
  refine ⟨i, ?_⟩
  rw [← C.fine_eq_refined]
  exact hi

theorem finalFineIndex_nonempty
    (O : G.toDependentSource.Output) (hdepth : 0 < depth) :
    Nonempty (FinalFineIndex H G O) := by
  obtain ⟨path⟩ := Output.path_nonempty G.toDependentSource O
  obtain ⟨i, hi⟩ := activeFine_nonempty_of_depth_pos H hdepth
  exact ⟨(path, ⟨i, hi⟩)⟩

/-- At every stage, every literal hierarchy child in parent fiber `p`, after
the new scale motion and every earlier path choice, lies in the local-radius
thickening of the prefix-translated actual parent. -/
theorem stage_child_subset_translatedParentCthickening
    (O : G.toDependentSource.Output)
    (path : (Output.toComposition G.toDependentSource O).Path)
    (k : Fin depth) (p : Index (k.1 + 1))
    (i : Index k.1)
    (hi : i ∈ (H.step k.1 k.2).combinatorics.index.fiber p)
    (j : Fin (G.toDependentSource.repetitions k)) :
    (translateTube
        (translateTube ((H.effectiveFamily k.1).tubes i) (O.omega k j))
        (Output.prefixVector G.toDependentSource O path k)).carrier ⊆
      Metric.cthickening (H.effectiveRadius (k.1 + 1) : Real)
        (translateTube ((H.effectiveFamily (k.1 + 1)).tubes p)
          (Output.prefixVector G.toDependentSource O path k)).carrier := by
  let C := (H.step k.1 k.2).combinatorics
  have hi' : i ∈ C.index.fine ∧ C.index.parent i = p := by
    exact (C.index.mem_fiber i p).1 hi
  have hiRef : i ∈ (H.family k.1).refinement.refined := by
    rw [← C.fine_eq_refined]
    exact hi'.1
  have hparent := H.effective_carrier_subset_parent k.1 k.2 i hiRef
  have hpEq : (H.step k.1 k.2).parentIndex i = p := by
    simpa [AdjacentTubeStep.parentIndex, C] using hi'.2
  have hparent' :
      ((H.effectiveFamily k.1).tubes i).carrier ⊆
        ((H.effectiveFamily (k.1 + 1)).tubes p).carrier := by
    simpa [hpEq] using hparent
  exact commonPrefix_localTranslate_subset_parentCthickening
    ((H.effectiveFamily k.1).tubes i)
    ((H.effectiveFamily (k.1 + 1)).tubes p)
    (O.omega k j) (Output.prefixVector G.toDependentSource O path k)
    (H.effectiveRadius (k.1 + 1)) hparent' (O.vector_norm_le k j)

#print axioms commonPrefix_localTranslate_subset_parentCthickening
#print axioms finalFineIndex_card
#print axioms finalFineTube_carrier_subset_totalRadius
#print axioms finalFineIndex_nonempty
#print axioms stage_child_subset_translatedParentCthickening

end HierarchyRandomMotionGeometry

end
end FamilyStickyHierarchyTranslatedFamilyV1
