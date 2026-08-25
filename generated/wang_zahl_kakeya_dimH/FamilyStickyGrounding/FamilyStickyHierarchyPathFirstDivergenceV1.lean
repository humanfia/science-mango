import FamilyStickyGrounding.FamilyStickyHierarchyJointRandomMotionCertificateV1
import FamilyStickyGrounding.FamilyStickyRandomLocalExactCarrierDedupV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyPathFirstDivergenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyRandomLocalExactCarrierDedupV1
open FamilyStickyRandomModelTubeCollisionGridV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# First divergence and common prefixes for hierarchy motion paths

This is the callback-free combinatorial producer needed before any global
collision refinement.  Two unequal dependent paths have a canonical least
layer where their choices differ.  Every earlier choice, and hence the
actual vector prefix used by the hierarchy certificate, agrees literally.

For a final occurrence we also expose its actual hierarchy child and parent
at every layer and package the corresponding occurrence in the B8 parent
collision grid.

The producer deliberately stops before one geometric statement which is not
a consequence of the current interfaces.  To route equality of two fully
composed final carriers into the local B8 collision class at their first
divergence `k`, one still has to prove simultaneously that their level-`k`
children have the same level-`k+1` parent and that, after removing the common
prefix, one locally translated child carrier is contained in the literal
`100`-tube of the other.  Later path coordinates may differ and cancel, so
final carrier equality alone cannot be rewritten into this local containment.
-/

section DependentPaths

variable {depth : Nat} {repetitions : Fin depth -> Nat}

/-- A path choosing one repetition coordinate at every finite layer. -/
abbrev ChoicePath := forall k : Fin depth, Fin (repetitions k)

/-- The finite set of layers where two dependent paths differ. -/
def differingLayers (a b : ChoicePath (repetitions := repetitions)) :
    Finset (Fin depth) :=
  Finset.univ.filter fun k => a k ≠ b k

theorem differingLayers_nonempty
    {a b : ChoicePath (repetitions := repetitions)} (hab : a ≠ b) :
    (differingLayers a b).Nonempty := by
  have hexists : exists k, a k ≠ b k := by
    by_contra h
    push Not at h
    exact hab (funext h)
  obtain ⟨k, hk⟩ := hexists
  exact ⟨k, by simp [differingLayers, hk]⟩

/-- Canonical least layer where two unequal paths differ. -/
def firstDivergenceLayer
    (a b : ChoicePath (repetitions := repetitions)) (hab : a ≠ b) :
    Fin depth :=
  (differingLayers a b).min' (differingLayers_nonempty hab)

theorem firstDivergenceLayer_mem
    (a b : ChoicePath (repetitions := repetitions)) (hab : a ≠ b) :
    firstDivergenceLayer a b hab ∈ differingLayers a b :=
  Finset.min'_mem _ _

theorem firstDivergenceLayer_choice_ne
    (a b : ChoicePath (repetitions := repetitions)) (hab : a ≠ b) :
    a (firstDivergenceLayer a b hab) ≠
      b (firstDivergenceLayer a b hab) := by
  simpa [differingLayers] using firstDivergenceLayer_mem a b hab

theorem firstDivergenceLayer_eq_before
    (a b : ChoicePath (repetitions := repetitions)) (hab : a ≠ b)
    (i : Fin depth) (hi : i < firstDivergenceLayer a b hab) :
    a i = b i := by
  by_contra hne
  have himem : i ∈ differingLayers a b := by
    simp [differingLayers, hne]
  have hle := Finset.min'_le (differingLayers a b) i himem
  exact (not_le_of_gt hi) hle

/-- Complete, proof-carrying first-divergence output. -/
structure FirstDivergenceCertificate
    (a b : ChoicePath (repetitions := repetitions)) where
  layer : Fin depth
  choice_ne : a layer ≠ b layer
  prefix_eq : forall i, i < layer -> a i = b i

def firstDivergenceCertificate
    (a b : ChoicePath (repetitions := repetitions)) (hab : a ≠ b) :
    FirstDivergenceCertificate a b where
  layer := firstDivergenceLayer a b hab
  choice_ne := firstDivergenceLayer_choice_ne a b hab
  prefix_eq := firstDivergenceLayer_eq_before a b hab

#print axioms differingLayers_nonempty
#print axioms firstDivergenceLayer_choice_ne
#print axioms firstDivergenceLayer_eq_before
#print axioms firstDivergenceCertificate

end DependentPaths

section HierarchyPaths

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- First divergence specialized to the actual joint hierarchy path. -/
def hierarchyFirstDivergenceLayer
    (a b : C.Path) (hab : a ≠ b) : Fin depth :=
  firstDivergenceLayer a b hab

theorem hierarchyFirstDivergence_choice_ne
    (a b : C.Path) (hab : a ≠ b) :
    a (hierarchyFirstDivergenceLayer C a b hab) ≠
      b (hierarchyFirstDivergenceLayer C a b hab) :=
  firstDivergenceLayer_choice_ne a b hab

theorem hierarchyFirstDivergence_eq_before
    (a b : C.Path) (hab : a ≠ b)
    (i : Fin depth) (hi : i < hierarchyFirstDivergenceLayer C a b hab) :
    a i = b i :=
  firstDivergenceLayer_eq_before a b hab i hi

/-- The literal ambient common prefix agrees at the first divergence. -/
theorem prefixVector_eq_at_hierarchyFirstDivergence
    (a b : C.Path) (hab : a ≠ b) :
    C.output.prefixVector a (hierarchyFirstDivergenceLayer C a b hab) =
      C.output.prefixVector b (hierarchyFirstDivergenceLayer C a b hab) := by
  unfold FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.prefixVector
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < hierarchyFirstDivergenceLayer C a b hab :=
    (Finset.mem_filter.mp hi).2
  rw [hierarchyFirstDivergence_eq_before C a b hab i hi']

/-- Actual hierarchy child descended from a final fine source at layer `k`. -/
def layerChild (a : C.FinalIndex) (k : Fin depth) : Index k.1 :=
  (Nat.zero_add k.1) ▸ H.ancestor 0 k.1 (by omega) a.2.1

/-- Its literal parent at the next hierarchy layer. -/
def layerParent (a : C.FinalIndex) (k : Fin depth) : Index (k.1 + 1) :=
  (H.step k.1 k.2).parentIndex (layerChild C a k)

theorem layerChild_mem_refined (a : C.FinalIndex) (k : Fin depth) :
    layerChild C a k ∈ (H.family k.1).refinement.refined := by
  change ((Nat.zero_add k.1) ▸ H.ancestor 0 k.1 (by omega) a.2.1) ∈
    (H.family k.1).refinement.refined
  exact H.mem_transport (Nat.zero_add k.1)
    (H.ancestor_mem 0 k.1 (by omega) a.2.1 a.2.2)

theorem layerParent_mem_refined (a : C.FinalIndex) (k : Fin depth) :
    layerParent C a k ∈ (H.family (k.1 + 1)).refinement.refined := by
  rw [← (H.step k.1 k.2).combinatorics.coarse_eq_refined]
  apply (H.step k.1 k.2).parentIndex_mem
  rw [(H.step k.1 k.2).combinatorics.fine_eq_refined]
  exact layerChild_mem_refined C a k

theorem layerChild_mem_parentFiber (a : C.FinalIndex) (k : Fin depth) :
    layerChild C a k ∈
      (H.step k.1 k.2).combinatorics.index.fiber (layerParent C a k) := by
  apply ((H.step k.1 k.2).combinatorics.index.mem_fiber
    (layerChild C a k) (layerParent C a k)).2
  refine ⟨?_, ?_⟩
  · rw [(H.step k.1 k.2).combinatorics.fine_eq_refined]
    exact layerChild_mem_refined C a k
  · rfl

theorem layerParent_mem_activeParents (a : C.FinalIndex) (k : Fin depth) :
    layerParent C a k ∈ (G.toDependentSource.layer k).activeParents := by
  change layerParent C a k ∈
    (H.step k.1 k.2).combinatorics.index.coarse
  rw [(H.step k.1 k.2).combinatorics.coarse_eq_refined]
  exact layerParent_mem_refined C a k

/-- The final occurrence viewed in the exact local B8 collision grid at one
hierarchy layer. -/
def layerLocalOccurrence (a : C.FinalIndex) (k : Fin depth) :
    LocalOccurrence
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate (layerParent C a k))
      (repetitions G.toDependentSource k) :=
  ⟨a.1 k, ⟨layerChild C a k, by
    simpa [parentPackingGrid,
      HierarchyRandomMotionGeometry.toDependentSource,
      hierarchyLayer,
      AllParentLayerData.parentSeedGrid,
      FamilyStickyActualTubeTestDataV1.ActualTubeTestData.seedGrid] using
      layerChild_mem_parentFiber C a k⟩⟩

/-- At first divergence the two actual B8 local repetition coordinates are
different.  No injectivity of the chosen vectors is asserted. -/
theorem layerLocalOccurrence_choice_ne_at_firstDivergence
    (a b : C.FinalIndex) (hab : a.1 ≠ b.1) :
    (layerLocalOccurrence C a
      (hierarchyFirstDivergenceLayer C a.1 b.1 hab)).1 ≠
    (layerLocalOccurrence C b
      (hierarchyFirstDivergenceLayer C a.1 b.1 hab)).1 :=
  hierarchyFirstDivergence_choice_ne C a.1 b.1 hab

#print axioms prefixVector_eq_at_hierarchyFirstDivergence
#print axioms layerChild_mem_parentFiber
#print axioms layerParent_mem_activeParents
#print axioms layerLocalOccurrence_choice_ne_at_firstDivergence

/-- View a final occurrence in a specified parent collision grid once its
actual layer child is certified to lie in that parent fibre. -/
def layerLocalOccurrenceInParent
    (a : C.FinalIndex) (k : Fin depth) (p : Index (k.1 + 1))
    (ha : layerChild C a k ∈
      (H.step k.1 k.2).combinatorics.index.fiber p) :
    LocalOccurrence
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate p)
      (repetitions G.toDependentSource k) :=
  ⟨a.1 k, ⟨layerChild C a k, by
    simpa [parentPackingGrid,
      HierarchyRandomMotionGeometry.toDependentSource,
      hierarchyLayer,
      AllParentLayerData.parentSeedGrid,
      FamilyStickyActualTubeTestDataV1.ActualTubeTestData.seedGrid] using ha⟩⟩

/-- The direct geometric output still missing from the present hierarchy
interfaces.  It is a target proposition, not a field accepted by any
producer in this module.

It says that exact equality of two fully composed final carriers with
different paths localizes at their canonical first divergence: the two
actual layer children have one common parent, and after the already proved
common prefix is removed, the second local translate lies in the first
local translate's literal `100`-tube. -/
def FirstDivergenceCollisionLocalizationTarget : Prop :=
  forall (a b : C.FinalIndex) (hab : a.1 ≠ b.1),
    (C.finalTube a).carrier = (C.finalTube b).carrier ->
      let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
      exists p : Index (k.1 + 1),
        layerChild C a k ∈
            (H.step k.1 k.2).combinatorics.index.fiber p ∧
          layerChild C b k ∈
            (H.step k.1 k.2).combinatorics.index.fiber p ∧
          (translateTube ((H.effectiveFamily k.1).tubes (layerChild C b k))
              (C.output.omega k (b.1 k))).carrier ⊆
            (hundredTube
              (translateTube
                ((H.effectiveFamily k.1).tubes (layerChild C a k))
                (C.output.omega k (a.1 k)))).carrier

/-- Once the exact geometric target has produced its common parent and
local containment, routing into the already counted B8 collision class is
purely definitional. -/
theorem layerChild_mem_candidateCollisionFinset_of_localContainment
    (a b : C.FinalIndex) (k : Fin depth) (p : Index (k.1 + 1))
    (ha : layerChild C a k ∈
      (H.step k.1 k.2).combinatorics.index.fiber p)
    (hb : layerChild C b k ∈
      (H.step k.1 k.2).combinatorics.index.fiber p)
    (hcontain :
      (translateTube ((H.effectiveFamily k.1).tubes (layerChild C b k))
          (C.output.omega k (b.1 k))).carrier ⊆
        (hundredTube
          (translateTube ((H.effectiveFamily k.1).tubes (layerChild C a k))
            (C.output.omega k (a.1 k)))).carrier) :
    layerChild C b k ∈
      candidateCollisionFinset
        (parentPackingGrid (G.toDependentSource.layer k)
          (C.output.layerOutput k).certificate p)
        (occurrenceCandidate
          (parentPackingGrid (G.toDependentSource.layer k)
            (C.output.layerOutput k).certificate p)
          (C.output.layerOutput k).omega
          (layerLocalOccurrenceInParent C a k p ha))
        ((C.output.layerOutput k).omega (b.1 k)) := by
  apply (mem_candidateCollisionFinset
    (parentPackingGrid (G.toDependentSource.layer k)
      (C.output.layerOutput k).certificate p)
    (occurrenceCandidate
      (parentPackingGrid (G.toDependentSource.layer k)
        (C.output.layerOutput k).certificate p)
      (C.output.layerOutput k).omega
      (layerLocalOccurrenceInParent C a k p ha))
    ((C.output.layerOutput k).omega (b.1 k))
    (layerChild C b k)).2
  refine ⟨?_, ?_⟩
  · simpa [parentPackingGrid,
      HierarchyRandomMotionGeometry.toDependentSource,
      hierarchyLayer,
      AllParentLayerData.parentSeedGrid,
      FamilyStickyActualTubeTestDataV1.ActualTubeTestData.seedGrid] using hb
  · simpa [occurrenceCandidate, modelCandidateTube,
      layerLocalOccurrenceInParent, parentPackingGrid,
      HierarchyRandomMotionGeometry.toDependentSource,
      hierarchyLayer,
      AllParentLayerData.parentSeedGrid,
      FamilyStickyActualTubeTestDataV1.ActualTubeTestData.seedGrid,
      FamilyStickyHierarchyRandomMotionAdapterV1.BoxCertifiedTestFamily.attachHierarchyFiber,
      FamilyStickySharedTranslationPackingExistenceV1.ActualTubeTranslationGrid.ofMotionBallPackingCertificate,
      FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.omega]
      using hcontain

#print axioms layerChild_mem_candidateCollisionFinset_of_localContainment
#print axioms FirstDivergenceCollisionLocalizationTarget

end HierarchyPaths

end

end FamilyStickyHierarchyPathFirstDivergenceV1
