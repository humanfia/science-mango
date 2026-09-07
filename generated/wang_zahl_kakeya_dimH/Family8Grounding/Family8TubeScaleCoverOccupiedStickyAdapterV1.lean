import Family4GlobalExtremalUpstream
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped ENNReal NNReal

namespace Family8TubeScaleCoverOccupiedStickyAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A supplied tube-scale cover as an occupied sticky cover

`Family4GlobalExtremalUpstream.TubeScaleCover` is supplied cover data: it
contains coarse tubes, a parent map, and the required carrier containment,
but it deliberately does not assert that every coarse code is occupied.  A
`StickyScaleCover` additionally authenticates both active sets through its
uniform refinements and requires surjectivity onto the active coarse set.

This module supplies the exact finite seam.  The active coarse set is the
image of the supplied parent map.  There are two versions:

* if the supplied active set already is the fine family's authenticated
  refinement, the original fine index type is retained;
* without that equality, the active fine set is made into a literal subtype
  and the occupied coarse image is canonically reindexed by `Fin`.

No maximal-density cover is constructed here.  In particular, these
constructions preserve any genuine sibling merging present in the supplied
parent map, but do not prove that such a nonidentity parent map exists.
-/

universe u

variable {delta tau : NNReal} {iota : Type u}
  [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}

/-- Exactly the coarse codes hit by active fine indices. -/
def occupiedParents
    (C : @TubeScaleCover delta tau iota _ fine active) :
    Finset (Fin C.count) :=
  active.image C.parent

@[simp]
theorem mem_occupiedParents
    (C : @TubeScaleCover delta tau iota _ fine active)
    (k : Fin C.count) :
    k ∈ occupiedParents C ↔
      ∃ i, i ∈ active ∧ C.parent i = k := by
  simp [occupiedParents]

theorem occupiedParents_card_le_active
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (occupiedParents C).card ≤ active.card := by
  exact Finset.card_image_le

/-! ## Retaining the original fine index type -/

/-- A supplied cover whose active source is already the fine refinement is a
literal sticky cover.  Unused coarse codes remain in `Fin C.count`, but are
not active; this retains the supplied quantitative count exactly. -/
def ofTubeScaleCover
    [Fintype iota]
    (C : @TubeScaleCover delta tau iota _ fine active)
    (hactive : active = fine.refinement.refined) :
    StickyScaleCover fine tau where
  coarseCard := C.count
  coarse :=
    { tubes := C.tubes
      refinement := UniformRefinement.ofFinset (occupiedParents C) }
  activeFine := active
  activeCoarse := occupiedParents C
  parent := C.parent
  activeFine_eq_refined := hactive
  activeCoarse_eq_refined := rfl
  parent_mem := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  parent_surjective := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
    exact ⟨i, hi, hik⟩
  carrier_subset := C.carrier_subset

@[simp]
theorem ofTubeScaleCover_coarseCard
    [Fintype iota]
    (C : @TubeScaleCover delta tau iota _ fine active)
    (hactive : active = fine.refinement.refined) :
    (ofTubeScaleCover C hactive).coarseCard = C.count :=
  rfl

@[simp]
theorem ofTubeScaleCover_activeCoarse
    [Fintype iota]
    (C : @TubeScaleCover delta tau iota _ fine active)
    (hactive : active = fine.refinement.refined) :
    (ofTubeScaleCover C hactive).activeCoarse = occupiedParents C :=
  rfl

@[simp]
theorem ofTubeScaleCover_parent
    [Fintype iota]
    (C : @TubeScaleCover delta tau iota _ fine active)
    (hactive : active = fine.refinement.refined) (i : iota) :
    (ofTubeScaleCover C hactive).parent i = C.parent i :=
  rfl

@[simp]
theorem ofTubeScaleCover_coarse_tubes
    [Fintype iota]
    (C : @TubeScaleCover delta tau iota _ fine active)
    (hactive : active = fine.refinement.refined) (k : Fin C.count) :
    (ofTubeScaleCover C hactive).coarse.tubes k = C.tubes k :=
  rfl

/-! ## The unconditional active-subtype construction -/

/-- The supplied active source as a literal finite uniform family. -/
abbrev activeFineFamily
    (_C : @TubeScaleCover delta tau iota _ fine active) :
    UniformTubeFamily delta {i // i ∈ active} :=
  fine.restrictTo active

/-- Keep the supplied coarse cardinality while restricting the source to its
actual active subtype.  The active coarse refinement is precisely the
occupied image, so surjectivity is automatic and no unused code becomes an
active tube. -/
def activeSubtypeScaleCover
    (C : @TubeScaleCover delta tau iota _ fine active) :
    StickyScaleCover (activeFineFamily C) tau where
  coarseCard := C.count
  coarse :=
    { tubes := C.tubes
      refinement := UniformRefinement.ofFinset (occupiedParents C) }
  activeFine := Finset.univ
  activeCoarse := occupiedParents C
  parent := fun i => C.parent i.1
  activeFine_eq_refined := rfl
  activeCoarse_eq_refined := rfl
  parent_mem := by
    intro i _hi
    exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩
  parent_surjective := by
    intro k hk
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, hik⟩
  carrier_subset := by
    intro i _hi
    exact C.carrier_subset i.1 i.2

@[simp]
theorem activeSubtypeScaleCover_activeFine
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (activeSubtypeScaleCover C).activeFine = Finset.univ :=
  rfl

@[simp]
theorem activeSubtypeScaleCover_activeCoarse
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (activeSubtypeScaleCover C).activeCoarse = occupiedParents C :=
  rfl

@[simp]
theorem activeSubtypeScaleCover_parent
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : {i // i ∈ active}) :
    (activeSubtypeScaleCover C).parent i = C.parent i.1 :=
  rfl

/-! ## Canonically deleting unused coarse codes -/

/-- An occupied supplied parent code, retaining its proof of occupation. -/
abbrev OccupiedParent
    (C : @TubeScaleCover delta tau iota _ fine active) :=
  {k // k ∈ occupiedParents C}

/-- The canonical enumeration of occupied supplied parent codes. -/
def occupiedParentEquiv
    (C : @TubeScaleCover delta tau iota _ fine active) :
    OccupiedParent C ≃ Fin (occupiedParents C).card :=
  (occupiedParents C).equivFin

/-- Delete every unused supplied coarse code and canonically reindex the
occupied image.  The new source and target refinements are both literal
universes, while tube carriers and the supplied parent assignment are
preserved under the reindexing equivalence. -/
def compactActiveSubtypeScaleCover
    (C : @TubeScaleCover delta tau iota _ fine active) :
    StickyScaleCover (activeFineFamily C) tau := by
  classical
  let e := occupiedParentEquiv C
  let coarse : UniformTubeFamily tau (Fin (occupiedParents C).card) :=
    { tubes := fun q => C.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := (occupiedParents C).card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i => e ⟨C.parent i.1, by
        exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        let p : OccupiedParent C := e.symm q
        obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp p.2
        let ii : {i // i ∈ active} := ⟨i, hi⟩
        refine ⟨ii, Finset.mem_univ ii, ?_⟩
        change e ⟨C.parent i, by
          exact Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩ = q
        have heq :
            (⟨C.parent i, by
              exact Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩ :
              OccupiedParent C) = p := by
          apply Subtype.ext
          exact hip
        rw [heq, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource := C.carrier_subset i.1 i.2
        change (fine.tubes i.1).carrier ⊆
          (C.tubes
            (e.symm (e ⟨C.parent i.1, by
              exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)).1).carrier
        rw [e.symm_apply_apply]
        exact hsource }

@[simp]
theorem compactActiveSubtypeScaleCover_coarseCard
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (compactActiveSubtypeScaleCover C).coarseCard =
      (occupiedParents C).card :=
  rfl

@[simp]
theorem compactActiveSubtypeScaleCover_activeFine
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (compactActiveSubtypeScaleCover C).activeFine = Finset.univ :=
  rfl

@[simp]
theorem compactActiveSubtypeScaleCover_activeCoarse
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (compactActiveSubtypeScaleCover C).activeCoarse = Finset.univ :=
  rfl

theorem compactActiveSubtypeScaleCover_coarseCard_le_active
    (C : @TubeScaleCover delta tau iota _ fine active) :
    (compactActiveSubtypeScaleCover C).coarseCard ≤ active.card := by
  exact occupiedParents_card_le_active C

/-- Decoding the compact parent gives exactly the original supplied parent
code.  Hence no geometric or combinatorial parent information is lost. -/
theorem compactActiveSubtypeScaleCover_parent_decodes
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : {i // i ∈ active}) :
    (occupiedParentEquiv C).symm
        ((compactActiveSubtypeScaleCover C).parent i) =
      ⟨C.parent i.1, by
        exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩ := by
  exact (occupiedParentEquiv C).symm_apply_apply _

/-- The compact parent's tube is definitionally the supplied parent's tube
after undoing the canonical occupied-image enumeration. -/
theorem compactActiveSubtypeScaleCover_parent_tube
    (C : @TubeScaleCover delta tau iota _ fine active)
    (i : {i // i ∈ active}) :
    (compactActiveSubtypeScaleCover C).coarse.tubes
        ((compactActiveSubtypeScaleCover C).parent i) =
      C.tubes (C.parent i.1) := by
  change C.tubes
      ((occupiedParentEquiv C).symm
        ((occupiedParentEquiv C)
          ⟨C.parent i.1, by
            exact Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)).1 =
    C.tubes (C.parent i.1)
  rw [(occupiedParentEquiv C).symm_apply_apply]

#print axioms occupiedParents_card_le_active
#print axioms ofTubeScaleCover
#print axioms activeSubtypeScaleCover
#print axioms compactActiveSubtypeScaleCover
#print axioms compactActiveSubtypeScaleCover_parent_decodes
#print axioms compactActiveSubtypeScaleCover_parent_tube

end
end Family8TubeScaleCoverOccupiedStickyAdapterV1
