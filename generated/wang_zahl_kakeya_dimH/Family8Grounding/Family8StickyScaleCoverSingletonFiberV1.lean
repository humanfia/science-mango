import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

/-!
# One active Sticky parent on a literal fibre

The middle-scale object selected by the exact assembly is one actual parent
fibre, not the full collection of parents.  This module restricts the fine
family to that literal fibre and equips it with a one-parent Sticky cover.
Consequently every active-parent cardinality appearing in a fibre-local
Equation (45) argument is exactly one; no identification with an unrelated
greedy or logarithmic selection is used.
-/

open Set
open scoped ENNReal NNReal

namespace Family8StickyScaleCoverSingletonFiberV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual fine family in the displayed parent fibre. -/
noncomputable abbrev singletonFiberFamily
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    UniformTubeFamily delta {i // i ∈ S.fiber k} :=
  fine.restrictTo (S.fiber k)

/-- The same displayed parent tube, reindexed by `Fin 1`. -/
noncomputable def singletonParentFamily
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    UniformTubeFamily rho (Fin 1) where
  tubes := fun _ ↦ S.coarse.tubes k
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem singletonParentFamily_tubes
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) (q : Fin 1) :
    (singletonParentFamily S k).tubes q = S.coarse.tubes k := by
  rfl

/-- A literal one-parent Sticky cover of one nonempty active fibre. -/
noncomputable def singletonFiberScaleCover
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    StickyScaleCover (singletonFiberFamily S k) rho := by
  classical
  refine
    { coarseCard := 1
      coarse := singletonParentFamily S k
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun _ ↦ 0
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := ?_
      carrier_subset := ?_ }
  · intro q _hq
    obtain ⟨i, hi, hiparent⟩ := S.parent_surjective k hk
    let j : {i // i ∈ S.fiber k} :=
      ⟨i, S.mem_fiber i k |>.2 ⟨hi, hiparent⟩⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    exact Subsingleton.elim _ _
  · intro i _hi
    change (fine.tubes i.1).carrier ⊆ (S.coarse.tubes k).carrier
    exact S.fiber_carrier_subset_parent k i

@[simp] theorem singletonFiberScaleCover_activeFine
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    (singletonFiberScaleCover S k hk).activeFine = Finset.univ := by
  rfl

@[simp] theorem singletonFiberScaleCover_activeCoarse
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    (singletonFiberScaleCover S k hk).activeCoarse = Finset.univ := by
  rfl

@[simp] theorem singletonFiberScaleCover_parent
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) (i : {i // i ∈ S.fiber k}) :
    (singletonFiberScaleCover S k hk).parent i =
      (⟨0, by simp [singletonFiberScaleCover]⟩ :
        Fin (singletonFiberScaleCover S k hk).coarseCard) := by
  rfl

@[simp] theorem singletonFiberScaleCover_fiber_zero
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    (singletonFiberScaleCover S k hk).fiber
        (⟨0, by simp [singletonFiberScaleCover]⟩ :
          Fin (singletonFiberScaleCover S k hk).coarseCard) = Finset.univ := by
  classical
  ext i
  simp [StickyScaleCover.fiber]

/-- The active-parent type used by fibre-local Eq45 has cardinality one. -/
@[simp] theorem singletonFiberScaleCover_activeParent_card
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    Fintype.card
        {q // q ∈ (singletonFiberScaleCover S k hk).activeCoarse} = 1 := by
  classical
  change Fintype.card {q : Fin 1 // q ∈ (Finset.univ : Finset (Fin 1))} = 1
  simp

/-- Restriction retained the literal source tube at every fibre index. -/
@[simp] theorem singletonFiberFamily_tubes
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (i : {i // i ∈ S.fiber k}) :
    (singletonFiberFamily S k).tubes i = fine.tubes i.1 := by
  rfl

#print axioms singletonParentFamily
#print axioms singletonFiberScaleCover
#print axioms singletonFiberScaleCover_fiber_zero
#print axioms singletonFiberScaleCover_activeParent_card
#print axioms singletonFiberFamily_tubes

end
end Family8StickyScaleCoverSingletonFiberV1
