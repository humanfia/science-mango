import Submission.Kakeya.ConvexGeometry.Shading
import Submission.Kakeya.Uniformity.Refinement

namespace Submission.Kakeya.ConvexFactoring

/-!
# Finite index factorizations

This module records the finite combinatorial partition underlying a convex
factorization.  Every active fine index is assigned to an active coarse index,
and the resulting fibers support exact covering, summation, and cardinality
identities.
-/

/-- A finite active fine family assigned to a finite active coarse family. -/
structure IndexFactorization (ι κ : Type*) [DecidableEq ι] [DecidableEq κ] where
  fine : Finset ι
  coarse : Finset κ
  parent : ι → κ
  parent_mem : ∀ i ∈ fine, parent i ∈ coarse

namespace IndexFactorization

/-- The fine indices assigned to one coarse index. -/
def fiber {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : IndexFactorization ι κ) (k : κ) : Finset ι :=
  P.fine.filter fun i ↦ P.parent i = k

@[simp] theorem mem_fiber {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : IndexFactorization ι κ) (i : ι) (k : κ) :
    i ∈ P.fiber k ↔ i ∈ P.fine ∧ P.parent i = k := by
  simp [fiber]

theorem fiber_subset_fine {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : IndexFactorization ι κ) (k : κ) : P.fiber k ⊆ P.fine :=
  Finset.filter_subset _ _

/-- The fibers over the active coarse indices cover the fine index set. -/
theorem biUnion_fiber_eq_fine {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : IndexFactorization ι κ) :
    P.coarse.biUnion P.fiber = P.fine := by
  ext i
  constructor
  · intro hi
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact P.fiber_subset_fine k hik
  · intro hi
    exact Finset.mem_biUnion.mpr ⟨P.parent i, P.parent_mem i hi,
      P.mem_fiber i (P.parent i) |>.2 ⟨hi, rfl⟩⟩

/-- Fiberwise summation over the indexed partition. -/
theorem sum_fiberwise {ι κ M : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddCommMonoid M] (P : IndexFactorization ι κ) (w : ι → M) :
    (∑ i ∈ P.fine, w i) = ∑ k ∈ P.coarse, ∑ i ∈ P.fiber k, w i := by
  simpa [fiber] using
    (Finset.sum_fiberwise_of_maps_to
      (s := P.fine) (t := P.coarse) (g := P.parent) P.parent_mem w).symm

/-- Cardinalities of the fibers add to the cardinality of the fine set. -/
theorem card_eq_sum_card_fiber {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (P : IndexFactorization ι κ) :
    P.fine.card = ∑ k ∈ P.coarse, (P.fiber k).card := by
  simpa using P.sum_fiberwise (fun _ ↦ (1 : ℕ))

end IndexFactorization

end Submission.Kakeya.ConvexFactoring
