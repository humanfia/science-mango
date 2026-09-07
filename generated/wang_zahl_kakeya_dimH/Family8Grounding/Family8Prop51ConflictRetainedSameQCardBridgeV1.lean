import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Mathlib.Tactic

/-!
# Same-q card bridge after conflict retention of the Prop. 5.1 bucket

An arbitrary downstream conflict selection `R` may retain only a subset of
the canonical Proposition 5.1 occurrence bucket.  Fibre-card dyadic
uniformity therefore still compares the fibre at one fixed retained
occurrence `q` with every other retained fibre.  Since greedy occurrence
fibres are pairwise disjoint and all lie in the original active fine set,
their total cardinality pays the product

`R.card * (blockAt F P q).fiber.card`

with the single factor two already present in the Prop. 5.1 bucket.

No conflict degree, global cardinality budget, or new occurrence selection is
used here.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace Family8Prop51ConflictRetainedSameQCardBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8Prop51SelectedOccurrenceSourceFrostmanV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- A fixed occurrence retained after any downstream conflict selection has
the weakest product-count bound inherited from the canonical Prop. 5.1
factor-two fibre bucket.  The occurrence `q` and the retained set `R` are
inputs; nothing is reselected. -/
theorem conflictRetained_card_mul_sameQ_fiberCard_le_two_mul_active
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (base : ENNReal) (M : Nat)
    (R : Finset (Fin (blocks F P).length))
    (hRsubset : R ⊆ prop51SelectedOccurrences P Y base M)
    (q : Fin (blocks F P).length) (hq : q ∈ R) :
    R.card * (blockAt F P q).fiber.card ≤ 2 * active.card := by
  have hqSelected : q ∈ prop51SelectedOccurrences P Y base M :=
    hRsubset hq
  have huniform : ∀ k ∈ R,
      (blockAt F P q).fiber.card ≤
        2 * (blockAt F P k).fiber.card := by
    intro k hk
    have h := prop51SelectedOccurrences_fiberCard_dyadicUniform
      P Y base M q hqSelected k (hRsubset hk)
    exact_mod_cast h
  have hdisjoint := blockAt_fibers_pairwiseDisjoint F P R
  have hunionSubset :
      R.biUnion (fun k => (blockAt F P k).fiber) ⊆ active := by
    intro i hi
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact blockAt_fiber_subset_active F P k hik
  calc
    R.card * (blockAt F P q).fiber.card =
        ∑ k ∈ R, (blockAt F P q).fiber.card := by simp
    _ ≤ ∑ k ∈ R, 2 * (blockAt F P k).fiber.card :=
      Finset.sum_le_sum fun k hk => huniform k hk
    _ = 2 * ∑ k ∈ R, (blockAt F P k).fiber.card := by
      rw [Finset.mul_sum]
    _ = 2 *
        (R.biUnion (fun k => (blockAt F P k).fiber)).card := by
      rw [Finset.card_biUnion hdisjoint]
    _ ≤ 2 * active.card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hunionSubset)

#print axioms
  conflictRetained_card_mul_sameQ_fiberCard_le_two_mul_active

end
end Family8Prop51ConflictRetainedSameQCardBridgeV1
