import Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
import Mathlib.Tactic

/-!
# Same-q count bridge for an arbitrary occurrence set

This file isolates the counting argument from every canonical Proposition 5.1
selection.  An arbitrary finite set of greedy occurrences is enough: if one
fixed occurrence fibre is at most twice every fibre in the set, pairwise
disjointness and containment in the active family pay the product of the set
cardinality with that fixed fibre cardinality.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace Family8ArbitraryOccurrenceSameQCardBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- An arbitrary same-q fibre-uniform occurrence set has the expected
factor-two product-count bound.  Membership of `q` is retained as an explicit
same-object certificate, although the counting calculation itself only needs
the stated uniformity hypothesis. -/
theorem arbitraryOccurrence_card_mul_sameQ_fiberCard_le_two_mul_active
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (q : Fin (blocks F P).length) (_hq : q ∈ R)
    (huniform : ∀ k, k ∈ R →
      (((blockAt F P q).fiber.card : Nat) : ENNReal) <=
        2 * (((blockAt F P k).fiber.card : Nat) : ENNReal)) :
    R.card * (blockAt F P q).fiber.card <= 2 * active.card := by
  have huniformNat : ∀ k, k ∈ R →
      (blockAt F P q).fiber.card <=
        2 * (blockAt F P k).fiber.card := by
    intro k hk
    exact_mod_cast huniform k hk
  have hdisjoint := blockAt_fibers_pairwiseDisjoint F P R
  have hunionSubset :
      R.biUnion (fun k => (blockAt F P k).fiber) ⊆ active := by
    intro i hi
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
    exact blockAt_fiber_subset_active F P k hik
  calc
    R.card * (blockAt F P q).fiber.card =
        ∑ k ∈ R, (blockAt F P q).fiber.card := by simp
    _ <= ∑ k ∈ R, 2 * (blockAt F P k).fiber.card :=
      Finset.sum_le_sum fun k hk => huniformNat k hk
    _ = 2 * ∑ k ∈ R, (blockAt F P k).fiber.card := by
      rw [Finset.mul_sum]
    _ = 2 *
        (R.biUnion (fun k => (blockAt F P k).fiber)).card := by
      rw [Finset.card_biUnion hdisjoint]
    _ <= 2 * active.card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hunionSubset)

#print axioms
  arbitraryOccurrence_card_mul_sameQ_fiberCard_le_two_mul_active

end

end Family8ArbitraryOccurrenceSameQCardBridgeV1
