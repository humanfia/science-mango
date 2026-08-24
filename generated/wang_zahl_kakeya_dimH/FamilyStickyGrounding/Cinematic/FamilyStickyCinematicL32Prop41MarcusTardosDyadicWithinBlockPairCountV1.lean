import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Pairwise
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicWithinBlockPairCountV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1

/-!
# Ordered symbol pairs supported in one actual dyadic block

This is the finite diagonal support used in Marcus--Tardos Lemma 4.  It is
produced by the actual recursive blocks rather than supplied as a cardinality
estimate.  Nodup makes the block containing the first symbol unique, and
hence embeds every supported ordered pair into the disjoint sigma of the
blocks' off-diagonals.
-/

def SameDyadicOrderedPair
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (order : List symbol) (p : symbol × symbol) : Prop :=
  p.1 ≠ p.2 ∧ ∃ i : BlockIndex depth order,
    p.1 ∈ blockAt depth order i ∧ p.2 ∈ blockAt depth order i

noncomputable def sameDyadicOrderedPairs
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (order : List symbol) : Finset (symbol × symbol) := by
  classical
  exact Finset.univ.filter (SameDyadicOrderedPair depth order)

theorem mem_order_of_mem_blockAt
    {symbol : Type*} {depth : Nat} {order : List symbol}
    {x : symbol} {i : BlockIndex depth order}
    (hx : x ∈ blockAt depth order i) : x ∈ order := by
  have hxflat : x ∈ (dyadicBlocks depth order).flatten :=
    List.mem_flatten.mpr ⟨blockAt depth order i, blockAt_mem depth order i, hx⟩
  simpa using hxflat

noncomputable def samePairBlockIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} {order : List symbol} (horder : order.Nodup)
    (p : symbol × symbol) (hp : SameDyadicOrderedPair depth order p) :
    BlockIndex depth order :=
  blockIndexOf horder (mem_order_of_mem_blockAt hp.2.choose_spec.1)

theorem first_mem_samePairBlockIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} {order : List symbol} (horder : order.Nodup)
    (p : symbol × symbol) (hp : SameDyadicOrderedPair depth order p) :
    p.1 ∈ blockAt depth order (samePairBlockIndex horder p hp) := by
  exact mem_blockAt_blockIndexOf horder
    (mem_order_of_mem_blockAt hp.2.choose_spec.1)

theorem second_mem_samePairBlockIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} {order : List symbol} (horder : order.Nodup)
    (p : symbol × symbol) (hp : SameDyadicOrderedPair depth order p) :
    p.2 ∈ blockAt depth order (samePairBlockIndex horder p hp) := by
  let i := hp.2.choose
  have hfirst : p.1 ∈ blockAt depth order i := hp.2.choose_spec.1
  have hi : samePairBlockIndex horder p hp = i :=
    blockIndexOf_eq_of_mem horder
      (mem_order_of_mem_blockAt hfirst) i hfirst
  rw [hi]
  exact hp.2.choose_spec.2

abbrev BlockOrderedPair
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (order : List symbol) (i : BlockIndex depth order) :=
  {p : symbol × symbol //
    p ∈ (blockAt depth order i).toFinset.offDiag}

noncomputable def samePairEmbedding
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} {order : List symbol} (horder : order.Nodup) :
    ↑(sameDyadicOrderedPairs depth order) →
      Sigma (BlockOrderedPair depth order) := by
  intro p
  have hp : SameDyadicOrderedPair depth order p.1 := by
    simpa [sameDyadicOrderedPairs] using p.2
  let i := samePairBlockIndex horder p.1 hp
  exact ⟨i, ⟨p.1, by
    simp only [Finset.mem_offDiag, List.mem_toFinset]
    exact ⟨first_mem_samePairBlockIndex horder p.1 hp,
      second_mem_samePairBlockIndex horder p.1 hp, hp.1⟩⟩⟩

theorem samePairEmbedding_injective
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} {order : List symbol} (horder : order.Nodup) :
    Function.Injective
      (samePairEmbedding (depth := depth) horder) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun z : Sigma (BlockOrderedPair depth order) =>
    (z.2 : symbol × symbol)) hpq

/-- The supported ordered symbol pairs are bounded by the literal sum of
the actual blocks' ordered-pair counts. -/
theorem card_sameDyadicOrderedPairs_le_sum_block_orderedPairs
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (order : List symbol) (horder : order.Nodup) :
    (sameDyadicOrderedPairs depth order).card ≤
      ∑ i : BlockIndex depth order,
        (blockAt depth order i).length *
          ((blockAt depth order i).length - 1) := by
  have hcard := Fintype.card_le_of_injective
    (samePairEmbedding (depth := depth) horder)
    (samePairEmbedding_injective (depth := depth) horder)
  rw [Fintype.card_sigma] at hcard
  simpa [Finset.offDiag_card, Nat.mul_sub_left_distrib,
    List.toFinset_card_of_nodup (blockAt_nodup horder _)] using hcard

#print axioms SameDyadicOrderedPair
#print axioms sameDyadicOrderedPairs
#print axioms mem_order_of_mem_blockAt
#print axioms samePairBlockIndex
#print axioms first_mem_samePairBlockIndex
#print axioms second_mem_samePairBlockIndex
#print axioms samePairEmbedding
#print axioms samePairEmbedding_injective
#print axioms card_sameDyadicOrderedPairs_le_sum_block_orderedPairs

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicWithinBlockPairCountV1
