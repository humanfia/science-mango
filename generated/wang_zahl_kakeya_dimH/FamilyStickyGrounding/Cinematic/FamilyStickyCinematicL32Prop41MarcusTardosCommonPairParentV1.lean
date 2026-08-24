import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceParentV1
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceParentV1

/-! # Binary parent map on actual filtered common-block pair indices -/

abbrev CommonPairIndex
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :=
  Fin (commonBlocks depth A B).length ×
    Fin (commonBlocks depth B A).length

def commonParentIndex
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (i : Fin (commonBlocks (depth + 1) A B).length) :
    Fin (commonBlocks depth A B).length :=
  ⟨i.1 / 2, by
    have hi : i.1 < 2 ^ (depth + 1) := by simpa using i.2
    have htarget : (commonBlocks depth A B).length = 2 ^ depth :=
      length_commonBlocks depth A B
    rw [htarget]
    have hi' : i.1 < 2 ^ depth * 2 := by
      simpa [pow_succ] using hi
    omega⟩

def commonPairParent
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (ij : CommonPairIndex (depth + 1) A B) :
    CommonPairIndex depth A B :=
  (commonParentIndex A B ij.1, commonParentIndex B A ij.2)

def binaryResidue (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt _ (by omega)⟩

def commonPairParentFiberEmbedding
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (parent : CommonPairIndex depth A B) :
    {child : CommonPairIndex (depth + 1) A B //
      commonPairParent A B child = parent} ↪ Fin 2 × Fin 2 where
  toFun child :=
    (binaryResidue child.1.1.1, binaryResidue child.1.2.1)
  inj' := by
    intro a b hres
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have ha := congrArg (fun p => p.1.1) a.2
      have hb := congrArg (fun p => p.1.1) b.2
      have hr := congrArg (fun p => p.1.1) hres
      simp only [commonPairParent, commonParentIndex] at ha hb
      simp only [binaryResidue] at hr
      omega
    · apply Fin.ext
      have ha := congrArg (fun p => p.2.1) a.2
      have hb := congrArg (fun p => p.2.1) b.2
      have hr := congrArg (fun p => p.2.1) hres
      simp only [commonPairParent, commonParentIndex] at ha hb
      simp only [binaryResidue] at hr
      omega

theorem commonPairParent_fiber_card_le_four
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (parent : CommonPairIndex depth A B) :
    ((Finset.univ : Finset (CommonPairIndex (depth + 1) A B)).filter
      fun child => commonPairParent A B child = parent).card ≤ 4 := by
  classical
  let fiber :=
    (Finset.univ : Finset (CommonPairIndex (depth + 1) A B)).filter
      fun child => commonPairParent A B child = parent
  have hinj : Function.Injective
      (fun child : {x // x ∈ fiber} =>
        commonPairParentFiberEmbedding A B parent
          ⟨child.1, (Finset.mem_filter.mp child.2).2⟩) := by
    intro a b hab
    apply Subtype.ext
    have hsub := (commonPairParentFiberEmbedding A B parent).injective hab
    exact congrArg
      (fun z : {child : CommonPairIndex (depth + 1) A B //
        commonPairParent A B child = parent} => z.1) hsub
  have hcard := Fintype.card_le_of_injective
    (f := fun child : {x // x ∈ fiber} =>
      commonPairParentFiberEmbedding A B parent
        ⟨child.1, (Finset.mem_filter.mp child.2).2⟩) hinj
  change fiber.card ≤ 4
  simpa [Fintype.card_prod] using hcard

theorem commonPairParent_occurrence
    {symbol : Type*} [DecidableEq symbol]
    {depth : Nat} (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support) :
    commonPairParent A B
        (occurrenceCommonPairIndex (depth + 1) A B x hx) =
      occurrenceCommonPairIndex depth A B x hx := by
  apply Prod.ext
  · apply Fin.ext
    exact occurrenceCommonIndex_succ_div_two A B x
      (Finset.mem_inter.mp hx).1
  · apply Fin.ext
    exact occurrenceCommonIndex_succ_div_two B A x
      (Finset.mem_inter.mp hx).2

#print axioms CommonPairIndex
#print axioms commonParentIndex
#print axioms commonPairParent
#print axioms commonPairParentFiberEmbedding
#print axioms commonPairParent_fiber_card_le_four
#print axioms commonPairParent_occurrence

end FamilyStickyCinematicL32Prop41MarcusTardosCommonPairParentV1
