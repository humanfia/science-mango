import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSingularPairCardV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosSingularPairCardV1

/-!
# Dyadic instance of the Marcus--Tardos singular-pair bound

The position-indexed common blocks are the literal dyadic blocks filtered to
the other cyclic support.  For cyclically intersection-reverse sequences,
at every depth at most one ordered pair of common blocks is singular.
-/

noncomputable def dyadicSingularPairs
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    Finset (Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) :=
  singularPairs (commonBlocks depth A B) (commonBlocks depth B A)
    (flatten_commonBlocks_nodup depth A B)
    (flatten_commonBlocks_nodup depth B A)

@[simp]
theorem mem_dyadicSingularPairs
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) :
    ij ∈ dyadicSingularPairs depth A B ↔
      FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1.SingularPair
        (commonBlocks depth A B) (commonBlocks depth B A)
        (flatten_commonBlocks_nodup depth A B)
        (flatten_commonBlocks_nodup depth B A) ij := by
  classical
  simp [dyadicSingularPairs]

theorem dyadicSingularPairs_card_le_one
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B) :
    (dyadicSingularPairs depth A B).card ≤ 1 := by
  classical
  rcases exists_commonOrder_split A B hreverse with
    ⟨u, v, hsplitA, hsplitB⟩
  have hflatA : (commonBlocks depth A B).flatten = u ++ v := by
    simpa using hsplitA
  have hflatB : (commonBlocks depth B A).flatten =
      u.reverse ++ v.reverse := by
    simpa using hsplitB
  simpa [dyadicSingularPairs] using
    singularPairs_card_le_one hflatA hflatB
      (flatten_commonBlocks_nodup depth A B)
      (flatten_commonBlocks_nodup depth B A)

#print axioms dyadicSingularPairs
#print axioms mem_dyadicSingularPairs
#print axioms dyadicSingularPairs_card_le_one

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1
