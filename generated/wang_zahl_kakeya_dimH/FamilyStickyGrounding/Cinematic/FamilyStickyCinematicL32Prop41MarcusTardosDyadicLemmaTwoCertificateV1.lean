import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicSingularPairV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoDataV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicPairLengthTotalV1
open FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1

/-!
# Complete finite per-depth Marcus--Tardos Lemma 2 certificate

The certificate exposes the actual cut, the unique-singular-pair bound, and
the subtraction-free summed `Q_st` inequality.  No asymptotic sequence-length
estimate is assumed.
-/

def dyadicPairSingular
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length) : Prop :=
  SingularPair (commonBlocks depth A B) (commonBlocks depth B A)
    (flatten_commonBlocks_nodup depth A B)
    (flatten_commonBlocks_nodup depth B A) ij

structure DyadicLemmaTwoCertificate
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) where
  left : List symbol
  right : List symbol
  firstSplit : (commonBlocks depth A B).flatten = left ++ right
  secondSplit : (commonBlocks depth B A).flatten =
    left.reverse ++ right.reverse
  singularCard : (dyadicSingularPairs depth A B).card ≤ 1
  qSumBound :
    (∑ ij : Fin (commonBlocks depth A B).length ×
      Fin (commonBlocks depth B A).length,
        dyadicPairQ depth A B left right ij) +
      regularSquareMass (dyadicPairSingular depth A B)
        (fun ij => (dyadicPairLength depth A B ij : Real)) ≤
      ((A.commonOrder B).length : Real)

theorem exists_dyadicLemmaTwoCertificate
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B) :
    Nonempty (DyadicLemmaTwoCertificate depth A B) := by
  classical
  rcases exists_commonOrder_split A B hreverse with
    ⟨u, v, hsplitA, hsplitB⟩
  have hflatA : (commonBlocks depth A B).flatten = u ++ v := by
    simpa using hsplitA
  have hflatB : (commonBlocks depth B A).flatten =
      u.reverse ++ v.reverse := by
    simpa using hsplitB
  have hsum := sum_q_add_regularSquareMass_le_sum_length
    (fun ij => dyadicPairQ depth A B u v ij)
    (fun ij => (dyadicPairLength depth A B ij : Real))
    (dyadicPairSingular depth A B)
    (fun ij _ => dyadicPairQ_le_length depth A B hflatA ij)
    (fun ij hregular =>
      dyadicPairQ_eq_regular_score depth A B hflatA hflatB ij hregular)
  rw [sum_dyadicPairLength_real_eq_commonOrder_length] at hsum
  exact ⟨{
    left := u
    right := v
    firstSplit := hflatA
    secondSplit := hflatB
    singularCard := dyadicSingularPairs_card_le_one depth A B hreverse
    qSumBound := hsum
  }⟩

#print axioms dyadicPairSingular
#print axioms DyadicLemmaTwoCertificate
#print axioms exists_dyadicLemmaTwoCertificate

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1
