import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosRotationSplitNormalFormV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosRotationSplitNormalFormV1

/-! # Exact common-order cut extracted from cyclic intersection reversal -/

theorem exists_commonOrder_split
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    (hreverse : A.IntersectionReverse B) :
    ∃ u v : List symbol,
      A.commonOrder B = u ++ v ∧
        B.commonOrder A = u.reverse ++ v.reverse :=
  exists_append_reverse_append_reverse_of_reverse_isRotated hreverse

theorem split_append_nodup
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    {u v : List symbol}
    (hsplit : A.commonOrder B = u ++ v) :
    (u ++ v).Nodup := by
  rw [← hsplit]
  exact commonOrder_nodup A B

#print axioms exists_commonOrder_split
#print axioms split_append_nodup

end FamilyStickyCinematicL32Prop41MarcusTardosCyclicCommonSplitV1
