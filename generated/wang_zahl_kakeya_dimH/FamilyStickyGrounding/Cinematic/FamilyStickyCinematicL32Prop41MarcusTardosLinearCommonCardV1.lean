import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosLinearCommonCardV1

open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1

/-! # Cardinality of the common order of two nodup linear lists -/

theorem linearOfList_commonOrder_length
    {α : Type*} [DecidableEq α] (C D : List α)
    (hC : C.Nodup) (hD : D.Nodup) :
    ((linearOfList C hC).commonOrder (linearOfList D hD)).length =
      (C.toFinset ∩ D.toFinset).card := by
  change (C.filter fun a => a ∈ D.toFinset).length =
    (C.toFinset ∩ D.toFinset).card
  rw [← List.toFinset_card_of_nodup (hC.filter _)]
  congr 1
  ext a
  simp

#print axioms linearOfList_commonOrder_length

end FamilyStickyCinematicL32Prop41MarcusTardosLinearCommonCardV1
