import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosReverseListIndexV1

def reverseIndex {symbol : Type*} (order : List symbol)
    (i : Fin order.length) : Fin order.reverse.length :=
  Fin.cast (by simp) i.rev

@[simp]
theorem reverseIndex_val {symbol : Type*} (order : List symbol)
    (i : Fin order.length) :
    (reverseIndex order i).1 = order.length - 1 - i.1 := by
  simp [reverseIndex, Fin.val_rev]
  omega

theorem reverse_get_reverseIndex
    {symbol : Type*} (order : List symbol) (i : Fin order.length) :
    order.reverse.get (reverseIndex order i) = order.get i := by
  rw [List.get_reverse' order (reverseIndex order i) (by
    rw [reverseIndex_val]
    omega)]
  congr
  rw [reverseIndex_val]
  omega

#print axioms reverseIndex
#print axioms reverse_get_reverseIndex

end FamilyStickyCinematicL32Prop41MarcusTardosReverseListIndexV1
