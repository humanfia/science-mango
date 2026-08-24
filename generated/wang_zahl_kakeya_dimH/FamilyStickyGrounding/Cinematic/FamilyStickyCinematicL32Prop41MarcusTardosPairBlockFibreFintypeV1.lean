import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1

open FamilyStickyCinematicL32Prop41MarcusTardosPairBlockOccurrenceProductCleanV1

/-! The literal intersection fibre inherits finiteness from the symbol type. -/

noncomputable instance pairBlockFibreFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    (blocksA blocksB : List (List α))
    (ij : Fin blocksA.length × Fin blocksB.length) :
    Fintype {a : α // PairBlockFibre blocksA blocksB ij a} :=
  Fintype.ofFinite _

#print axioms pairBlockFibreFintype

end FamilyStickyCinematicL32Prop41MarcusTardosPairBlockFibreFintypeV1
