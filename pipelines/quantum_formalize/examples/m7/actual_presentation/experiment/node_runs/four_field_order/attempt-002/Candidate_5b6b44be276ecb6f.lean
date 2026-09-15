import FrozenTarget_5b6b44be276ecb6f
theorem M7.ActualPresentation.four_field_order : QuantumHarnessFrozenTarget := by
  intro N inst g h
  have unit_eq (a b : M7.ActualPresentation.UnitKey N) :
      a = b ↔ (a.unit : ZMod N).val = (b.unit : ZMod N).val := by
    constructor
    · rintro rfl
      rfl
    · intro hv
      have hu : a.unit = b.unit := Units.ext ((ZMod.val_injective N) hv)
      cases a
      cases b
      cases hu
      rfl
  have unit_lt (a b : M7.ActualPresentation.UnitKey N) :
      a < b ↔ (a.unit : ZMod N).val < (b.unit : ZMod N).val := Iff.rfl
  simp only [M7.ActualPresentation.encode, M7.Presentation.mk,
    Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex]
  simp [toLex, unit_eq, unit_lt, Fin.ext_iff, Fin.lt_iff_val_lt_val,
    Fin.le_iff_val_le_val]
  <;> tauto
