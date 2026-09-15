import FrozenTarget_a0df3f703bf212e0
theorem M7.ActualPresentation.four_field_order : QuantumHarnessFrozenTarget := by
  intro N _ g h
  have unit_eq (a b : M7.ActualPresentation.UnitKey N) :
      a = b ↔ (a.unit : ZMod N).val = (b.unit : ZMod N).val := by
    constructor
    · rintro rfl
      rfl
    · intro hab
      have hu : a.unit = b.unit := Units.ext (ZMod.val_injective N hab)
      cases a
      cases b
      cases hu
      rfl
  have unit_lt (a b : M7.ActualPresentation.UnitKey N) :
      a < b ↔ (a.unit : ZMod N).val < (b.unit : ZMod N).val := by
    rfl
  simp [M7.ActualPresentation.encode, M7.Presentation.mk,
    Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex,
    Prod.mk.injEq, unit_eq, unit_lt, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    <;> tauto
