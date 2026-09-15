import FrozenTarget_04c3aaaea36e1ad0
theorem M7.ActualPresentation.four_field_order : QuantumHarnessFrozenTarget := by
  intro N inst g h
  have unit_eq : ∀ a b : M7.ActualPresentation.UnitKey N,
      a = b ↔ (a.unit : ZMod N).val = (b.unit : ZMod N).val := by
    intro a b
    constructor
    · intro hab
      subst b
      rfl
    · intro hab
      have hu : a.unit = b.unit := Units.ext (ZMod.val_injective hab)
      cases a
      cases b
      cases hu
      rfl
  have unit_lt : ∀ a b : M7.ActualPresentation.UnitKey N,
      a < b ↔ (a.unit : ZMod N).val < (b.unit : ZMod N).val := by
    intros
    rfl
  simp [M7.ActualPresentation.encode, M7.Presentation.mk,
    Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex,
    Equiv.refl_apply, Prod.mk.injEq, unit_eq, unit_lt,
    Fin.lt_def, Fin.le_def, Fin.ext_iff] <;> tauto
