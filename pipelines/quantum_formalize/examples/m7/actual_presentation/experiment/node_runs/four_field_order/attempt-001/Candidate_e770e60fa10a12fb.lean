import FrozenTarget_e770e60fa10a12fb
theorem M7.ActualPresentation.four_field_order : QuantumHarnessFrozenTarget := by
  intro N inst g h
  have eq_le {α : Type*} [PartialOrder α] (a b : α) :
      a = b ↔ a ≤ b ∧ b ≤ a := by
    constructor
    · intro h
      subst b
      exact ⟨le_rfl, le_rfl⟩
    · exact fun h => le_antisymm h.1 h.2
  simp only [M7.ActualPresentation.encode, M7.Presentation.mk,
    Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex, eq_le]
  let a := (g.unit : ZMod N).val
  let b := (h.unit : ZMod N).val
  let s := g.leftShift.val
  let t := h.leftShift.val
  let r := g.rightShift.val
  let u := h.rightShift.val
  change
    ((a < b ∨ (a ≤ b ∧ b ≤ a) ∧ g.exchange < h.exchange) ∨
      ((a < b ∨ (a ≤ b ∧ b ≤ a) ∧ g.exchange ≤ h.exchange) ∧
        (b < a ∨ (b ≤ a ∧ a ≤ b) ∧ h.exchange ≤ g.exchange)) ∧
      (s < t ∨ (s ≤ t ∧ t ≤ s) ∧ r ≤ u)) ↔
    (a < b ∨ (a ≤ b ∧ b ≤ a) ∧
      (g.exchange < h.exchange ∨
        (g.exchange ≤ h.exchange ∧ h.exchange ≤ g.exchange) ∧
        (s < t ∨ (s ≤ t ∧ t ≤ s) ∧ r ≤ u)))
  omega
