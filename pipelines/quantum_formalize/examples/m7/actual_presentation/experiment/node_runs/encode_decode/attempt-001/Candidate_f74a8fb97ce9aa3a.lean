import FrozenTarget_f74a8fb97ce9aa3a
theorem M7.ActualPresentation.encode_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a
  intro N inst a
  have h (s : Fin N) : ((s.val : ZMod N)).val = s.val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt]
  repeat' match goal with
    | x : Prod _ _ ⊢ _ => cases x
    | x : M7.ActualPresentation.UnitKey _ ⊢ _ => cases x
  dsimp [M7.ActualPresentation.encode, M7.ActualPresentation.decode,
    M7.Presentation.mk, M7.Presentation.outer,
    M7.Presentation.left, M7.Presentation.right]
  repeat' first | rfl | apply Prod.ext | apply Fin.ext
  all_goals simp only [h]
