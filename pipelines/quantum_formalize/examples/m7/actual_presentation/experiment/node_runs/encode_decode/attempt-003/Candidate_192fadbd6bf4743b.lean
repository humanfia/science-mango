import FrozenTarget_192fadbd6bf4743b
theorem M7.ActualPresentation.encode_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a : M7.ActualPresentation.Encoded N), M7.ActualPresentation.encode (M7.ActualPresentation.decode a) = a
  intro N inst a
  have h : ∀ s : Fin N, ((s.val : ZMod N).val) = s.val := by
    intro s
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt]
  rcases a with ⟨⟨u, b⟩, s, t⟩
  cases u
  cases b <;>
    simp [M7.ActualPresentation.encode, M7.ActualPresentation.decode,
      M7.Presentation.mk, M7.Presentation.outer,
      M7.Presentation.left, M7.Presentation.right, h] <;> rfl
