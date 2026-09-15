import FrozenTarget_3563a3e8bf5f5acf
theorem M7.DescentTrace.recover_prefix : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), p.IsPrefix (M5.BinaryRecovery.recover c p n)
  intro c p n
  induction n generalizing p with
  | zero =>
      exact ⟨[], by simp [M5.BinaryRecovery.recover]⟩
  | succ n ih =>
      have h (b : Bool) : p.IsPrefix (M5.BinaryRecovery.recover c (p ++ [b]) n) :=
        (show p.IsPrefix (p ++ [b]) from ⟨[b], rfl⟩).trans (ih (p ++ [b]))
      simp only [M5.BinaryRecovery.recover]
      first
      | exact h _
      | split <;> exact h _
