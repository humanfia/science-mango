import FrozenTarget_071844c5a76e8cf8
theorem M5.ResidueRecovery.pick_bound : QuantumHarnessFrozenTarget := by
  change ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length
  intro T f xs
  induction xs with
  | nil => simp [M5.ResidueRecovery.pick]
  | cons x xs ih =>
      simp only [M5.ResidueRecovery.pick, List.length_cons]
      split
      · simp
      · cases h : M5.ResidueRecovery.pick f xs with
        | mk result cost =>
            simp_all only [Prod.snd] <;> omega
