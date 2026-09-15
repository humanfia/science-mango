import FrozenTarget_04fa754e51cf007d
theorem M5.BinaryRecovery.recover_positive : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n)
  intro c p n
  induction n generalizing p with
  | zero =>
      intro hs hp
      simpa [M5.BinaryRecovery.recover] using hp
  | succ n ih =>
      intro hs hp
      have hsplit := hs p (by omega)
      have hchild (b : Bool) : ∀ q : List Bool, q.length < (p ++ [b]).length + n → c q = c (q ++ [false]) + c (q ++ [true]) := by
        intro q hq
        apply hs q
        simp only [List.length_append, List.length_cons, List.length_nil] at hq
        omega
      by_cases hf : 0 < c (p ++ [false])
      · simpa [M5.BinaryRecovery.recover, hf] using ih (p ++ [false]) (hchild false) hf
      · have ht : 0 < c (p ++ [true]) := by omega
        simpa [M5.BinaryRecovery.recover, hf] using ih (p ++ [true]) (hchild true) ht
