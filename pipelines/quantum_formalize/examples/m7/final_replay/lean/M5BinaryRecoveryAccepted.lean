import M5BinaryRecovery

theorem M5.BinaryRecovery.recover_length : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M5.BinaryRecovery.recover c p n).length = p.length + n
  intro c p n
  induction n generalizing p with
  | zero => simp [M5.BinaryRecovery.recover]
  | succ n ih =>
      simp only [M5.BinaryRecovery.recover]
      split <;> simp [ih, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem M5.BinaryRecovery.recover_positive : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (∀ q : List Bool, q.length < p.length + n → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M5.BinaryRecovery.recover c p n) := by
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

theorem M5.BinaryRecovery.recover_valid : ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m) := by
  change ∀ (c : List Bool → ℤ) (Valid : List Bool → Prop) (m : ℕ), (∀ q : List Bool, q.length < m → c q = c (q ++ [false]) + c (q ++ [true])) → (∀ q : List Bool, q.length = m → 0 < c q → Valid q) → 0 < c [] → (M5.BinaryRecovery.recover c [] m).length = m ∧ Valid (M5.BinaryRecovery.recover c [] m)
  intro c Valid m hs hv hp
  have hlen : (M5.BinaryRecovery.recover c [] m).length = m := by
    simpa only [List.length_nil, Nat.zero_add] using M5.BinaryRecovery.recover_length c [] m
  refine ⟨hlen, hv _ hlen ?_⟩
  apply M5.BinaryRecovery.recover_positive c [] m
  · simpa only [List.length_nil, Nat.zero_add] using hs
  · exact hp
#print axioms M5.BinaryRecovery.recover_length
#print axioms M5.BinaryRecovery.recover_positive
#print axioms M5.BinaryRecovery.recover_valid
