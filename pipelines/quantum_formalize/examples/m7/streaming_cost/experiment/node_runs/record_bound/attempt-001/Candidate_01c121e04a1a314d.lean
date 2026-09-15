import FrozenTarget_01c121e04a1a314d
theorem M7.StreamingCost.record_bound : QuantumHarnessFrozenTarget := by
  intro N inst p a b hp
  have hb : ∀ (n : ℕ) (q : Fin n → M7.StreamingCost.Eval) (c d : ℕ),
      (∀ j, (q j).outer ≤ c ∧ (q j).inner ≤ d) →
      (M7.StreamingCost.allFin n q).outer ≤ n * c ∧
      (M7.StreamingCost.allFin n q).inner ≤ n * d := by
    intro n q c d hq
    simpa only [M7.StreamingCost.allFin] using
      M7.StreamingCost.cursor_bound n q 0 n c d hq
  have h :
      (M7.StreamingCost.allRecords N p).outer ≤
        Fintype.card ((ZMod N)ˣ) * (2 * (N * (N * a))) ∧
      (M7.StreamingCost.allRecords N p).inner ≤
        Fintype.card ((ZMod N)ˣ) * (2 * (N * (N * b))) := by
    unfold M7.StreamingCost.allRecords
    apply hb
    intro u
    apply hb
    intro e
    apply hb
    intro s
    apply hb
    intro t
    exact hp _
  simpa only [M7.StreamingCost.recordCount, pow_two, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using h
