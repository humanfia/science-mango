import FrozenTarget_3b875a943638fde3
theorem M8.TaggedStore.indexed_write : QuantumHarnessFrozenTarget := by
  change ∀ (start i : ℕ) (bit : Bool) (mem : List Bool), (M8.TaggedStore.write (M8.TaggedStore.address (start + i)) bit (M8.TaggedStore.packFrom start mem)).1 = M8.TaggedStore.packFrom start (mem.set i bit)
  intro start i bit mem
  induction mem generalizing start i with
  | nil =>
      simp [M8.TaggedStore.packFrom, M8.TaggedStore.write]
  | cons b bs ih =>
      cases i with
      | zero =>
          simp [M8.TaggedStore.packFrom, M8.TaggedStore.write,
            (M8.TaggedStore.comparison_exact (M8.TaggedStore.address start) (M8.TaggedStore.address start)).1]
      | succ i =>
          have hne : M8.TaggedStore.address (start + Nat.succ i) ≠ M8.TaggedStore.address start := by
            intro h
            have he := M8.TaggedStore.address_representation.1 h
            omega
          have hc : (M8.TaggedStore.compare (M8.TaggedStore.address (start + Nat.succ i)) (M8.TaggedStore.address start)).1 = false := by
            rw [(M8.TaggedStore.comparison_exact _ _).1]
            simp [hne]
          have hshift : start + Nat.succ i = (start + 1) + i := by omega
          simpa [M8.TaggedStore.packFrom, M8.TaggedStore.write, hc, ← hshift] using
            congrArg (fun s : M8.TaggedStore.Store => (M8.TaggedStore.address start, b) :: s) (ih (start + 1) i)
