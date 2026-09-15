import FrozenTarget_f4fa593936d2d1d4
theorem M6.Transfer.memory_forced : QuantumHarnessFrozenTarget := by
  intro R N inst p
  have aux : ∀ (n : ℕ) (hn : n < R) (i : ZMod N),
      p.val.1 i ⟨n, hn⟩ = M6.Transfer.labels p (i - (n + 1 : ℕ)) := by
    intro n
    induction n with
    | zero =>
        intro hn i
        have h := congrFun (p.property (i - 1)) (⟨0, hn⟩ : Fin R)
        simpa [M6.Transfer.shift, M6.Transfer.labels] using h
    | succ n ih =>
        intro hn i
        have h := congrFun (p.property (i - 1)) (⟨n + 1, hn⟩ : Fin R)
        have hs : p.val.1 i ⟨n + 1, hn⟩ =
            p.val.1 (i - 1) ⟨n, by omega⟩ := by
          simpa [M6.Transfer.shift] using h
        rw [hs, ih (by omega) (i - 1)]
        congr 1
        push_cast <;> ring
  intro i j
  exact aux j.val j.isLt i
