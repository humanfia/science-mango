import M6Transfer

theorem M6.Transfer.memory_follows : ∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h := by
  change ∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h
  intro R N inst h
  unfold M6.Transfer.Follows
  intro i
  funext j
  by_cases hj : j.val = 0
  · simp [M6.Transfer.memoryAt, M6.Transfer.shift, hj]
  · simp only [M6.Transfer.memoryAt, M6.Transfer.shift, dif_neg hj]
    apply congrArg h
    have hp : j.val - 1 + 1 = j.val := by omega
    rw [hp, Nat.cast_add, Nat.cast_one]
    ring

theorem M6.Transfer.shift_coordinates : ∀ (R : ℕ) (m : M6.Transfer.Memory (R+1)) (t : M6.Transfer.Bit), M6.Transfer.shift m t 0 = t ∧ ∀ j : Fin R, M6.Transfer.shift m t j.succ = m j.castSucc := by
  intro R m t
  constructor
  · rfl
  · intro j
    unfold M6.Transfer.shift
    split
    · rename_i h
      change j.val + 1 = 0 at h
      omega
    · apply congrArg m
      apply Fin.ext
      simp

theorem M6.Transfer.memory_forced : ∀ (R N : ℕ) [NeZero N] (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) (j : Fin R), p.val.1 i j = M6.Transfer.labels p (i - (j.val + 1 : ℕ)) := by
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

theorem M6.Transfer.labels_bijective : ∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N) := by
  change ∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N)
  intro R N inst
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      rw [M6.Transfer.memory_forced R N p i j,
        M6.Transfer.memory_forced R N q i j, hpq]
    · exact hpq
  · intro h
    exact ⟨⟨(M6.Transfer.memoryAt h, h), M6.Transfer.memory_follows R N h⟩, rfl⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ZMod N → M6.Transfer.Memory R → M6.Transfer.Bit → K), (∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i (p.val.1 i) (M6.Transfer.labels p i)) = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i (M6.Transfer.memoryAt h i) (h i)
