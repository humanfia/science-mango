import M6Transfer

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (p : M6.Transfer.ClosedWalk R N) (i : ZMod N) (j : Fin R), p.val.1 i j = M6.Transfer.labels p (i - (j.val + 1 : ℕ))
