import FrozenTarget_1be1c3faa3a69ecf
theorem M6.Pinned.decode_unique : QuantumHarnessFrozenTarget := by
  intro m P hP v
  unfold M6.Pinned.assigned at hP
  constructor
  · intro hv
    unfold M6.Pinned.agrees at hv
    funext i
    have ha := hP i
    have hv' := hv i
    cases hi : P i <;> simp_all [M6.Pinned.decode]
  · intro hv
    subst v
    unfold M6.Pinned.agrees
    intro i
    cases hi : P i <;> simp [M6.Pinned.decode, hi]
