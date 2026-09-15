import M6Transfer


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (c : Fin (R+1) → M6.Transfer.Bit) (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.output c (M6.Transfer.memoryAt h i) (h i) = M6.Transfer.cyclicOutput c h i
