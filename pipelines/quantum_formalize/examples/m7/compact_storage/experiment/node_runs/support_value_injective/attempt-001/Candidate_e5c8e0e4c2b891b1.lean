import FrozenTarget_e5c8e0e4c2b891b1
theorem M7.CompactStorage.support_value_injective : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], Function.Injective (@M7.CompactStorage.supportBits N) ∧ Function.Injective (@M7.CompactStorage.valueBits N)
  intro N inst
  constructor
  · intro A B h
    apply Finset.ext
    intro x
    have hx := congrFun h (⟨x.val, ZMod.val_lt x⟩ : Fin N)
    have hx' := congrArg (fun b : Bool => b = true) hx
    simpa [M7.CompactStorage.supportBits, ZMod.natCast_zmod_val] using hx'
  · intro x y h
    have hx := congrFun h (⟨x.val, ZMod.val_lt x⟩ : Fin N)
    simpa [M7.CompactStorage.valueBits, ZMod.natCast_zmod_val, eq_comm] using hx
