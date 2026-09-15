import FrozenTarget_967d94c28d38aa33
theorem M7.Action.affine_bijective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (s : ZMod N), Function.Bijective (M7.Action.affine u s)
  intro N inst u s
  constructor
  · intro a b h
    change (u : ZMod N) * a + s = (u : ZMod N) * b + s at h
    have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * x) (add_right_cancel h)
    simpa [← mul_assoc] using h'
  · intro y
    refine ⟨(↑(u⁻¹) : ZMod N) * (y - s), ?_⟩
    simp [M7.Action.affine, ← mul_assoc]
