import FrozenTarget_3070385fb2b6abce
theorem M6.ActualCSS.J_dot : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (v w : M6.Pinned.Vector (2*N)), M6.Character.dot (M6.Flatten.J N v) (M6.Flatten.J N w) = M6.Character.dot v w
  intro N _ v w
  have hrev (a b : M6.Physical.Block N) :
      M6.Physical.dot N (fun i => a (-i)) (fun i => b (-i)) =
        M6.Physical.dot N a b := by
    change (∑ i : ZMod N, a (-i) * b (-i)) = ∑ i : ZMod N, a i * b i
    exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun _ => rfl)
  have hJ (z t : M6.Physical.Word N) :
      M6.Physical.pairing N (M6.Physical.J N z) (M6.Physical.J N t) =
        M6.Physical.pairing N z t := by
    change M6.Physical.dot N (fun i => z.2 (-i)) (fun i => t.2 (-i)) +
        M6.Physical.dot N (fun i => z.1 (-i)) (fun i => t.1 (-i)) =
      M6.Physical.dot N z.1 t.1 + M6.Physical.dot N z.2 t.2
    rw [hrev, hrev, add_comm]
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_dot, hJ]
  exact (by simpa only [M6.Flatten.flatten_right] using
    (M6.Flatten.flatten_dot N (M6.Flatten.unflatten N v)
      (M6.Flatten.unflatten N w)).symm)
