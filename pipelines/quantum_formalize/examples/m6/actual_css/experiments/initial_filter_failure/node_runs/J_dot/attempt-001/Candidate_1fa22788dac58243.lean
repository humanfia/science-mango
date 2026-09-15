import FrozenTarget_1fa22788dac58243
theorem M6.ActualCSS.J_dot : QuantumHarnessFrozenTarget := by
  intro N _ v w
  classical
  have hJ (z t : M6.Physical.Word N) :
      M6.Physical.pairing N (M6.Physical.J N z) (M6.Physical.J N t) =
        M6.Physical.pairing N z t := by
    unfold M6.Physical.pairing M6.Physical.J M6.Physical.rev
    simp only [← Finset.sum_add_distrib]
    apply Fintype.sum_equiv (Equiv.neg (ZMod N))
    intro i
    simp [add_comm]
  change M6.Character.dot
      (M6.Flatten.flatten N (M6.Physical.J N (M6.Flatten.unflatten N v)))
      (M6.Flatten.flatten N (M6.Physical.J N (M6.Flatten.unflatten N w))) = _
  rw [M6.Flatten.flatten_dot, hJ]
   rw [← M6.Flatten.flatten_dot, M6.Flatten.flatten_right, M6.Flatten.flatten_right]
