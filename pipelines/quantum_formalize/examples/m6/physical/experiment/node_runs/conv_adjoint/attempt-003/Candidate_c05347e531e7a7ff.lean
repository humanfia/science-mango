import FrozenTarget_c05347e531e7a7ff
theorem M6.Physical.conv_adjoint : QuantumHarnessFrozenTarget := by
  intro N inst a h u
  classical
  simp only [M6.Physical.dot, M6.Physical.rev, M6.Physical.conv,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r hr
  refine Finset.sum_bij (fun i _ => i + r) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact add_right_cancel hij
  · intro j hj
    refine ⟨j - r, Finset.mem_univ _, ?_⟩
    simp
  · intro i hi
    simp [sub_eq_add_neg, neg_add, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_comm, mul_left_comm]
