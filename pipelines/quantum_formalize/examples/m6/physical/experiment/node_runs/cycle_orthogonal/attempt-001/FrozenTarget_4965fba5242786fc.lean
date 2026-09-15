import M6Physical

theorem M6.Physical.conv_adjoint : ∀ (N : ℕ) [NeZero N] (a h u : M6.Physical.Block N), M6.Physical.dot N (M6.Physical.rev N (M6.Physical.conv N a h)) u = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.conv N a u) := by
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

theorem M6.Physical.dot_delta : ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N) (i : ZMod N), M6.Physical.dot N (M6.Physical.delta N i) a = a i := by
  change ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N) (i : ZMod N), M6.Physical.dot N (M6.Physical.delta N i) a = a i
  intro N _ a i
  classical
  simp [M6.Physical.dot, M6.Physical.delta, ite_mul]

theorem M6.Physical.rev_involution : ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a := by
  change ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a
  intro N a
  funext i
  simp only [M6.Physical.rev, neg_neg]

theorem M6.Physical.boundary_pairing : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.syndrome N a b z) := by
  intro N inst a b h z
  classical
  simp only [M6.Physical.pairing, M6.Physical.J, M6.Physical.boundary,
    Prod.fst, Prod.snd, M6.Physical.conv_adjoint]
  simp [M6.Physical.syndrome, M6.Physical.dot, mul_add,
    Finset.sum_add_distrib, add_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.syndrome N a b z = 0 ↔ ∀ h : M6.Physical.Block N, M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = 0
