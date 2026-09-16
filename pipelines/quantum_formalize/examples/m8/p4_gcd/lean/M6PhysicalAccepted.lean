import M6Physical

theorem M6.Physical.conv_add : ∀ (N : ℕ) [NeZero N] (a u v : M6.Physical.Block N), M6.Physical.conv N a (u+v) = M6.Physical.conv N a u + M6.Physical.conv N a v := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (a u v : M6.Physical.Block N), M6.Physical.conv N a (u+v) = M6.Physical.conv N a u + M6.Physical.conv N a v
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst a u v
  funext i
  simp only [M6.Physical.conv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

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

theorem M6.Physical.conv_assoc : ∀ (N : ℕ) [NeZero N] (a b c : M6.Physical.Block N), M6.Physical.conv N a (M6.Physical.conv N b c) = M6.Physical.conv N (M6.Physical.conv N a b) c := by
  classical
  intro N inst a b c
  funext x
  simp only [M6.Physical.conv, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_bij (fun k _ => j + k) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro u hu v hv huv
    exact add_left_cancel huv
  · intro k hk
    refine ⟨k - j, by simp, ?_⟩
    abel
  · intro k hk
    have h₁ : j + k - j = k := by abel
    have h₂ : x - (j + k) = x - j - k := by abel
    simp only [h₁, h₂, mul_assoc]

theorem M6.Physical.conv_comm : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a
  intro N inst a b
  classical
  funext i
  unfold M6.Physical.conv
  refine Finset.sum_bij (fun r _ => i - r) ?_ ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_univ _
  · intro r hr s hs h
    simpa only [sub_sub_cancel] using congrArg (fun t => i - t) h
  · intro r hr
    exact ⟨i - r, Finset.mem_univ _, sub_sub_cancel i r⟩
  · intro r hr
    simp only [sub_sub_cancel, mul_comm]

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

theorem M6.Physical.rev_weight : ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N), M6.Physical.weight N (M6.Physical.rev N a) = M6.Physical.weight N a := by
  change ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N), M6.Physical.weight N (M6.Physical.rev N a) = M6.Physical.weight N a
  intro N inst a
  classical
  unfold M6.Physical.weight M6.Physical.rev
  refine Finset.card_bij (fun i _ => -i) ?_ ?_ ?_
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i hi j hj hij
    exact neg_injective hij
  · intro j hj
    refine ⟨-j, ?_, neg_neg j⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, neg_neg] using hj

theorem M6.Physical.J_involution : ∀ (N : ℕ) (z : M6.Physical.Word N), M6.Physical.J N (M6.Physical.J N z) = z := by
  change ∀ (N : ℕ) (z : M6.Physical.Word N), M6.Physical.J N (M6.Physical.J N z) = z
  intro N z
  rcases z with ⟨a, b⟩
  simp [M6.Physical.J, M6.Physical.rev_involution]

theorem M6.Physical.J_weight : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Physical.wordWeight N (M6.Physical.J N z) = M6.Physical.wordWeight N z := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Physical.wordWeight N (M6.Physical.J N z) = M6.Physical.wordWeight N z
  intro N inst z
  simp [M6.Physical.wordWeight, M6.Physical.J, M6.Physical.rev_weight, Nat.add_comm]

theorem M6.Physical.boundary_cycle : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0 := by
  change ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0
  intro N inst a b h
  unfold M6.Physical.boundary
  unfold M6.Physical.syndrome
  simp only [M6.Physical.conv_assoc, M6.Physical.conv_comm N b a]
  funext i
  exact ZModModule.add_self _

theorem M6.Physical.boundary_pairing : ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.syndrome N a b z) := by
  intro N inst a b h z
  classical
  simp only [M6.Physical.pairing, M6.Physical.J, M6.Physical.boundary,
    Prod.fst, Prod.snd, M6.Physical.conv_adjoint]
  simp [M6.Physical.syndrome, M6.Physical.dot, mul_add,
    Finset.sum_add_distrib, add_comm]

theorem M6.Physical.cycle_orthogonal : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.syndrome N a b z = 0 ↔ ∀ h : M6.Physical.Block N, M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = 0 := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (z : M6.Physical.Word N), M6.Physical.syndrome N a b z = 0 ↔ ∀ h : M6.Physical.Block N, M6.Physical.pairing N (M6.Physical.J N (M6.Physical.boundary N a b h)) z = 0
  intro N inst a b z
  classical
  constructor
  · intro hs h
    rw [M6.Physical.boundary_pairing, hs]
    simp [M6.Physical.dot]
  · intro H
    funext i
    have hi := H (M6.Physical.rev N (M6.Physical.delta N i))
    rw [M6.Physical.boundary_pairing, M6.Physical.rev_involution,
      M6.Physical.dot_delta] at hi
    exact hi
#print axioms M6.Physical.conv_add
#print axioms M6.Physical.conv_adjoint
#print axioms M6.Physical.boundary_pairing
#print axioms M6.Physical.conv_assoc
#print axioms M6.Physical.conv_comm
#print axioms M6.Physical.boundary_cycle
#print axioms M6.Physical.dot_delta
#print axioms M6.Physical.rev_involution
#print axioms M6.Physical.J_involution
#print axioms M6.Physical.cycle_orthogonal
#print axioms M6.Physical.rev_weight
#print axioms M6.Physical.J_weight
