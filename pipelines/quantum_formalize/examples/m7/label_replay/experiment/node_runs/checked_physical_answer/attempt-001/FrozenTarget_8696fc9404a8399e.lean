import M7LabelReplay

theorem M7.LabelReplay.check_sound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (r : M7.LabelReplay.Certificate N), M7.LabelReplay.check c r = true → r.signature = M7.RecipeSignature.signature c ∧ (∀ i : Fin (2*N+1), r.coefficients i = (M7.LabelReplay.Q c (M6.Pinned.free (2*N))).coeff i.val) ∧ r.answer = M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ∧ r.pins = M7.LabelReplay.pinData c := by
  intro N inst c r h
  unfold M7.LabelReplay.check at h
  have hEq := of_decide_eq_true h
  subst r
  exact ⟨rfl, fun i => rfl, rfl, rfl⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N) (r : M7.LabelReplay.Certificate N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M7.LabelReplay.check c r = true → (r.answer = none ↔ (M7.RecipeSignature.signature c).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), r.answer = some (d,v,k) → M7.DefaultQuery.distance c = some d ∧ v ∈ M7.Transport.LX c ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ c ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N)
