import M7LabelReplay

theorem M7.LabelReplay.check_sound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (r : M7.LabelReplay.Certificate N), M7.LabelReplay.check c r = true → r.signature = M7.RecipeSignature.signature c ∧ (∀ i : Fin (2*N+1), r.coefficients i = (M7.LabelReplay.Q c (M6.Pinned.free (2*N))).coeff i.val) ∧ r.answer = M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ∧ r.pins = M7.LabelReplay.pinData c := by
  intro N inst c r h
  unfold M7.LabelReplay.check at h
  have hEq := of_decide_eq_true h
  subst r
  exact ⟨rfl, fun i => rfl, rfl, rfl⟩

theorem M7.LabelReplay.self_check : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M7.LabelReplay.check c (M7.LabelReplay.expected c) = true := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M7.LabelReplay.check c (M7.LabelReplay.expected c) = true
  intro N _ c
  classical
  simp [M7.LabelReplay.check, M7.LabelReplay.expected]

theorem M7.LabelReplay.trace_recover : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (d : ℕ) (P : M6.Pinned.Pins (2*N)) (xs : List (Fin (2*N))), (M7.LabelReplay.endpoint P (M7.LabelReplay.trace c d P xs), M7.LabelReplay.queryCount (M7.LabelReplay.trace c d P xs)) = M6.Pinned.recover (fun P => (M7.LabelReplay.Q c P).coeff d) P xs := by
  intro N inst c d P xs
  induction xs generalizing P with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [M7.LabelReplay.trace, M6.Pinned.recover]
      rw [← ih]
      simp [M7.LabelReplay.endpoint, M7.LabelReplay.queryCount, Nat.add_comm]

theorem M7.LabelReplay.checked_physical_answer : ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N) (r : M7.LabelReplay.Certificate N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M7.LabelReplay.check c r = true → (r.answer = none ↔ (M7.RecipeSignature.signature c).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), r.answer = some (d,v,k) → M7.DefaultQuery.distance c = some d ∧ v ∈ M7.Transport.LX c ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ c ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N) := by
  intro N w inst c r hA hB h0A h0B hconn hcheck
  have hs := (M7.LabelReplay.check_sound N c r hcheck).2.2.1
  have hp := M7.ClosedSolve.closed_pointwise N w c hA hB h0A h0B hconn
  have ha := hp.2.2.1
  rw [hs]
  constructor
  · exact ha.1
  · intro d k v hv
    have hw := ha.2.2.1
    first
    | specialize hw d k v hv
    | specialize hw d v k hv
    simpa only [M7.DefaultQuery.distance, M7.Transport.distance,
      M6.Final.LX, M6.Final.CX, M6.Final.BX, M6.Final.CZ, M6.Final.BZ,
      M7.Transport.LX, M7.Transport.CX, M7.Transport.BX,
      M7.Transport.LZ, M7.Transport.CZ, M7.Transport.BZ,
      M7.Domain.coefficients_indicator] using hw
#print axioms M7.LabelReplay.check_sound
#print axioms M7.LabelReplay.checked_physical_answer
#print axioms M7.LabelReplay.self_check
#print axioms M7.LabelReplay.trace_recover
