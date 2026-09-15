import M7DescentTrace

theorem M7.DescentTrace.check_bound : ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).2 ≤ 2*ss.length := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).2 ≤ 2 * ss.length
  intro c p ss
  induction ss generalizing p with
  | nil => simp [M7.DescentTrace.check]
  | cons s ss ih =>
      simp only [M7.DescentTrace.check, List.length_cons]
      split
      · dsimp only
        have h := ih (p ++ [s.bit])
        omega
      · dsimp only
        omega

theorem M7.DescentTrace.check_trace : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.check c p (M7.DescentTrace.trace c p n) = (true,2*n) := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.check c p (M7.DescentTrace.trace c p n) = (true, 2 * n)
  intro c p n
  induction n generalizing p with
  | zero =>
      simp [M7.DescentTrace.trace, M7.DescentTrace.check]
  | succ n ih =>
      simp [M7.DescentTrace.trace, M7.DescentTrace.check, ih, Nat.mul_succ, Nat.add_comm]

theorem M7.DescentTrace.check_unique : ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → ss = M7.DescentTrace.trace c p ss.length := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → ss = M7.DescentTrace.trace c p ss.length
  intro c p ss
  induction ss generalizing p with
  | nil =>
      intro h
      rfl
  | cons s ss ih =>
      intro h
      rcases s with ⟨a, b, z, o⟩
      simp only [M7.DescentTrace.check] at h
      split at h
      · rename_i hg
        simp only [Bool.and_eq_true, beq_iff_eq] at hg
        rcases hg with ⟨⟨⟨ha, hz⟩, ho⟩, hb⟩
        subst a
        subst z
        subst o
        subst b
        change (M7.DescentTrace.check c (p ++ [M7.DescentTrace.choose (c (p ++ [false]))]) ss).1 = true at h
        change M7.DescentTrace.Step.mk p (M7.DescentTrace.choose (c (p ++ [false]))) (c (p ++ [false])) (c (p ++ [true])) :: ss = M7.DescentTrace.Step.mk p (M7.DescentTrace.choose (c (p ++ [false]))) (c (p ++ [false])) (c (p ++ [true])) :: M7.DescentTrace.trace c (p ++ [M7.DescentTrace.choose (c (p ++ [false]))]) ss.length
        exact congrArg (List.cons _) (ih _ h)
      · cases h

theorem M7.DescentTrace.endpoint_recover : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.endpoint p (M7.DescentTrace.trace c p n) = M5.BinaryRecovery.recover c p n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), M7.DescentTrace.endpoint p (M7.DescentTrace.trace c p n) = M5.BinaryRecovery.recover c p n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      by_cases h : 0 < c (p ++ [false])
      · simpa [M7.DescentTrace.trace, M7.DescentTrace.endpoint, M7.DescentTrace.choose, M5.BinaryRecovery.recover, h] using ih (p ++ [false])
      · simpa [M7.DescentTrace.trace, M7.DescentTrace.endpoint, M7.DescentTrace.choose, M5.BinaryRecovery.recover, h] using ih (p ++ [true])

theorem M7.DescentTrace.recover_prefix : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), p.IsPrefix (M5.BinaryRecovery.recover c p n) := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), p.IsPrefix (M5.BinaryRecovery.recover c p n)
  intro c p n
  induction n generalizing p with
  | zero =>
      exact ⟨[], by simp [M5.BinaryRecovery.recover]⟩
  | succ n ih =>
      have h (b : Bool) : p.IsPrefix (M5.BinaryRecovery.recover c (p ++ [b]) n) :=
        (show p.IsPrefix (p ++ [b]) from ⟨[b], rfl⟩).trans (ih (p ++ [b]))
      simp only [M5.BinaryRecovery.recover]
      first
      | exact h _
      | split <;> exact h _

theorem M7.DescentTrace.trace_length : ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.DescentTrace.trace c p n).length = n := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.DescentTrace.trace c p n).length = n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp only [M7.DescentTrace.trace, List.length_cons, ih]

theorem M7.DescentTrace.checked_endpoint : ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → M7.DescentTrace.endpoint p ss = M5.BinaryRecovery.recover c p ss.length := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → M7.DescentTrace.endpoint p ss = M5.BinaryRecovery.recover c p ss.length
  intro c p ss h
  exact (congrArg (M7.DescentTrace.endpoint p) (M7.DescentTrace.check_unique c p ss h)).trans (M7.DescentTrace.endpoint_recover c p ss.length)

theorem M7.DescentTrace.positive_checked : ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → (∀ q : List Bool, q.length < p.length + ss.length → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M7.DescentTrace.endpoint p ss) := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → (∀ q : List Bool, q.length < p.length + ss.length → c q = c (q ++ [false]) + c (q ++ [true])) → 0 < c p → 0 < c (M7.DescentTrace.endpoint p ss)
  intro c p ss hcheck hpartition hpositive
  rw [M7.DescentTrace.checked_endpoint c p ss hcheck]
  exact M5.BinaryRecovery.recover_positive c p ss.length hpartition hpositive
#print axioms M7.DescentTrace.check_bound
#print axioms M7.DescentTrace.check_trace
#print axioms M7.DescentTrace.check_unique
#print axioms M7.DescentTrace.endpoint_recover
#print axioms M7.DescentTrace.checked_endpoint
#print axioms M7.DescentTrace.positive_checked
#print axioms M7.DescentTrace.recover_prefix
#print axioms M7.DescentTrace.trace_length
