import M7DescentTrace

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (c : List Bool → ℤ) (p : List Bool) (ss : List M7.DescentTrace.Step), (M7.DescentTrace.check c p ss).1 = true → M7.DescentTrace.endpoint p ss = M5.BinaryRecovery.recover c p ss.length
