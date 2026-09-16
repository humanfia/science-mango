import FrozenTarget_7ea968095d7ddd60
theorem M8.CoverageFoundation.no_separated : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated c
  intro N inst c hfull hsep
  rcases hsep with ⟨m, q, hm, hq, hN, hcop, hA, hB⟩
  rcases hfull with hAfull | hBfull
  · have hdiv : q ∣ N := ⟨m, by simpa [Nat.mul_comm] using hN⟩
    have hle := M8.CoverageFoundation.coset_direction N c.1 (AddSubgroup.zmultiples (q : ZMod N)) hA
    change M8.CoverageFoundation.direction c.1 = ⊤ at hAfull
    rw [hAfull] at hle
    exact M8.CoverageFoundation.proper_multiples N q hq hdiv (le_antisymm le_top hle)
  · have hdiv : m ∣ N := ⟨q, hN⟩
    have hle := M8.CoverageFoundation.coset_direction N c.2 (AddSubgroup.zmultiples (m : ZMod N)) hB
    change M8.CoverageFoundation.direction c.2 = ⊤ at hBfull
    rw [hBfull] at hle
    exact M8.CoverageFoundation.proper_multiples N m hm hdiv (le_antisymm le_top hle)
