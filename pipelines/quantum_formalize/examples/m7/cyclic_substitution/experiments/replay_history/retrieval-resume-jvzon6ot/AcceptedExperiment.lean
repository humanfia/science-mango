import M7CyclicSubstitution

theorem M7.CyclicSubstitution.hom_polynomial : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u) (p : M6.Cyclic.BinaryPolynomial), M7.CyclicSubstitution.hom u h (M6.Cyclic.image N p) = p.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.point u) := by
  intro N inst u h p
  unfold M7.CyclicSubstitution.hom M6.Cyclic.image
  exact AdjoinRoot.lift_mk h p

theorem M7.CyclicSubstitution.hom_root : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u), M7.CyclicSubstitution.hom u h (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u := by
  intro N inst u h
  unfold M7.CyclicSubstitution.hom M7.CyclicSubstitution.rho
  exact AdjoinRoot.lift_root h
#print axioms M7.CyclicSubstitution.hom_polynomial
#print axioms M7.CyclicSubstitution.hom_root
