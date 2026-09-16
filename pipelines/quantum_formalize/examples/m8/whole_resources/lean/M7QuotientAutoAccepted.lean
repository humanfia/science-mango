import M7QuotientAuto

theorem M7.QuotientAuto.polynomial_substitution : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (p : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (p.comp (Polynomial.X ^ (u : ZMod N).val)) = M7.QuotientAuto.substitution u (M6.Cyclic.image N p) := by
  intro N inst u p
  unfold M7.QuotientAuto.substitution
  rw [M7.CyclicSubstitution.hom_polynomial]
  unfold M6.Cyclic.image
  rw [← AdjoinRoot.aeval_eq]
  simp only [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq,
    Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rfl

theorem M7.QuotientAuto.substitution_root : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u := by
  intro N inst u
  exact M7.CyclicSubstitution.hom_root N u (M7.CyclicSubstitution.point_root N u)

theorem M7.QuotientAuto.substitution_scalars : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (r : ZMod 2), M7.QuotientAuto.substitution u ((AdjoinRoot.of (M6.Cyclic.modulus N)) r) = (AdjoinRoot.of (M6.Cyclic.modulus N)) r := by
  intro N inst u r
  unfold M7.QuotientAuto.substitution M7.CyclicSubstitution.hom
  exact AdjoinRoot.lift_of (M7.CyclicSubstitution.point_root N u)

theorem M7.QuotientAuto.substitution_comp : ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, (M7.QuotientAuto.substitution v).comp (M7.QuotientAuto.substitution u) = M7.QuotientAuto.substitution (v*u) := by
  intro N inst u v
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp only [RingHom.comp_apply, M7.QuotientAuto.substitution_scalars]
  · change M7.QuotientAuto.substitution v (M7.QuotientAuto.substitution u (M7.CyclicSubstitution.rho N)) = M7.QuotientAuto.substitution (v * u) (M7.CyclicSubstitution.rho N)
    rw [M7.QuotientAuto.substitution_root, M7.QuotientAuto.substitution_root]
    change M7.QuotientAuto.substitution v (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) = M7.CyclicSubstitution.point (v * u)
    rw [map_pow, M7.QuotientAuto.substitution_root]
    simpa only [mul_comm] using M7.CyclicSubstitution.point_mul N v u

theorem M7.QuotientAuto.substitution_one : ∀ (N : ℕ) [NeZero N], M7.QuotientAuto.substitution (1 : (ZMod N)ˣ) = RingHom.id (M6.Cyclic.CycleRing N) := by
  intro N inst
  apply AdjoinRoot.ringHom_ext
  · ext r
    exact M7.QuotientAuto.substitution_scalars N (1 : (ZMod N)ˣ) r
  · change M7.QuotientAuto.substitution (1 : (ZMod N)ˣ) (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.rho N
    rw [M7.QuotientAuto.substitution_root, M7.CyclicSubstitution.point_one]

theorem M7.QuotientAuto.substitution_left_inverse : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (x : M6.Cyclic.CycleRing N), M7.QuotientAuto.substitution (u⁻¹) (M7.QuotientAuto.substitution u x) = x := by
  intro N inst u x
  change ((M7.QuotientAuto.substitution (u⁻¹)).comp (M7.QuotientAuto.substitution u)) x = x
  rw [M7.QuotientAuto.substitution_comp N u (u⁻¹), inv_mul_cancel, M7.QuotientAuto.substitution_one N]
  rfl

theorem M7.QuotientAuto.substitution_right_inverse : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (x : M6.Cyclic.CycleRing N), M7.QuotientAuto.substitution u (M7.QuotientAuto.substitution (u⁻¹) x) = x := by
  intro N inst u x
  change ((M7.QuotientAuto.substitution u).comp (M7.QuotientAuto.substitution (u⁻¹))) x = x
  rw [M7.QuotientAuto.substitution_comp N (u⁻¹) u, mul_inv_cancel, M7.QuotientAuto.substitution_one N]
  rfl

theorem M7.QuotientAuto.substitution_bijective : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, Function.Bijective (M7.QuotientAuto.substitution u) := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, Function.Bijective (M7.QuotientAuto.substitution u)
  intro N inst u
  constructor
  · intro x y h
    have h' := congrArg (M7.QuotientAuto.substitution (u⁻¹)) h
    simpa only [M7.QuotientAuto.substitution_left_inverse N u] using h'
  · intro y
    exact ⟨M7.QuotientAuto.substitution (u⁻¹) y, M7.QuotientAuto.substitution_right_inverse N u y⟩
#print axioms M7.QuotientAuto.polynomial_substitution
#print axioms M7.QuotientAuto.substitution_root
#print axioms M7.QuotientAuto.substitution_scalars
#print axioms M7.QuotientAuto.substitution_comp
#print axioms M7.QuotientAuto.substitution_one
#print axioms M7.QuotientAuto.substitution_left_inverse
#print axioms M7.QuotientAuto.substitution_right_inverse
#print axioms M7.QuotientAuto.substitution_bijective
